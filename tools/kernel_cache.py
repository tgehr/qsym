"""Cache elaborated terms; replay every declaration through the current Lean kernel."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
import pathlib
import re
import subprocess
import tempfile

def digest(data):
	return hashlib.sha256(data).hexdigest()

class KernelCache:
	def __init__(self,root,command):
		self.root=root
		self.command=command
		self.directory=root/"build/kernel-cache"
		self.directory.mkdir(parents=True,exist_ok=True)
		self.digests={}
		self.env=os.environ.copy()
		self.env.pop("QSYM_PROOF_CACHE",None)
		self.version=subprocess.run(command+["--version"],cwd=root/"lean",env=self.env,
			check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True).stdout

	def key(self,path,source):
		# Module filenames are not mathematical inputs. Replaying under the current
		# environment also checks any filename-dependent private declarations.
		return digest(json.dumps([self.version,digest(source)]).encode())

	def entry(self,key,source):
		if not re.fullmatch(r"[0-9a-f]{64}",key):
			return None
		compiled=self.directory/(key+".olean")
		try:
			record=json.loads((self.directory/(key+".json")).read_text())
			if record!={"version":self.version,"source":source,"olean":self.file_digest(compiled)}:
				return None
		except (OSError,ValueError,TypeError):
			return None
		return compiled

	def file_digest(self,path):
		# Many individual receipts refer to one module. Hash its bytes once while
		# its identity and modification metadata stay unchanged; never cache the
		# kernel's verdict. Replacements and in-place edits invalidate this memo.
		def signature():
			s=path.stat()
			return s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns
		before=signature()
		if path in self.digests and self.digests[path][0]==before:
			return self.digests[path][1]
		value=digest(path.read_bytes())
		if signature()!=before:
			raise OSError("cache module changed while hashing")
		self.digests[path]=(before,value)
		return value

	def output(self):
		return tempfile.TemporaryDirectory(prefix="compile-",dir=self.directory)

	def store(self,path,source,compiled):
		if path.read_bytes()!=source:
			raise RuntimeError("certificate changed during checking: "+str(path))
		key=self.key(path,source)
		data=compiled.read_bytes()
		with tempfile.NamedTemporaryFile(dir=self.directory,delete=False) as out:
			out.write(data)
		os.replace(out.name,self.directory/(key+".olean"))
		record={"version":self.version,"source":digest(source),"olean":digest(data)}
		with tempfile.NamedTemporaryFile(mode="w",dir=self.directory,delete=False) as out:
			json.dump(record,out)
		os.replace(out.name,self.directory/(key+".json"))

	def candidate(self,path):
		source=path.read_bytes()
		# Both exporter import sets are supplied by the shared QSym environment.
		imports=re.findall(rb"^import ([^\n]+)",source,re.M)
		if imports not in ([b"QSym"],[b"QSym.Sum",b"QSym.AxiomCheck"]):
			return None
		key=self.key(path,source)
		legacy=digest(json.dumps([self.version,str(path.relative_to(self.root)),digest(source)]).encode())
		for direct in (key,legacy):
			compiled=self.entry(direct,digest(source))
			if compiled is not None:
				return compiled
		try:
			record=json.loads((self.directory/(key+".member.json")).read_text())
			if set(record)!={"version","source","module","module_source"} or record["version"]!=self.version or record["source"]!=digest(source):
				return None
			return self.entry(record["module"],record["module_source"])
		except (OSError,ValueError,TypeError,KeyError):
			return None

	def remember_members(self,path,source,members):
		# Called only for a successfully checked batch assembled from these exact
		# source snapshots. Reuse still replays the entire module, never a verdict.
		if path.read_bytes()!=source:
			raise RuntimeError("batch changed during checking: "+str(path))
		compiled=self.candidate(path)
		if compiled is None:
			raise RuntimeError("checked batch has no valid cache entry: "+str(path))
		for file,original in members:
			if file.read_bytes()!=original:
				raise RuntimeError("certificate changed during batch checking: "+str(file))
			record={"version":self.version,"source":digest(original),"module":compiled.stem,"module_source":digest(source)}
			with tempfile.NamedTemporaryFile(mode="w",dir=self.directory,delete=False) as out:
				json.dump(record,out)
			os.replace(out.name,self.directory/(self.key(file,original)+".member.json"))

	def recheck(self,paths,jobs):
		candidates={}
		for path in paths:
			compiled=self.candidate(path)
			if compiled is not None:
				candidates.setdefault(compiled,[]).append(path)
		def run(group):
			before={path:path.read_bytes() for _,files in group for path in files}
			if any(self.candidate(path)!=compiled for compiled,files in group for path in files):
				raise RuntimeError("certificate changed before replay")
			try:
				completed=subprocess.run(self.command+["--run",str(self.root/"tools/recheck.lean")]+
					[str(compiled) for compiled,_ in group],cwd=self.root/"lean",env=self.env,
					stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=180*len(group))
				if completed.returncode:
					return []
				records=[json.loads(line) for line in completed.stdout.splitlines()]
				if [r.get("path") for r in records]!=[str(c) for c,_ in group]:
					return []
			except (subprocess.TimeoutExpired,ValueError,AttributeError):
				return []
			checked=[]
			for (compiled,files),record in zip(group,records):
				for path in files:
					if path.read_bytes()!=before[path] or self.candidate(path)!=compiled:
						raise RuntimeError("certificate or cache changed during replay: "+str(path))
				if record.get("ok") is True and isinstance(record.get("declarations"),int) and record["declarations"]>0:
					print(f"kernel rechecked {len(files)} certificate(s) from {compiled.name}",flush=True)
					checked.extend(files)
				else:
					print("Cached terms need re-elaboration: "+", ".join(path.name for path in files),flush=True)
			return checked
		candidates=list(candidates.items())
		groups=[candidates[i:i+16] for i in range(0,len(candidates),16)]
		with ThreadPoolExecutor(max_workers=jobs) as pool:
			return {path for group in pool.map(run,groups) for path in group}

def compiled_rules(source):
	# Re-elaborate every current statement and compare it with the compiled law.
	# The bodies were checked by the build; do not repeat their tactic search.
	pattern=r"theorem (\w+)(.*?) :\n    (.*?) := (?:qsym_cached% )?by\n.*?(?=\n#qsym_check_axioms)"
	entries=re.findall(pattern,source,re.S)
	names=re.findall(r"^theorem (\w+)",source,re.M)
	if not names or [name for name,_,_ in entries]!=names or len(set(names))!=len(names):
		raise RuntimeError("could not audit every generated rule statement")
	parts=["import QSym\nnamespace QSym.CurrentRules"]
	for name,binders,statement in entries:
		quantifier="∀"+binders+",\n    " if binders.strip() else ""
		parts.append(f"theorem {name} :\n    {quantifier}{statement} :=\n  @QSym.Generated.{name}\n"
			f"#qsym_check_axioms {name}\n")
	return "\n".join(parts)+"\nend QSym.CurrentRules\n"
