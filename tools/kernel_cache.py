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
		self.env=os.environ.copy()
		self.env.pop("QSYM_PROOF_CACHE",None)
		self.version=subprocess.run(command+["--version"],cwd=root/"lean",env=self.env,
			check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True).stdout

	def key(self,path,source):
		return digest(json.dumps([self.version,str(path.relative_to(self.root)),digest(source)]).encode())

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
		compiled=self.directory/(key+".olean")
		try:
			record=json.loads((self.directory/(key+".json")).read_text())
			if record!={"version":self.version,"source":digest(source),"olean":digest(compiled.read_bytes())}:
				return None
		except (OSError,ValueError,TypeError):
			return None
		return compiled

	def recheck(self,paths,jobs):
		candidates=[(path,self.candidate(path)) for path in paths]
		candidates=[pair for pair in candidates if pair[1] is not None]
		def run(group):
			before={path:path.read_bytes() for path,_ in group}
			if any(compiled.stem!=self.key(path,before[path]) for path,compiled in group):
				raise RuntimeError("certificate changed before replay")
			try:
				completed=subprocess.run(self.command+["--run",str(self.root/"tools/recheck.lean")]+
					[str(compiled) for _,compiled in group],cwd=self.root/"lean",env=self.env,
					stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180*len(group))
				if completed.returncode:
					return []
				records=[json.loads(line) for line in completed.stdout.splitlines()]
				if [r.get("path") for r in records]!=[str(c) for _,c in group]:
					return []
			except (subprocess.TimeoutExpired,ValueError,AttributeError):
				return []
			checked=[]
			for (path,_),record in zip(group,records):
				if path.read_bytes()!=before[path]:
					raise RuntimeError("certificate changed during replay: "+str(path))
				if record.get("ok") is True and isinstance(record.get("declarations"),int) and record["declarations"]>0:
					print("kernel rechecked "+path.name,flush=True)
					checked.append(path)
				else:
					print("Cached terms need re-elaboration: "+path.name,flush=True)
			return checked
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
