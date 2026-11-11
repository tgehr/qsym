#!/usr/bin/env python3
import argparse
import json
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"tools"))
from kernel_cache import KernelCache,compiled_rules
from certificate_batches import make_batches

def main():
	parser=argparse.ArgumentParser()
	parser.add_argument("--lake",default="lake")
	parser.add_argument("--lean")
	args=parser.parse_args()
	command=[args.lean] if args.lean else [args.lake,"env","lean"]
	directory=ROOT/"build/cache-tests"
	directory.mkdir(parents=True,exist_ok=True)
	env=os.environ.copy(); env.pop("QSYM_PROOF_CACHE",None)
	def lean(name,source,succeeds=True,cache=None,compile=False):
		path=directory/(name+".lean"); path.write_text(source)
		options=["-R",str(ROOT),"-o",str(path.with_suffix(".olean"))] if compile else []
		current=env.copy()
		if cache:
			current["QSYM_PROOF_CACHE"]=str(cache)
		result=subprocess.run(command+options+[str(path)],cwd=ROOT/"lean",env=current,
			stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
		assert (result.returncode==0)==succeeds,(name,result.stdout)
		if not succeeds:
			assert any(x in result.stdout for x in ("cached proof does not check","unexpected axioms","type mismatch","missing cache dependency")),result.stdout
		return path,result.stdout

	seed="""import QSym
namespace QSym.CacheFixture
def anchor : Nat := 1
private theorem auxiliary (n : Nat) : n = n := rfl
theorem reused (n : Nat) : n = n := auxiliary n
theorem changed (n : Nat) : n = n := rfl
theorem anchor_eq : anchor = 1 := rfl
theorem truth : True := True.intro
end QSym.CacheFixture
"""
	path,_=lean("Seed",seed,compile=True)
	cached=path.with_suffix(".olean")
	positive="""import QSym
namespace QSym.CacheFixture
def anchor : Nat := 1
theorem reused (n : Nat) : n = n := by qsym_cached
#qsym_check_axioms reused
theorem changed (n : Nat) : n + 1 = 1 + n := qsym_cached% by omega
#qsym_check_axioms changed
theorem anchor_eq : anchor = 1 := by qsym_cached
#qsym_check_axioms anchor_eq
end QSym.CacheFixture
"""
	_,output=lean("Reuse",positive,cache=cached)
	assert output.count("rechecked cached proof")==2,output
	lean("ChangedStatement",positive.replace("n = n := by qsym_cached","n = 0 := by qsym_cached"),False,cached)
	lean("ChangedDependency",positive.replace("anchor : Nat := 1","anchor : Nat := 2"),False,cached)
	lean("NoCache",positive.replace("by qsym_cached","qsym_cached% by rfl"))
	lean("MissingCache",positive.replace("by qsym_cached","qsym_cached% by rfl"),cache=directory/"missing.olean")
	sorry,_=lean("SorrySeed","import QSym\nnamespace QSym.CacheFixture\ntheorem truth : True := by sorry\nend QSym.CacheFixture\n",compile=True)
	lean("CachedSorry","import QSym\nnamespace QSym.CacheFixture\ntheorem truth : True := by qsym_cached\n#qsym_check_axioms truth\nend QSym.CacheFixture\n",False,sorry.with_suffix(".olean"))

	mutator=directory/"Mutate.lean"
	mutator.write_text("""import Lean
open Lean
def main (args : List String) : IO Unit := do
  let (data, _region) ← readModuleData args[0]!
  for mode in ["wrongType", "wrongValue", "cycle", "missing", "axiom", "duplicate", "reverse"] do
    let mut constants := data.constants.map fun c => match c with
      | .thmInfo v =>
        if v.name == `QSym.CacheFixture.truth then
          if mode == "wrongType" then .thmInfo { v with type := mkConst ``False }
          else if mode == "cycle" then .thmInfo { v with value := mkConst v.name }
          else c
        else if v.name == `QSym.CacheFixture.changed && mode == "missing" then
          .thmInfo { v with type := mkConst ``True, value := mkConst `QSym.CacheFixture.truth }
        else c
      | .defnInfo v =>
        if v.name == `QSym.CacheFixture.anchor && mode == "wrongValue" then
          .defnInfo { v with value := mkNatLit 2 }
        else c
      | _ => c
    if mode == "missing" then
      constants := constants.filter fun c => c.name != `QSym.CacheFixture.truth
    if mode == "axiom" then
      constants := constants.push (.axiomInfo { name := `QSym.CacheFixture.forged, levelParams := [], type := mkConst ``False, isUnsafe := false })
    if mode == "duplicate" then constants := constants.push constants[0]!
    if mode == "reverse" then constants := constants.reverse
    saveModuleData (args[1]! ++ "/" ++ mode ++ ".olean") `Mutated
      { data with constants, constNames := constants.map (·.name) }
""")
	subprocess.run(command+["--run",str(mutator),str(cached),str(directory)],cwd=ROOT/"lean",env=env,check=True,timeout=180)
	modules=[cached]+[directory/(mode+".olean") for mode in ("wrongType","wrongValue","cycle","missing","axiom","duplicate","reverse")]+[sorry.with_suffix(".olean"),cached]
	result=subprocess.run(command+["--run",str(ROOT/"tools/recheck.lean")]+list(map(str,modules)),
		cwd=ROOT/"lean",env=env,check=True,stdout=subprocess.PIPE,text=True,timeout=180)
	records=[json.loads(line) for line in result.stdout.splitlines()]
	assert [r["ok"] for r in records]==[True,False,False,False,False,False,False,True,False,True],records

	# Receipts bind exact source bytes, toolchain identity, and compiled bytes.
	with tempfile.TemporaryDirectory(dir=directory) as temporary:
		root=pathlib.Path(temporary); (root/"lean").symlink_to(ROOT/"lean",target_is_directory=True)
		cache=KernelCache(root,command)
		file=root/"Case.lean"; file.write_text("import QSym\ntheorem test : True := True.intro\n")
		compiled=root/"Case.olean"; compiled.write_bytes(cached.read_bytes())
		source=file.read_bytes(); cache.store(file,source,compiled)
		candidate=cache.candidate(file); assert candidate is not None
		for imports,accepted in (("QSym.Sum\nimport QSym.AxiomCheck",True),("Mathlib",False)):
			file.write_text("import "+imports+"\ntheorem test : True := True.intro\n")
			cache.store(file,file.read_bytes(),compiled)
			assert (cache.candidate(file) is not None)==accepted
		file.write_bytes(source)
		file.write_bytes(source+b"-- changed\n"); assert cache.candidate(file) is None
		file.write_bytes(source); candidate.write_bytes(b"corrupt"); assert cache.candidate(file) is None
		cache.store(file,source,compiled)
		candidate=cache.candidate(file); data=candidate.read_bytes(); before=candidate.stat()
		candidate.write_bytes(bytes([data[0]^1])+data[1:])
		os.utime(candidate,ns=(before.st_atime_ns,before.st_mtime_ns))
		assert cache.candidate(file) is None,"same-size edits must invalidate the hash memo"
		cache.store(file,source,compiled)
		candidate.with_suffix(".json").write_text("{}"); assert cache.candidate(file) is None
		cache.store(file,source,compiled)
		cache.version+="changed"; assert cache.candidate(file) is None
		try:
			cache.store(file,b"old source",compiled)
		except RuntimeError:
			pass
		else:
			raise AssertionError("accepted a source change during compilation")

	# Adding or moving a certificate must not discard its neighbors' proofs.
	# Replay the actual batched declarations after changing both batch size and
	# membership, then verify exact-source and receipt corruption boundaries.
	cache=KernelCache(ROOT,command)
	member_dir=directory/"members"; member_dir.mkdir(exist_ok=True)
	files=[]
	for name,body in (("A","True := True.intro"),("C","(1 : Nat) = 1 := rfl")):
		file=member_dir/(name+".lean")
		file.write_text("import QSym\nnamespace QSym.Certificate\ntheorem result : "+body+"\n#qsym_check_axioms result\nend QSym.Certificate\n")
		files.append(file)
	checks,members=make_batches(ROOT,files,2)
	assert len(checks)==1
	batch=checks[0]; original=batch.read_bytes()
	compiled,_=lean("MemberBatch",original.decode(),compile=True)
	cache.store(batch,original,compiled.with_suffix(".olean"))
	cache.remember_members(batch,original,members[batch])
	assert cache.recheck(files,1)==set(files)
	inserted=member_dir/"B.lean"
	inserted.write_bytes(files[0].read_bytes().replace(b"True := True.intro",b"(2 : Nat) = 2 := rfl"))
	assert cache.recheck([files[0],inserted,files[1]],1)==set(files)
	assert make_batches(ROOT,[files[0],inserted,files[1]],1)[0]==[files[0],inserted,files[1]]
	moved=member_dir/"Renamed.lean"; moved.write_bytes(files[0].read_bytes())
	assert cache.recheck([moved],1)=={moved}
	unchanged=files[0].read_bytes()
	files[0].write_bytes(unchanged.replace(b"True := True.intro",b"False := True.intro"))
	assert cache.recheck(files,1)=={files[1]}
	try:
		cache.remember_members(batch,original,members[batch])
	except RuntimeError:
		pass
	else:
		raise AssertionError("accepted a constituent source change")
	files[0].write_bytes(unchanged)
	receipt=cache.directory/(cache.key(files[0],unchanged)+".member.json")
	record=json.loads(receipt.read_text())
	for key,value in (("source","0"*64),("module_source","0"*64),("module","../escape"),("version","wrong")):
		receipt.write_text(json.dumps({**record,key:value}))
		assert cache.candidate(files[0]) is None
	receipt.write_text(json.dumps(record))
	assert cache.recheck(files,1)==set(files)

	generated=(ROOT/"lean/QSym/Generated.lean").read_text()
	first=generated[generated.index("theorem "):generated.index("\ntheorem ",generated.index("theorem ")+1)]
	lean("CurrentStatement",compiled_rules(first))
	wrong=first.replace("v_x := qsym_cached%", "(some (1 : ℝ)) := qsym_cached%",1)
	assert wrong!=first
	lean("StaleStatement",compiled_rules(wrong),False)
	for malformed in ("",first+first,first.replace(" := qsym_cached% by"," := missing")):
		try:
			compiled_rules(malformed)
		except RuntimeError:
			pass
		else:
			raise AssertionError("accepted malformed generated rules")
	print("Verification cache checks passed.",flush=True)

if __name__=="__main__":
	main()
