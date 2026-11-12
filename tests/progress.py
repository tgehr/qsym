#!/usr/bin/env python3
import argparse
import contextlib
import io
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import threading

ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"tools"))
from lean_progress import Progress,run_build

def main():
	parser=argparse.ArgumentParser()
	parser.add_argument("--lake",default="lake")
	args=parser.parse_args()
	lake=shutil.which(args.lake) or str(pathlib.Path(args.lake).resolve())
	directory=ROOT/"build/progress-tests"
	directory.mkdir(parents=True,exist_ok=True)
	with tempfile.TemporaryDirectory(dir=directory) as temporary:
		root=pathlib.Path(temporary)
		(root/"QSym").mkdir()
		for name in ("Progress","ProofCache","AxiomCheck"):
			shutil.copyfile(ROOT/f"lean/QSym/{name}.lean",root/f"QSym/{name}.lean")
		shutil.copyfile(ROOT/"lean/lean-toolchain",root/"lean-toolchain")
		(root/"lakefile.toml").write_text('name = "progress_test"\ndefaultTargets = ["Fixture"]\n[[lean_lib]]\nname = "QSym"\n[[lean_lib]]\nname = "Fixture"\n')
		fixture=root/"Fixture.lean"
		prefix='''import QSym.ProofCache
import QSym.AxiomCheck
open Lean Elab Tactic
elab "pause" : tactic => do IO.sleep 2500
namespace QSym.Generated
'''
		def source(n):
			return prefix+f'''theorem r_slow : ({n} : Nat) = {n} := qsym_cached% by pause; rfl
#qsym_check_axioms r_slow
theorem r_reused : True := qsym_cached% by trivial
#qsym_check_axioms r_reused
end QSym.Generated
'''
		runner=root/"run.py"
		runner.write_text("import os,sys\nsys.path.insert(0,"+repr(str(ROOT/"tools"))+")\nfrom lean_progress import run_build\nraise SystemExit(run_build("+repr([lake,"--no-ansi","build"])+","+repr(str(root))+",os.environ,sys.argv[1],2,0.1))\n")
		counter=0
		def run(cancel=False,cache=None):
			nonlocal counter
			counter+=1
			path=root/f"events-{counter}.jsonl"; path.touch()
			env=os.environ.copy(); env.pop("QSYM_PROOF_CACHE",None)
			env["QSYM_PROGRESS_FILE"]=str(path)
			if cache: env["QSYM_PROOF_CACHE"]=str(cache)
			p=subprocess.Popen([sys.executable,str(runner),str(path)],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
			lines=[]; active=threading.Event()
			def read():
				for line in p.stdout:
					lines.append(line)
					if "active: QSym.Generated.r_slow" in line: active.set()
			t=threading.Thread(target=read);t.start()
			try:
				if cancel:
					assert active.wait(30),"no live rule progress before cancellation"
					p.terminate()
				p.wait(timeout=60)
			finally:
				if p.poll() is None: p.kill(); p.wait()
				t.join(timeout=10)
			output="".join(lines)
			(directory/f"run-{counter}.log").write_text(output)
			records=[json.loads(line) for line in path.read_text().splitlines()]
			(directory/f"events-{counter}.jsonl").write_text(path.read_text())
			return p.returncode,output,records
		fixture.write_text(source(1))
		code,output,records=run()
		assert code==0,output
		assert output.index("active: QSym.Generated.r_slow")<output.index("Built Fixture"),output
		assert "2 rule checks observed" in output and "slow rule: QSym.Generated.r_slow" in output,output
		assert [r["name"] for r in records if r["event"]=="checked"]==["QSym.Generated.r_slow","QSym.Generated.r_reused"],records
		code,output,records=run()
		assert code==0 and not records and "0 rule checks observed" in output,output
		cache=root/"Seed.olean";shutil.copyfile(root/".lake/build/lib/lean/Fixture.olean",cache)
		fixture.write_text(source(2))
		code,output,records=run(cache=cache)
		assert code==0,output
		assert "rechecked cached proof" in output,output
		assert any(r["name"]=="QSym.Generated.r_slow" and r["event"]=="tactics" for r in records),records
		assert not any(r["name"]=="QSym.Generated.r_reused" and r["event"]=="tactics" for r in records),records
		for proof,message in (("exact True.intro","type mismatch"),("sorry","unexpected axioms")):
			fixture.write_text(prefix+f"theorem r_bad : False := qsym_cached% by {proof}\n#qsym_check_axioms r_bad\nend QSym.Generated\n")
			code,output,records=run(cache=cache)
			assert code!=0 and message in output and "build failed" in output,output
			assert not any(r["event"]=="checked" for r in records),records
		poison=root/"Poison.lean"
		poison.write_text("import QSym.ProofCache\nnamespace QSym.Generated\ntheorem r_reused : True := by sorry\nend QSym.Generated\n")
		subprocess.run([lake,"env","lean","-o",str(poison.with_suffix(".olean")),str(poison)],cwd=root,check=True,capture_output=True,timeout=30)
		fixture.write_text(prefix+"theorem r_reused : True := by qsym_cached\n#qsym_check_axioms r_reused\nend QSym.Generated\n")
		code,output,records=run(cache=poison.with_suffix(".olean"))
		assert code!=0 and "unexpected axioms" in output,output
		assert any(r["event"]=="cache" for r in records) and not any(r["event"]=="checked" for r in records),records
		if os.name=="posix":
			fixture.write_text(source(3).replace("IO.sleep 2500","IO.sleep 60000"))
			code,output,records=run(cancel=True)
			assert code==143 and "build failed (exit 143)" in output,output
			assert not any(r["event"]=="checked" for r in records),records
			path=root/"signal.jsonl";path.touch()
			with contextlib.redirect_stdout(io.StringIO()):
				code=run_build([sys.executable,"-c","import os,signal;os.kill(os.getpid(),signal.SIGTERM)"],root,os.environ.copy(),path,0)
			assert code==143
		path=root/"partial.jsonl";path.write_text('{"event":"start","name":"a","module":"m","time_ms":1}\n{"event":')
		with contextlib.redirect_stdout(io.StringIO()):
			p=Progress(path,2);p.read();assert len(p.active)==1 and not p.completed
			with path.open("a") as stream: stream.write('"checked","name":"a","module":"m","time_ms":501}\ninvalid\n')
			p.read();assert not p.active and p.completed[("m","a")][0]==0.5 and p.warned
			path.unlink();p.read()
		cli=root/"cli"; (cli/"lean/QSym").mkdir(parents=True)
		(cli/"lean/QSym/Generated.lean").write_text("theorem one\ntheorem two\n")
		fake=root/"fake-lake"
		fake.write_text("#!"+sys.executable+"\nimport json,os,pathlib,sys\npathlib.Path("+repr(str(root/"invocation.json"))+").write_text(json.dumps({'args':sys.argv[1:],'progress':os.getenv('QSYM_PROGRESS_FILE'),'cache':os.getenv('QSYM_PROOF_CACHE')}))\nraise SystemExit(7)\n")
		fake.chmod(0o700)
		entry=root/"cli.py"
		entry.write_text("import pathlib,sys\nsys.path.insert(0,"+repr(str(ROOT/"tools"))+")\nimport build_lean\nbuild_lean.ROOT=pathlib.Path("+repr(str(cli))+")\nraise SystemExit(build_lean.main())\n")
		env=os.environ.copy();env.update(QSYM_PROGRESS_FILE="inherited",QSYM_PROOF_CACHE="inherited")
		def invoke(*options):
			return subprocess.run([sys.executable,str(entry),"--lake",str(fake),*options],env=env,capture_output=True,text=True,timeout=15)
		p=invoke("--reuse-proofs");assert p.returncode==7 and "No previous Generated.olean" in p.stdout and "build failed (exit 7)" in p.stdout,p
		invocation=json.loads((root/"invocation.json").read_text())
		assert invocation["args"]==["--no-ansi","build"] and invocation["cache"] is None
		assert pathlib.Path(invocation["progress"]).is_file()
		p=invoke("--no-progress");assert p.returncode==7 and "[Lean" not in p.stdout,p
		invocation=json.loads((root/"invocation.json").read_text());assert invocation=={"args":["build"],"cache":None,"progress":None},invocation
		old=cli/"lean/.lake/build/lib/lean/QSym/Generated.olean";old.parent.mkdir(parents=True);old.write_bytes(b"proof-cache-fixture")
		p=invoke("--reuse-proofs");assert p.returncode==7 and "Rechecking cached rule proofs" in p.stdout,p
		invocation=json.loads((root/"invocation.json").read_text());assert pathlib.Path(invocation["cache"]).read_bytes()==old.read_bytes()
		for value in ("0","-1","nan","inf"):
			p=invoke("--progress-interval",value);assert p.returncode==2,p
	print("Live Lean progress checks passed.",flush=True)

if __name__=="__main__":
	main()
