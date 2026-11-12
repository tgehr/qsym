#!/usr/bin/env python3
"""Reuse proof candidates, never unchecked declarations or verification results."""
import argparse
import hashlib
import os
import pathlib
import re
import subprocess
import tempfile
from lean_progress import run_build

ROOT=pathlib.Path(__file__).resolve().parents[1]

def main():
	parser=argparse.ArgumentParser()
	parser.add_argument("--lake",default="lake")
	parser.add_argument("--reuse-proofs",action="store_true")
	parser.add_argument("--no-progress",action="store_true")
	parser.add_argument("--progress-interval",type=float,default=10)
	args=parser.parse_args()
	if not 0<args.progress_interval<float("inf"):
		parser.error("--progress-interval must be positive and finite")
	env=os.environ.copy()
	env.pop("QSYM_PROOF_CACHE",None)
	env.pop("QSYM_PROGRESS_FILE",None)
	old=ROOT/"lean/.lake/build/lib/lean/QSym/Generated.olean"
	if args.reuse_proofs and old.is_file():
		data=old.read_bytes()
		directory=ROOT/"build/proof-cache"
		directory.mkdir(parents=True,exist_ok=True)
		path=directory/(hashlib.sha256(data).hexdigest()+".olean")
		path.write_bytes(data)
		env["QSYM_PROOF_CACHE"]=str(path)
		print("Rechecking cached rule proofs with Lean's kernel; missing or stale proofs use tactics.",flush=True)
	elif args.reuse_proofs:
		print("No previous Generated.olean; rule proofs will use source tactics when rebuilt.",flush=True)
	if args.no_progress:
		return subprocess.call([args.lake,"build"],cwd=ROOT/"lean",env=env)
	directory=ROOT/"build/lean-progress"
	directory.mkdir(parents=True,exist_ok=True)
	with tempfile.NamedTemporaryFile(dir=directory,suffix=".jsonl",delete=False) as stream:
		path=pathlib.Path(stream.name)
	env["QSYM_PROGRESS_FILE"]=str(path)
	total=len(re.findall(r"^theorem ",(ROOT/"lean/QSym/Generated.lean").read_text(),re.M))
	return run_build([args.lake,"--no-ansi","build"],ROOT/"lean",env,path,total,args.progress_interval)

if __name__=="__main__":
	raise SystemExit(main())
