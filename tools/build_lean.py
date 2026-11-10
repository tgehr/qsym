#!/usr/bin/env python3
"""Reuse proof candidates, never unchecked declarations or verification results."""
import argparse
import hashlib
import os
import pathlib
import subprocess

ROOT=pathlib.Path(__file__).resolve().parents[1]

def main():
	parser=argparse.ArgumentParser()
	parser.add_argument("--lake",default="lake")
	parser.add_argument("--reuse-proofs",action="store_true")
	args=parser.parse_args()
	env=os.environ.copy()
	env.pop("QSYM_PROOF_CACHE",None)
	old=ROOT/"lean/.lake/build/lib/lean/QSym/Generated.olean"
	if args.reuse_proofs and old.is_file():
		data=old.read_bytes()
		directory=ROOT/"build/proof-cache"
		directory.mkdir(parents=True,exist_ok=True)
		path=directory/(hashlib.sha256(data).hexdigest()+".olean")
		path.write_bytes(data)
		env["QSYM_PROOF_CACHE"]=str(path)
		print("Rechecking cached rule proofs with Lean's kernel; missing or stale proofs use tactics.",flush=True)
	subprocess.run([args.lake,"build"],cwd=ROOT/"lean",env=env,check=True)

if __name__=="__main__":
	main()
