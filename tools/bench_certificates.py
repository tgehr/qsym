#!/usr/bin/env python3
"""Time trace simplification/export plus Lean checking, with a prebuilt library."""
import argparse
import json
import pathlib
import statistics
import subprocess
import sys
import tempfile
import time
from verify import ROOT,audit

def run(command,cwd):
	start=time.perf_counter()
	result=subprocess.run(command,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=600)
	if result.returncode:
		raise RuntimeError(result.stdout)
	audit(result.stdout)
	return time.perf_counter()-start

def main():
	parser=argparse.ArgumentParser(description=__doc__)
	parser.add_argument("--exporter",type=pathlib.Path,default=ROOT/"build/scalar-export")
	parser.add_argument("--lake",default="lake")
	parser.add_argument("--lean",help="invoke Lean directly with configured LEAN_PATH")
	parser.add_argument("--rounds",type=int,default=3)
	args=parser.parse_args()
	if args.rounds<1:
		parser.error("--rounds must be positive")
	lean=[args.lean] if args.lean else [args.lake,"env","lean"]
	samples=[]
	with tempfile.TemporaryDirectory(prefix="qsym-certificates-") as directory:
		root=pathlib.Path(directory)
		# One untimed warmup, then fresh outputs each round. One Lean process
		# checks all examples so repeated import/startup costs do not dominate.
		for i in range(args.rounds+1):
			out=root/str(i)
			export=run([str(args.exporter.resolve()),str(out)],ROOT)
			files=sorted(out.glob("*.lean"))
			if not files:
				raise RuntimeError("exporter produced no certificates")
			bundle=root/"Certificates.lean"
			contents=[p.read_text() for p in files]
			bundle.write_text("import QSym\n"+"\n".join(s.replace("import QSym\n","") for s in contents))
			check=run(lean+[str(bundle)],ROOT/"lean")
			print(f"{'warmup' if i==0 else 'round '+str(i)}: export {export:.3f}s, Lean {check:.3f}s",file=sys.stderr,flush=True)
			if i:
				samples.append(dict(export=export,check=check,total=export+check))
		print(json.dumps(dict(certificates=len(files),bytes=sum(len(s.encode()) for s in contents),
			seconds={k:statistics.median(s[k] for s in samples) for k in samples[0]},samples=samples),indent=2))

if __name__=="__main__":
	main()
