#!/usr/bin/env python3
"""Measure import, per-file and batched checking; profile with the kernel enabled."""
import argparse
import json
import pathlib
import re
import statistics
import subprocess
import tempfile
import time
from verify import ROOT,audit

def main():
	parser=argparse.ArgumentParser(description=__doc__)
	parser.add_argument("--exporter",type=pathlib.Path,default=ROOT/"build/sum-bench")
	parser.add_argument("--size",type=int,default=128)
	parser.add_argument("--rounds",type=int,default=3)
	parser.add_argument("--timeout",type=int,default=600,help="timeout in seconds for each process")
	parser.add_argument("--lake",default="lake")
	parser.add_argument("--lean",help="Lean wrapper with configured LEAN_PATH")
	parser.add_argument("--select",default="",help="comma-separated certificate names; empty selects all")
	parser.add_argument("--output",type=pathlib.Path,help="write JSON results to this file")
	args=parser.parse_args()
	if args.rounds<1 or args.timeout<1 or not 1<=args.size<=4096:
		parser.error("positive rounds/timeout and a size between 1 and 4096 are required")
	lean=[args.lean] if args.lean else [args.lake,"env","lean"]
	def run(command):
		start=time.perf_counter()
		p=subprocess.run(command,cwd=ROOT/"lean",text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=args.timeout)
		if p.returncode:
			raise RuntimeError(p.stdout)
		audit(p.stdout)
		return time.perf_counter()-start,p.stdout
	def profile(path):
		_,output=run(lean+["-Dprofiler=true",str(path)])
		parts=output.split("cumulative profiling times:\n")
		if len(parts)!=2:
			raise RuntimeError("Lean did not report cumulative profiling times")
		scale={"ns":1e-9,"us":1e-6,"μs":1e-6,"µs":1e-6,"ms":1e-3,"s":1}
		return {name:float(value)*scale[unit] for name,value,unit in
			re.findall(r"^\s+([^\n]+?)\s+([0-9.]+)(ns|us|μs|µs|ms|s)\s*$",parts[1],re.M)}
	with tempfile.TemporaryDirectory(prefix="qsym-profile-") as directory:
		root=pathlib.Path(directory)
		_,output=run([str(args.exporter.resolve()),str(root),str(args.size)])
		metrics={}
		for line in output.splitlines():
			name,micros,size,steps=line.split("\t")
			metrics[name]={"export_seconds":int(micros)/1e6,"bytes":int(size),"steps_or_operands":int(steps)}
		selected=set(args.select.split(",")) if args.select else set(metrics)
		if not selected<=metrics.keys():
			parser.error("unknown certificate selection")
		files=[root/(name+".lean") for name in sorted(selected)]
		imports="import QSym\nimport QSym.Sum\n"
		empty=root/"Imports.lean"; empty.write_text(imports)
		bundle=root/"Batch.lean"
		bundle.write_text(imports+"\n".join(re.sub(r"^import [^\n]+\n","",p.read_text(),flags=re.M) for p in files))
		results={"size":args.size,"rounds":args.rounds,"kernel_checking":True,"complete":False,"certificates":{}}
		def save():
			if args.output:
				args.output.write_text(json.dumps(results,indent=2)+"\n")
		for name,path in [("imports",empty)]+[(p.stem,p) for p in files]+[("batch",bundle)]:
			run(lean+[str(path)])
			samples=[run(lean+[str(path)])[0] for _ in range(args.rounds)]
			data={"wall_seconds":statistics.median(samples),"samples":samples}
			if name not in ("imports","batch"):
				data.update(metrics[name])
				results["certificates"][name]=data
			else:
				results[name]=data
			print(f"{name}: {data['wall_seconds']:.3f}s",flush=True)
			save()
			if name not in ("imports","batch"):
				data["profile_cumulative_seconds"]=profile(path); save()
		# Profiler categories overlap; wall times, including imports, are measured separately.
		results["complete"]=True; save()
		text=json.dumps(results,indent=2)+"\n"
		print(text,end="")

if __name__=="__main__":
	main()
