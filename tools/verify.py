#!/usr/bin/env python3
"""Check certificates and reject unsound rules/results; no external Python deps."""
import argparse
import pathlib
import re
import subprocess
import sys

ROOT=pathlib.Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS={"propext","Classical.choice","Quot.sound"}

def audit(output):
	if "sorryAx" in output or "declaration uses 'sorry'" in output:
		raise RuntimeError("unchecked proof found")
	for axioms in re.findall(r"depends on axioms:\s*\[([^]]*)\]",output):
		used={x.strip() for x in axioms.split(",") if x.strip()}
		if not used<=ALLOWED_AXIOMS:
			raise RuntimeError(f"unexpected axioms: {used - ALLOWED_AXIOMS}")

def main():
	parser=argparse.ArgumentParser()
	parser.add_argument("--lake",default="lake")
	# Useful when sharing a preinstalled Mathlib tree; normal users use Lake.
	parser.add_argument("--lean",help="invoke this Lean directly, with configured LEAN_PATH")
	args=parser.parse_args()

	def check(path,succeeds=True):
		cmd=[args.lean] if args.lean else [args.lake,"env","lean"]
		completed=subprocess.run(cmd+[str(path.resolve())],cwd=ROOT/"lean",
			stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
		if succeeds:
			if completed.returncode:
				raise RuntimeError(completed.stdout)
			audit(completed.stdout)
		else:
			if completed.returncode==0:
				raise RuntimeError(f"invalid proof was accepted: {path.name}")
			if not any(s in completed.stdout for s in ("unsolved goals","type mismatch")):
				raise RuntimeError("negative test failed for the wrong reason:\n"+completed.stdout)
		print(("checked " if succeeds else "rejected ")+path.name)

	# Recheck generated theorems here so their full axiom reports are audited,
	# even when Lake reused cached build outputs.
	check(ROOT/"lean/QSym/Generated.lean")
	check(ROOT/"lean/QSym/Audit.lean")
	check(ROOT/"tests/Regression.lean")
	files=sorted((ROOT/"build/certificates").glob("*.lean"))
	if len(files)!=7:
		raise RuntimeError("expected seven freshly generated certificates")
	for file in files:
		check(file)

	negative=ROOT/"build/negative"
	negative.mkdir(exist_ok=True)
	bad_rules=negative/"bad.qs"
	bad_rules.write_text("rule bad(x:Real): mulR(real(0),x) => real(0);\n")
	subprocess.run([str(ROOT/"build/rulec"),str(bad_rules),str(negative/"bad.d"),
		str(negative/"BadRule.lean")],check=True,stdout=subprocess.PIPE)
	check(negative/"BadRule.lean",succeeds=False)

	good=(ROOT/"build/certificates/Guarded.lean").read_text()
	corrupt,count=re.subn(
		r"(theorem simplification \(ρ : Env\) : .*? = )\(Expr.eval ρ n\d+\)( :=)",
		r"\g<1>some (42 : ℝ)\2",good,count=1)
	if count!=1:
		raise RuntimeError("could not construct the tampering test")
	(negative/"Corrupted.lean").write_text(corrupt)
	check(negative/"Corrupted.lean",succeeds=False)
	print("All checks passed; only Lean's standard foundational axioms were used.")

if __name__=="__main__":
	try:
		main()
	except (RuntimeError,subprocess.CalledProcessError) as error:
		print(error,file=sys.stderr)
		sys.exit(1)
