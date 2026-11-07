#!/usr/bin/env python3
"""Check certificates and reject unsound rules/results; no external Python deps."""
import argparse
from concurrent.futures import ThreadPoolExecutor
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
	parser.add_argument("--jobs",type=int,default=1,help="parallel certificate checks")
	args=parser.parse_args()
	if args.jobs<1:
		parser.error("--jobs must be positive")

	def check(path,succeeds=True,timeout=180):
		cmd=[args.lean] if args.lean else [args.lake,"env","lean"]
		completed=subprocess.run(cmd+[str(path.resolve())],cwd=ROOT/"lean",
			stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=timeout)
		if succeeds:
			if completed.returncode:
				raise RuntimeError(completed.stdout)
			audit(completed.stdout)
		else:
			if completed.returncode==0:
				raise RuntimeError(f"invalid proof was accepted: {path.name}")
			if not any(s in completed.stdout for s in ("unsolved goals","type mismatch","is false","unexpected axioms")):
				raise RuntimeError("negative test failed for the wrong reason:\n"+completed.stdout)
		print(("checked " if succeeds else "rejected ")+path.name,flush=True)

	certificates=[]
	def certificate(path):
		if re.search(r"\b(by|decreasing_by|sorry|admit|native_decide)\b",path.read_text()):
			raise RuntimeError("tactic or unchecked proof in certificate: "+path.name)
		certificates.append(path)

	# Recheck generated theorems here so their full axiom reports are audited,
	# even when Lake reused cached build outputs.
	check(ROOT/"lean/QSym/Generated.lean",timeout=900)
	check(ROOT/"lean/QSym/Audit.lean")
	check(ROOT/"tests/Regression.lean")
	check(ROOT/"tests/Language.lean")
	check(ROOT/"tests/Certificates.lean")
	check(ROOT/"build/Syntax.lean")
	certificate(ROOT/"build/Repl.lean")
	certificate(ROOT/"build/ReplFacts.lean")
	certificate(ROOT/"build/ReplExpand.lean")
	for directory,count in (("guards",24),("folding",73),("relations",37),("quadratics",42),("order",68),("identities",84),("compact",19),("associative",14),("signs",51),("sum",7)):
		files=sorted((ROOT/"build"/directory).glob("*.lean"))
		if len(files)!=count:
			raise RuntimeError(f"expected {count} {directory} certificates")
		for file in files:
			certificate(file)
	predicates=sorted((ROOT/"build/predicates").glob("*.lean"))
	if len(predicates)!=34:
		raise RuntimeError("expected 34 predicate certificates")
	for file in predicates:
		certificate(file)
	elementary=sorted((ROOT/"build/elementary").glob("*.lean"))
	if len(elementary)!=82:
		raise RuntimeError("expected 82 elementary certificates")
	for file in elementary:
		certificate(file)
	language=sorted((ROOT/"build/language").glob("*.lean"))
	if len(language)!=47 or not (ROOT/"build/language/Builtins.lean").is_file():
		raise RuntimeError("expected 47 language certificates")
	for file in language:
		certificate(file)

	scalars=sorted((ROOT/"build/scalar").glob("*.lean"))
	if len(scalars)!=59:
		raise RuntimeError("expected 59 scalar certificates")
	for file in scalars:
		certificate(file)
	files=sorted((ROOT/"build/certificates").glob("*.lean"))
	if len(files)!=7:
		raise RuntimeError("expected seven freshly generated certificates")
	for file in files:
		certificate(file)

	with ThreadPoolExecutor(max_workers=args.jobs) as pool:
		for _ in pool.map(check,certificates):
			pass

	negative=ROOT/"build/negative"
	negative.mkdir(exist_ok=True)
	# Audit a shared dependency before introducing a new axiom: a cache must
	# never hide later declarations, even through transitive dependencies.
	for name,body in (
		("NewAxiom","axiom injected : False\ntheorem forged : False := injected"),
		("Sorry","theorem forged : False := by sorry")):
		path=negative/(name+".lean")
		path.write_text("import QSym\n#qsym_check_axioms QSym.Numeric.sound\n"+body+"\n#qsym_check_axioms forged\n")
		check(path,succeeds=False)
	bad_rules=negative/"bad.qs"
	bad_rules.write_text("rule bad(x:ℝ):1·x⇒0;\n",encoding="utf-8")
	subprocess.run([str(ROOT/"build/rulec"),str(bad_rules),str(negative/"bad.d"),
		str(negative/"BadRule.lean")],check=True,stdout=subprocess.PIPE)
	check(negative/"BadRule.lean",succeeds=False)
	bad_rules.write_text("rule bad_abs(x:ℝ):|x|⇒x;\n",encoding="utf-8")
	subprocess.run([str(ROOT/"build/rulec"),str(bad_rules),str(negative/"bad_abs.d"),
		str(negative/"BadAbs.lean")],check=True,stdout=subprocess.PIPE)
	check(negative/"BadAbs.lean",succeeds=False)
	for name,rule in (
		("BadFloor","lemma bad(x:ℝ,n:ℤ):floor(x)⇒n when toℝ(n)≤x,defined(n);"),
		("BadCubeRoot","rewrite bad(x:ℝ):cbrt(x)⇒powerR(x,real(1,3));"),
		("BadSqrtBranch","lemma bad(z:ℂ,w:ℂ):csqrt(z)⇒w when w^2=z,defined(w);"),
		("BadLogBase","lemma bad(x:ℝ,y:ℝ):log2(x)⇒y when powerR(10,y)=x,defined(y);"),
		("BadOrSwap","lemma bad(p:𝔹,q:𝔹):p∨q⇒q∨p;"),
		("BadCondition","rewrite bad(x:ℝ):|x|⇒x when x≤0;"),
		("BadArgPower","rewrite bad(z:ℂ):carg(cpow(z,real(3,2)))⇒real(3,2)*carg(z);"),
		("BadLogPower","rewrite bad(z:ℂ):clog(cpow(z,real(3,2)))⇒real(3,2)*clog(z);"),
		("BadArgBoundary","rewrite bad(z:ℂ):carg(cexp(z))⇒cimag(z) when -π≤cimag(z),cimag(z)≤π;"),
		("BadNormPower","rewrite bad(z:ℂ,w:ℂ):cabs(cpow(z,w))⇒pow(cabs(z),creal(w));"),
		("BadComplexLog","rewrite bad(z:ℂ):clog(cexp(z))⇒z;"),
		("BadComplexRoot","rewrite bad(z:ℂ):csqrt(z^2)⇒z;"),
		("BadLogProduct","rewrite bad(x:ℝ,y:ℝ):log(x*y)⇒log(x)+log(y);"),
		("BadNestedPower","rewrite bad(x:ℝ,y:ℝ,z:ℝ):powerR(powerR(x,y),z)⇒powerR(x,y*z);"),
		("BadRealRoot","rewrite bad(x:ℝ):sqrt(x^2)⇒x;"),
		("BadDistribution","rewrite bad(p:𝔹,q:𝔹,r:𝔹):(p∨q)∧r⇒(p∧r)∨(q∧r);"),
		("BadSwap","rewrite bad(p:𝔹,q:𝔹):p∧q⇒q∧p;"),
		("BadQuadraticDiscriminant","lemma bad(x:ℝ):x^2+1≠0⇒x≠-1∧x≠1;"),
		("BadQuadraticLeading","lemma bad(x:ℂ,a:ℂ):a*(x^2-1)≠0⇒x≠-1∧x≠1;"),
		("BadRootSelection","lemma bad(z:ℂ):z⇒ⅈ when z^2+1=0;"),
		("BadFactorization","lemma bad(p:ℝ,x:ℝ,y:ℝ):p≠0⇒x≠0∧y≠0 when defined(x),defined(y);"),
		("BadSignedSum","rewrite bad(x:ℝ,y:ℝ):x+y=0⇒x=0∧y=0;"),
		("BadProductBoundary","rewrite bad(x:ℝ,y:ℝ):x*y<0⇒y<0 when 0≤x;"),
		("BadEvenMonotonicity","rewrite bad(x:ℝ,y:ℝ):x^2<y^2⇒x<y;"),
		("BadEvenZero","rewrite bad(x:ℝ,y:ℝ):x^0≤y^0⇒abs(x)≤abs(y);"),
		("BadEvenSign","rewrite bad(x:ℝ):x^2<0⇒x<0;"),
		("BadEvenProductZero","rewrite bad(x:ℝ,y:ℝ):x^2*y<0⇒y<0;"),
		("BadPowerDirection","rewrite bad(x:ℝ,y:ℝ):powerR(real(1,2),x)<powerR(real(1,2),y)⇒x<y;"),
		("BadSqrtBound","rewrite bad(x:ℝ,y:ℝ):sqrt(x)≤y⇒x≤y^2;"),
		("BadAbsBound","rewrite bad(x:ℝ,y:ℝ):abs(x)=y⇒x=-y∨x=y;"),
		("BadQuadraticSign","rewrite bad(x:ℝ):2-x^2≤0⇒-sqrt(2)≤x∧x≤sqrt(2);"),
		("BadComplexExpInjective","rewrite bad(z:ℂ,w:ℂ):cexp(z)≠cexp(w)⇒z≠w;"),
		("BadComplexSqrtProduct","rewrite bad(z:ℂ,w:ℂ):csqrt(z)*csqrt(w)⇒csqrt(z*w);"),
		("BadComplexNormInjective","rewrite bad(z:ℂ,w:ℂ):cabs(z)≠cabs(w)⇒z≠w;"),
		("BadComplexPowerProduct","rewrite bad(z:ℂ,w:ℂ,t:ℂ):powerC(z,t)*powerC(w,t)⇒powerC(z*w,t);"),
		("BadComplexOddPower","rewrite bad(z:ℂ,w:ℂ):z^3≠w^3⇒z≠w;"),
		("BadMinComparison","rewrite bad(x:ℝ,y:ℝ,t:ℝ):min(x,y)<t⇒x<t∧y<t;"),
		("MissingDomain","fact bad(x:ℝ,a:ℝ,b:ℝ):x<b when x<a,a≤b;")):
		bad_rules.write_text(rule+"\n",encoding="utf-8")
		subprocess.run([str(ROOT/"build/rulec"),str(bad_rules),str(negative/(name+".d")),
			str(negative/(name+".lean"))],check=True,stdout=subprocess.PIPE)
		check(negative/(name+".lean"),succeeds=False)
	(negative/"BadComplexExpBoundary.lean").write_text("import QSym\n"
		"theorem forged (z w : ℂ) (hz : -Real.pi≤z.im) (hz' : z.im≤Real.pi)\n"
		"    (hw : -Real.pi<w.im) (hw' : w.im≤Real.pi) : Complex.exp z=Complex.exp w ↔ z=w :=\n"
		"  QSym.Identities.cexp_inj hz hz' hw hw'\n")
	check(negative/"BadComplexExpBoundary.lean",succeeds=False)
	(negative/"PartialIsNotTotal.lean").write_text("import QSym\nopen QSym\n"
		"theorem forged (x : Option ℝ) (h : Value.Defined x) : Value.Defined (Functions.logR.apply x) :=\n"
		"  Functions.logR.total (fun _ => True.intro) x h\n")
	check(negative/"PartialIsNotTotal.lean",succeeds=False)

	fact=(ROOT/"build/elementary/AbsFact.lean").read_text()
	weak,count=re.subn(r"\(g1 : (\(v\d+ ρ\)) = some true\)",
		r"(g1 : Value.Refines \1 (some true))",fact)
	if not count:
		raise RuntimeError("could not construct the weak-assumption test")
	(negative/"WeakAssumption.lean").write_text(weak)
	check(negative/"WeakAssumption.lean",succeeds=False)
	claim=re.search(r"theorem refinement .*? : (Value.Refines .*?) :=",fact).group(1)
	claim=re.sub(r"\bn(\d+)\b",r"Certificate.n\1",claim)
	(negative/"MissingAssumption.lean").write_text(fact+"\nnamespace QSym\n"
		+"theorem forged (ρ : Env) : "+claim+" := Certificate.refinement ρ rfl\nend QSym\n")
	check(negative/"MissingAssumption.lean",succeeds=False)

	guarded=(ROOT/"build/scalar/IntervalAbs.lean").read_text()
	corrupt,count=re.subn(
		r"(Generated\.r_real_abs_nonpositive \(v\d+ ρ\)) \(p\d+ ρ g\d+\)",
		r"\1 (Value.refines_refl (some true))",guarded,count=1)
	if count!=1:
		raise RuntimeError("could not construct the wrong-premise test")
	(negative/"WrongPremise.lean").write_text(corrupt)
	check(negative/"WrongPremise.lean",succeeds=False)
	selected=(ROOT/"build/quadratics/ComplexSelectUpper.lean").read_text()
	corrupt,count=re.subn(r"from ⟨_, \(p\d+ ρ(?: g\d+)*\)⟩", "from ⟨_, rfl⟩", selected, count=1)
	if count!=1:
		raise RuntimeError("could not construct the invalid-definedness test")
	(negative/"WrongDerivedDomain.lean").write_text(corrupt)
	check(negative/"WrongDerivedDomain.lean",succeeds=False)
	projected=(ROOT/"build/order/AssumedSquareSum.lean").read_text()
	corrupt,count=re.subn(r"Value\.and_true_left", "Value.and_true_right", projected, count=1)
	if count!=1:
		raise RuntimeError("could not construct the invalid-fact-projection test")
	(negative/"WrongFactProjection.lean").write_text(corrupt)
	check(negative/"WrongFactProjection.lean",succeeds=False)
	polynomial=(ROOT/"build/scalar/Polynomial.lean").read_text()
	corrupt,count=re.subn(r"(let ac\d+ : Replay.Tree := \(\.leaf )\d+",r"\g<1>999999",polynomial,count=1)
	if count!=1:
		raise RuntimeError("could not construct the invalid-permutation test")
	(negative/"WrongPermutation.lean").write_text(corrupt)
	check(negative/"WrongPermutation.lean",succeeds=False)
	deep=(ROOT/"build/associative/Deep512.lean").read_text()
	corrupt,count=re.subn(r"(theorem cac\d+_\d+ : Replay.Tree.counts ac\d+_\d+ = \[\(\d+,)1",r"\g<1>2",deep,count=1)
	if count!=1:
		raise RuntimeError("could not construct the invalid-multiplicity test")
	(negative/"WrongMultiplicity.lean").write_text(corrupt)
	check(negative/"WrongMultiplicity.lean",succeeds=False)
	value=(ROOT/"build/associative/RepeatedSum.lean").read_text()
	corrupt,count=re.subn(r"(noncomputable def v\d+[^\n]*? := )Value.mul",r"\1Value.add",value,count=1)
	if count!=1:
		raise RuntimeError("could not construct the invalid-evaluation test")
	(negative/"WrongEvaluation.lean").write_text(corrupt)
	check(negative/"WrongEvaluation.lean",succeeds=False)
	root=(ROOT/"build/signs/OddBound.lean").read_text()
	corrupt,count=re.subn(r"(def n\d+ : Expr .real := \(.real \()2(\)\))",r"\g<1>3\2",root,count=1)
	if count!=1:
		raise RuntimeError("could not construct the incorrect-root test")
	(negative/"WrongRoot.lean").write_text(corrupt)
	check(negative/"WrongRoot.lean",succeeds=False)
	sum_source=(ROOT/"build/sum/real_.lean").read_text()
	for name,pattern,replacement in (
		("WrongSumMultiplicity",r"(def output[^\n]*?\.term \d+,)2",r"\g<1>3"),
		("WrongSumLiteral",r"(def output[^\n]*?\.literal \(\()128",r"\g<1>129")):
		corrupt,count=re.subn(pattern,replacement,sum_source,count=1)
		if count!=1:
			raise RuntimeError("could not construct "+name)
		(negative/(name+".lean")).write_text(corrupt)
		check(negative/(name+".lean"),succeeds=False)
	partial=(ROOT/"build/sum/Partial3.lean").read_text()
	corrupt,count=re.subn(r"(def output[^\n]*? := )[^\n]+",r"\1[]",partial,count=1)
	if count!=1:
		raise RuntimeError("could not construct the invalid sum cancellation test")
	(negative/"WrongSumCancellation.lean").write_text(corrupt)
	check(negative/"WrongSumCancellation.lean",succeeds=False)
	rational=(ROOT/"build/scalar/Rational.lean").read_text()
	corrupt,count=re.subn(r"(Numeric\.sound ρ n\d+) n\d+ rfl",r"\1 (.real 42) rfl",rational,count=1)
	if count!=1:
		raise RuntimeError("could not construct the invalid-arithmetic test")
	(negative/"WrongArithmetic.lean").write_text(corrupt)
	check(negative/"WrongArithmetic.lean",succeeds=False)

	good=(ROOT/"build/certificates/Guarded.lean").read_text()
	corrupt,count=re.subn(
		r"(theorem simplification \(ρ : Env\).*? = )\(Expr.eval ρ n\d+\)( :=)",
		r"\g<1>some (42 : ℝ)\2",good,count=1)
	if count!=1:
		raise RuntimeError("could not construct the tampering test")
	(negative/"Corrupted.lean").write_text(corrupt)
	check(negative/"Corrupted.lean",succeeds=False)
	print("All checks passed; only Lean's standard foundational axioms were used.")

if __name__=="__main__":
	try:
		main()
	except (RuntimeError,subprocess.CalledProcessError,subprocess.TimeoutExpired) as error:
		print(error,file=sys.stderr)
		sys.exit(1)
