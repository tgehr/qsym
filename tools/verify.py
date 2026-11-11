#!/usr/bin/env python3
"""Check certificates and reject unsound rules/results; no external Python deps."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import pathlib
import re
import subprocess
import sys
from kernel_cache import KernelCache,compiled_rules
from certificate_batches import make_batches

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
	parser.add_argument("--jobs",type=int,default=1,help="parallel certificate and rejection checks")
	parser.add_argument("--batch-size",type=int,default=1,help="check independent standard certificates in shared Lean processes")
	parser.add_argument("--fast",action="store_true",help="recheck cached proof terms with the current Lean kernel, falling back to source elaboration")
	parser.add_argument("--stack-size",type=int,default=65536,help="Lean thread stack in KiB, including batched stress tests")
	args=parser.parse_args()
	if args.jobs<1 or args.batch_size<1 or args.stack_size<1:
		parser.error("--jobs, --batch-size and --stack-size must be positive")
	cmd=[args.lean] if args.lean else [args.lake,"env","lean"]
	cmd+=["-s",str(args.stack_size)]
	cache=KernelCache(ROOT,cmd)

	def run_check(path,succeeds=True,timeout=180,save=False):
		source=path.read_bytes()
		with cache.output() as temporary:
			compiled=pathlib.Path(temporary)/"Checked.olean"
			options=["-R",str(ROOT),"-o",str(compiled)] if save else []
			completed=subprocess.run(cmd+options+[str(path.resolve())],cwd=ROOT/"lean",env=cache.env,
				stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=timeout)
			if path.read_bytes()!=source:
				raise RuntimeError("proof changed during checking: "+str(path))
			if succeeds and completed.returncode==0:
				audit(completed.stdout)
				if save:
					cache.store(path,source,compiled)
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
	negative_checks=[]
	def check(path,succeeds=True,timeout=180,save=False):
		if succeeds:
			run_check(path,timeout=timeout,save=save)
		else:
			negative_checks.append((path,path.read_bytes(),timeout))

	certificates=[]
	def certificate(path):
		if re.search(r"\b(by|decreasing_by|sorry|admit|native_decide)\b",path.read_text()):
			raise RuntimeError("tactic or unchecked proof in certificate: "+path.name)
		certificates.append(path)

	if args.fast:
		current=ROOT/"build/CurrentRules.lean"
		current.write_text(compiled_rules((ROOT/"lean/QSym/Generated.lean").read_text()))
		check(current,timeout=1800)
	else:
		# Independent full audit includes proof construction, even after a fast build.
		check(ROOT/"lean/QSym/Generated.lean",timeout=1800)
	check(ROOT/"lean/QSym/Audit.lean")
	check(ROOT/"tests/Regression.lean")
	check(ROOT/"tests/Language.lean")
	check(ROOT/"tests/Certificates.lean")
	check(ROOT/"tests/Lookup.lean")
	check(ROOT/"tests/Domain.lean")
	check(ROOT/"build/Syntax.lean")
	certificate(ROOT/"build/Repl.lean")
	certificate(ROOT/"build/ReplFacts.lean")
	certificate(ROOT/"build/ReplExpand.lean")
	certificate(ROOT/"build/ReplDomain.lean")
	for directory,count in (("guards",24),("folding",73),("relations",37),("quadratics",42),("order",68),("identities",84),("compact",19),("associative",22),("regions",6),("counted",24),("joins",28),("lookup",20),("signs",51),("sum",7),("rational",24),("transcendental",65),("powers",62),("functions",93),("exponentials",93),("trigonometry",287),("trig-algebra",255),("radicals",42),("inverses",60),("domains",198),("assumptions",115)):
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

	discrete=sorted((ROOT/"build/discrete").glob("*.lean"))
	if len(discrete)!=137:
		raise RuntimeError("expected 137 discrete scalar certificates")
	for file in discrete:
		certificate(file)

	# Find unchanged individual certificates before constructing batches. Their
	# original modules remain usable even if additions moved every batch boundary.
	unchanged=cache.recheck(certificates,args.jobs) if args.fast else set()
	checks,members=make_batches(ROOT,[p for p in certificates if p not in unchanged],args.batch_size)
	rechecked=cache.recheck(checks,args.jobs) if args.fast else set()
	def check_group(path):
		files=members.get(path,[(path,path.read_bytes())])
		source=path.read_bytes()
		try:
			if path not in rechecked:
				check(path,timeout=180*len(files),save=True)
		except (RuntimeError,subprocess.TimeoutExpired):
			if path not in members:
				raise
			print(f"{path.name} failed; checking {len(files)} constituent certificates individually.",flush=True)
			for file,original in files:
				if file.read_bytes()!=original:
					raise RuntimeError("certificate changed during batch checking: "+str(file))
				check(file,save=True)
			return
		if path in members:
			cache.remember_members(path,source,files)
	with ThreadPoolExecutor(max_workers=args.jobs) as pool:
		for _ in pool.map(check_group,checks):
			pass
	print(f"Checked {len(certificates)} tactic-free certificates.",flush=True)

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
	domain=(ROOT/"build/domains/Reciprocal.lean").read_text()
	corrupt,count=re.subn(r"(theorem domain_correct .*?Domain.Correct .*? )\(Expr.eval ρ Certificate.n\d+\)( :=)",
		r"\1(some true)\2",domain,count=1)
	if count!=1:
		raise RuntimeError("could not construct the invalid-domain test")
	(negative/"WrongDomainCondition.lean").write_text(corrupt)
	check(negative/"WrongDomainCondition.lean",succeeds=False)
	domain=(ROOT/"build/domains/GuardedUndefined.lean").read_text()
	head,body=domain.split("namespace QSym.DomainCertificate\n",1)
	corrupt=body.replace("(.bool false)","(.bool true)").replace("some false","some true")
	if corrupt==body:
		raise RuntimeError("could not construct the invalid-guard-domain test")
	(negative/"WrongMaskDomain.lean").write_text(head+"namespace QSym.DomainCertificate\n"+corrupt)
	check(negative/"WrongMaskDomain.lean",succeeds=False)
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
		("BadPowerUnitNotOne","rewrite bad(x:ℝ,t:ℝ):powerR(x,t)=1⇒x=1 when t≠1;"),
		("BadPowerUnitParity","rewrite bad(x:ℝ,t:ℝ):powerR(x,t)=1⇒t=0∨x=1∨x=-1;"),
		("BadComplexRealPower","rewrite bad(z:ℂ,w:ℂ):powerC(z,w)⇒toℂ(powerR(creal(z),creal(w))) when cimag(z)=0,cimag(w)=0;"),
		("BadComplexUnitNonreal","rewrite bad(z:ℂ,w:ℂ):powerC(z,w)=1⇒creal(w)=0∨z=1∨(z=-1∧inZ(creal(w)/2)) when cimag(w)=0;"),
		("BadIndicatorOverlap","rewrite bad(p:𝔹,q:𝔹):[p]+[q]⇒[p∨q];"),
		("BadStrictGuardReversal","lemma bad(p:𝔹,x:ℝ):[p]*x⇒mulR([p],x);"),
		("BadNestedIntegerCancel","rewrite bad(x:ℤ,y:ℤ):(x+y)-y⇒y;"),
		("BadNestedRationalCancel","rewrite bad(x:ℚ,y:ℚ):x*(y/x)⇒x;"),
		("BadReverseNestedRational","lemma bad(x:ℚ,y:ℚ):y⇒x*(y/x) when defined(x);"),
		("BadIntegerCancel","rewrite bad(x:ℤ):x+x⇒0;"),
		("BadNaturalProduct","rewrite bad(x:ℕ,y:ℕ):x*y≠0⇒x≠0∨y≠0;"),
		("BadRationalPower","rewrite bad(x:ℚ):x^2*x^3⇒x^6;"),
		("BadRationalReverseCancellation","lemma bad(x:ℚ):rat(1,1)⇒x/x when defined(x);"),
		("BadIntegerSquare","rewrite bad(x:ℤ):x^2⇒x;"),
		("BadNaturalStrictSelf","rewrite bad(x:ℕ):x<x⇒true;"),
		("BadComplexSinHalfTurn","rewrite bad(z:ℂ):csin(z+toℂ(π))⇒csin(z);"),
		("BadComplexTanQuarterTurn","rewrite bad(z:ℂ):ctan(z+toℂ(π/2))⇒ctan(z);"),
		("BadRealPeriodIndex","rewrite bad(x:ℝ):sin(2*π*x)⇒0;"),
		("BadIntegerHalfPeriod","rewrite bad(k:ℤ):cos(π*k)⇒1;"),
		("BadIntegerHalfSign","rewrite bad(x:ℝ,k:ℤ):sin(x+π*k)⇒sin(x);"),
		("BadComplexSinhRealPeriod","rewrite bad(z:ℂ):csinh(z+toℂ(2*π))⇒csinh(z);"),
		("BadComplexTanhHalfImaginaryPeriod","rewrite bad(z:ℂ):ctanh(z+ⅈ*toℂ(π/2))⇒ctanh(z);"),
		("BadIntegerOddParity","rewrite bad(k:ℤ):powRZ(-1,2*k+1)⇒1;"),
		("BadRealIndexParity","rewrite bad(x:ℝ):powerR(-1,2*x)⇒1;"),
		("BadComplexCoshNonzero","rewrite bad(z:ℂ):ccosh(z)≠0⇒true;"),
		("BadHyperbolicSumSquares","rewrite bad(z:ℂ):ccosh(z)^2+csinh(z)^2⇒complex(1,0);"),
		("BadComplexPeriodIndex","rewrite bad(z:ℂ,w:ℂ):csin(z+toℂ(2*π)*w)⇒csin(z);"),
		("BadNegativeQuarterSign","rewrite bad(z:ℂ):csin(z-toℂ(π/2))⇒ccos(z);"),
		("BadRealAcoshInverse","rewrite bad(x:ℝ):acosh(cosh(x))⇒x;"),
		("BadComplexAsinInverse","rewrite bad(z:ℂ):casin(csin(z))⇒z;"),
		("BadComplexAcosInverse","rewrite bad(z:ℂ):cacos(ccos(z))⇒z;"),
		("BadComplexAtanInverse","rewrite bad(z:ℂ):catan(ctan(z))⇒z;"),
		("BadComplexAsinhInverse","rewrite bad(z:ℂ):casinh(csinh(z))⇒z;"),
		("BadComplexAcoshInverse","rewrite bad(z:ℂ):cacosh(ccosh(z))⇒z;"),
		("BadComplexAtanhInverse","rewrite bad(z:ℂ):catanh(ctanh(z))⇒z;"),
		("BadComplexAcoshRoot","rewrite bad(z:ℂ):csinh(cacosh(z))⇒csqrt(z^2-1);"),
		("BadSqrtSixth","rewrite bad(x:ℝ):sqrt(x^6)⇒x^3;"),
		("BadSqrtFactorDomain","rewrite bad(x:ℝ,y:ℝ):sqrt(x^2*y)⇒abs(x)*sqrt(y);"),
		("BadCbrtEven","rewrite bad(x:ℝ):cbrt(x^2)⇒x;"),
		("BadCbrtAbsolute","rewrite bad(x:ℝ):cbrt(x^3)⇒abs(x);"),
		("BadRootScaleSign","rewrite bad(a:ℝ,b:ℝ):powerR(a^2*b,real(1,2))⇒a*sqrt(b) when 0≤b;"),
		("BadRootScaleDegree","rewrite bad(a:ℝ,b:ℝ):powerR(a^2*b,real(1,3))⇒a*powerR(b,real(1,3)) when 0≤a,0≤b;"),
		("BadComplexCubeRoot","rewrite bad(z:ℂ):cpow(z^3,real(1,3))⇒z;"),
		("BadCosQuarterTurn","lemma bad(x:ℝ):cos(x)⇒sin(x-real(1,2)*π);"),
		("BadTanPeriod","lemma bad(x:ℝ):tan(x)⇒tan(x-real(1,2)*π);"),
		("BadComplexCosImaginaryPart","rewrite bad(z:ℂ):cimag(ccos(z))⇒sin(creal(z))*sinh(cimag(z));"),
		("BadComplexSinRealPart","rewrite bad(z:ℂ):creal(csin(z))⇒sin(creal(z))*cos(cimag(z));"),
		("BadTanExpansion","rewrite bad(x:ℝ):sin(x)⇒tan(x)*cos(x);"),
		("BadComplexTanhExpansion","rewrite bad(z:ℂ):csinh(z)⇒ctanh(z)*ccosh(z);"),
		("BadExponentialPower","rewrite bad(z:ℂ,w:ℂ):powerC(cexp(z),w)⇒cexp(z*w);"),
		("BadExponentialRoot","rewrite bad(z:ℂ):csqrt(cexp(z))⇒cexp(z/2);"),
		("BadExponentialPowerBoundary","rewrite bad(z:ℂ,w:ℂ):powerC(cexp(z),w)⇒cexp(z*w) when -π≤cimag(z),cimag(z)≤π;"),
		("BadPhasePower","rewrite bad(x:ℝ,z:ℂ):powerC(cis(x),z)⇒cexp(ⅈ*x*z);"),
		("BadRealExponentialPower","rewrite bad(x:ℝ,y:ℝ):powerR(exp(x),y)⇒exp(x+y);"),
		("BadPhaseInverse","rewrite bad(x:ℝ):cis(x)⁻¹⇒cis(x);"),
		("BadExponentialRealPart","rewrite bad(z:ℂ):creal(cexp(z))⇒cos(cimag(z));"),
		("BadExponentialReal","rewrite bad(z:ℂ):cexp(z)⇒toℂ(exp(creal(z)));"),
		("BadHalfPowerNegative","rewrite bad(z:ℂ):powerC(z,real(1,2))⇒toℂ(sqrt(-creal(z))) when cimag(z)=0,creal(z)<0;"),
		("BadErfcDirection","rewrite bad(x:ℝ,y:ℝ):erfc(x)<erfc(y)⇒x<y;"),
		("BadAcosDirection","rewrite bad(x:ℝ,y:ℝ):acos(x)≤acos(y)⇒x≤y;"),
		("BadSinInjective","rewrite bad(x:ℝ,y:ℝ):sin(x)≠sin(y)⇒x≠y;"),
		("BadCoshInjective","rewrite bad(x:ℝ,y:ℝ):cosh(x)≠cosh(y)⇒x≠y;"),
		("BadComplexSinhInjective","rewrite bad(z:ℂ,w:ℂ):csinh(z)≠csinh(w)⇒z≠w;"),
		("BadImaginarySin","rewrite bad(z:ℂ):csin(ⅈ*z)⇒ⅈ*csin(z);"),
		("BadImaginaryCosSign","rewrite bad(z:ℂ):ccos(ⅈ*z)⇒-ccosh(z);"),
		("BadCancelNonnegative","rewrite bad(a:ℝ,x:ℝ,y:ℝ):a*x<a*y⇒x<y when 0≤a;"),
		("BadCancelNegativeDirection","rewrite bad(a:ℝ,x:ℝ,y:ℝ):a*x≤a*y⇒x≤y when a<0;"),
		("BadAsinDomain","rewrite bad(x:ℝ,y:ℝ):x<y⇒asin(x)<asin(y);"),
		("BadFloor","lemma bad(x:ℝ,n:ℤ):floor(x)⇒n when toℝ(n)≤x,defined(n);"),
		("BadFloorSum","rewrite bad(x:ℝ,y:ℝ):floor(x+y)⇒floor(x)+floor(y);"),
		("BadFloorBoundary","rewrite bad(x:ℝ,n:ℤ):floor(x)≤n⇒x≤toℝ(n)+1;"),
		("BadCeilBoundary","rewrite bad(x:ℝ,n:ℤ):ceil(x)<n⇒x<toℝ(n);"),
		("BadComplexLogInverse","rewrite bad(z:ℂ):clog(z⁻¹)⇒-clog(z);"),
		("BadComplexLogProduct","rewrite bad(z:ℂ,w:ℂ):clog(z*w)⇒clog(z)+clog(w);"),
		("BadComplexRealLog","rewrite bad(z:ℂ):clog(z)⇒toℂ(log(creal(z))) when cimag(z)=0;"),
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
		("BadPowerBases","rewrite bad(x:ℝ,y:ℝ,t:ℝ):powerR(x,t)<powerR(y,t)⇒x<y when 0<t;"),
		("BadPowerSign","rewrite bad(x:ℝ,y:ℝ,t:ℝ):powerR(x,t)≤powerR(y,t)⇒x≤y when t<0,0<x,0<y;"),
		("BadPowerBaseUnit","rewrite bad(x:ℝ,y:ℝ,b:ℝ):powerR(b,x)≠powerR(b,y)⇒x≠y when 0<b;"),
		("BadInverseSigns","rewrite bad(x:ℝ,y:ℝ):x⁻¹<y⁻¹⇒y<x;"),
		("BadComplexPowerRange","rewrite bad(z:ℂ,w:ℂ,t:ℂ):powerC(z,t)≠powerC(w,t)⇒z≠w when cimag(t)=0,0<creal(t);"),
		("BadComplexPowerZero","rewrite bad(z:ℂ,w:ℂ,t:ℂ):powerC(z,t)≠powerC(w,t)⇒z≠w when t=0;"),
		("BadComplexPowerNonzero","rewrite bad(z:ℂ,t:ℂ):powerC(z,t)≠0⇒z≠0;"),
		("BadRealRoot","rewrite bad(x:ℝ):sqrt(x^2)⇒x;"),
		("BadDistribution","rewrite bad(p:𝔹,q:𝔹,r:𝔹):(p∨q)∧r⇒(p∧r)∨(q∧r);"),
		("BadSwap","rewrite bad(p:𝔹,q:𝔹):p∧q⇒q∧p;"),
		("BadReciprocalClear","rewrite bad(x:ℝ,y:ℝ):x⁻¹+y≠0⇒1+y≠0;"),
		("BadComplexReciprocalClear","rewrite bad(x:ℂ,y:ℂ):x⁻¹+y≠0⇒1+y≠0;"),
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
	for name,body in (
		("BadPowerZero","theorem forged (x y t : ℝ) (hx : 0≤x) (hy : 0≤y) (ht : 0≤t) : x^t=y^t ↔ x=y :=\n"
			"  Real.rpow_left_inj hx hy ht\n"),
		("BadComplexPowerReal","theorem forged (z w t : ℂ) (hl : 0<t.re) (hu : t.re≤1) : z^t=w^t ↔ z=w :=\n"
			"  QSym.Elementary.cpow_contract_eq rfl hl hu\n"),
		("BadComplexPowerNegativeRange","theorem forged (z w t : ℂ) (hi : t.im=0) (hu : t.re<0) : z^t=w^t ↔ z=w :=\n"
			"  QSym.Elementary.cpow_negative_contract_eq hi (le_of_lt hu) hu\n")):
		path=negative/(name+".lean"); path.write_text("import QSym\n"+body)
		check(path,succeeds=False)
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
	deep=(ROOT/"build/regions/RawRealSum.lean").read_text()
	corrupt,count=re.subn(r"(def ac\d+_b\d+ : Replay.Bag 0 := \.leaf )1",r"\g<1>2",deep,count=1)
	if count!=1:
		raise RuntimeError("could not construct the invalid-multiplicity test")
	(negative/"WrongMultiplicity.lean").write_text(corrupt)
	check(negative/"WrongMultiplicity.lean",succeeds=False)
	for name,pattern,replacement in (
		("WrongBagBranch",r"(def ac\d+_b\d+ : Replay.Bag \d+ := \.node )([^\n]+)",r"\1Replay.Bag.zero Replay.Bag.zero"),
		("WrongBagIndex",r"(Replay.Bag.atom_sound Replay\.\w+ \(ac\d+_env ρ\) \d+ )\d+",r"\g<1>999999"),
		("WrongLookupLeaf",r"(\.leaf )v\d+",r"\1(fun _ => none)"),
		("WrongLookupOrder",r"\.node \(\.leaf (v\d+)\) \(\.leaf (v\d+)\)",r".node (.leaf \2) (.leaf \1)")):
		corrupt,count=re.subn(pattern,replacement,deep,count=1)
		if count!=1:
			raise RuntimeError("could not construct "+name)
		(negative/(name+".lean")).write_text(corrupt)
		check(negative/(name+".lean"),succeeds=False)

	counted=(ROOT/"build/regions/CountedSum.lean").read_text()
	root=re.search(r"theorem refinement .*? : Value.Refines \(Expr.eval ρ n(\d+)\)",counted).group(1)
	for name,pattern,replacement in (
		("WrongRegionCount",rf"(def b{root} : Region[^\n]+?\()\.twicePlusOne",r"\1.twice"),
		("WrongRegionOperand",rf"(def b{root} : Region[^\n]+? := \.item )n\d+",r"\1(Expr.real 0)")):
		corrupt,count=re.subn(pattern,replacement,counted,count=1)
		if count!=1:
			raise RuntimeError("could not construct "+name)
		(negative/(name+".lean")).write_text(corrupt)
		check(negative/(name+".lean"),succeeds=False)

	# Keep malformed symbolic powers small enough to report a type error.
	for name,file,pattern,replacement in (
		("WrongRepeatCoefficient","RealSumLarge",r"(Value\.refines_repeat_addR .+? )4294967295 ",r"\g<1>4294967294 "),
		("WrongRepeatExponent","ComplexProductGrouped",r"(Value\.refines_repeat_mul .+? )7 ",r"\g<1>6 "),
		("WrongRepeatWitness","RealSumMapped",r"Positive\.toNat_twicePlusOne",r"Positive.toNat_twice"),
		("WrongRepeatPremise","RealSumMapped",r"(\(x := \(v\d+ ρ\)\) \(y := (\(v\d+ ρ\))\)) \(p\d+ ρ\)",r"\1 (Value.refines_refl \2)")):
		source=(ROOT/"build/counted"/(file+".lean")).read_text()
		corrupt,count=re.subn(pattern,replacement,source,count=1)
		if count!=1:
			raise RuntimeError("could not construct "+name)
		(negative/(name+".lean")).write_text(corrupt)
		check(negative/(name+".lean"),succeeds=False)

	joined=(ROOT/"build/joins/RealSum3.lean").read_text()
	for name,pattern,replacement in (
		("WrongJoinOperation",r"\(Value\.refines_add \(a :=",r"(Value.refines_mul (a :="),
		("WrongJoinOperands",r"(\(Value\.refines_add )\(a := (\(v\d+ ρ\))\) \(b := (\(v\d+ ρ\))\)",r"\1(a := \3) (b := \2)"),
		("WrongJoinPremise",r"(\(Value\.refines_add .+? \(x := (\(v\d+ ρ\))\) \(y := \(v\d+ ρ\)\)) \(p\d+ ρ\)",r"\1 (Value.refines_refl \2)")):
		corrupt,count=re.subn(pattern,replacement,joined,count=1)
		if count!=1:
			raise RuntimeError("could not construct "+name)
		(negative/(name+".lean")).write_text(corrupt)
		check(negative/(name+".lean"),succeeds=False)

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
	def reject(item):
		path,source,timeout=item
		if path.read_bytes()!=source:
			raise RuntimeError("negative test changed before checking: "+str(path))
		run_check(path,succeeds=False,timeout=timeout)
	with ThreadPoolExecutor(max_workers=args.jobs) as pool:
		for _ in pool.map(reject,negative_checks):
			pass
	print(f"Rejected {len(negative_checks)} invalid proofs.",flush=True)
	print("All checks passed; only Lean's standard foundational axioms were used.")

if __name__=="__main__":
	try:
		main()
	except (RuntimeError,subprocess.CalledProcessError,subprocess.TimeoutExpired) as error:
		print(error,file=sys.stderr)
		sys.exit(1)
