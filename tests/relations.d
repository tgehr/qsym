module relation_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("ArgHalfPower","carg(cpow(z,1/2))","carg(z)/2"),
		Example("ArgThirdPower","carg(cpow(z,1/3))","carg(z)/3"),
		Example("ArgRoot","carg(csqrt(z))","carg(z)/2"),
		Example("LogHalfPower","clog(cpow(z,1/2))","clog(z)/2"),
		Example("LogRoot","clog(csqrt(z))","clog(z)/2"),
		Example("NormRoot","cabs(csqrt(z))","sqrt(cabs(z))"),
		Example("RootSquared","csqrt(z)^2","z"),
		Example("ArgPowerFact","carg(cpow(z,x))","x*carg(z)",["0<x","x≤1"]),
		Example("LogPowerFact","clog(cpow(z,x))","toℂ(x)*clog(z)",["0<x","x≤1"]),
		Example("NormRealPower","cabs(cpow(z,x))","pow(cabs(z),x)"),
		Example("NormExponential","cabs(cexp(z))","exp(creal(z))"),
		Example("NormInverse","cabs(z⁻¹)","cabs(z)⁻¹"),
		Example("NormPower","cabs(z^3)","cabs(z)^3"),
		Example("NormCast","cabs(toℂ(x))","abs(x)"),
		Example("RealLog","creal(clog(z))","log(cabs(z))"),
		Example("ImaginaryLog","cimag(clog(z))","carg(z)"),
		Example("LogExpFact","clog(cexp(z))","z",["-π<cimag(z)","cimag(z)≤π"]),
		Example("ArgExpFact","carg(cexp(z))","cimag(z)",["-π<cimag(z)","cimag(z)≤π"]),
		Example("ArgPhaseFact","carg(cis(x))","x",["-π<x","x≤π"]),
		Example("SinhAsinh","sinh(asinh(x))","x"),
		Example("AsinhSinh","asinh(sinh(x))","x"),
		Example("CosAsin","cos(asin(x))","sqrt(1-x^2)"),
		Example("SinAcos","sin(acos(x))","sqrt(1-x^2)"),
		Example("ConjugateSin","conj(csin(z))","csin(conj(z))"),
		Example("ConjugateCos","conj(ccos(z))","ccos(conj(z))"),
		Example("ConjugateSinh","conj(csinh(z))","csinh(conj(z))"),
		Example("ConjugateCosh","conj(ccosh(z))","ccosh(conj(z))"),
		Example("ArgZeroPower","carg(cpow(0,1/2))","carg(cpow(0,1/2))"),
		Example("ArgUnboundedPower","carg(cpow(z,3/2))","carg(cpow(z,3/2))"),
		Example("ArgNegativePower","carg(cpow(z,-1/2))","carg(cpow(z,-1/2))"),
		Example("LogUnboundedPower","clog(cpow(z,3/2))","clog(cpow(z,3/2))"),
		Example("ComplexExponent","carg(cpow(z,1/2+ⅈ))","carg(cpow(z,1/2+ⅈ))"),
		Example("LogExpUnbounded","clog(cexp(z))","clog(cexp(z))"),
		Example("ArgExpUnbounded","carg(cexp(z))","carg(cexp(z))"),
		Example("ArgLowerBoundary","carg(cis(-π))","π"),
		Example("ArgUpperBoundary","carg(cis(π))","π"),
		Example("GuardedArgRoot","[z≠0]*carg(cpow(z,1/2))","[z≠0]*carg(z)/2")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,t:ℝ,z:ℂ,w:ℂ,p:𝔹"); return s; }
private Result run(Arena a,Term t,Term[] facts,bool trace=false){
	return simplify(a,t,facts,Options(DensityMode.preserve,trace));
}
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected,a.sort(input))).output;
		auto fast=run(a,input,facts),checked=run(a,input,facts,true);
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(run(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"builtin relation regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: relation-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,run(a,s.parse(a,c.input),facts,true)));
	}
	writeln("Wrote relation certificates.");
}
