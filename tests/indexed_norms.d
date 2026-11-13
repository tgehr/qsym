module indexed_norm_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; bool domain,unchanged; }
Example[] examples(){
	return [
		Example("RealNatural","abs(x^n)","abs(x)^n"),
		Example("RealInteger","abs(x^k)","abs(x)^k"),
		Example("ComplexNatural","cabs(z^n)","cabs(z)^n"),
		Example("ComplexInteger","cabs(z^k)","cabs(z)^k"),
		Example("ConjugateNatural","conj(z^n)","conj(z)^n"),
		Example("ConjugateInteger","conj(z^k)","conj(z)^k"),
		Example("RealInverse","abs((1/x)^k)","(1/abs(x))^k"),
		Example("ComplexInverse","cabs((1/z)^k)","(1/cabs(z))^k"),
		Example("ConjugateInverse","conj((1/z)^k)","(1/conj(z))^k"),
		Example("NormConjugate","cabs(conj(z^k))","cabs(z)^k"),
		Example("DoubleConjugate","conj(conj(z)^n)","z^n"),
		Example("AbsoluteNorm","abs(cabs(z^k))","cabs(z)^k"),
		Example("RealLog","abs(log(x)^n)","abs(log(x))^n"),
		Example("ComplexLog","cabs(clog(z)^k)","cabs(clog(z))^k"),
		Example("ConjugateLog","conj(clog(z)^n)","conj(clog(z))^n"),
		Example("NaturalIndex","cabs(z^(n+1))","cabs(z)^(n+1)"),
		Example("IntegerIndex","conj(z^(k-1))","conj(z)^(k-1)"),
		Example("PartialIndex","cabs(z^(n sub 1))","cabs(z)^(n sub 1)"),
		Example("RealMask","[p]*abs(x^k)","[p]*abs(x)^k"),
		Example("ComplexMask","[p]*cabs(z^k)","[p]*cabs(z)^k"),
		Example("ConjugateMask","[p]*conj(z^k)","[p]*conj(z)^k"),
		Example("FalseReal","[false]*abs((1/x)^k)","0"),
		Example("FalseComplex","[false]*cabs((1/z)^k)","0"),
		Example("FalseConjugate","[false]*conj((1/z)^k)","toℂ(0)"),
		Example("TrueReal","[true]*abs(x^n)","abs(x)^n"),
		Example("TrueComplex","[true]*cabs(z^n)","cabs(z)^n"),
		Example("TrueConjugate","[true]*conj(z^n)","conj(z)^n"),
		Example("UndefinedRealMask","[1/0=1]*abs(x^k)","[1/0=1]*abs(x)^k"),
		Example("UndefinedComplexMask","[1/0=1]*cabs(z^k)","[1/0=1]*cabs(z)^k"),
		Example("UndefinedConjugateMask","[1/0=1]*conj(z^k)","[1/0=1]*conj(z)^k"),
		Example("ZeroRealBase","abs((0:ℝ)^k)","(0:ℝ)^k"),
		Example("ZeroComplexBase","cabs((0:ℂ)^k)","(0:ℝ)^k"),
		Example("ZeroConjugateBase","conj((0:ℂ)^k)","(0:ℂ)^k"),
		Example("RealDomain","abs(x^k)","x≠0∨0≤k",[],true),
		Example("ComplexDomain","cabs(z^k)","z≠0∨0≤k",[],true),
		Example("ConjugateDomain","conj(z^k)","z≠0∨0≤k",[],true),
		Example("ZeroDomain","cabs((0:ℂ)^k)","0≤k",[],true),
		Example("NaturalDomain","cabs(z^n)","true",[],true),
		Example("UndefinedNaturalIndex","cabs(z^(0 sub 1))","false",[],true),
		Example("UndefinedRealBase","abs((1/0)^n)","false",[],true),
		Example("UndefinedComplexBase","cabs((1/toℂ(0))^n)","false",[],true),
		Example("NegativeIntegerPower","cabs(z^(-3:ℤ))","cabs(z)^(-3:ℤ)"),
		Example("NegativeRealPower","abs(x^(-3:ℤ))","abs(x)^(-3:ℤ)"),
		Example("NegativeConjugatePower","conj(z^(-3:ℤ))","conj(z)^(-3:ℤ)"),
		Example("NegativeZeroDomain","cabs((0:ℂ)^(-1:ℤ))","false",[],true),
		Example("ZeroPower","cabs(z^(0:ℕ))","1"),
		Example("RealAssumption","abs(x^k)","x^k",["0≤x"]),
		Example("IndexAssumption","cabs(z^k)","cabs(z)^2",["k=2"]),
		Example("UnitCircleNatural","cabs(cis(x)^n)","1"),
		Example("UnitCircleInteger","cabs(cexp(ⅈ*toℂ(x))^k)","1"),
		Example("NegativeUnitNatural","abs((-1:ℝ)^n)","1"),
		Example("NegativeUnitInteger","abs((-1:ℝ)^k)","1"),
		Example("GeneralComplexPower","conj(z^w)","conj(z^w)",[],false,true),
		Example("GeneralComplexNorm","cabs(z^w)","cabs(z^w)",[],false,true),
	];
}
@system void main(string[] args){
	enforce(args.length==2,"usage: indexed-norm-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; Syntax s; s.declare("x:ℝ,z:ℂ,w:ℂ,n:ℕ,k:ℤ,p:𝔹");
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input); if(c.domain) input=definedness(a,input);
		auto expected=simplify(a,s.parse(a,c.expected,a.sort(input)),facts).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		enforce(!fast.exhausted&&fast.output==expected,c.name~": "~s.format(a,fast.output)~"; expected "~s.format(a,expected));
		enforce(fast.output==checked.output&&!checked.exhausted,c.name~" tracing");
		enforce(!c.unchanged||fast.output==input,c.name~" branch boundary");
		auto again=simplify(a,fast.output,facts);
		enforce(!again.exhausted&&again.output==fast.output,c.name~" idempotence");
		auto roundtrip=simplify(a,s.parse(a,s.format(a,fast.output),a.sort(fast.output)),facts);
		enforce(!roundtrip.exhausted&&roundtrip.output==fast.output,c.name~" round trip");
		write(buildPath(args[1],c.name~".lean"),exportLean(a,checked));
		writeln(c.name,": ",s.format(a,fast.output));
	}
	writeln("Checked ",examples().length," indexed norm cases and wrote certificates.");
}
