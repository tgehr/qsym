module folding_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("FloorPositive","floor(7/3)","int(2)"),
		Example("FloorNegative","floor(-7/3)","int(-3)"),
		Example("CeilPositive","ceil(7/3)","int(3)"),
		Example("CeilNegative","ceil(-7/3)","int(-2)"),
		Example("RoundPositive","round(3/2)","int(2)"),
		Example("RoundNegative","round(-3/2)","int(-1)"),
		Example("RoundBelow","round(-8/5)","int(-2)"),
		Example("IntegerTrue","inZ(3)","true"),
		Example("IntegerFalse","inZ(3/2)","false"),
		Example("IntegerNegative","inZ(-2)","true"),
		Example("Gcd","gcd(int(-24),int(18))","nat(6)"),
		Example("GcdZero","gcd(int(0),int(0))","nat(0)"),
		Example("BooleanEquality","true=false","false"),
		Example("NaturalIndexedPower","powNN(nat(3),nat(4))","nat(81)"),
		Example("IntegerIndexedPower","powZN(int(-3),nat(3))","int(-27)"),
		Example("RationalIndexedPower","powQN(rat(2,3),nat(3))","rat(8,27)"),
		Example("RealIndexedPower","powRN(3,nat(4))","81"),
		Example("ComplexIndexedPower","powCN(1+ⅈ,nat(2))","2*ⅈ"),
		Example("RationalNegativePower","powQZ(rat(2,3),int(-2))","rat(9,4)"),
		Example("RealNegativePower","powRZ(2,int(-3))","1/8"),
		Example("ComplexNegativePower","powCZ(1+ⅈ,int(-2))","-ⅈ/2"),
		Example("ReciprocalRoot","pow(4,-1/2)","1/2"),
		Example("ComplexGeneralNegative","cpow(1+ⅈ,-2)","-ⅈ/2"),
		Example("CubeRoot","cbrt(27/8)","3/2"),
		Example("NegativeCubeRoot","cbrt(-8)","-2"),
		Example("Hypotenuse","hypot(3,4)","5"),
		Example("HypotenuseIrrational","hypot(1,1)","sqrt(2)"),
		Example("ComplexNorm","cabs(3+4*ⅈ)","5"),
		Example("ComplexRoot","csqrt(3+4*ⅈ)","2+ⅈ"),
		Example("ComplexRootNegativeImag","csqrt(3-4*ⅈ)","2-ⅈ"),
		Example("ImaginaryRoot","csqrt(-4)","2*ⅈ"),
		Example("Exp2","exp2(5)","32"),
		Example("Exp2Negative","exp2(-3)","1/8"),
		Example("Log2","log2(8)","3"),
		Example("Log2Fraction","log2(1/8)","-3"),
		Example("Log10","log10(1000)","3"),
		Example("ExpOne","exp(1)","e"),
		Example("LogE","log(e)","1"),
		Example("AsinZero","asin(0)","0"),
		Example("AsinOne","asin(1)","π/2"),
		Example("AcosOne","acos(1)","0"),
		Example("AcosZero","acos(0)","π/2"),
		Example("AcosNegativeOne","acos(-1)","π"),
		Example("AtanZero","atan(0)","0"),
		Example("AtanOne","atan(1)","π/4"),
		Example("AsinhZero","asinh(0)","0"),
		Example("AcoshOne","acosh(1)","0"),
		Example("AtanhZero","atanh(0)","0"),
		Example("ComplexAsinZero","casin(0)","complex(0,0)"),
		Example("ComplexAcosZero","cacos(0)","toℂ(π/2)"),
		Example("ComplexAtanZero","catan(0)","complex(0,0)"),
		Example("ComplexAsinhZero","casinh(0)","complex(0,0)"),
		Example("ComplexAcoshOne","cacosh(1)","complex(0,0)"),
		Example("ComplexAtanhZero","catanh(0)","complex(0,0)"),
		Example("ErfZero","erf(0)","0"),
		Example("ErfcZero","erfc(0)","1"),
		Example("Gamma","tgamma(6)","120"),
		Example("GammaComplex","cgamma(5)","complex(24,0)"),
		Example("LogGammaOne","lgamma(1)","0"),
		Example("Polar","cfromrt(2,π/2)","2*ⅈ"),
		Example("ImaginaryExponential","cexpi(π)","complex(-1,0)"),
		Example("PositiveArgument","carg(4)","0"),
		Example("NegativeArgument","carg(-4)","π"),
		Example("ImaginaryArgument","carg(2*ⅈ)","π/2"),
		Example("NegativeImaginaryArgument","carg(-2*ⅈ)","-π/2"),
		Example("Atan2Axis","atan2(2,0)","π/2"),
		Example("IrrationalSine","sin(1)","sin(1)"),
		Example("InvalidLog","log2(0)","log2(0)"),
		Example("InvalidArgument","carg(0)","carg(0)"),
		Example("InvalidGamma","tgamma(0)","tgamma(0)"),
		Example("InvalidRoot","sqrt(-1)","sqrt(-1)"),
		Example("InvalidPower","powRZ(0,int(-1))","powRZ(0,int(-1))"),
		Example("GuardedInvalid","[false]*log2(0)","0")
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
	assert(!failures,"constant folding regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: folding-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,run(a,s.parse(a,c.input),facts,true)));
	}
	writeln("Wrote folding certificates.");
}
