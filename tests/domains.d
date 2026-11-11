module domain_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("ComplexTanhAsinhPole","ctanh(casinh(ⅈ))","false"),
		Example("ComplexTanhAsinhNegativePole","ctanh(casinh(-ⅈ))","false"),
		Example("ComplexTanhAcoshPole","ctanh(cacosh(0))","false"),
		Example("RealTanhAcoshOutside","tanh(acosh(-2))","false"),
		Example("ComplexTanhAsinhMaskedPole","[false]*ctanh(casinh(ⅈ))","true"),
		Example("ComplexTanhAcoshMaskedPole","[false]*ctanh(cacosh(0))","true"),
		Example("RealTanhAcoshBoundary","tanh(acosh(1))","true"),
		Example("RealTanhAsinhPartial","tanh(asinh(log(x)))","0<x"),
		Example("RightComplexLog","clog(z)*[z≠0]","true"),
		Example("LeftComplexLog","[z≠0]*clog(z)","true"),
		Example("MiddleGuard","log(x)*[x>0]*(1/x)","true"),
		Example("EndGuard","log(x)*(1/x)*[x>0]","true"),
		Example("NestedRightGuard","log(x)*((1/x)*[x>0])","true"),
		Example("FalseRightGuard","log(0)*[false]","true"),
		Example("GuardSumBoundary","log(0)+[false]","false"),
		Example("StrictRightIndicator","mulR(log(0),[false])","false"),
		Example("StrictGuardedBody","mulR(maskR(false,log(0)),1/0)","false"),
		Example("RationalRightGuard","q⁻¹*[q≠0]","true"),
		Example("IntegerRightGuard","floor(log(x))*[x>0]","true"),
		Example("NaturalRightGuard","denominator(qfromnd(k,j))*[j≠0]","true"),
		Example("GuardOrder","[x≠0]*[1/x>0]","true"),
		Example("PartialGuardOrder","[1/x>0]*[x≠0]","x≠0"),
		Example("Literal","42","true"),
		Example("Variable","x","true"),
		Example("Reciprocal","1/x","x≠0"),
		Example("ZeroReciprocal","1/0","false"),
		Example("StrictZero","0*(1/0)","false"),
		Example("StrictCancel","1/x-1/x","x≠0"),
		Example("StrictZeroPower","(1/x)^0","x≠0"),
		Example("GuardedInverse","[x≠0]/x","true"),
		Example("GuardedUndefined","[false]*(1/0)","true"),
		Example("TrueGuard","[true]*(1/x)","x≠0"),
		Example("VariableGuard","[p]/x","¬p∨x≠0"),
		Example("PartialGuard","[1/x>0]*0","x≠0"),
		Example("GuardProduct","[x≠0]*[1/x>0]*log(x)","true"),
		Example("NestedGuard","[x≠0]*([1/x>0]*log(x))","true"),
		Example("ShortAnd","false∧1/0>0","true"),
		Example("ShortOr","true∨1/0>0","true"),
		Example("StrictAndLeft","1/0>0∧false","false"),
		Example("StrictOrLeft","1/0>0∨true","false"),
		Example("BooleanAnd","p∧1/x>0","¬p∨x≠0"),
		Example("BooleanOr","p∨1/x>0","p∨x≠0"),
		Example("BooleanNot","¬(1/x>0)","x≠0"),
		Example("BooleanEquality","(1/x>0)=p","x≠0"),
		Example("Sqrt","sqrt(x)","0≤x"),
		Example("SqrtNegative","sqrt(-1)","false"),
		Example("SqrtZero","sqrt(0)","true"),
		Example("SqrtReciprocal","sqrt(1/x)","0<x"),
		Example("Log","log(x)","0<x"),
		Example("LogZero","log(0)","false"),
		Example("LogNested","log(log(x))","1<x"),
		Example("LogReciprocal","log(1/x)","0<x"),
		Example("LogBaseTwo","log2(x)","0<x"),
		Example("LogBaseTen","log10(x)","0<x"),
		Example("Tangent","tan(x)","cos(x)≠0"),
		Example("TangentPole","tan(π/2)","false"),
		Example("TangentRegular","tan(π)","true"),
		Example("Asin","asin(x)","-1≤x∧x≤1"),
		Example("Acos","acos(x)","-1≤x∧x≤1"),
		Example("AsinBoundary","asin(-1)","true"),
		Example("AsinOutside","asin(2)","false"),
		Example("Acosh","acosh(x)","1≤x"),
		Example("Atanh","atanh(x)","-1<x∧x<1"),
		Example("AtanhPole","atanh(1)","false"),
		Example("CompositionBeforeRewrite","tanh(atanh(x))","-1<x∧x<1"),
		Example("RealPower","x^y","(0≤x∨inZ(y))∧(x≠0∨0≤y)"),
		Example("ZeroRealPower","0^y","0≤y"),
		Example("NegativeRealPower","(-2)^y","inZ(y)"),
		Example("RealPowerZeroZero","powerR(0,0)","true"),
		Example("RealPowerZeroNegative","powerR(0,-1/2)","false"),
		Example("NegativeFractionalPower","powerR(-2,1/2)","false"),
		Example("NegativeIntegerPower","powerR(-2,-3)","true"),
		Example("IntegerPower","powRZ(x,k)","x≠0∨int(0)≤k"),
		Example("RationalPower","powQZ(q,k)","q≠rat(0,1)∨int(0)≤k"),
		Example("NaturalPower","powRN(1/x,n)","x≠0"),
		Example("RationalInverse","1/q","q≠rat(0,1)"),
		Example("RationalConstructor","qfromnd(k,j)","j≠int(0)"),
		Example("AtanTwo","atan2(x,y)","y≠0∨x≠0"),
		Example("AtanTwoOrigin","atan2(0,0)","false"),
		Example("ComplexRoot","csqrt(z)","true"),
		Example("ComplexLog","clog(z)","z≠0"),
		Example("ComplexArgument","carg(z)","z≠0"),
		Example("ComplexTan","ctan(z)","ccos(z)≠0"),
		Example("ComplexTanh","ctanh(z)","ccosh(z)≠0"),
		Example("ComplexAtan","catan(z)","z≠ⅈ∧z≠-ⅈ"),
		Example("ComplexAtanPositivePole","catan(ⅈ)","false"),
		Example("ComplexAtanNegativePole","catan(-ⅈ)","false"),
		Example("ComplexAtanh","catanh(z)","z≠1∧z≠-1"),
		Example("ComplexAtanhPole","catanh(-1)","false"),
		Example("ComplexPower","z^w","z≠0∨(0≤creal(w)∧cimag(w)=0)"),
		Example("ComplexZeroPower","cpow(0,w)","0≤creal(w)∧cimag(w)=0"),
		Example("ComplexZeroZero","cpow(0,0)","true"),
		Example("ComplexZeroImaginary","cpow(0,ⅈ)","false"),
		Example("ComplexZeroNegative","cpow(0,-1)","false"),
		Example("ComplexZeroPositive","cpow(0,1/2)","true"),
		Example("ComplexIntegerPower","powCZ(z,k)","z≠0∨int(0)≤k"),
		Example("ComplexNested","csin(casin(clog(z)))","z≠0"),
		Example("RealGamma","tgamma(x)","0<x∨¬inZ(x)"),
		Example("RealGammaPole","tgamma(-2)","false"),
		Example("RealGammaFraction","tgamma(-1/2)","true"),
		Example("LogGamma","lgamma(x)","(0<x∨¬inZ(x))∧tgamma(x)≠0"),
		Example("LogGammaPole","lgamma(0)","false"),
		Example("ComplexGamma","cgamma(z)","cimag(z)≠0∨(0<creal(z)∨¬inZ(creal(z)))"),
		Example("ComplexGammaPole","cgamma(-2)","false"),
		Example("ComplexGammaOffAxis","cgamma(-2+ⅈ)","true"),
		Example("AssumedInverse","1/x","true",["x≠0"]),
		Example("AssumedSqrt","sqrt(x)","true",["0≤x"]),
		Example("AssumedUndefined","sqrt(x)","false",["x<0"]),
		Example("AssumedGuard","[p]/x","x≠0",["p"]),
		Example("AssumedPartial","sqrt(1/x)","true",["1/x>0"]),
		Example("Density","puncture(lebesgue())","true"),
		Example("DensityPoint","densityAt(puncture(lebesgue()),1/x)","x≠0"),
		Example("Measure","forget(puncture(lebesgue()))","true")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ,p:𝔹,n:ℕ,k:ℤ,j:ℤ,q:ℚ"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		scope(failure) writeln("FAIL ",c.name);
		auto session=Session.open(); auto a=session.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto original=s.parse(a,c.input),condition=definedness(a,original);
		auto options=Options.init; options.distributeLogic=false;
		auto expected=simplify(a,s.parse(a,c.expected),facts,options);
		auto fast=simplifyDomain(a,original,facts),checked=simplifyDomain(a,original,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||expected.exhausted||fast.output!=expected.output){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output)," expected ",s.format(a,expected.output)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		assert(a.sort(fast.output)==Sort.boolean,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts,options).output==fast.output,c.name~" is not idempotent");
		auto roundtrip=s.parse(a,s.format(a,fast.output));
		assert(simplify(a,roundtrip,facts,options).output==fast.output,c.name~" does not roundtrip");
		exportDomainLean(a,original,checked);
	}
	assert(!failures,"domain regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: domain-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		scope(failure) writeln("FAIL ",c.name);
		auto session=Session.open(); auto a=session.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto original=s.parse(a,c.input);
		write(buildPath(args[1],c.name~".lean"),exportDomainLean(a,original,
			simplifyDomain(a,original,facts,Options(DensityMode.preserve,true))));
	}
	foreach(i;0..cast(uint)Builtin.invalid){
		auto f=cast(Builtin)i,info=builtinInfo(f);
		auto session=Session.open(); auto a=session.arena;
		Term[] xs; foreach(j,sort;info.args) xs~=a.variable(sort,cast(uint)j);
		auto original=a.call(f,xs);
		write(buildPath(args[1],"Builtin_"~info.code~".lean"),exportDomainLean(a,original,
			simplifyDomain(a,original,[],Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length+cast(uint)Builtin.invalid," domain certificates.");
}
