module exponential_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("NewsinhLog","sinh(log(x))","(x-x⁻¹)/2"),
		Example("NewsinhLogPartial","sinh(log(log(x)))","((log(x))-(log(x))⁻¹)/2"),
		Example("NewsinhLogMasked","[false]*(sinh(log(x)))","0"),
		Example("NewsinhLogTwo","sinh(log(2))","((2)-(2)⁻¹)/2"),
		Example("NewsinhLogHalf","sinh(log(1/2))","((1/2)-(1/2)⁻¹)/2"),
		Example("NewsinhLogOne","sinh(log(1))","((1)-(1)⁻¹)/2"),
		Example("NewsinhLogGuard","[0<x]*(sinh(log(x)))","[0<x]*((x-x⁻¹)/2)"),
		Example("NewcoshLog","cosh(log(x))","(x+x⁻¹)/2"),
		Example("NewcoshLogPartial","cosh(log(log(x)))","((log(x))+(log(x))⁻¹)/2"),
		Example("NewcoshLogMasked","[false]*(cosh(log(x)))","0"),
		Example("NewcoshLogTwo","cosh(log(2))","((2)+(2)⁻¹)/2"),
		Example("NewcoshLogHalf","cosh(log(1/2))","((1/2)+(1/2)⁻¹)/2"),
		Example("NewcoshLogOne","cosh(log(1))","((1)+(1)⁻¹)/2"),
		Example("NewcoshLogGuard","[0<x]*(cosh(log(x)))","[0<x]*((x+x⁻¹)/2)"),
		Example("NewtanhLog","tanh(log(x))","(x^2-1)/(x^2+1)"),
		Example("NewtanhLogPartial","tanh(log(log(x)))","((log(x))^2-1)/((log(x))^2+1)"),
		Example("NewtanhLogMasked","[false]*(tanh(log(x)))","0"),
		Example("NewtanhLogTwo","tanh(log(2))","((2)^2-1)/((2)^2+1)"),
		Example("NewtanhLogHalf","tanh(log(1/2))","((1/2)^2-1)/((1/2)^2+1)"),
		Example("NewtanhLogOne","tanh(log(1))","((1)^2-1)/((1)^2+1)"),
		Example("NewtanhLogGuard","[0<x]*(tanh(log(x)))","[0<x]*((x^2-1)/(x^2+1))"),
		Example("NewcsinhLog","csinh(clog(z))","(z-z⁻¹)/2"),
		Example("NewcsinhLogPartial","csinh(clog(clog(z)))","((clog(z))-(clog(z))⁻¹)/2"),
		Example("NewcsinhLogMasked","[false]*(csinh(clog(z)))","toℂ(0)"),
		Example("NewcsinhLogTwo","csinh(clog(2))","((2)-(2)⁻¹)/2"),
		Example("NewcsinhLogNegativeCut","csinh(clog(-2))","((-2)-(-2)⁻¹)/2"),
		Example("NewcsinhLogUpper","csinh(clog(2*ⅈ))","((2*ⅈ)-(2*ⅈ)⁻¹)/2"),
		Example("NewcsinhLogLower","csinh(clog(-2*ⅈ))","((-2*ⅈ)-(-2*ⅈ)⁻¹)/2"),
		Example("NewcsinhLogOne","csinh(clog(1))","((1)-(1)⁻¹)/2"),
		Example("NewccoshLog","ccosh(clog(z))","(z+z⁻¹)/2"),
		Example("NewccoshLogPartial","ccosh(clog(clog(z)))","((clog(z))+(clog(z))⁻¹)/2"),
		Example("NewccoshLogMasked","[false]*(ccosh(clog(z)))","toℂ(0)"),
		Example("NewccoshLogTwo","ccosh(clog(2))","((2)+(2)⁻¹)/2"),
		Example("NewccoshLogNegativeCut","ccosh(clog(-2))","((-2)+(-2)⁻¹)/2"),
		Example("NewccoshLogUpper","ccosh(clog(2*ⅈ))","((2*ⅈ)+(2*ⅈ)⁻¹)/2"),
		Example("NewccoshLogLower","ccosh(clog(-2*ⅈ))","((-2*ⅈ)+(-2*ⅈ)⁻¹)/2"),
		Example("NewccoshLogOne","ccosh(clog(1))","((1)+(1)⁻¹)/2"),
		Example("NewctanhLog","ctanh(clog(z))","(z^2-1)/(z^2+1)"),
		Example("NewctanhLogPartial","ctanh(clog(clog(z)))","((clog(z))^2-1)/((clog(z))^2+1)"),
		Example("NewctanhLogMasked","[false]*(ctanh(clog(z)))","toℂ(0)"),
		Example("NewctanhLogTwo","ctanh(clog(2))","((2)^2-1)/((2)^2+1)"),
		Example("NewctanhLogNegativeCut","ctanh(clog(-2))","((-2)^2-1)/((-2)^2+1)"),
		Example("NewctanhLogUpper","ctanh(clog(2*ⅈ))","((2*ⅈ)^2-1)/((2*ⅈ)^2+1)"),
		Example("NewctanhLogLower","ctanh(clog(-2*ⅈ))","((-2*ⅈ)^2-1)/((-2*ⅈ)^2+1)"),
		Example("NewctanhLogOne","ctanh(clog(1))","((1)^2-1)/((1)^2+1)"),
		Example("NewctanhLogMaskedUpperPole","[false]*ctanh(clog(ⅈ))","toℂ(0)"),
		Example("NewctanhLogMaskedLowerPole","[false]*ctanh(clog(-ⅈ))","toℂ(0)"),
		Example("NewsinhLogMaskedZero","[false]*sinh(log(0))","0"),
		Example("NewcsinhLogMaskedZero","[false]*csinh(clog(0))","toℂ(0)"),

		Example("NewLog2Product","log2(x*y)","log2(x)+log2(y)",["0<x", "0<y"]),
		Example("NewLog2Quotient","log2(x/y)","log2(x)-log2(y)",["0<x", "0<y"]),
		Example("NewLog2Inverse","log2(x⁻¹)","-log2(x)",[]),
		Example("NewLog2Power","log2(x^4)","4*log2(x)",["0<x"]),
		Example("NewLog2Matching","log2(powerR(2,x))","x",[]),
		Example("NewLog2MatchingPartial","log2(powerR(2,log(x)))","log(x)",[]),
		Example("NewLog2MatchingNegative","log2(powerR(2,-x))","-x",[]),
		Example("NewLog2MatchingNested","log2(powerR(2,log2(x)))","log2(x)",[]),
		Example("NewLog2ProductGuard","[0<x∧0<y]*log2(x*y)","[0<x∧0<y]*(log2(x)+log2(y))",[]),
		Example("NewLog2InversePartial","log2(log(x)⁻¹)","-log2(log(x))",[]),
		Example("NewLog2PowerPartial","log2(log(x)^3)","3*log2(log(x))",["0<log(x)"]),
		Example("NewLog2ProductPartial","log2(log(x)*y)","log2(log(x))+log2(y)",["0<log(x)", "0<y"]),
		Example("NewLog2UnknownProduct","log2(x*y)","log2(x*y)",[]),
		Example("NewLog2NegativeProduct","log2(x*y)","log2(x*y)",["x<0", "y<0"]),
		Example("NewLog2NegativePower","log2(x^2)","log2(x^2)",["x<0"]),
		Example("NewLog2MaskedPole","[false]*log2(0⁻¹)","0",[]),
		Example("NewLog2MaskedProduct","[false]*log2(x*y)","0",[]),
		Example("NewLog2InverseOne","log2(1⁻¹)","0",[]),
		Example("NewLog10Product","log10(x*y)","log10(x)+log10(y)",["0<x", "0<y"]),
		Example("NewLog10Quotient","log10(x/y)","log10(x)-log10(y)",["0<x", "0<y"]),
		Example("NewLog10Inverse","log10(x⁻¹)","-log10(x)",[]),
		Example("NewLog10Power","log10(x^4)","4*log10(x)",["0<x"]),
		Example("NewLog10Matching","log10(powerR(10,x))","x",[]),
		Example("NewLog10MatchingPartial","log10(powerR(10,log(x)))","log(x)",[]),
		Example("NewLog10MatchingNegative","log10(powerR(10,-x))","-x",[]),
		Example("NewLog10MatchingNested","log10(powerR(10,log10(x)))","log10(x)",[]),
		Example("NewLog10ProductGuard","[0<x∧0<y]*log10(x*y)","[0<x∧0<y]*(log10(x)+log10(y))",[]),
		Example("NewLog10InversePartial","log10(log(x)⁻¹)","-log10(log(x))",[]),
		Example("NewLog10PowerPartial","log10(log(x)^3)","3*log10(log(x))",["0<log(x)"]),
		Example("NewLog10ProductPartial","log10(log(x)*y)","log10(log(x))+log10(y)",["0<log(x)", "0<y"]),
		Example("NewLog10UnknownProduct","log10(x*y)","log10(x*y)",[]),
		Example("NewLog10NegativeProduct","log10(x*y)","log10(x*y)",["x<0", "y<0"]),
		Example("NewLog10NegativePower","log10(x^2)","log10(x^2)",["x<0"]),
		Example("NewLog10MaskedPole","[false]*log10(0⁻¹)","0",[]),
		Example("NewLog10MaskedProduct","[false]*log10(x*y)","0",[]),
		Example("NewLog10InverseOne","log10(1⁻¹)","0",[]),

		Example("Euler","e","exp(1)"),
		Example("EulerSquare","e^2","exp(2)"),
		Example("EulerInverse","1/e","exp(-1)"),
		Example("EulerVariablePower","e^x","exp(x)"),
		Example("EulerNaturalPower","e^n","exp(toℝ(n))"),
		Example("EulerIntegerPower","e^k","exp(toℝ(k))"),
		Example("EulerComplexPower","e^z","cexp(z)"),
		Example("EulerFullTurn","e^(2*π*ⅈ)","complex(1,0)"),
		Example("EulerHalfTurn","e^(π*ⅈ)","complex(-1,0)"),
		Example("EulerQuarterTurn","e^(π*ⅈ/2)","ⅈ"),
		Example("EulerNegativeTurn","e^(-2*π*ⅈ)","complex(1,0)"),
		Example("EulerRealLog","e^log(x)","x"),
		Example("EulerComplexLog","e^clog(z)","z"),
		Example("EulerLogShift","e^(1+log(x))","e*x"),
		Example("EulerLogScale","e^(y*log(x))","x^y"),
		Example("EulerComplexLogScale","e^(w*clog(z))","cpow(z,w)"),
		Example("EulerCancellation","exp(-1)*e","1"),
		Example("FoldedCancellation","exp(1)*exp(-1)","1"),
		Example("EulerProduct","e*exp(x)","exp(x+1)"),
		Example("EulerPowerProduct","exp(x)*e^3","exp(x+3)"),
		Example("EulerQuotient","e/exp(x)","exp(1-x)"),
		Example("QuotientEuler","exp(x)/e","exp(x-1)"),
		Example("NestedQuotient","exp(x)/(e*exp(y))","exp(x-y-1)"),
		Example("RealInverse","1/exp(x)","exp(-x)"),
		Example("RealProduct","exp(x)*exp(y)","exp(x+y)"),
		Example("RealRealPower","exp(x)^y","exp(x*y)"),
		Example("RealNegativePower","exp(x)^(-3)","exp(-3*x)"),
		Example("RealNaturalPower","exp(x)^n","exp(toℝ(n)*x)"),
		Example("RealIntegerPower","exp(x)^k","exp(toℝ(k)*x)"),
		Example("RealRoot","sqrt(exp(x))","exp(x/2)"),
		Example("EulerRoot","sqrt(e)","exp(1/2)"),
		Example("RealFractionalPower","exp(x)^(1/3)","exp(x/3)"),
		Example("RealRootProduct","sqrt(exp(x))*exp(-x/2)","1"),
		Example("RealNestedPower","(e^x)^y","exp(x*y)"),
		Example("RealLogCancellation","exp(log(x))*exp(-log(x))","1"),
		Example("ComplexReal","cexp(x)","toℂ(exp(x))"),
		Example("ComplexRealOne","cexp(1)","toℂ(e)"),
		Example("ComplexRealNegative","cexp(-1)","toℂ(exp(-1))"),
		Example("ComplexRealFact","cexp(z)","toℂ(exp(creal(z)))",["cimag(z)=0"]),
		Example("ComplexInverse","1/cexp(z)","cexp(-z)"),
		Example("ComplexEulerCancellation","cexp(-1)*e","complex(1,0)"),
		Example("ComplexEulerProduct","e*cexp(z)","cexp(z+1)"),
		Example("ComplexEulerQuotient","cexp(z)/e","cexp(z-1)"),
		Example("ComplexMixedProduct","exp(x)*cexp(z)","cexp(z+x)"),
		Example("ComplexMixedQuotient","exp(x)/cexp(z)","cexp(toℂ(x)-z)"),
		Example("ComplexCastProduct","cexp(x)*cexp(y)","toℂ(exp(x+y))"),
		Example("ComplexCastQuotient","cexp(x)/cexp(y)","toℂ(exp(x-y))"),
		Example("ComplexNaturalPower","cexp(z)^n","cexp(toℂ(n)*z)"),
		Example("ComplexIntegerPower","cexp(z)^k","cexp(toℂ(k)*z)"),
		Example("ComplexRealNaturalPower","cexp(x)^n","toℂ(exp(toℝ(n)*x))"),
		Example("ComplexRealIntegerPower","cexp(x)^k","toℂ(exp(toℝ(k)*x))"),
		Example("ComplexRealBasePower","cpow(cexp(x),z)","cexp(x*z)"),
		Example("ComplexRealRoot","csqrt(cexp(x))","toℂ(exp(x/2))"),
		Example("ComplexStripPower","cpow(cexp(z),w)","cexp(z*w)",["-π<cimag(z)","cimag(z)≤π"]),
		Example("ComplexStripRoot","csqrt(cexp(z))","cexp(z/2)",["-π<cimag(z)","cimag(z)≤π"]),
		Example("ComplexPowerRetained","cpow(cexp(z),w)","cpow(cexp(z),w)"),
		Example("ComplexRootRetained","csqrt(cexp(z))","csqrt(cexp(z))"),
		Example("ComplexPowerUpperCut","cpow(cexp(π*ⅈ),1/2)","ⅈ"),
		Example("ComplexPowerLowerCut","cpow(cexp(-π*ⅈ),1/2)","ⅈ"),
		Example("ComplexHalfPositive","cpow(4,1/2)","complex(2,0)"),
		Example("ComplexHalfZero","cpow(0,1/2)","complex(0,0)"),
		Example("ComplexHalfNegative","cpow(-4,1/2)","2*ⅈ"),
		Example("ComplexHalfNonnegativeFact","cpow(z,1/2)","toℂ(sqrt(creal(z)))",["cimag(z)=0","0≤creal(z)"]),
		Example("ComplexHalfExponentFact","cpow(z,w)","toℂ(sqrt(creal(z)))",["w=1/2","cimag(z)=0","0≤creal(z)"]),
		Example("PhaseProduct","cis(x)*cis(y)","cis(x+y)"),
		Example("PhaseInverse","1/cis(x)","cis(-x)"),
		Example("PhaseConjugate","conj(cis(x))","cis(-x)"),
		Example("PhaseQuotient","cis(x)/cis(y)","cis(x-y)"),
		Example("PhaseSquare","cis(x)^2","cis(2*x)"),
		Example("PhaseNegativePower","cis(x)^(-3)","cis(-3*x)"),
		Example("PhaseNaturalPower","cis(x)^n","cis(toℝ(n)*x)"),
		Example("PhaseIntegerPower","cis(x)^k","cis(toℝ(k)*x)"),
		Example("PhaseComplexProduct","cis(x)*cexp(z)","cexp(z+ⅈ*x)"),
		Example("PhaseRealProduct","cis(x)*exp(y)","cexp(y+ⅈ*x)"),
		Example("PhaseEulerProduct","cis(x)*e","cexp(1+ⅈ*x)"),
		Example("PhaseComplexQuotient","cexp(z)/cis(x)","cexp(z-ⅈ*x)"),
		Example("PhaseStripPower","cpow(cis(x),z)","cexp(ⅈ*x*z)",["-π<x","x≤π"]),
		Example("PhasePowerRetained","cpow(cis(x),z)","cpow(cis(x),z)"),
		Example("PhaseRealPart","creal(cis(x))","cos(x)"),
		Example("PhaseImaginaryPart","cimag(cis(x))","sin(x)"),
		Example("ComplexRealPart","creal(cexp(z))","exp(creal(z))*cos(cimag(z))"),
		Example("ComplexImaginaryPart","cimag(cexp(z))","exp(creal(z))*sin(cimag(z))"),
		Example("EulerRealPart","creal(e^(ⅈ*x))","cos(x)"),
		Example("EulerImaginaryPart","cimag(e^(ⅈ*x))","sin(x)"),
		Example("EulerNorm","cabs(e^z)","exp(creal(z))"),
		Example("EulerConjugate","conj(e^z)","cexp(conj(z))"),
		Example("EulerGuard","[e^x>0]","1"),
		Example("EulerEquality","[e^x=e^y]","[x=y]"),
		Example("EulerPhaseGuard","[e^(2*π*ⅈ)=1]","1"),
		Example("EulerAssumption","e^x","1",["x=0"]),
		Example("GuardedCancellation","[x>0]*exp(log(x))*exp(-log(x))","[x>0]"),
		Example("MaskedRealUndefined","[false]*e^(1/0)","0"),
		Example("MaskedComplexUndefined","[false]*cexp(1/0)","complex(0,0)")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ,n:ℕ,k:ℤ"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=c.input==c.expected?input:simplify(a,s.parse(a,c.expected,a.sort(input)),facts).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected),fast.exhausted?" (exhausted)":""); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"exponential regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	foreach(pair;[["e","e"],["exp(1)","e"],["cexp(1)","toℂ(e)"],["ⅈ*e","ⅈ·e"],["e^2","exp(2)"],["e^z","cexp(z)"]]){
		auto t=simplify(a,s.parse(a,pair[0])).output,printed=s.format(a,t);
		assert(printed==pair[1],pair[0]~": "~printed);
		auto roundtrip=simplify(a,s.parse(a,printed)).output;
		assert(roundtrip==t&&a.sort(roundtrip)==a.sort(t),printed);
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: exponential-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length," exponential certificates.");
}
