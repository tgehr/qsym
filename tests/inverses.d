module inverse_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("NewExpAsinh","exp(asinh(x))","x+sqrt(1+x^2)"),
		Example("NewExpAsinhPartial","exp(asinh(log(x)))","log(x)+sqrt(1+log(x)^2)"),
		Example("NewExpAsinhMasked","[false]*(exp(asinh(x)))","0"),
		Example("NewExpAsinhGuard","[0<x∧x<1]*(exp(asinh(x)))","[0<x∧x<1]*(x+sqrt(1+x^2))"),
		Example("NewExpAcosh","exp(acosh(x))","x+sqrt(x^2-1)"),
		Example("NewExpAcoshPartial","exp(acosh(log(x)))","log(x)+sqrt(log(x)^2-1)"),
		Example("NewExpAcoshMasked","[false]*(exp(acosh(x)))","0"),
		Example("NewExpAcoshGuard","[0<x∧x<1]*(exp(acosh(x)))","[0<x∧x<1]*(x+sqrt(x^2-1))"),
		Example("NewCoshAtanh","cosh(atanh(x))","1/sqrt(1-x^2)"),
		Example("NewCoshAtanhPartial","cosh(atanh(log(x)))","1/sqrt(1-log(x)^2)"),
		Example("NewCoshAtanhMasked","[false]*(cosh(atanh(x)))","0"),
		Example("NewCoshAtanhGuard","[0<x∧x<1]*(cosh(atanh(x)))","[0<x∧x<1]*(1/sqrt(1-x^2))"),
		Example("NewSinhAtanh","sinh(atanh(x))","x/sqrt(1-x^2)"),
		Example("NewSinhAtanhPartial","sinh(atanh(log(x)))","log(x)/sqrt(1-log(x)^2)"),
		Example("NewSinhAtanhMasked","[false]*(sinh(atanh(x)))","0"),
		Example("NewSinhAtanhGuard","[0<x∧x<1]*(sinh(atanh(x)))","[0<x∧x<1]*(x/sqrt(1-x^2))"),
		Example("NewComplexExpAsinh","cexp(casinh(z))","z+csqrt(z^2+1)"),
		Example("NewComplexExpAsinhPartial","cexp(casinh(clog(z)))","clog(z)+csqrt(clog(z)^2+1)"),
		Example("NewComplexExpAsinhMasked","[false]*(cexp(casinh(z)))","toℂ(0)"),
		Example("NewComplexExpAsinhUpperCut","cexp(casinh(2*ⅈ))","(2*ⅈ)+csqrt((2*ⅈ)^2+1)"),
		Example("NewComplexExpAsinhLowerCut","cexp(casinh(-2*ⅈ))","(-2*ⅈ)+csqrt((-2*ⅈ)^2+1)"),
		Example("NewComplexExpAsinhNegativeCut","cexp(casinh(-2))","(-2)+csqrt((-2)^2+1)"),
		Example("NewComplexExpAsinhOne","cexp(casinh(1))","(1)+csqrt((1)^2+1)"),
		Example("NewComplexExpAsinhMinusOne","cexp(casinh(-1))","(-1)+csqrt((-1)^2+1)"),
		Example("NewComplexExpAcosh","cexp(cacosh(z))","z+csqrt(z-1)*csqrt(z+1)"),
		Example("NewComplexExpAcoshPartial","cexp(cacosh(clog(z)))","clog(z)+csqrt(clog(z)-1)*csqrt(clog(z)+1)"),
		Example("NewComplexExpAcoshMasked","[false]*(cexp(cacosh(z)))","toℂ(0)"),
		Example("NewComplexExpAcoshUpperCut","cexp(cacosh(2*ⅈ))","(2*ⅈ)+csqrt((2*ⅈ)-1)*csqrt((2*ⅈ)+1)"),
		Example("NewComplexExpAcoshLowerCut","cexp(cacosh(-2*ⅈ))","(-2*ⅈ)+csqrt((-2*ⅈ)-1)*csqrt((-2*ⅈ)+1)"),
		Example("NewComplexExpAcoshNegativeCut","cexp(cacosh(-2))","(-2)+csqrt((-2)-1)*csqrt((-2)+1)"),
		Example("NewComplexExpAcoshOne","cexp(cacosh(1))","(1)+csqrt((1)-1)*csqrt((1)+1)"),
		Example("NewComplexExpAcoshMinusOne","cexp(cacosh(-1))","(-1)+csqrt((-1)-1)*csqrt((-1)+1)"),
		Example("NewsinhAtanhZero","sinh(atanh(0))","(0)/sqrt(1-(0)^2)"),
		Example("NewsinhAtanhHalf","sinh(atanh(1/2))","(1/2)/sqrt(1-(1/2)^2)"),
		Example("NewsinhAtanhNegativeHalf","sinh(atanh(-1/2))","(-1/2)/sqrt(1-(-1/2)^2)"),
		Example("NewcoshAtanhZero","cosh(atanh(0))","1/sqrt(1-(0)^2)"),
		Example("NewcoshAtanhHalf","cosh(atanh(1/2))","1/sqrt(1-(1/2)^2)"),
		Example("NewcoshAtanhNegativeHalf","cosh(atanh(-1/2))","1/sqrt(1-(-1/2)^2)"),
		Example("NewExpAsinhZero","exp(asinh(0))","(0)+sqrt(1+(0)^2)"),
		Example("NewExpAsinhNegative","exp(asinh(-2))","(-2)+sqrt(1+(-2)^2)"),
		Example("NewExpAcoshOne","exp(acosh(1))","1"),

		Example("NewRealTanasin","tan(asin(x))","x/sqrt(1-x^2)"),
		Example("NewRealTanasinPartial","tan(asin(log(x)))","(log(x))/sqrt(1-(log(x))^2)"),
		Example("NewRealTanasinMask","[false]*(tan(asin(x)))","0"),
		Example("NewRealTanasinHalf","tan(asin(1/2))","(1/2)/sqrt(1-(1/2)^2)"),
		Example("NewRealTanasinNegativeHalf","tan(asin(-1/2))","(-1/2)/sqrt(1-(-1/2)^2)"),
		Example("NewRealTanasinGuard","[0<x∧x<1]*(tan(asin(x)))","[0<x∧x<1]*(x/sqrt(1-x^2))"),
		Example("NewRealTanacos","tan(acos(x))","sqrt(1-x^2)/x"),
		Example("NewRealTanacosPartial","tan(acos(log(x)))","sqrt(1-(log(x))^2)/(log(x))"),
		Example("NewRealTanacosMask","[false]*(tan(acos(x)))","0"),
		Example("NewRealTanacosHalf","tan(acos(1/2))","sqrt(1-(1/2)^2)/(1/2)"),
		Example("NewRealTanacosNegativeHalf","tan(acos(-1/2))","sqrt(1-(-1/2)^2)/(-1/2)"),
		Example("NewRealTanacosGuard","[0<x∧x<1]*(tan(acos(x)))","[0<x∧x<1]*(sqrt(1-x^2)/x)"),
		Example("NewComplexTanasin","ctan(casin(z))","z/csqrt(1-z^2)"),
		Example("NewComplexTanasinPartial","ctan(casin(clog(z)))","(clog(z))/csqrt(1-(clog(z))^2)"),
		Example("NewComplexTanasinMask","[false]*(ctan(casin(z)))","toℂ(0)"),
		Example("NewComplexTanasinPositiveCut","ctan(casin(2))","(2)/csqrt(1-(2)^2)"),
		Example("NewComplexTanasinNegativeCut","ctan(casin(-2))","(-2)/csqrt(1-(-2)^2)"),
		Example("NewComplexTanasinUpper","ctan(casin(2*ⅈ))","(2*ⅈ)/csqrt(1-(2*ⅈ)^2)"),
		Example("NewComplexTanasinLower","ctan(casin(-2*ⅈ))","(-2*ⅈ)/csqrt(1-(-2*ⅈ)^2)"),
		Example("NewComplexTanasinHalf","ctan(casin(1/2))","(1/2)/csqrt(1-(1/2)^2)"),
		Example("NewComplexTanacos","ctan(cacos(z))","csqrt(1-z^2)/z"),
		Example("NewComplexTanacosPartial","ctan(cacos(clog(z)))","csqrt(1-(clog(z))^2)/(clog(z))"),
		Example("NewComplexTanacosMask","[false]*(ctan(cacos(z)))","toℂ(0)"),
		Example("NewComplexTanacosPositiveCut","ctan(cacos(2))","csqrt(1-(2)^2)/(2)"),
		Example("NewComplexTanacosNegativeCut","ctan(cacos(-2))","csqrt(1-(-2)^2)/(-2)"),
		Example("NewComplexTanacosUpper","ctan(cacos(2*ⅈ))","csqrt(1-(2*ⅈ)^2)/(2*ⅈ)"),
		Example("NewComplexTanacosLower","ctan(cacos(-2*ⅈ))","csqrt(1-(-2*ⅈ)^2)/(-2*ⅈ)"),
		Example("NewComplexTanacosHalf","ctan(cacos(1/2))","csqrt(1-(1/2)^2)/(1/2)"),
		Example("NewRealasinPole1","[false]*tan(asin(1))","0"),
		Example("NewRealasinPoleMinus","[false]*tan(asin(-1))","0"),
		Example("NewRealacosPole0","[false]*tan(acos(0))","0"),
		Example("NewComplexasinPole1","[false]*ctan(casin(1))","toℂ(0)"),
		Example("NewComplexasinPoleMinus","[false]*ctan(casin(-1))","toℂ(0)"),
		Example("NewComplexacosPole0","[false]*ctan(cacos(0))","toℂ(0)"),

		Example("NewasinNeg","asin(-x)","-asin(x)"),
		Example("NewasinNegPartial","asin(-log(x))","-asin(log(x))"),
		Example("NewasinNegMask","[false]*(asin(-x))","0"),
		Example("NewasinNegGuard","[0<x∧x<1]*(asin(-x))","[0<x∧x<1]*(-asin(x))"),
		Example("NewasinNegHalf","asin(-(1/2))","-asin((1/2))"),
		Example("NewatanNeg","atan(-x)","-atan(x)"),
		Example("NewatanNegPartial","atan(-log(x))","-atan(log(x))"),
		Example("NewatanNegMask","[false]*(atan(-x))","0"),
		Example("NewatanNegGuard","[0<x∧x<1]*(atan(-x))","[0<x∧x<1]*(-atan(x))"),
		Example("NewatanNegHalf","atan(-(1/2))","-atan((1/2))"),
		Example("NewasinhNeg","asinh(-x)","-asinh(x)"),
		Example("NewasinhNegPartial","asinh(-log(x))","-asinh(log(x))"),
		Example("NewasinhNegMask","[false]*(asinh(-x))","0"),
		Example("NewasinhNegGuard","[0<x∧x<1]*(asinh(-x))","[0<x∧x<1]*(-asinh(x))"),
		Example("NewasinhNegHalf","asinh(-(1/2))","-asinh((1/2))"),
		Example("NewatanhNeg","atanh(-x)","-atanh(x)"),
		Example("NewatanhNegPartial","atanh(-log(x))","-atanh(log(x))"),
		Example("NewatanhNegMask","[false]*(atanh(-x))","0"),
		Example("NewatanhNegGuard","[0<x∧x<1]*(atanh(-x))","[0<x∧x<1]*(-atanh(x))"),
		Example("NewatanhNegHalf","atanh(-(1/2))","-atanh((1/2))"),
		Example("NewacosNeg","acos(-x)","π-acos(x)"),
		Example("NewacosNegPartial","acos(-log(x))","π-acos(log(x))"),
		Example("NewacosNegMask","[false]*(acos(-x))","0"),
		Example("NewacosNegGuard","[0<x∧x<1]*(acos(-x))","[0<x∧x<1]*(π-acos(x))"),
		Example("NewacosNegHalf","acos(-(1/2))","π-acos((1/2))"),
		Example("NewRealComplement","asin(x)+acos(x)","π/2"),
		Example("NewRealComplementReverse","acos(x)+asin(x)","π/2"),
		Example("NewRealComplementPartial","asin(log(x))+acos(log(x))","π/2"),
		Example("NewRealComplementMask","[false]*(asin(x)+acos(x))","0"),
		Example("NewRealComplementZero","asin((0))+acos((0))","π/2"),
		Example("NewRealComplementOne","asin((1))+acos((1))","π/2"),
		Example("NewRealComplementMinusOne","asin((-1))+acos((-1))","π/2"),
		Example("NewComplexComplement","casin(z)+cacos(z)","toℂ(π/2)"),
		Example("NewComplexComplementReverse","cacos(z)+casin(z)","toℂ(π/2)"),
		Example("NewComplexComplementPartial","casin(clog(z))+cacos(clog(z))","toℂ(π/2)"),
		Example("NewComplexComplementMask","[false]*(casin(z)+cacos(z))","toℂ(0)"),
		Example("NewComplexComplementPositiveCut","casin((2))+cacos((2))","toℂ(π/2)"),
		Example("NewComplexComplementNegativeCut","casin((-2))+cacos((-2))","toℂ(π/2)"),
		Example("NewComplexComplementUpper","casin((2*ⅈ))+cacos((2*ⅈ))","toℂ(π/2)"),
		Example("NewComplexComplementLower","casin((-2*ⅈ))+cacos((-2*ⅈ))","toℂ(π/2)"),

		Example("RealTanhAsinh","tanh(asinh(x))","x/sqrt(1+x^2)"),
		Example("RealTanhAcosh","tanh(acosh(x))","sqrt(x^2-1)/x"),
		Example("ComplexTanhAsinh","ctanh(casinh(z))","z/csqrt(z^2+1)"),
		Example("ComplexTanhAcosh","ctanh(cacosh(z))","csqrt(z-1)*csqrt(z+1)/z"),
		Example("RealTanhAsinhZero","tanh(asinh(0))","0"),
		Example("RealTanhAsinhNegative","tanh(asinh(-2))","-2/sqrt(5)"),
		Example("RealTanhAcoshOne","tanh(acosh(1))","0"),
		Example("RealTanhAcoshTwo","tanh(acosh(2))","sqrt(3)/2"),
		Example("RealTanhAsinhPartial","tanh(asinh(log(x)))","log(x)/sqrt(1+log(x)^2)"),
		Example("RealTanhAcoshPartial","tanh(acosh(log(x)))","sqrt(log(x)^2-1)/log(x)"),
		Example("RealTanhAcoshGuard","[1≤x]*tanh(acosh(x))","[1≤x]*sqrt(x^2-1)/x"),
		Example("ComplexTanhAsinhPositiveCut","ctanh(casinh(2*ⅈ))","2/toℂ(sqrt(3))"),
		Example("ComplexTanhAsinhNegativeCut","ctanh(casinh(-2*ⅈ))","-2/toℂ(sqrt(3))"),
		Example("ComplexTanhAcoshNegativeCut","ctanh(cacosh(-2))","toℂ(sqrt(3)/2)"),
		Example("ComplexTanhAcoshPositive","ctanh(cacosh(2))","toℂ(sqrt(3)/2)"),
		Example("ComplexTanhAcoshOne","ctanh(cacosh(1))","toℂ(0)"),
		Example("ComplexTanhAcoshMinusOne","ctanh(cacosh(-1))","toℂ(0)"),
		Example("ComplexTanhAsinhPartial","ctanh(casinh(clog(z)))","clog(z)/csqrt(clog(z)^2+1)"),
		Example("ComplexTanhAcoshPartial","ctanh(cacosh(1/z))","csqrt(1/z-1)*csqrt(1/z+1)/(1/z)"),
		Example("ComplexTanhAsinhMaskedPole","[false]*ctanh(casinh(ⅈ))","toℂ(0)"),
		Example("ComplexTanhAcoshMaskedPole","[false]*ctanh(cacosh(0))","toℂ(0)"),
		Example("RealCoshAcosh","cosh(acosh(x))","x"),
		Example("RealSinhAcosh","sinh(acosh(x))","sqrt(x^2-1)"),
		Example("RealTanhAtanh","tanh(atanh(x))","x"),
		Example("RealAtanhTanh","atanh(tanh(x))","x"),
		Example("RealAcoshCosh","acosh(cosh(x))","abs(x)"),
		Example("RealAcoshCoshNegative","acosh(cosh(x))","-x",["x<0"]),
		Example("RealAcoshCoshNonnegative","acosh(cosh(x))","x",["0≤x"]),
		Example("RealSinhAcoshFour","sinh(acosh(4))","sqrt(15)"),
		Example("RealCoshAcoshTwo","cosh(acosh(2))","2"),
		Example("RealTanhAtanhHalf","tanh(atanh(1/2))","1/2"),
		Example("RealAtanhTanhOne","atanh(tanh(1))","1"),
		Example("RealAcoshCoshNegativeThree","acosh(cosh(-3))","3"),
		Example("RealAcoshCoshZero","acosh(cosh(0))","0"),
		Example("RealTanhAtanhGuard","[abs(x)<1]*tanh(atanh(x))","[abs(x)<1]*x"),
		Example("RealCoshAcoshGuard","[1≤x]*cosh(acosh(x))","[1≤x]*x"),
		Example("RealPartialComposition","cosh(acosh(log(x)))","log(x)"),
		Example("RealNested","atanh(tanh(atanh(tanh(x))))","x"),
		Example("ComplexSinAsin","csin(casin(z))","z"),
		Example("ComplexCosAcos","ccos(cacos(z))","z"),
		Example("ComplexTanAtan","ctan(catan(z))","z"),
		Example("ComplexSinhAsinh","csinh(casinh(z))","z"),
		Example("ComplexCoshAcosh","ccosh(cacosh(z))","z"),
		Example("ComplexTanhAtanh","ctanh(catanh(z))","z"),
		Example("OverloadedSinAsin","sin(asin(z))","z"),
		Example("OverloadedTanhAtanh","tanh(atanh(z))","z"),
		Example("ComplexSinAsinCut","csin(casin(2))","toℂ(2)"),
		Example("ComplexCosAcosCut","ccos(cacos(-2))","toℂ(-2)"),
		Example("ComplexTanAtanPoint","ctan(catan(1+2*ⅈ))","1+2*ⅈ"),
		Example("ComplexSinhAsinhCut","csinh(casinh(2*ⅈ))","2*ⅈ"),
		Example("ComplexCoshAcoshCut","ccosh(cacosh(-2))","toℂ(-2)"),
		Example("ComplexTanhAtanhPoint","ctanh(catanh(1+2*ⅈ))","1+2*ⅈ"),
		Example("ComplexCosAsin","ccos(casin(z))","csqrt(1-z^2)"),
		Example("ComplexSinAcos","csin(cacos(z))","csqrt(1-z^2)"),
		Example("ComplexCoshAsinh","ccosh(casinh(z))","csqrt(z^2+1)"),
		Example("ComplexSinhAcosh","csinh(cacosh(z))","csqrt(z-1)*csqrt(z+1)"),
		Example("ComplexCosAsinCut","ccos(casin(2))","ⅈ*sqrt(3)"),
		Example("ComplexSinAcosCut","csin(cacos(-2))","ⅈ*sqrt(3)"),
		Example("ComplexCoshAsinhPositiveCut","ccosh(casinh(2*ⅈ))","ⅈ*sqrt(3)"),
		Example("ComplexCoshAsinhNegativeCut","ccosh(casinh(-2*ⅈ))","ⅈ*sqrt(3)"),
		Example("ComplexSinhAcoshNegativeCut","csinh(cacosh(-2))","-toℂ(sqrt(3))"),
		Example("ComplexSinhAcoshPositive","csinh(cacosh(2))","toℂ(sqrt(3))"),
		Example("ComplexSinhAcoshZero","csinh(cacosh(0))","ⅈ"),
		Example("ComplexSinhAcoshOne","csinh(cacosh(1))","toℂ(0)"),
		Example("ComplexPartialComposition","csin(casin(clog(z)))","clog(z)"),
		Example("ComplexPartialTangent","ctan(catan(1/z))","1/z"),
		Example("ComplexGuard","[z≠0]*csin(casin(1/z))","[z≠0]/z"),
		Example("ComplexCast","ccos(cacos(toℂ(x)))","toℂ(x)"),
		Example("ComplexNested","csin(casin(csinh(casinh(z))))","z"),
		Example("ComplexNorm","cabs(ctanh(catanh(z)))","cabs(z)"),
		Example("ComplexIdentityGuard","[csin(casin(z))=z]","1"),
		Example("MaskedUndefined","[false]*ctanh(catanh(1))","toℂ(0)"),
		Example("RealTanhAtanhPower","tanh(atanh(x^2))","x^2"),
		Example("RealSinhAcoshSquared","sinh(acosh(x))^2","x^2-1"),
		Example("ComplexSinhAcoshSquared","csinh(cacosh(z))^2","z^2-1"),
		Example("ComplexCosAsinSquared","ccos(casin(z))^2","1-z^2"),
		Example("ComplexCoshAsinhSquared","ccosh(casinh(z))^2","1+z^2"),
		Example("RealSinhAcoshGuard","[1≤x]*sinh(acosh(x))","[1≤x]*sqrt(x^2-1)"),
		Example("ComplexRootBranch","csinh(cacosh(-2))+csqrt((-2)^2-1)","toℂ(0)"),
		Example("RealAcoshCoshAbsolute","acosh(cosh(abs(x)))","abs(x)"),
		Example("ComplexCoshAcoshPartial","ccosh(cacosh(clog(z)))","clog(z)")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,z:ℂ"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected,a.sort(input)),facts).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"inverse-function regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax(); auto z=s.parse(a,"z");
	foreach(source;["casin(csin(z))","cacos(ccos(z))","catan(ctan(z))","casinh(csinh(z))","cacosh(ccosh(z))","catanh(ctanh(z))"]){
		auto result=simplify(a,s.parse(a,source));
		assert(!result.exhausted&&result.output!=z,"inverse branch must be retained: "~source);
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: inverse-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length," inverse-function certificates.");
}
