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
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected),facts).output;
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
