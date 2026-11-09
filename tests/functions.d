module function_order_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	Example[] result;
	foreach(f;["erf","sinh","asinh","tanh","atan","asin","cbrt","acosh","atanh"]){
		result~=Example(f~"Lt",f~"(x)<"~f~"(y)","x<y");
		result~=Example(f~"Le",f~"(x)≤"~f~"(y)","x≤y");
		result~=Example(f~"Eq",f~"(x)="~f~"(y)","x=y");
		result~=Example(f~"Ne",f~"(x)≠"~f~"(y)","x≠y");
	}
	foreach(f;["erfc","acos"]){
		result~=Example(f~"Lt",f~"(x)<"~f~"(y)","y<x");
		result~=Example(f~"Le",f~"(x)≤"~f~"(y)","y≤x");
		result~=Example(f~"Eq",f~"(x)="~f~"(y)","x=y");
		result~=Example(f~"Ne",f~"(x)≠"~f~"(y)","x≠y");
	}
	foreach(f;["sin","cos","tan","sinh","cosh","tanh"]) result~=Example(f~"RealCast","c"~f~"(x)","toℂ("~f~"(x))");
	return result~[
		Example("GaussianCdf","(1+erf(x/sqrt(2)))/2<(1+erf(y/sqrt(2)))/2","x<y"),
		Example("PositiveFactor","2*x<2*y","x<y"),
		Example("NegativeFactor","-2*x≤-2*y","y≤x"),
		Example("AssumedFactor","sin(x)*x<sin(x)*y","x<y",["0<sin(x)"]),
		Example("NegativeAssumedFactor","sin(x)*x≤sin(x)*y","y≤x",["sin(x)<0"]),
		Example("PartialFactor","x/log(2)≤y/log(2)","x≤y"),
		Example("FactorUnit","exp(x)*y<exp(x)","y<1"),
		Example("FactorUnitLeft","-exp(x)<-exp(x)*y","y<1"),
		Example("UnknownFactor","sin(x)*x<sin(x)*y","sin(x)<0∧0<x-y∨0<sin(x)∧x-y<0"),
		Example("NestedIncreasing","erf(sinh(x))<erf(sinh(y))","x<y"),
		Example("NestedDecreasing","acos(erfc(x))≤acos(erfc(y))","x≤y"),
		Example("PartialArguments","asin(log(x))<asin(log(y))","x<y"),
		Example("PartialInverse","atanh(1/x)≤atanh(1/y)","y≤x",["0≤x","0≤y"]),
		Example("SquareArguments","asinh(1+x^2)<asinh(1+y^2)","abs(x)<abs(y)"),
		Example("AssumedOrder","[erf(x)<erf(y)]","1",["x<y"]),
		Example("AssumedReverse","[erfc(x)≥erfc(y)]","1",["x≤y"]),
		Example("AssumedFunctionOrder","x<y","true",["erf(x)<erf(y)"]),
		Example("ContradictoryGuard","[asinh(x)<asinh(y)]*[y≤x]","0"),
		Example("MaskedUndefined","[false]*[acos(2)<acos(3)]","0"),
		Example("AsinEndpoints","asin(-1)<asin(1)","true"),
		Example("AcosEndpoints","acos(-1)<acos(1)","false"),
		Example("CubeSigns","cbrt(-8)<cbrt(1)","true"),
		Example("AcoshEndpoint","acosh(1)<acosh(2)","true"),
		Example("AtanhInterior","atanh(-1/2)<atanh(1/2)","true"),
		Example("DifferentFunctions","asin(x)<atan(y)","asin(x)<atan(y)"),
		Example("RealSinRetained","sin(x)<sin(y)","sin(x)<sin(y)"),
		Example("RealCosRetained","cos(x)≤cos(y)","cos(x)≤cos(y)"),
		Example("RealCoshRetained","cosh(x)=cosh(y)","cosh(x)=cosh(y)"),
		Example("ComplexSinImaginary","csin(ⅈ*z)","ⅈ*csinh(z)"),
		Example("ComplexCosImaginary","ccos(ⅈ*z)","ccosh(z)"),
		Example("ComplexTanImaginary","ctan(ⅈ*z)","ⅈ*ctanh(z)"),
		Example("ComplexSinhImaginary","csinh(ⅈ*z)","ⅈ*csin(z)"),
		Example("ComplexCoshImaginary","ccosh(ⅈ*z)","ccos(z)"),
		Example("ComplexTanhImaginary","ctanh(ⅈ*z)","ⅈ*ctan(z)"),
		Example("ComplexRealArgument","csin(ⅈ*x)","ⅈ*sinh(x)"),
		Example("ComplexTanRealImaginary","ctan(ⅈ*x)","ⅈ*tanh(x)"),
		Example("ComplexTanhRealImaginary","ctanh(ⅈ*x)","ⅈ*tan(x)"),
		Example("ComplexRotatedTwice","csin(ⅈ*(ⅈ*z))","-csin(z)"),
		Example("ComplexTanhRotatedTwice","ctanh(ⅈ*(ⅈ*z))","-ctanh(z)"),
		Example("ComplexSineRetained","csin(z)=csin(w)","csin(z)=csin(w)"),
		Example("ComplexSinhRetained","csinh(z)=csinh(w)","csinh(z)=csinh(w)"),
		Example("ComplexTanhRetained","ctanh(z)=ctanh(w)","ctanh(z)=ctanh(w)"),
		Example("ComplexMaskedPole","[false]*ctanh(ⅈ*π/2)","complex(0,0)")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=c.input==c.expected?input:simplify(a,s.parse(a,c.expected),facts).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected),fast.exhausted?" (exhausted)":""); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"function comparison regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: function-order-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote function comparison certificates.");
}
