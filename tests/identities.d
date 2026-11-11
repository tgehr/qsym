module identity_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("MinUpper","[min(x,y)≤x]","1"),
		Example("MaxLower","[y≤max(x,y)]","1"),
		Example("MinLt","min(x,y)<t","x<t∨y<t"),
		Example("MinLe","min(x,y)≤t","x≤t∨y≤t"),
		Example("LtMin","t<min(x,y)","t<x∧t<y"),
		Example("LeMin","t≤min(x,y)","t≤x∧t≤y"),
		Example("MaxLt","max(x,y)<t","x<t∧y<t"),
		Example("MaxLe","max(x,y)≤t","x≤t∧y≤t"),
		Example("LtMax","t<max(x,y)","t<x∨t<y"),
		Example("LeMax","t≤max(x,y)","t≤x∨t≤y"),
		Example("MinMaxSum","min(x,y)+max(x,y)","x+y"),
		Example("MinMaxProduct","3*min(x,y)*max(x,y)","3*x*y"),
		Example("MinAbsorb","min(x,max(x,y))","x"),
		Example("MaxAbsorb","max(x,min(x,y))","x"),
		Example("MinMaxEqual","min(x,y)=max(x,y)","x=y"),
		Example("MinPartial","min(log(x),y)<t","log(x)<t∨y<t"),
		Example("InverseNegative","[1/x<0]","[x<0]"),
		Example("InversePositive","[0<1/x]","[0<x]"),
		Example("InverseNonnegative","[0≤1/x]","[0≤x]"),
		Example("InverseNonpositive","[1/x≤0]","[x≤0]"),
		Example("InverseInjective","1/x=1/y","x=y"),
		Example("ComplexInverseInjective","1/z=1/w","z=w"),
		Example("ShiftedCubes","(x+1)^3<(y+1)^3","x<y"),
		Example("ShiftedHighPower","(x+1)^101<(y+1)^101","x<y"),
		Example("ShiftedFifths","(x+1)^5≤(y+1)^5","x≤y"),
		Example("AbsEven","abs(x)^4","x^4"),
		Example("LogEvenPower","log(x^6)","6*log(abs(x))"),
		Example("RealExpLogScale","exp(2*log(x))","x^2"),
		Example("RealExpLogGeneral","exp(y*log(x))","x^y"),
		Example("RealExpLogSum","exp(log(x)+y)","x*exp(y)"),
		Example("RealExpLogAffine","exp(t+3*log(x))","x^3*exp(t)"),
		Example("RealSqrtProduct","sqrt(x)*sqrt(y)","sqrt(x*y)"),
		Example("RealSqrtCoefficient","3*sqrt(x)*sqrt(y)","3*sqrt(x*y)"),
		Example("RealPowerProduct","x^t*y^t","(x*y)^t",["0≤x","0≤y"]),
		Example("RealPowerUnrestricted","x^t*y^t","x^t*y^t"),
		Example("SinUpper","sin(x)≤1","true"),
		Example("SinLower","-1≤sin(x)","true"),
		Example("CosUpper","cos(x)≤1","true"),
		Example("CosLower","-1≤cos(x)","true"),
		Example("SineImpossible","[1<sin(x)]","0"),
		Example("SineCosineProduct","2*sin(x)*cos(x)","sin(2*x)"),
		Example("ComplexSineCosineProduct","2*csin(z)*ccos(z)","csin(2*z)"),
		Example("RealTanhOdd","tanh(-x)","-tanh(x)"),
		Example("ComplexTanOdd","ctan(-z)","-ctan(z)"),
		Example("ComplexSinhOdd","csinh(-z)","-csinh(z)"),
		Example("ComplexCoshEven","ccosh(-z)","ccosh(z)"),
		Example("ComplexTanhOdd","ctanh(-z)","-ctanh(z)"),
		Example("ComplexHyperbolic","ccosh(z)^2-csinh(z)^2","toℂ(1)"),
		Example("ComplexExpLogScale","cexp(2*clog(z))","z^2"),
		Example("ComplexExpLogGeneral","cexp(w*clog(z))","cpow(z,w)"),
		Example("ComplexExpLogSum","cexp(clog(z)+w)","z*cexp(w)"),
		Example("ComplexExpLogAffine","cexp(w+3*clog(z))","z^3*cexp(w)"),
		Example("ComplexExpNonzero","[cexp(z)=0]","0"),
		Example("ComplexLogInjective","[clog(z)=clog(w)]","[z=w]"),
		Example("ComplexLogZero","[clog(z)=0]","[z=1]"),
		Example("ComplexSqrtInjective","[csqrt(z)=csqrt(w)]","[z=w]"),
		Example("ComplexSqrtZero","[csqrt(z)=0]","[z=0]"),
		Example("ComplexExpStrip","cexp(z)=cexp(w)","z=w",["-π<im(z)","im(z)≤π","-π<im(w)","im(w)≤π"]),
		Example("ComplexExpUnrestricted","cexp(z)=cexp(w)","cexp(z)=cexp(w)"),
		Example("ComplexNormRetained","cabs(z)","cabs(z)"),
		Example("ComplexNormConstant","cabs(3+4*ⅈ)","5"),
		Example("ComplexNormCartesian","cabs(cfromri(x,y))","sqrt(x^2+y^2)"),
		Example("ComplexNormZero","[cabs(z)=0]","[z=0]"),
		Example("ComplexNormPositive","[0<cabs(z)]","[z≠0]"),
		Example("ComplexNormNonpositive","[cabs(z)≤0]","[z=0]"),
		Example("ComplexNormNonnegative","[0≤cabs(z)]","1"),
		Example("ComplexNormNegative","[cabs(z)<0]","0"),
		Example("ComplexNormMask","cabs([p]*z)","[p]*cabs(z)"),
		Example("ComplexNormSquares","cabs(z)^2+cabs(w)^2=0","z=0∧w=0"),
		Example("ComplexNormFact","z","toℂ(0)",["cabs(z)=0"]),
		Example("ComplexPartsScope","[cabs(z)=0]*z+z","z"),
		Example("ConjugateReal","creal(conj(z))","creal(z)"),
		Example("ConjugateImaginary","cimag(conj(z))","-cimag(z)"),
		Example("ConjugateCast","conj(toℂ(x))","toℂ(x)"),
		Example("ConjugateCartesian","conj(cfromri(x,y))","cfromri(x,-y)"),
		Example("ConjugateProduct","z*conj(z)","toℂ(cabs(z)^2)"),
		Example("ConjugateProductCoefficient","3*w*z*conj(z)","3*w*toℂ(cabs(z)^2)"),
		Example("ConjugateProductCancellation","z*conj(z)-toℂ(cabs(z)^2)","toℂ(0)"),
		Example("RealSquare","creal(z^2)","creal(z)^2-cimag(z)^2"),
		Example("ImaginarySquare","cimag(z^2)","2*creal(z)*cimag(z)"),
		Example("ConjugateEquality","z=conj(z)","cimag(z)=0"),
		Example("ComplexSqrtBranch","csqrt(z)*csqrt(w)","csqrt(z)*csqrt(w)"),
		Example("ComplexOddPowerUnsafe","z^3=w^3","z^3=w^3")
	];
}
private Term deepSum(Arena a,uint count=512){
	auto t=a.variable(Sort.real_,0);
	foreach(i;0..count) t=a.add(t,a.real_(1));
	return t;
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,t:ℝ,z:ℂ,w:ℂ,p:𝔹,q:𝔹"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected,a.sort(input))).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected),fast.exhausted?" (exhausted)":""); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"identity regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	auto options=Options(DensityMode.preserve,true); options.maxAlgebraWork=20_000;
	auto r=simplify(a,s.parse(a,"(x+1)^101<(y+1)^101"),options);
	assert(!r.exhausted&&r.output==s.parse(a,"x<y"),"compare before expanding powers");
	exportLean(a,r);
}
unittest{
	foreach(trace;[false,true]){
		auto owner=Session.open(); auto a=owner.arena; auto x=a.variable(Sort.real_,0);
		auto r=simplify(a,deepSum(a),Options(DensityMode.preserve,trace));
		assert(!r.exhausted&&r.output==a.add(x,a.real_(512)),"deep DAG simplification");
		if(trace) exportLean(a,r);
	}
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	auto t=s.parse(a,"cabs(z)");
	assert(simplify(a,t).output==t,"retain symbolic complex norms");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: identity-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	auto owner=Session.open(); auto a=owner.arena;
	write(buildPath(args[1],"DeepDAG.lean"),exportLean(a,simplify(a,deepSum(a,128),Options(DensityMode.preserve,true))));
	writeln("Wrote identity certificates.");
}
