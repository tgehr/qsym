module sqrt_branch_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:

private struct Case{ string name,input,expected; string[] facts; string law; bool domain,blocked; }
private Case[] cases(){
	return [
		Case("ConjRe","conj(csqrt(z))","csqrt(conj(z))",["0≤creal(z)"],"complex_sqrt_conj_re"),
		Case("ConjIm","conj(csqrt(z))","csqrt(conj(z))",["cimag(z)≠0"],"complex_sqrt_conj_im"),
		Case("InvRe","csqrt(z⁻¹)","csqrt(z)⁻¹",["0≤creal(z)"],"complex_sqrt_inv_re"),
		Case("InvIm","csqrt(z⁻¹)","csqrt(z)⁻¹",["cimag(z)≠0"],"complex_sqrt_inv_im"),
		Case("ConjCut","conj(csqrt(z))","-csqrt(z)",["creal(z)<0","cimag(z)=0"]),
		Case("InvCut","csqrt(z⁻¹)","-csqrt(z)⁻¹",["creal(z)<0","cimag(z)=0"],"complex_sqrt_inv_cut"),
		Case("ConjUnknown","conj(csqrt(z))","conj(csqrt(z))",[],"complex_sqrt_conj",false,true),
		Case("InvUnknown","csqrt(z⁻¹)","csqrt(z⁻¹)",[],"complex_sqrt_inv",false,true),
		Case("ConjMissingIm","conj(csqrt(z))","conj(csqrt(z))",["creal(z)<0"],"complex_sqrt_conj",false,true),
		Case("InvMissingIm","csqrt(z⁻¹)","csqrt(z⁻¹)",["creal(z)<0"],"complex_sqrt_inv",false,true),
		Case("ConjMissingSign","conj(csqrt(z))","conj(csqrt(z))",["cimag(z)=0"],"complex_sqrt_conj",false,true),
		Case("InvMissingSign","csqrt(z⁻¹)","csqrt(z⁻¹)",["cimag(z)=0"],"complex_sqrt_inv",false,true),
		Case("ConjRight","conj(csqrt(3+4*ⅈ))","2-ⅈ"),
		Case("ConjLeftUpper","conj(csqrt(-3+4*ⅈ))","1-2*ⅈ"),
		Case("ConjLeftLower","conj(csqrt(-3-4*ⅈ))","1+2*ⅈ"),
		Case("InvRight","csqrt((3+4*ⅈ)⁻¹)","(2-ⅈ)/5"),
		Case("InvLeftUpper","csqrt((-3+4*ⅈ)⁻¹)","(1-2*ⅈ)/5"),
		Case("InvLeftLower","csqrt((-3-4*ⅈ)⁻¹)","(1+2*ⅈ)/5"),
		Case("ConjNegativeReal","conj(csqrt(-4))","-2*ⅈ"),
		Case("InvNegativeReal","csqrt(toℂ(-4)⁻¹)","ⅈ/2"),
		Case("ConjPositiveReal","conj(csqrt(4))","toℂ(2)"),
		Case("InvPositiveReal","csqrt(toℂ(4)⁻¹)","toℂ(1/2)"),
		Case("ConjImaginaryLine","conj(csqrt(cfromri(0,x)))","csqrt(cfromri(0,-x))"),
		Case("InvImaginaryLine","csqrt(cfromri(0,x)⁻¹)","csqrt(cfromri(0,x))⁻¹"),
		Case("ConjNegativeAxis","conj(csqrt(toℂ(x)))","-csqrt(toℂ(x))",["x<0"]),
		Case("InvNegativeAxis","csqrt(toℂ(x)⁻¹)","-csqrt(toℂ(x))⁻¹",["x<0"]),
		Case("ConjPartial","conj(csqrt(1/z))","csqrt(conj(1/z))",["cimag(1/z)≠0"]),
		Case("InvPartial","csqrt((1/z+1)⁻¹)","csqrt(1/z+1)⁻¹",["0≤creal(1/z+1)"]),
		Case("ConjMask","[p]*conj(csqrt(z))","[p]*csqrt(conj(z))",["cimag(z)≠0"]),
		Case("InvMask","[p]*csqrt(z⁻¹)","[p]*csqrt(z)⁻¹",["cimag(z)≠0"]),
		Case("ConjZero","conj(csqrt(0))","toℂ(0)"),
		Case("ConjZeroDomain","conj(csqrt(0))","true",[],"",true),
		Case("InvZeroDomain","csqrt(toℂ(0)⁻¹)","false",[],"",true),
		Case("InvDomain","csqrt(z⁻¹)","z≠0",[],"",true),
		Case("ConjDomain","conj(csqrt(1/z))","z≠0",[],"",true),
		Case("ConjUndefined","conj(csqrt(toℂ(1)/0))","false",[],"",true),
		Case("InvUndefined","csqrt((toℂ(1)/0)⁻¹)","false",[],"",true),
		Case("FalseMaskPole","[false]*csqrt(toℂ(0)⁻¹)","toℂ(0)"),
		Case("TrueMaskPole","[true]*csqrt(toℂ(0)⁻¹)","false",[],"",true),
		Case("UndefinedMask","[1/0=1]*conj(csqrt(z))","false",[],"",true)
	];
}
int main(string[] args){
	enforce(args.length==2);mkdirRecurse(args[1]);
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena;Syntax s;s.declare("z:ℂ,x:ℝ,p:𝔹");
		Term[] facts;foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input);if(c.domain) input=definedness(a,input);
		auto expected=simplify(a,s.parse(a,c.expected,a.sort(input)),facts),r=simplify(a,input,facts,Options(DensityMode.preserve,true));
		enforce(!r.exhausted&&!expected.exhausted&&r.output==expected.output,c.name~": "~s.format(a,r.output)~"; expected "~s.format(a,expected.output));
		auto fast=simplify(a,input,facts);enforce(!fast.exhausted&&fast.output==r.output,c.name~" trace");
		auto again=simplify(a,r.output,facts);enforce(!again.exhausted&&again.output==r.output,c.name~" idempotence");
		auto roundtrip=simplify(a,s.parse(a,s.format(a,r.output),a.sort(r.output)),facts);enforce(!roundtrip.exhausted&&roundtrip.output==r.output,c.name~" round trip");
		auto proof=exportLean(a,r);if(c.law.length) enforce((proof.indexOf("r_"~c.law)>=0)!=c.blocked,c.name~" law path");
		write(buildPath(args[1],c.name~".lean"),proof);writeln(c.name,": ",s.format(a,r.output));
	}
	writeln(cases().length," square-root branch cases");return 0;
}
