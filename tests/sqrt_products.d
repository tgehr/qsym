module sqrt_product_tests;
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
		Case("MulMiddle","csqrt(z)*csqrt(w)","csqrt(z*w)",["-π<carg(z)+carg(w)", "carg(z)+carg(w)≤π"],"complex_sqrt_mul_middle"),
		Case("MulUpper","csqrt(z)*csqrt(w)","-csqrt(z*w)",["π<carg(z)+carg(w)"],"complex_sqrt_mul_upper"),
		Case("MulLower","csqrt(z)*csqrt(w)","-csqrt(z*w)",["carg(z)+carg(w)≤-π"],"complex_sqrt_mul_lower"),
		Case("DivMiddle","csqrt(z)/csqrt(w)","csqrt(z/w)",["-π<carg(z)-carg(w)", "carg(z)-carg(w)≤π"],"complex_sqrt_div_middle"),
		Case("DivUpper","csqrt(z)/csqrt(w)","-csqrt(z/w)",["π<carg(z)-carg(w)"],"complex_sqrt_div_upper"),
		Case("DivLower","csqrt(z)/csqrt(w)","-csqrt(z/w)",["carg(z)-carg(w)≤-π"],"complex_sqrt_div_lower"),
		Case("MulPi","csqrt(z)*csqrt(w)","csqrt(z*w)",["carg(z)+carg(w)=π"],"complex_sqrt_mul_pi"),
		Case("MulNegPi","csqrt(z)*csqrt(w)","-csqrt(z*w)",["carg(z)+carg(w)=-π"],"complex_sqrt_mul_neg_pi"),
		Case("DivPi","csqrt(z)/csqrt(w)","csqrt(z/w)",["carg(z)-carg(w)=π"],"complex_sqrt_div_pi"),
		Case("DivNegPi","csqrt(z)/csqrt(w)","-csqrt(z/w)",["carg(z)-carg(w)=-π"],"complex_sqrt_div_neg_pi"),
		Case("MulUnknown","csqrt(z)*csqrt(w)","csqrt(z)*csqrt(w)",[],"complex_sqrt_mul_",false,true),
		Case("DivUnknown","csqrt(z)/csqrt(w)","csqrt(z)/csqrt(w)",[],"complex_sqrt_div_",false,true),
		Case("MulMissingUpper","csqrt(z)*csqrt(w)","csqrt(z)*csqrt(w)",["-π<carg(z)+carg(w)"],"complex_sqrt_mul_",false,true),
		Case("DivMissingLower","csqrt(z)/csqrt(w)","csqrt(z)/csqrt(w)",["carg(z)-carg(w)≤π"],"complex_sqrt_div_",false,true),
		Case("MulExactCut","csqrt(-1)*csqrt(-4)","toℂ(-2)"),
		Case("DivExactCut","csqrt(-1)/csqrt(-4)","toℂ(1/2)"),
		Case("MulConjugate","csqrt(-3+4*ⅈ)*csqrt(-3-4*ⅈ)","toℂ(5)"),
		Case("MulOpposite","csqrt(3+4*ⅈ)*csqrt(-3-4*ⅈ)","4-3*ⅈ"),
		Case("DivExactLower","csqrt(-3-4*ⅈ)/csqrt(-3+4*ⅈ)","(-3-4*ⅈ)/5"),
		Case("DivExactUpper","csqrt(-3+4*ⅈ)/csqrt(-3-4*ⅈ)","(-3+4*ⅈ)/5"),
		Case("MulZero","csqrt(0)*csqrt(w)","toℂ(0)"),
		Case("DivZeroNumerator","csqrt(0)/csqrt(w)","w≠0",[],"",true),
		Case("DivZeroDenominator","csqrt(z)/csqrt(0)","false",[],"",true),
		Case("DivZeroBoth","csqrt(0)/csqrt(0)","false",[],"",true),
		Case("MulUndefined","csqrt(toℂ(1)/0)*csqrt(w)","false",[],"",true),
		Case("DivUndefined","csqrt(z)/csqrt(toℂ(1)/0)","false",[],"",true),
		Case("MulZeroUndefined","csqrt(0)*csqrt(toℂ(1)/0)","false",[],"",true),
		Case("MulDomain","csqrt(1/z)*csqrt(w)","z≠0",[],"",true),
		Case("DivDomain","csqrt(z)/csqrt(w)","w≠0",[],"",true),
		Case("DivPartialDomain","csqrt(1/z)/csqrt(w)","z≠0∧w≠0",[],"",true),
		Case("MulMask","[p]*csqrt(z)*csqrt(w)","[p]*csqrt(z*w)",["-π<carg(z)+carg(w)", "carg(z)+carg(w)≤π"]),
		Case("DivMask","[p]*(csqrt(z)/csqrt(w))","[p]*(-csqrt(z/w))",["carg(z)-carg(w)≤-π"]),
		Case("FalseMaskPole","[false]*(csqrt(z)/csqrt(0))","toℂ(0)"),
		Case("TrueMaskPole","[true]*(csqrt(z)/csqrt(0))","false",[],"",true),
		Case("UndefinedMask","[1/0=1]*(csqrt(z)*csqrt(w))","false",[],"",true),
		Case("PartialMul","csqrt(1/z)*csqrt(w)","csqrt(w/z)",["-π<carg(1/z)+carg(w)", "carg(1/z)+carg(w)≤π"]),
		Case("PartialDiv","csqrt(1/z)/csqrt(w)","-csqrt(1/(z*w))",["π<carg(1/z)-carg(w)"])
	];
}
int main(string[] args){
	enforce(args.length==2);mkdirRecurse(args[1]);
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena;Syntax s;s.declare("z:ℂ,w:ℂ,x:ℝ,p:𝔹");
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
	writeln(cases().length," square-root product cases");return 0;
}
