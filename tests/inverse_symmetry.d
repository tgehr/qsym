module inverse_symmetry_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:

private struct Case{ string name,input,expected; string[] facts; string law; bool domain,blocked; }
private Case[] cases(){
	Case[] r=[
		Case("AtanhNeg","catanh(-z)","-catanh(z)",[],"complex_atanh_neg"),
		Case("AtanNeg","catan(-z)","-catan(z)",[],"complex_atan_neg"),
		Case("AtanhNegPartial","catanh(-(1/z))","-catanh(1/z)",[],"complex_atanh_neg"),
		Case("AtanNegPartial","catan(-(1/z))","-catan(1/z)",[],"complex_atan_neg"),
		Case("AtanhRealLiteral","catanh(-2)","-catanh(2)",[],"complex_atanh_negative_real_literal"),
		Case("AtanRealLiteral","catan(-2+ⅈ)","-catan(2-ⅈ)",[],"complex_atan_negative_real_literal"),
		Case("AtanhImaginaryLiteral","catanh(-2*ⅈ)","-catanh(2*ⅈ)",[],"complex_atanh_negative_imaginary_literal"),
		Case("AtanImaginaryLiteral","catan(-2*ⅈ)","-catan(2*ⅈ)",[],"complex_atan_negative_imaginary_literal"),
		Case("AtanhConjIm","conj(catanh(z))","catanh(conj(z))",["cimag(z)≠0"],"complex_atanh_conj_im"),
		Case("AtanhConjRe","conj(catanh(z))","catanh(conj(z))",["-1<creal(z)","creal(z)<1"],"complex_atanh_conj_re"),
		Case("AtanConjRe","conj(catan(z))","catan(conj(z))",["creal(z)≠0"],"complex_atan_conj_re"),
		Case("AtanConjIm","conj(catan(z))","catan(conj(z))",["-1<cimag(z)","cimag(z)<1"],"complex_atan_conj_im"),
		Case("AtanhUpper","conj(catanh(2+ⅈ))","catanh(2-ⅈ)"),
		Case("AtanhLower","conj(catanh(2-ⅈ))","catanh(2+ⅈ)"),
		Case("AtanhBranchLine","conj(catanh(1+ⅈ))","catanh(1-ⅈ)"),
		Case("AtanRight","conj(catan(1+2*ⅈ))","catan(1-2*ⅈ)"),
		Case("AtanLeft","conj(catan(-1+2*ⅈ))","catan(-1-2*ⅈ)"),
		Case("AtanBranchLine","conj(catan(1+ⅈ))","catan(1-ⅈ)"),
		Case("AtanhImaginary","conj(catanh(cfromri(0,x)))","catanh(conj(cfromri(0,x)))"),
		Case("AtanReal","conj(catan(toℂ(x)))","catan(toℂ(x))"),
		Case("AtanhRealInside","conj(catanh(toℂ(x)))","catanh(toℂ(x))",["-1<x","x<1"]),
		Case("AtanImaginaryInside","conj(catan(cfromri(0,x)))","catan(conj(cfromri(0,x)))",["-1<x","x<1"]),
		Case("AtanhUnknown","conj(catanh(z))","conj(catanh(z))",[],"complex_atanh_conj",false,true),
		Case("AtanUnknown","conj(catan(z))","conj(catan(z))",[],"complex_atan_conj",false,true),
		Case("AtanhMissingLower","conj(catanh(z))","conj(catanh(z))",["creal(z)<1"],"complex_atanh_conj",false,true),
		Case("AtanMissingUpper","conj(catan(z))","conj(catan(z))",["-1<cimag(z)"],"complex_atan_conj",false,true),
		Case("AtanhPositiveCut","conj(catanh(2))","conj(catanh(2))",[],"complex_atanh_conj",false,true),
		Case("AtanhNegativeCut","conj(catanh(-2))","-conj(catanh(2))",[],"complex_atanh_conj",false,true),
		Case("AtanPositiveCut","conj(catan(2*ⅈ))","conj(catan(2*ⅈ))",[],"complex_atan_conj",false,true),
		Case("AtanNegativeCut","conj(catan(-2*ⅈ))","-conj(catan(2*ⅈ))",[],"complex_atan_conj",false,true),
		Case("AtanhConjPartial","conj(catanh(1/z))","catanh(conj(1/z))",["cimag(1/z)≠0"]),
		Case("AtanConjPartial","conj(catan(1/z))","catan(conj(1/z))",["creal(1/z)≠0"]),
		Case("AtanhMask","[p]*conj(catanh(z))","[p]*catanh(conj(z))",["cimag(z)≠0"]),
		Case("AtanMask","[p]*conj(catan(z))","[p]*catan(conj(z))",["creal(z)≠0"])
	];
	foreach(i,f;["catanh","catan"]){
		auto pole=i?"ⅈ":"toℂ(1)",tag=i?"Atan":"Atanh";
		r~=[
			Case(tag~"PositivePole","conj("~f~"("~pole~"))","false",[],"",true),
			Case(tag~"NegativePole",f~"(-("~pole~"))","false",[],"",true),
			Case(tag~"UndefinedInput",f~"(-(toℂ(1)/0))","false",[],"",true),
			Case(tag~"FalsePole","[false]*conj("~f~"("~pole~"))","toℂ(0)"),
			Case(tag~"TruePole","[true]*conj("~f~"("~pole~"))","false",[],"",true),
			Case(tag~"UndefinedMask","[1/0=1]*conj("~f~"(z))","false",[],"",true),
			Case(tag~"Zero",f~"(-toℂ(0))","toℂ(0)")
		];
	}
	return r;
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
	writeln(cases().length," inverse-symmetry cases");return 0;
}
