module type_value_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,expected; }
private Case[] cases(){
	return [
		Case("RealAscii","Real","ℝ"),Case("RealUnicode","ℝ","ℝ"),
		Case("RealAliases","Real=ℝ","true"),Case("RealNotAliases","Real≠ℝ","false"),
		Case("DifferentTypes","Real=Complex","false"),Case("TypeUniverse","Type=ℝ","false"),
		Case("NatAliases","Nat=ℕ","true"),Case("IntAliases","Int=ℤ","true"),
		Case("RatAliases","Rat=ℚ","true"),Case("BoolAliases","Bool=𝔹","true"),
		Case("ComplexAliases","Complex=ℂ","true"),Case("SetAliases","Set(Real)=Set(ℝ)","true"),
		Case("RealMember","1∈ℝ","true"),Case("TypeMember","ℝ∈Type","true"),
		Case("TypeIdentity","(λ(T:Type).T)(Real)","ℝ"),
		Case("TypeReturn","λ(n:ℕ).Real","λ(n:ℕ). ℝ"),
		Case("AppliedTypeEqual","(λ(T:Type).T)(ℝ)=Real","true"),
		Case("CapturedType","(λ(T:Type).λ(n:ℕ).T)(ℝ)(2)","ℝ"),
		Case("UnicodeAnnotation","λ(t:ℝ).(0:ℝ)","λ(t:ℝ). (0:ℝ)"),
		Case("AsciiAnnotation","λ(t:Real).(0:Real)","λ(t:ℝ). (0:ℝ)"),
		Case("TypeDefined","defined(Real)","true"),
		Case("TypeUniverseNonempty","{T:Type|true}⊆{T:Type|false}","false")
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true));
		enforce(!r.exhausted,c.name~" exhausted"); enforce(s.format(a,r)==c.expected,c.name~": "~s.format(a,r));
		enforce(!s.scalar.variables.length,c.name~" introduced a variable");
		auto again=s.run(a,c.expected); enforce(s.format(a,again)==c.expected,c.name~" round trip");
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
}
unittest{
	run(); auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
	foreach(name;["Real","ℝ","Nat","ℕ","Int","ℤ","Rat","ℚ","Complex","ℂ","Bool","𝔹","Type"])
		assertThrown(s.declare(name~":ℝ"));
	assertThrown(s.run(a,"Real+1")); assertThrown(s.run(a,"Real(1)"));
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/type-values"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," type-value certificates"); return 0;
}
