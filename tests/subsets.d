module subset_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,expected,variables; string[] facts; bool domain; }
private Case[] cases(){
	return [
		Case("MembershipAssumption","x","1","",["x∈{x:ℝ|x=1}"]),
		Case("MembershipIverson","[x=1]","1","",["x∈{x:ℝ|x=1}"]),
		Case("MembershipQuery","x∈{y:ℝ|y>0}","true","",["x∈{x:ℝ|x=1}"]),
		Case("MembershipDomain","1/x","true","",["x∈{x:ℝ|x=1}"],true),
		Case("LambdaAssumption","n","2","n:ℕ",["(λ(i:ℕ).i=2)(n)"]),
		Case("FunctionDomainAssumption","log(x)","true","",["x∈domain(λ(y:ℝ).log(y))"],true),
		Case("DefinedAssumption","x/x","1","",["defined((λ(y:ℝ).1/y)(x))"]),
		Case("NotMemberAssumption","1/x","true","",["x∉{y:ℝ|y=0}"],true),
		Case("MixedAssumptions","x+y","3","",["y=2","x∈{x:ℝ|x=1}"]),
		Case("SubsetSelf","S⊆S","true","S:Set(ℝ)"),
		Case("SubsetSymbolic","S⊆T","(S⊆T)","S:Set(ℝ),T:Set(ℝ)"),
		Case("NotSubsetSelf","S⊈S","false","S:Set(ℝ)"),
		Case("EmptySubset","{x:ℝ|false}⊆S","true","S:Set(ℝ)"),
		Case("SubsetUniverse","S⊆{x:ℝ|true}","true","S:Set(ℝ)"),
		Case("UniverseNotEmpty","{x:ℝ|true}⊆{x:ℝ|false}","false"),
		Case("NaturalUniverse","{x:ℕ|true}⊆{x:ℕ|false}","false"),
		Case("IntegerUniverse","{x:ℤ|true}⊆{x:ℤ|false}","false"),
		Case("RationalUniverse","{x:ℚ|true}⊆{x:ℚ|false}","false"),
		Case("ComplexUniverse","{x:ℂ|true}⊆{x:ℂ|false}","false"),
		Case("BooleanUniverse","{x:𝔹|true}⊆{x:𝔹|false}","false"),
		Case("FunctionUniverse","{f:ℕ→ℕ|true}⊆{f:ℕ→ℕ|false}","false"),
		Case("SetUniverse","{S:Set(ℕ)|true}⊆{S:Set(ℕ)|false}","false"),
		Case("NotMember","1∉{x:ℝ|x=0}","true"),
		Case("SubsetDomain","S⊆T","true","S:Set(ℝ),T:Set(ℝ)",[],true),
		Case("MemberDomain","x∈S","true","S:Set(ℝ)",[],true),
		Case("SubsetPartialSelf","guard(false,S)⊆guard(false,S)","false","S:Set(ℝ)",[],true),
		Case("EmptySubsetPartial","{x:ℝ|false}⊆guard(false,S)","false","S:Set(ℝ)",[],true),
		Case("NotMemberPartial","1∉guard(false,S)","false","S:Set(ℝ)",[],true),
		Case("NotSubsetPartial","guard(false,S)⊈S","false","S:Set(ℝ)",[],true),
		Case("UndefinedPredicateSet","0∈{x:ℝ|1/x>0}","false"),
		Case("RestrictedDomain","guard(x>0,log(x))","0<x","",[],true),
		Case("ApplicationDomain","f(x)","holds((x∈domain(f)))","f:ℝ→ℝ",[],true),
		Case("DisabledFunctionDomain","domain(guard(false,λ(x:ℝ).x))","{x:ℝ | false}"),
		Case("SubsetFact","S⊆S","true","S:Set(ℝ)",["S⊆S"])
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
		if(c.variables.length) s.declare(c.variables);
		auto facts=s.assumptions(a,c.facts),predicates=FunctionSyntax.predicates(facts);
		auto r=s.run(a,c.source,predicates,Options(DensityMode.preserve,true),c.domain),output=s.format(a,r);
		enforce(!r.exhausted,c.name~" exhausted"); enforce(output==c.expected,c.name~": "~output);
		auto again=s.run(a,output,predicates); enforce(s.format(a,again)==output,c.name~" round trip");
		auto certificate=s.exportCertificate(a,r,facts);
		if(directory.length) write(buildPath(directory,c.name~".lean"),certificate);
	}
}
unittest{
	run(); auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
	s.declare("S:Set(ℝ),T:Set(ℕ),f:ℕ→ℕ");
	foreach(x;["S⊆T","1⊆S","S⊆1","λ(x:ℝ).x⊆x"]) assertThrown(s.run(a,x));
	assertThrown(s.assumption(a,"f=0")); assertThrown(s.assumption(a,"1"));
	assertThrown(s.assumption(a,"x∈S"));
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/subsets"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," subset certificates"); return 0;
}
