module control_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce,assertThrown;
@safe:

struct Example{ string name,input,expected,domain; }
private Syntax syntax(){ Syntax s; s.declare("a:ℕ,b:ℕ,c:ℕ,j:ℤ,r:ℚ,x:ℝ,z:ℂ,p:𝔹,q:𝔹"); return s; }
private Example[] examples(){
	return [
		Example("SubDomain","a sub b","a sub b","b≤a"),
		Example("SubLiteral","8 sub 3","5","true"),
		Example("SubUnderflow","2 sub 5","2 sub 5","false"),
		Example("SubZero","a sub 0","a","true"),
		Example("SubSelf","a sub a","0","true"),
		Example("SubAddLeft","(a+b) sub a","b","true"),
		Example("SubAddRight","(a+b) sub b","a","true"),
		Example("SubAddCancel","(a sub b)+b","a","b≤a"),
		Example("SubNested","(a sub b) sub c","a sub (b+c)","b≤a∧c≤a sub b"),
		Example("SubAssociation","8 sub 2 sub 1","5","true"),
		Example("SubRightGroup","8 sub (2 sub 1)","7","true"),
		Example("SubSumPrecedence","8 sub 2+1","7","true"),
		Example("SubSumGroup","8 sub (2+1)","5","true"),
		Example("SubProductPrecedence","8 sub 2*3","2","true"),
		Example("SubProductGroup","2*(8 sub 3)","10","true"),
		Example("SubBig","18446744073709551616 sub 1","18446744073709551615","true"),
		Example("SubStrictZero","0*(2 sub 5)","0","false"),
		Example("SubHidden","[false]*(2 sub 5)","0","true"),
		Example("SubSelectedUnderflow","if p then 2 sub 5 else a","if p then 2 sub 5 else a","¬p"),
		Example("IfTrueNatural","if true then a else a","a","true"),
		Example("IfFalseNatural","if false then a else a","a","true"),
		Example("IfSameNatural","if p then a else a","a","true"),
		Example("IfTrueInteger","if true then j else j","j","true"),
		Example("IfFalseInteger","if false then j else j","j","true"),
		Example("IfSameInteger","if p then j else j","j","true"),
		Example("IfTrueRational","if true then r else r","r","true"),
		Example("IfFalseRational","if false then r else r","r","true"),
		Example("IfSameRational","if p then r else r","r","true"),
		Example("IfTrueReal","if true then x else x","x","true"),
		Example("IfFalseReal","if false then x else x","x","true"),
		Example("IfSameReal","if p then x else x","x","true"),
		Example("IfTrueComplex","if true then z else z","z","true"),
		Example("IfFalseComplex","if false then z else z","z","true"),
		Example("IfSameComplex","if p then z else z","z","true"),
		Example("IfTrueBool","if true then q else q","q","true"),
		Example("IfFalseBool","if false then q else q","q","true"),
		Example("IfSameBool","if p then q else q","q","true"),
		Example("IfTwoNaturals","if p then a else b","[p]*a+[¬p]*b","true"),
		Example("IfMixed","if p then a else x","[p]*a+[¬p]*x","true"),
		Example("IfExactMixed","if p then 1 else 1/2","[p]+[¬p]/2","true"),
		Example("IfBoolIdentity","if p then true else false","p","true"),
		Example("IfBoolNot","if p then false else true","¬p","true"),
		Example("IfBoolThen","if p then q else false","p∧q","true"),
		Example("IfBoolElse","if p then false else q","¬p∧q","true"),
		Example("IfLazyThen","if true then 3 else 1/0","3","true"),
		Example("IfLazyElse","if false then 1/0 else 3","3","true"),
		Example("IfLazyBool","if true then false else 1/0=0","false","true"),
		Example("IfGuardedInverse","if p then 1/x else 0","[p]/x","¬p∨x≠0"),
		Example("IfGuardedElse","if p then 0 else 1/x","[¬p]/x","p∨x≠0"),
		Example("IfDomainPartition","if x=0 then 0 else 1/x","[x≠0]/x","true"),
		Example("IfSubDomain","if b≤a then a sub b else 0","if b≤a then a sub b else 0","true"),
		Example("IfPartialCondition","if 1/0=0 then 2 else 2","2","false"),
		Example("IfNestedThen","if true then if false then 1 else 2 else 3","2","true"),
		Example("IfNestedElse","if false then 1 else if true then 2 else 3","2","true"),
		Example("IfAddition","1+(if p then a else b)","([p]*a+[¬p]*b)+1","true"),
		Example("IfComparison","(if true then a else b)<c","a<c","true"),
		Example("IfNumericCast","(if p then a else b:ℝ)","([p]*a+[¬p]*b:ℝ)","true")
	];
}
unittest{
	size_t failures;
	void check(bool condition,string message){ if(!condition){ ++failures; writeln(message); } }
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=s.parse(a,c.input);
		auto expected=simplify(a,s.parse(a,c.expected,a.sort(input))).output;
		auto fast=simplify(a,input),checked=simplify(a,input,Options(DensityMode.preserve,true));
		check(!fast.exhausted&&!checked.exhausted,c.name~" exhausted");
		check(fast.output==expected,c.name~": "~s.format(a,fast.output)~"; expected "~s.format(a,expected));
		check(fast.output==checked.output,c.name~" tracing disagreement");
		check(simplify(a,fast.output).output==fast.output,c.name~" idempotence");
		auto roundtrip=s.parse(a,s.format(a,fast.output),a.sort(fast.output));
		check(simplify(a,roundtrip).output==fast.output,c.name~" round trip");
		auto dom=simplifyDomain(a,input),want=simplify(a,s.parse(a,c.domain));
		check(!dom.exhausted&&dom.output==want.output,c.name~" domain: "~s.format(a,dom.output));
		exportLean(a,checked);
	}
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	foreach(bad;["x sub a","a sub (-1)","a sub r","if a then 1 else 2","if p then 1 else false",
		"if p then a","if p a else b","if p then else b","then","else"])
		assertThrown(s.parse(a,bad));
	foreach(name;["if","then","else","sub"]) assertThrown(s.declare(name~":ℕ"));
	assert(!failures,"control regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: control-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length," control and partial-subtraction certificates.");
}
