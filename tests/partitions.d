module partition_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected,domain; }
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ,p:𝔹,q:𝔹"); return s; }
private string functionDomain(string f,string x,bool complex){
	if(f=="log") return complex?"("~x~")≠complex(0,0)":"0<("~x~")";
	if(f=="sqrt"&&!complex) return "0≤("~x~")";
	if(f=="tanh"&&complex) return "cosh("~x~")≠complex(0,0)";
	return "true";
}
private Example[] examples(){
	Example[] result;
	foreach(complex;[false,true]) foreach(f;["sin","cos","exp","log","sqrt","tanh","abs"]){
		auto x=complex?"z":"x",y=complex?"w":"y",bad=complex?"1/complex(0,0)":"1/real(0)";
		auto name=(complex?"Complex":"Real")~f;
		string call(string x){ return f~"("~x~")"; }
		string choice(string p,string x,string y){ return "if "~p~" then "~x~" else "~y; }
		void add(string suffix,string input,string expected,string domain){ result~=Example(name~suffix,input,expected,domain); }
		auto c=choice("p",x,y),want=choice("p",call(x),call(y));
		add("Choice",call(c),want,functionDomain(f,c,complex));
		add("Commuted",call("[¬p]*"~y~"+[p]*"~x),want,functionDomain(f,c,complex));
		c=choice("p∧q",x,y);
		add("Conjunction",call(c),choice("p∧q",call(x),call(y)),functionDomain(f,c,complex));
		c=choice("p∨q",x,y);
		add("Disjunction",call(c),choice("p∨q",call(x),call(y)),functionDomain(f,c,complex));
		c="[p]*"~x~"+[q]*"~y;
		add("UnrelatedGuards",call(c),call(c),functionDomain(f,c,complex));
		add("Same",call(choice("p",x,x)),call(x),functionDomain(f,x,complex));
		add("InactiveUndefined",call(choice("true",x,bad)),call(x),functionDomain(f,x,complex));
		add("ActiveUndefined",call(choice("false",x,bad)),call(bad),"false");
		add("UndefinedCondition",call(choice("1/0=0",x,y)),choice("1/0=0",call(x),call(y)),"false");
	}
	result~=Example("SqrtSquares","sqrt(if p then x^2 else y^2)","if p then abs(x) else abs(y)","true");
	result~=Example("LogExponentials","log(if p then exp(x) else exp(y))","if p then x else y","0<([p]*exp(x)+[¬p]*exp(y))");
	result~=Example("ExpLogs","exp(if p then log(x) else log(y))","if p then x else y","(¬p∨0<x)∧(p∨0<y)");
	result~=Example("SinNegation","sin(if p then x else -x)","if p then sin(x) else -sin(x)","true");
	result~=Example("CosNegation","cos(if p then x else -x)","cos(x)","true");
	result~=Example("AbsNegation","abs(if p then x else -x)","abs(x)","true");
	result~=Example("SqrtBoundary","sqrt(if p then 0 else x^2)","sqrt([¬p]*x^2)","true");
	result~=Example("HiddenLogZero","log(if true then exp(x) else 0)","x","true");
	result~=Example("HiddenNegativeSqrt","sqrt(if false then -1 else x^2)","abs(x)","true");
	result~=Example("ComplexSqrtCut","sqrt(if p then complex(-4,0) else complex(4,0))","if p then complex(0,2) else complex(2,0)","true");
	result~=Example("ComplexLogCut","log(if p then complex(-1,0) else complex(1,0))","[p]*log(complex(-1,0))","([p]*complex(-1,0)+[¬p]*complex(1,0))≠0");
	result~=Example("ComplexAbsSigns","abs(if p then z else -z)","abs(z)","true");
	result~=Example("ComplexCosSigns","cos(if p then z else -z)","cos(z)","true");
	result~=Example("NestedChoice","sin(if p then (if q then x else y) else -x)","if p then (if q then sin(x) else sin(y)) else -sin(x)","true");
	result~=Example("BoolEqSelf","p=p","true","true");
	result~=Example("BoolPartialEqSelf","(1/0=0)=(1/0=0)","true","false");
	result~=Example("BoolEqDistinct","p=q","p=q","true");
	return result;
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
		auto domainOptions=Options.init; domainOptions.distributeLogic=false;
		auto dom=simplifyDomain(a,input),want=simplify(a,s.parse(a,c.domain),domainOptions);
		check(!dom.exhausted&&dom.output==want.output,c.name~" domain: "~s.format(a,dom.output));
		exportLean(a,checked);
	}
	assert(!failures,"partition regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: partition-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length," conditional function certificates.");
}
