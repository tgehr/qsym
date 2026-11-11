module compact_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.exception:enforce;
import std.stdio:writeln;
@safe:

struct Example{ string name,input,expected; bool expand; }
Example[] examples(){
	return [
		Example("RealPower","(x+1)^10","(x+1)^10"),
		Example("LargePower","(x+y+1)^1000","(x+y+1)^1000"),
		Example("ComplexPower","(z+w)^10","(z+w)^10"),
		Example("CollectPowers","(x+1)^10+2*(x+1)^10","3*(x+1)^10"),
		Example("CancelPowers","(x+1)^10/(x+1)^8","(x+1)^2"),
		Example("NestedPowers","((x+1)^3)^4","(x+1)^12"),
		Example("NumericPower","2^10","1024"),
		Example("EvenBound","(x+1)^10<2^10","-3<x∧x<1"),
		Example("EvenClosedBound","(x+1)^10≤2^10","-3≤x∧x≤1"),
		Example("EvenEquality","(x+1)^10=2^10","x=-3∨x=1"),
		Example("EvenNegativeBound","(x+1)^10<(-2)^10","-3<x∧x<1"),
		Example("EvenZero","x^10<0^10","false"),
		Example("RealIdentity","(x+y)^2=x^2+2*x*y+y^2","true"),
		Example("ComplexIdentity","(z+w)^2=z^2+2*z*w+w^2","true"),
		Example("ProofModeIsolation","[(x+y)^2=x^2+2*x*y+y^2]*(x+y)^2","(x+y)^2"),
		Example("HiddenQuadratic","(x+1)^2+x=1","x=-3∨x=0"),
		Example("ExpandedReal","(x+1)^3","x^3+3*x^2+3*x+1",true),
		Example("ExpandedComplex","(z+w)^2","z^2+2*z*w+w^2",true),
		Example("PartialPower","[x≠0]*(x⁻¹+1)^10","[x≠0]*(x⁻¹+1)^10")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ,p:𝔹"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected,a.sort(input))).output;
		auto options=Options.init; options.expandPowers=c.expand;
		auto fast=simplify(a,input,options); options.trace=true;
		auto checked=simplify(a,input,options);
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,options).output==fast.output,c.name~" is not idempotent");
	}
	assert(!failures,"compact simplification regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax(); s.declare("v:ℝ");
	foreach(source;["(x+1)^10","(z+w)^10","(x+y+1)^1000"]){
		auto input=s.parse(a,source),result=simplify(a,input);
		assert(!result.exhausted&&result.output==input,source~" expanded");
	}
	foreach(pair;[["x+(y+1)","x+y+1"],["x*(y*v)","x·y·v"],
		["x+(-y+1)","x-y+1"],["x+(-y-1)","x-y-1"],["x-(-y+1)","x-(-y+1)"],
		["x-(y+1)","x-(y+1)"],["x*([p]*y)","[p]·(x·y)"],
		["x*(y*([p]*v))","[p]·(x·y·v)"]]){
		auto t=s.parse(a,pair[0]),printed=s.format(a,t);
		assert(printed==pair[1],printed);
		assert(simplify(a,s.parse(a,printed)).output==simplify(a,t).output,printed);
	}
	auto options=Options(DensityMode.preserve,true,100_000,8,1000); options.expandPowers=true;
	auto limited=simplify(a,s.parse(a,"(x+1)^100"),options);
	assert(limited.exhausted); exportLean(a,limited);
}
@system void main(string[] args){
	enforce(args.length==2,"usage: compact-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto options=Options(DensityMode.preserve,true); options.expandPowers=c.expand;
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),options)));
	}
	writeln("Wrote compact certificates.");
}
