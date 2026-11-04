module guard_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("NestedBounds","[x^2≤1]*[x<1]","[-1≤x∧x<1]"),
		Example("NestedBoundsReverse","[x<1]*[x^2≤1]","[x<1∧-1≤x]"),
		Example("NestedContradiction","[x<0]*[y>0]*[1<x]","0"),
		Example("NonAdjacentBounds","[x<2]*[y>0]*[x<1]","[y>0∧x<1]"),
		Example("StrictPuncture","[x≤1]*[x≠1]","[x<1]"),
		Example("StrictPunctureReverse","[x≠1]*[x≤1]","[x<1]"),
		Example("PointPuncture","[0≤x]*[x≤0]*[x≠0]","0"),
		Example("OutsideExclusion","[0≤x]*[x<1]*[x≠2]","[0≤x∧x<1]"),
		Example("OrAbsorb","x<0∨(x<0∧y>0)","x<0"),
		Example("AndAbsorb","x<0∧(x<0∨y>0)","x<0"),
		Example("NestedUnion","x<1∨y>0∨x<2","y>0∨x<2"),
		Example("LowerPuncture","[0≤x]*[x≠0]","[0<x]"),
		Example("LowerPunctureReverse","[x≠0]*[0≤x]","[0<x]"),
		Example("LowerNonAdjacent","[x>1]*[y>0]*[x>2]","[0<y∧2<x]"),
		Example("UpperUnionMixed","x<1∨x≤1","x≤1"),
		Example("LowerUnionMixed","1<x∨1≤x","1≤x"),
		Example("PartialContradiction","[x<0]*[log(x)=0]*[1<x]","0"),
		Example("PartialChain","[x<0]*[log(x)=0]*[y>0]","[x<0∧log(x)=0∧y>0]")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,t:ℝ,z:ℂ,w:ℂ,p:𝔹"); return s; }
private Result run(Arena a,Term t,Term[] facts,bool trace=false){
	return simplify(a,t,facts,Options(DensityMode.preserve,trace));
}
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected)).output;
		auto fast=run(a,input,facts),checked=run(a,input,facts,true);
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(run(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"guard simplification regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: guard-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,run(a,s.parse(a,c.input),facts,true)));
	}
	writeln("Wrote guard certificates.");
}
