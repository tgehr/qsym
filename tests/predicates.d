module predicate_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("LinearEquality","[3*x+1=7]","[x=2]"),
		Example("NegativeLinearEquality","[-2*x+3=9]","[x=-3]"),
		Example("QuadraticGuard","[x^2=1]*[x<1]","[x=-1]"),
		Example("QuadraticGuardReverse","[x<1]*[x^2=1]","[x=-1]"),
		Example("QuadraticRoots","[x^2-3*x+2=0]","[x=1∨x=2]"),
		Example("RationalRoots","[6*x^2+x-1=0]","[x=-1/2∨x=1/3]"),
		Example("RepeatedRoot","[4*x^2-12*x+9=0]","[x=3/2]"),
		Example("NoRealRoots","[x^2+x+1=0]","0"),
		Example("NegativeDefinite","-x^2+x-1<0","true"),
		Example("QuadraticOpenInterval","x^2<1","-1<x∧x<1"),
		Example("QuadraticClosedInterval","x^2≤1","-1≤x∧x≤1"),
		Example("QuadraticOutside","1<x^2","x<-1∨1<x"),
		Example("QuadraticNonzero","x^2-1≠0","x≠-1∧x≠1"),
		Example("SquareNonnegative","0≤(x-2)^2","true"),
		Example("SquareNegative","(x-2)^2<0","false"),
		Example("SquareNonpositive","(x-2)^2≤0","x=2"),
		Example("SquarePositive","0<(x-2)^2","x≠2"),
		Example("EmptyRoots","[x^2=1]*[0<x]*[x<1]","0"),
		Example("RootBound","[x^2=1]*[0≤x]","[x=1]"),
		Example("RootBody","[x^2=1]*[x<1]*x","-[x=-1]"),
		Example("PartialRoots","[log(x)^2=1]*[log(x)<1]","[log(x)=-1]"),
		Example("PartialDeadBranch","[x^2=1]*[x<1]*log(x+1)","[x=-1]*log(0)"),
		Example("QuadraticFacts","x", "-1",["x^2=1","x<1"]),
		Example("QuadraticFactsReverse","x", "-1",["x<1","x^2=1"]),
		Example("QuadraticConjunctionFact","x", "-1",["x^2=1∧x<1"]),
		Example("RepeatedRootFact","x^2", "9/4",["4*x^2-12*x+9=0"]),
		Example("RedundantBound","[x<2]*[x<1]","[x<1]"),
		Example("RedundantBoundReverse","[x<1]*[x<2]","[x<1]"),
		Example("ClosedStrictBound","[x≤1]*[x<2]","[x≤1]"),
		Example("ClosedPoint","[x≤2]*[2≤x]","[x=2]"),
		Example("IrrationalRoots","x^2=2","x=-sqrt(2)∨x=sqrt(2)"),
		Example("Multivariate","x*y=1","x*y=1"),
		Example("PartialDisjunction","[x=0∨log(-1)=0]*[x≠0]","[x=0∨log(-1)=0]*[x≠0]"),
		Example("GuardedInverse","[x^2=1]*[x<1]/(x+1)","[x=-1]/0")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,p:𝔹"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected)).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"predicate simplification regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	assert(s.format(a,s.parse(a,"y+mulR(-[p],x)"))=="y+mulR(-[p],x)");
	foreach(pair;[["[3*x+1=7]","[x=2]"],["[x^2=1]*[x<1]","[x=-1]"],
		["x-2","x-2"],["-x","-x"],["-2*x","-2·x"],["x-y=0","x=y"]]){
		auto t=simplify(a,s.parse(a,pair[0])).output;
		assert(s.format(a,t)==pair[1],s.format(a,t));
	}
	foreach(source;["x-2","x-y","-(x+y)","-2*x*y","(-x)^3","(-x)^2", "x=-2/3",
		"z=1+ⅈ","z-(1+ⅈ)","(-2+3*ⅈ)*z","-(2+3*ⅈ)*z","complex(-2,0)","[p]*(-x)","mulR([p],-x)"]){
		auto t=s.parse(a,source),formatted=s.parse(a,s.format(a,t));
		assert(a.sort(t)==a.sort(formatted),source);
		assert(simplify(a,t).output==simplify(a,formatted).output,source~": "~s.format(a,t));
	}
	auto input=s.parse(a,"[x^2=1]*[x<1]");
	foreach(work;[size_t(0),1,100]){
		auto options=Options(DensityMode.preserve,true); options.maxAlgebraWork=work;
		auto r=simplify(a,input,[s.parse(a,"y>0")],options);
		assert(r.exhausted); exportLean(a,r);
	}
	assert(simplify(a,s.parse(a,"x")).output==s.parse(a,"x"));
}
@system void main(string[] args){
	enforce(args.length==2,"usage: predicate-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote predicate certificates.");
}
