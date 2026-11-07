module associative_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.exception:enforce;
import std.stdio:writeln;
@safe:

struct Example{ string name,input,expected; bool expand; }
Example[] examples(){
	return [
		Example("RepeatedSum","(x+1)*(x+1)","(x+1)^2"),
		Example("PermutedSum","(x+1)*(1+x)","(x+1)^2"),
		Example("RepeatedComplexSum","(z+1)*(1+z)","(z+1)^2"),
		Example("RepeatedPartialSum","(1/x+1)*(1+1/x)","(1/x+1)^2"),
		Example("RepeatedFactors","(x+1)*(y+1)*(x+1)*(y+1)","(x+1)^2*(y+1)^2"),
		Example("RepeatedWithCoefficient","3*(x+1)*(x+1)","3*(x+1)^2"),
		Example("RepeatedWithPower","(x+1)^7*(x+1)*(x+1)","(x+1)^9"),
		Example("RepeatedCancellation","(x+1)*(x+1)/(x+1)","x+1"),
		Example("RepeatedExpansion","(x+1)*(x+1)","x^2+2*x+1",true),
		Example("DistinctFactors","(x+1)*(y+1)","(x+1)*(y+1)"),
		Example("DistinctExpansion","(x+1)*(y+1)","x*y+x+y+1",true),
		Example("ZeroPartialProduct","0*(1/x+1)*(1/x+1)","0"),
		Example("GuardedRepeated","[x≠0]*(1/x+1)*(1/x+1)","[x≠0]*(1/x+1)^2")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ"); return s; }
private Term deepSum(Arena a,uint count){
	auto t=a.variable(Sort.real_,0);
	foreach(i;0..count) t=a.add(t,a.real_(1));
	return t;
}
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected)).output;
		auto options=Options.init; options.expandPowers=c.expand;
		auto fast=simplify(a,input,options); options.trace=true;
		auto checked=simplify(a,input,options);
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,options).output==fast.output,c.name~" is not idempotent");
	}
	assert(!failures,"associative simplification regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena;
	auto options=Options(DensityMode.preserve,true);
	auto r=simplify(a,deepSum(a,512),options);
	assert(!r.exhausted&&r.output==a.add(a.variable(Sort.real_,0),a.real_(512)));
	assert(r.derivation.deductions.length<64,"normalizing every prefix again");
	// Same operator heads, different arguments: the generated join index must
	// reject these pairs without using the budget on their Cartesian product.
	auto t=a.real_(0);
	foreach(i;0..128){
		t=a.add(t,a.pow(a.call(Builtin.sinR,[a.variable(Sort.real_,i)]),2));
		t=a.add(t,a.pow(a.call(Builtin.cosR,[a.variable(Sort.real_,i+128)]),2));
	}
	options.maxAlgebraWork=100_000;
	r=simplify(a,t,options);
	assert(!r.exhausted,"unindexed pair search");
	assert(simplify(a,r.output,options).output==r.output);
}
@system void main(string[] args){
	enforce(args.length==2,"usage: associative-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto options=Options(DensityMode.preserve,true); options.expandPowers=c.expand;
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),options)));
	}
	auto owner=Session.open(); auto a=owner.arena;
	write(buildPath(args[1],"Deep512.lean"),exportLean(a,simplify(a,deepSum(a,512),Options(DensityMode.preserve,true))));
	writeln("Wrote associative certificates.");
}
