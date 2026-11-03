module all;
import qsym;
import qsym.spec;

@safe unittest{
	import std.exception:assertThrown;
	import std.algorithm:canFind;
	auto session=Session.open();
	auto a=session.arena;
	auto x=a.variable(Sort.real_,0),z=a.real_(0);
	auto t=a.add(x,z);
	auto fast=simplify(a,t);
	assertThrown(exportLean(a,fast));
	auto checked=simplify(a,t,Options(DensityMode.preserve,true));
	assert(exportLean(a,checked).canFind("theorem simplification"));
	assertThrown(simplify(a,x,Options(DensityMode.distributionOnly)));
	// Traversal is iterative, even for input deeper than the process stack.
	foreach(i;0..50_000) t=a.add(t,z);
	import core.memory:GC;
	GC.collect();
	assert(simplify(a,t).output==x);
	// Sharing: both arguments point at the same subterm.
	auto sharedTerm=a.add(a.add(x,z),a.add(x,z));
	assert(simplify(a,sharedTerm).output==a.mul(a.real_(2),x));
}

void main(){}
