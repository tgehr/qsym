module guard_budget_tests;
import qsym;
import std.conv:to;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:
private struct Case{ string name,source,expected; }
private Case[] cases(){ return [
	Case("Quadratic","[x^2=1]*[x<1]","[x=-1]"),
	Case("Disjunction","[x=-1∨x=1]*[x<1]","[x=-1]"),
	Case("PositiveAfterUnknown","abs(x)+[x>0]*abs(x)","abs(x)+[x>0]*x"),
	Case("NegativeAfterUnknown","abs(x)+[x<0]*abs(x)","abs(x)-[x<0]*x"),
	Case("DifferentContexts","[x<0]*abs(x)+[x>0]*abs(x)","-[x<0]*x+[x>0]*x"),
	Case("ShiftedContexts","[x<1]*abs(x-1)+[x>1]*abs(x-1)","[x<1]*(1-x)+[x>1]*(x-1)"),
	Case("PartialGuard","[x<0]*[log(x)=0]*[1<x]","0"),
	Case("NestedBounds","[x^2≤1]*[x<1]","[-1≤x∧x<1]")
]; }
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/guard-budget";mkdirRecurse(directory);
	auto limit=args.length>2?to!uint(args[2]):20000U;
	foreach(c;cases()){
		auto owner=Session.open();auto a=owner.arena;Syntax s;s.declare("x:ℝ");
		auto options=Options(DensityMode.preserve,true);options.maxAlgebraWork=limit;
		auto input=s.parse(a,c.source),r=simplify(a,input,[],options);
		enforce(!r.exhausted,c.name~" exhausted");
		auto expected=simplify(a,s.parse(a,c.expected),[],options);
		enforce(!expected.exhausted&&r.output==expected.output,c.name~": "~s.format(a,r.output));
		options.trace=false;auto fast=simplify(a,input,[],options);enforce(!fast.exhausted&&fast.output==r.output,c.name~" tracing changed output");
		auto again=simplify(a,r.output,[],options);enforce(!again.exhausted&&again.output==r.output,c.name~" not normalized");
		write(buildPath(directory,c.name~".lean"),exportLean(a,r));writeln(c.name,": ",s.format(a,r.output));
	}
	writeln(cases().length," guard-budget cases; budget=",limit);return 0;
}
