module discrete_interval_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:
private struct Case{ string name,source,expected; string[] facts; }
private Case[] cases(){ return [
	Case("AndAssociation","(p∧q)∧r","p∧(q∧r)"),
	Case("OrAssociation","(p∨q)∨r","p∨(q∨r)"),
	Case("UpperChain","(p∧n≤10)∧n≤11","p∧n≤10"),
	Case("PrefixJoin","n≤1∨(n≠0∧n≤11∧n≤12)","n≤11"),
	Case("PrefixReverse","(n≠0∧n≤11)∨n≤1","n≤11"),
	Case("BillionCover","1000000001≤n∨(n≤1∨n≠0∧n≤1000000001∧n≤1000000002)","true"),
	Case("Adjacent","n≤3∨(4≤n∧n≤10)","n≤10"),
	Case("AdjacentReverse","(4≤n∧n≤10)∨n≤3","n≤10"),
	Case("ReversedBounds","n≤3∨(n≤10∧4≤n)","n≤10"),
	Case("ReversedBoundsRight","(n≤10∧4≤n)∨n≤3","n≤10"),
	Case("ThreePredecessorCover","1000000001≤n∨(n≤2∨n≤1000000001∧2≤n)","true"),
	Case("Overlap","n≤5∨(3≤n∧n≤10)","n≤10"),
	Case("OverlapReverse","(3≤n∧n≤10)∨n≤5","n≤10"),
	Case("StrictAdjacent","n<4∨(4≤n∧n<11)","n≤10"),
	Case("SingletonAdjacent","n≤3∨(4≤n∧n≤4)","n≤4"),
	Case("Gap","n≤1∨(3≤n∧n≤10)","n≤1∨(3≤n∧n≤10)"),
	Case("GapPoint","2≤1∨(3≤2∧2≤10)","false"),
	Case("UpperEndpoint","10≤3∨(4≤10∧10≤10)","true"),
	Case("OutsideEndpoint","11≤3∨(4≤11∧11≤10)","false"),
	Case("SymbolicAdjacent","n≤a∨(b≤n∧n≤c)","n≤c",["b≤a+1","a≤c"]),
	Case("SymbolicReverse","(b≤n∧n≤c)∨n≤a","n≤c",["b≤a+1","a≤c"]),
	Case("SymbolicClosure","n≠0∧k+1<n∨n≠0∧k≤n∨n≤k","true"),
	Case("NonzeroCover","n≠0∨n≤k","true"),
	Case("NonzeroReverse","n≤k∨n≠0","true"),
	Case("LowerCover","(n≠0∧k≤n)∨n≤k","true"),
	Case("LowerReverse","n≤k∨(n≠0∧k≤n)","true"),
	Case("IntegerAdjacent","i≤-3∨(-2≤i∧i≤5)","i≤5"),
	Case("IntegerReverse","(-2≤i∧i≤5)∨i≤-3","i≤5"),
	Case("IntegerReversedBounds","i≤-3∨(i≤5∧-2≤i)","i≤5"),
	Case("IntegerReversedBoundsRight","(i≤5∧-2≤i)∨i≤-3","i≤5"),
	Case("IntegerOverlap","i≤-3∨(-7≤i∧i≤5)","i≤5"),
	Case("IntegerStrict","i<-2∨(-2≤i∧i<6)","i≤5"),
	Case("IntegerGap","i≤-3∨(-1≤i∧i≤5)","i≤-3∨(-1≤i∧i≤5)"),
	Case("IntegerGapPoint","(-2:ℤ)≤-3∨(-1≤(-2:ℤ)∧(-2:ℤ)≤5)","false"),
	Case("IntegerSymbolic","i≤j∨(l≤i∧i≤m)","i≤m",["l≤j+1","j≤m"]),
	Case("IntegerSymbolicReverse","(l≤i∧i≤m)∨i≤j","i≤m",["l≤j+1","j≤m"]),
	Case("PartialGuardFalse","((false∧log(-1)<0)∧p)","false"),
	Case("PartialGuardTrue","((true∨log(-1)<0)∨p)","true")
]; }
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/discrete-intervals";mkdirRecurse(directory);
	foreach(c;cases()){
		auto owner=Session.open();auto a=owner.arena;Syntax s;s.declare("n:ℕ,k:ℕ,a:ℕ,b:ℕ,c:ℕ,i:ℤ,j:ℤ,l:ℤ,m:ℤ,p:𝔹,q:𝔹,r:𝔹,x:ℝ");
		Term[] facts;foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.source),options=Options(DensityMode.preserve,true);
		auto result=simplify(a,input,facts,options),expected=simplify(a,s.parse(a,c.expected,a.sort(input)),facts,options);
		auto text=s.format(a,result.output);enforce(!result.exhausted&&!expected.exhausted,c.name~" exhausted");
		enforce(result.output==expected.output,c.name~": "~text~" expected "~s.format(a,expected.output));
		options.trace=false;auto fast=simplify(a,input,facts,options);enforce(!fast.exhausted&&fast.output==result.output,c.name~" tracing changed result");
		auto again=simplify(a,result.output,facts,options);enforce(!again.exhausted&&again.output==result.output,c.name~" not normalized");
		auto parsed=simplify(a,s.parse(a,text,a.sort(result.output)),facts,options);enforce(!parsed.exhausted&&parsed.output==result.output,c.name~" round trip");
		write(buildPath(directory,c.name~".lean"),exportLean(a,result));writeln(c.name,": ",text);
	}
	writeln(cases().length," discrete-interval cases");return 0;
}
