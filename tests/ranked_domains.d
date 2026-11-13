module ranked_domain_tests;
import qsym;
import std.conv:to;
import std.datetime.stopwatch:StopWatch,AutoStart;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected; bool ranked=true; }
private Case[] cases(){ return [
	Case("Masked","μ(f:ℕ→ℕ).λ(n:ℕ).([n=0]*2+[¬(n=0)]*([n≤10]*f(n sub 1)+[¬(n≤10)]*f(n+1)))","{n:ℕ|n≤10}"),
	Case("Conditional","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 2 else if n≤10 then f(n sub 1) else f(n+1)","{n:ℕ|n≤10}"),
	Case("Billion","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 2 else if n≤1000000000 then f(n sub 1) else f(n+1)","{n:ℕ|n≤1000000000}"),
	Case("Strict","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 2 else if n<10 then f(n sub 1) else f(n+1)","{n:ℕ|n≤9}"),
	Case("Parameter","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 2 else if n≤k then f(n sub 1) else f(n+1)","{n:ℕ|n≤k}",false),
	Case("ZeroCutoff","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 2 else f(n+1)","{n:ℕ|n=0}"),
	Case("Nonlinear","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 2 else if n≤1000000000 then f(n sub 1)*f(n sub 1)+n else f(n+1)","{n:ℕ|n≤1000000000}"),
	Case("RealValues","μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 2 else if n≤10 then exp(f(n sub 1)) else f(n+1)","{n:ℕ|n≤10}"),
	Case("SelfLoop","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 2 else if n≤10 then f(n) else f(n+1)","{n:ℕ|n=0}"),
	Case("MissingBase","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)+f(n sub 3)","{n:ℕ|n≤1}",false),
	Case("UndefinedBase","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 sub 1 else if n≤10 then f(n sub 1) else f(n+1)","{n:ℕ|false}",false),
	Case("Upward","μ(f:ℕ→ℕ).λ(n:ℕ).if n=5 then 2 else f(n+1)","{n:ℕ|n≤5}",false)
]; }
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/ranked-domains"; mkdirRecurse(directory);
	foreach(c;cases()){
		auto owner=Session.open(); FunctionSyntax s; s.declare("k:ℕ"); auto watch=StopWatch(AutoStart.yes);
		auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true),true),text=s.format(owner.arena,r);
		watch.stop(); auto count=owner.arena.length;
		enforce(!r.exhausted,c.name~" exhausted");
		enforce(text==s.format(owner.arena,s.run(owner.arena,c.expected)),c.name~": "~text);
		auto code=s.exportCertificate(owner.arena,r);
		if(c.ranked){
			enforce(code.indexOf("SetFixed.Predicate.least_nat_of_closed")>=0,c.name~" missing restricted induction");
			enforce(code.indexOf("SetFixed.Predicate.step_least")<0,c.name~" enumerated recursive depths");
			enforce(code.indexOf("Recursion.solve_")<0,c.name~" solved recurrence values");
			enforce(count<1500,c.name~" work budget: "~to!string(count));
		}
		enforce(s.format(owner.arena,s.run(owner.arena,text))==text,c.name~" round trip");
		enforce(s.format(owner.arena,s.run(owner.arena,c.source,[],Options(DensityMode.preserve,false),true))==text,c.name~" tracing changed result");
		write(buildPath(directory,c.name~".lean"),code);
		writeln(c.name,": ",text,"; ",watch.peek.total!"msecs"," ms; ",count," nodes");
	}
	writeln(cases().length," ranked-domain cases"); return 0;
}
