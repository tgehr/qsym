module fixed_domain_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.conv:to;
import std.string:indexOf;
@safe:
private struct Case{ string name,source; }
private Case[] cases(){ return [
	Case("Fibonacci","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)"),
	Case("FibonacciStrict","μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2)"),
	Case("Reversed","μ(f:ℕ→ℕ).λ(n:ℕ).if 1<n then f(n sub 1)+f(n sub 2) else n"),
	Case("Tribonacci","μ(f:ℕ→ℕ).λ(n:ℕ).if n<3 then n*n else f(n sub 1)+f(n sub 2)+f(n sub 3)"),
	Case("Coefficients","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n+1 else 2*f(n sub 1)+3*f(n sub 2)+n"),
	Case("Product","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n+1 else f(n sub 1)*f(n sub 2)"),
	Case("NonlinearReal","μ(f:ℕ→ℝ).λ(n:ℕ).if n≤1 then n else exp(f(n sub 1))+f(n sub 2)"),
	Case("BoolOr","μ(f:ℕ→𝔹).λ(n:ℕ).n=0∨f(n sub 1)"),
	Case("InactiveLoop","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)+[false]*f(n+1)")
]; }
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true),true),text=s.format(a,r);
		enforce(!r.exhausted&&text=="{n:ℕ | true}",c.name~": "~text);
		enforce(s.format(a,s.run(a,text))==text,c.name~" round trip");
		auto certificate=s.exportCertificate(a,r);
		enforce(certificate.indexOf("SetFixed.Predicate")>=0&&certificate.indexOf("SetFixed.domain_univ")>=0,c.name~" missing set-domain proof");
		if(directory.length) write(buildPath(directory,c.name~".lean"),certificate);
	}
}
unittest{
	run();
	foreach(source;[
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else if n=1 then 1 else f(n sub 1)+f(n sub 2)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n sub 1)+f(n sub 2)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n)+1",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n+1)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(f(n sub 1))",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else if f(n sub 1)=0 then 1 else f(n+1)",
		"μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 0 else 1/f(n sub 1)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n sub 1 else f(n sub 1)+f(n sub 2)"
	]){
		auto owner=Session.open(); FunctionSyntax s;
		auto text=s.format(owner.arena,s.run(owner.arena,source,[],Options(DensityMode.preserve,true),true));
		enforce(text.indexOf("domain(μ(")==0,"unsupported domain claimed total: "~text);
	}
	foreach(order;2..8){
		string sum; foreach(k;1..order+1){ if(sum.length) sum~="+"; sum~="f(n sub "~to!string(k)~")"; }
		auto source="μ(f:ℕ→ℕ).λ(n:ℕ).if n<"~to!string(order)~" then n else "~sum;
		auto owner=Session.open(); FunctionSyntax s;
		enforce(s.format(owner.arena,s.run(owner.arena,source,[],Options(DensityMode.preserve,true),true))=="{n:ℕ | true}","recurrence order "~to!string(order));
	}
	auto owner=Session.open(); FunctionSyntax s; s.declare("k:ℕ");
	auto fib=cases()[0].source;
	enforce(s.format(owner.arena,s.run(owner.arena,"defined(("~fib~")(k))"))=="true","symbolic argument");
	enforce(s.format(owner.arena,s.run(owner.arena,"defined(("~fib~")(0 sub 1))"))=="false","partial argument");
	enforce(s.format(owner.arena,s.run(owner.arena,"defined((k≠0)∧(0 sub 1≤k))"))=="k=0","partial nonzero bound");
	enforce(s.format(owner.arena,s.run(owner.arena,"defined(3≤k∧(0 sub 1≤k))"))=="k≤2","partial lower bound");
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/fixed-domains"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," fixed-domain certificates"); return 0;
}
