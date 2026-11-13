module partial_domain_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.conv:to;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected; }
private Case[] cases(){ return [
	Case("MissingBase","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)+f(n sub 3)","{n:ℕ | n≤1}"),
	Case("Self","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n)","{n:ℕ | n≤1}"),
	Case("Increasing","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n+1)","{n:ℕ | n≤1}"),
	Case("Upward","μ(f:ℕ→ℕ).λ(n:ℕ).if n=5 then 7 else f(n+1)","{n:ℕ | n≤5}"),
	Case("NestedBase","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else if n=1 then 1 else f(n sub 1)+f(n sub 2)","{n:ℕ | true}"),
	Case("PartialLeaf","μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n sub 1 else f(n sub 1)+f(n sub 2)","{n:ℕ | n=1}"),
	Case("Empty","μ(f:ℕ→ℕ).λ(n:ℕ).f(n sub 1)+f(n sub 2)","{n:ℕ | false}"),
	Case("Nonlinear","μ(f:ℕ→ℝ).λ(n:ℕ).if n≤1 then n else exp(f(n sub 1))+f(n sub 3)","{n:ℕ | n≤1}"),
	Case("RealSelf","μ(f:ℝ→ℝ).λ(x:ℝ).if x>0 then log(x) else f(x)","{x:ℝ | 0<x}"),
	Case("RealReflection","μ(f:ℝ→ℝ).λ(x:ℝ).if x<0 then f(-x) else sqrt(x)","{x:ℝ | true}"),
	Case("RealPuncture","μ(f:ℝ→ℝ).λ(x:ℝ).if x<0 then f(-x) else 1/x","{x:ℝ | x≠0}"),
	Case("RationalSelf","μ(f:ℚ→ℚ).λ(q:ℚ).if q≠0 then 1/q else f(q)","{q:ℚ | q≠0}"),
	Case("ComplexSelf","μ(f:ℂ→ℂ).λ(z:ℂ).if z≠0 then clog(z) else f(z)","{z:ℂ | z≠0}"),
	Case("IntegerJump","μ(f:ℤ→ℤ).λ(i:ℤ).if i≤0 then i else f(0)","{i:ℤ | true}"),
	Case("BooleanSelf","μ(f:𝔹→ℕ).λ(p:𝔹).if p then 1 else f(p)","{p:𝔹 | p}"),
	Case("SparseUpward","μ(f:ℕ→ℕ).λ(n:ℕ).if n=5 then 7 else f(n+2)","{n:ℕ | n=5∨(n=3∨n=1)}"),
	Case("PartialGuard","μ(f:ℝ→ℝ).λ(x:ℝ).if 1/x>0 then 1 else f(x)","{x:ℝ | 0<x}"),
	Case("InverseCycle","μ(f:ℝ→ℝ).λ(x:ℝ).if x=0 then 1 else f(1/x)","{x:ℝ | x=0}")
]; }
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
		auto r=s.run(a,"domain("~c.source~")",[],Options(DensityMode.preserve,true)),text=s.format(a,r);
		enforce(!r.exhausted&&text==c.expected,c.name~": "~text);
		enforce(s.format(a,s.run(a,text))==text,c.name~" round trip");
		auto certificate=s.exportCertificate(a,r);
		enforce(certificate.indexOf("SetFixed.Predicate")>=0,c.name~" missing set-domain proof");
		if(directory.length) write(buildPath(directory,c.name~".lean"),certificate);
	}
}
private void runCalls(string directory=""){
	auto fib=cases()[0].source;
	foreach(pair;[["0","true","Zero"],["1","true","One"],["2","false","Two"],["7","false","Seven"],["0 sub 1","false","Undefined"],["n","n≤1","Symbolic"]]){
		auto owner=Session.open(); FunctionSyntax s; s.declare("n:ℕ");
		auto r=s.run(owner.arena,"defined(("~fib~")("~pair[0]~"))",[],Options(DensityMode.preserve,true));
		enforce(!r.exhausted&&s.format(owner.arena,r)==pair[1],"argument "~pair[0]);
		if(directory.length) write(buildPath(directory,"Defined"~pair[2]~".lean"),s.exportCertificate(owner.arena,r));
	}
}
unittest{
	run(); runCalls();
	foreach(order;2..7) foreach(base;0..order){
		string sum; foreach(k;1..order+1){ if(sum.length) sum~="+"; sum~="f(n sub "~to!string(k)~")"; }
		auto source="μ(f:ℕ→ℕ).λ(n:ℕ).if n<"~to!string(base)~" then n else "~sum;
		auto owner=Session.open(); FunctionSyntax s;
		auto expected=base==0?"false":base==1?"n=0":"n≤"~to!string(base-1);
		auto text=s.format(owner.arena,s.run(owner.arena,source,[],Options(DensityMode.preserve,true),true));
		enforce(text=="{n:ℕ | "~expected~"}","missing base "~to!string(base)~"/"~to!string(order)~": "~text);
	}
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/partial-domains"; mkdirRecurse(directory); run(directory); runCalls(directory);
	writeln(cases().length+6," partial-domain certificates"); return 0;
}
