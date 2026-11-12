module recursion_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,expected,variables; bool domain; }
private Case[] cases(){
	return [
		Case("Constant","(μ(f:ℕ→ℕ).λ(n:ℕ).7)(2)","7"),
		Case("ConstantDomain","domain(μ(f:ℕ→ℕ).λ(n:ℕ).7)","{x:ℕ | true}"),
		Case("Identity","μ(f:ℕ→ℕ).f","λ(x:ℕ). undefined(ℕ)"),
		Case("IdentityEta","μ(f:ℕ→ℕ).λ(n:ℕ).f(n)","λ(x:ℕ). undefined(ℕ)"),
		Case("IdentityCall","(μ(f:ℕ→ℕ).f)(2)","undefined(ℕ)"),
		Case("IdentityDomain","domain(μ(f:ℕ→ℕ).f)","{x:ℕ | false}"),
		Case("IdentityMember","0∈domain(μ(f:ℕ→ℕ).f)","false"),
		Case("Defined","defined(μ(f:ℕ→ℕ).λ(n:ℕ).f(n+1))","true"),
		Case("Count","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n sub 1)+1)(3)","3"),
		Case("Fibonacci","(μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2))(6)","8"),
		Case("Factorial","(mu(f:Nat→Nat).lambda(n:Nat).if n=0 then 1 else n*f(n sub 1))(4)","24"),
		Case("DeadDivergence","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else f(n+1))(0)","1"),
		Case("MaskedDivergence","(μ(f:ℕ→ℕ).λ(n:ℕ).[n≠0]*f(n+1))(0)","0"),
		Case("ConstantMask","(μ(f:ℕ→ℕ).λ(n:ℕ).[false]*f(n))(3)","0"),
		Case("NestedCall","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(f(n sub 1)))(2)","0"),
		Case("Sequence","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else seq(f(n sub 1),1))(2)","1"),
		Case("GuardedDivergence","(μ(f:ℕ→ℕ).λ(n:ℕ|n≠0).f(n+1))(0)","undefined(ℕ)"),
		Case("BoundedDomainInside","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else if n<10 then f(n sub 1) else f(n+1))(3)","true","",true),
		Case("DomainMembership","2∈domain(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n sub 1))","true"),
		Case("BooleanOr","(μ(f:ℕ→𝔹).λ(n:ℕ).n=0∨f(n sub 1))(2)","true"),
		Case("BooleanAnd","(μ(f:ℕ→𝔹).λ(n:ℕ).n≠0∧f(n sub 1))(2)","false"),
		Case("BooleanNot","(μ(f:ℕ→𝔹).λ(n:ℕ).if n=0 then true else ¬f(n sub 1))(3)","false"),
		Case("Integer","(μ(f:ℤ→ℤ).λ(n:ℤ).if n≤0 then 0 else f(n-1)-1)(2)","-2"),
		Case("Rational","(μ(f:ℕ→ℚ).λ(n:ℕ).if n=0 then 1 else f(n sub 1)/2)(2)","1/4"),
		Case("Real","(μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 1 else sqrt(f(n sub 1)))(2)","1"),
		Case("Complex","(μ(f:ℕ→ℂ).λ(n:ℕ).if n=0 then 1 else f(n sub 1)*ⅈ)(2)","-1"),
		Case("Capture","(λ(x:ℕ).μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then x else f(n sub 1))(7)(2)","7"),
		Case("Shadow","(λ(f:ℕ).μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else f(n sub 1))(9)(2)","1"),
		Case("SymbolicCall","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n sub 1))(n)","","n:ℕ"),
		Case("SymbolicDomain","domain(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n sub 1))"),
		Case("BottomDomain","domain(undefined(ℕ→ℕ))","{x:ℕ | false}"),
		Case("BottomDefined","defined(undefined(ℝ))","false"),
		Case("BottomHolds","holds(undefined(𝔹))","false"),
		Case("UndefinedInput","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n sub 1))(0 sub 1)","false","",true)
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
		if(c.variables.length) s.declare(c.variables);
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true),c.domain),output=s.format(a,r);
		enforce(!r.exhausted,c.name~" exhausted");
		if(c.expected.length) enforce(output==c.expected,c.name~": "~output);
		if(!r.scalarOnly){
			auto n=r.bindings.normalize(r.reduction.output,4096,true);
			enforce(n.output==r.reduction.output,c.name~" not a normal form");
		}
		auto again=s.run(a,output); enforce(s.format(a,again)==output,c.name~" round trip: "~output~" -> "~s.format(a,again));
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
}
unittest{
	run(); auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
	foreach(source;["μ(f:ℕ).0","μ(f:ℕ→ℕ).0","μ(f:ℕ→ℕ).λ(n:ℕ).if defined(f(n)) then 0 else 1",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n∈domain(f) then 0 else 1","μ(f:(ℕ→ℕ)→ℕ).λ(g:ℕ→ℕ).0",
		"μ(f:ℕ→ℕ).λ(n:ℕ).(λ(x:ℕ).x)(f(n))"])
		assertThrown(s.run(a,source));
	auto source="(μ(f:ℕ→ℕ).λ(n:ℕ).f(n+1))(0)",r=s.run(a,source);
	enforce(r.exhausted,"divergent recursion must stay unresolved");
	enforce(!r.scalarOnly&&!r.lowered,"divergent recursion invented a value");
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/recursion"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," recursion certificates"); return 0;
}
