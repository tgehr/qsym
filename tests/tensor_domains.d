module tensor_domain_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected,variables; }
private Case[] cases(){ return [
	Case("UndefinedSeed","defined(((0,1),(1,1))^0@(0 sub 1,1))","false"),
	Case("UndefinedMatrix","defined(((0 sub 1,1),(1,1))^0@(0,1))","false"),
	Case("UndefinedMatmul","defined(A@undefined(ℝ^(2×2)))","false","A:ℝ^(2×2)"),
	Case("UndefinedMatvec","defined(A@undefined(ℝ^2))","false","A:ℝ^(2×2)"),
	Case("UndefinedDot","defined(dot(undefined(ℤ^2),v))","false","v:ℤ^2"),
	Case("UndefinedAdd","defined(undefined(ℚ^2)+v)","false","v:ℚ^2"),
	Case("UndefinedMultiply","defined(((1:ℚ),1/0)·(0,0))","false"),
	Case("ZeroPowerPartial","domain(λ(x:ℝ). ((1/x,0),(0,1))^0)","{x:ℝ|x≠0}"),
	Case("ZeroPowerUndefined","defined(undefined(ℂ^(2×2))^0)","false"),
	Case("PartialPowerExponent","domain(λ(n:ℕ). A^(n sub 1))","{n:ℕ|n≠0}","A:ℝ^(2×2)"),
	Case("FibonacciDomain","domain(λ(n:ℕ).((0,1),(1,1))^(n sub 1)@(0,1))","{n:ℕ|n≠0}"),
	Case("BillionPower","defined(((0,1),(1,1))^1000000000@(0,1))","true"),
	Case("RealDotDomain","domain(λ(x:ℝ). dot((1/x,2),(3,4)))","{x:ℝ|x≠0}"),
	Case("ComplexDotDomain","domain(λ(z:ℂ). dot((1/z,ⅈ),(ⅈ,1)))","{z:ℂ|z≠0}"),
	Case("NestedAddDomain","domain(λ(x:ℝ). ((1/x,0),(0,1))+A)","{x:ℝ|x≠0}","A:ℝ^(2×2)"),
	Case("NestedMultiplyDomain","domain(λ(x:ℝ). ((1/x,0),(0,1))·A)","{x:ℝ|x≠0}","A:ℝ^(2×2)"),
	Case("MatvecDomain","domain(λ(x:ℝ). ((1/x,0),(0,1))@((1:ℝ),2))","{x:ℝ|x≠0}"),
	Case("MatmulDomain","domain(λ(x:ℝ). A@((1/x,0),(0,1)))","{x:ℝ|x≠0}","A:ℝ^(2×2)"),
	Case("TwoPartialOperands","domain(λ(x:ℝ). ((1/x,0),(0,1))@((1/(x-1),0),(0,1)))","{x:ℝ|x≠0∧x≠1}"),
	Case("GuardedMatrix","defined(guard(false,A)@v)","false","A:ℝ^(2×2),v:ℝ^2"),
	Case("MaskedElement","defined(([false]*(1/0),1)+(2,3))","true"),
	Case("PartialFunction","domain(λ(x:ℝ). A@f(x))","{x:ℝ|holds(x∈domain(f))}","A:ℝ^(2×2),f:ℝ→ℝ^2"),
	Case("EmptyAddLeft","defined(undefined(ℝ^0)+u)","false","u:ℝ^0"),
	Case("EmptyAddRight","defined(u+undefined(ℝ^0))","false","u:ℝ^0"),
	Case("EmptyDotLeft","defined(dot(undefined(ℝ^0),u))","false","u:ℝ^0"),
	Case("EmptyDotRight","defined(dot(u,undefined(ℝ^0)))","false","u:ℝ^0"),
	Case("EmptyRows","defined(B@undefined(ℝ^2))","false","B:ℝ^(0×2)"),
	Case("EmptyMatrixLeft","defined(undefined(ℝ^(0×2))@v)","false","v:ℝ^2"),
	Case("EmptyInner","defined(A@B)","true","A:ℝ^(2×0),B:ℝ^(0×3)"),
	Case("EmptyInnerPartial","defined(A@undefined(ℝ^(0×3)))","false","A:ℝ^(2×0)"),
	Case("EmptyPower","defined(Z^n)","true","Z:ℝ^(0×0),n:ℕ"),
	Case("EmptyPowerPartial","defined(undefined(ℝ^(0×0))^0)","false"),
	Case("SymbolicDimension","defined(C@v)","true","m:ℕ,n:ℕ,C:ℝ^(m×n),v:ℝ^n"),
	Case("SymbolicDimensionPartial","defined(C@undefined(ℝ^n))","false","m:ℕ,n:ℕ,C:ℝ^(m×n)"),
	Case("RationalDot","defined(dot(q,r))","true","q:ℚ^2,r:ℚ^2"),
	Case("IntegerPower","defined(A^n)","true","A:ℤ^(2×2),n:ℕ"),
	Case("Projection","defined(get(A^n@v,1))","true","A:ℤ^(3×3),v:ℤ^3,n:ℕ"),
	Case("PartialProjection","domain(λ(n:ℕ).get(A^(n sub 1)@v,0))","{n:ℕ|n≠0}","A:ℤ^(3×3),v:ℤ^3")
]; }
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/tensor-domains"; mkdirRecurse(directory);
	foreach(c;cases()){
		writeln(c.name);
		auto owner=Session.open(); FunctionSyntax s; if(c.variables.length) s.declare(c.variables);
		auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
		enforce(!r.exhausted,c.name~" exhausted");
		auto e=s.run(owner.arena,c.expected); enforce(!e.exhausted,c.name~" expected exhausted");
		auto expected=s.format(owner.arena,e); enforce(text==expected,c.name~": "~text~" expected "~expected);
		auto again=s.run(owner.arena,text); enforce(s.format(owner.arena,again)==text,c.name~" round trip");
		enforce(s.inspectType(owner.arena,text)==s.inspectType(owner.arena,c.source),c.name~" type changed");
		enforce(s.format(owner.arena,s.run(owner.arena,c.source,[],Options(DensityMode.preserve,false)))==text,c.name~" tracing changed output");
		if(!r.scalarOnly&&!r.lowered){ auto next=r; next.reduction=r.bindings.normalize(r.reduction.output,4096,true); enforce(s.format(owner.arena,next)==text,c.name~" not normalized"); }
		auto proof=s.exportCertificate(owner.arena,r);
		enforce(proof.indexOf("TensorDomains.Binary.defined")>=0,c.name~" missing tensor domain proof");
		enforce(proof.indexOf("Spectral.")<0,c.name~" evaluated spectrum during domain computation");
		write(buildPath(directory,c.name~".lean"),proof); writeln(text);
	}
	writeln(cases().length," tensor-domain cases");
	foreach(pair;[
		["A^(n sub 1)","(A^(n sub 1))"],
		["λ(n:ℕ). A^(n sub 1)","λ(n:ℕ). (A^(n sub 1))"],
		["A^(n+1)","(A^(n+1))"],
		["A^(n*m)","(A^(n·m))"],
		["A^n","(A^n)"],
		["A^2","(A^2)"]
	]){
		auto owner=Session.open(); FunctionSyntax s; s.declare("A:ℝ^(2×2),n:ℕ,m:ℕ");
		auto r=s.run(owner.arena,pair[0]),text=s.format(owner.arena,r);
		enforce(!r.exhausted&&text==pair[1],pair[0]~": "~text);
		auto again=s.run(owner.arena,text); enforce(!again.exhausted&&s.format(owner.arena,again)==text,pair[0]~" round trip");
		enforce(s.inspectType(owner.arena,text)==s.inspectType(owner.arena,pair[0]),pair[0]~" type changed");
		writeln(text);
	}
	writeln("6 tensor-power round trips"); return 0;
}
