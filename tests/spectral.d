module spectral_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected,variables; bool spectral=true; }
private Case[] cases(){ return [
	Case("NaturalFreeExponent","((2,0),(0,3))^n@(4,5)","(4*2^n,5*3^n)","n:ℕ"),
	Case("RationalFreeExponent","(((2:ℚ),1),(0,3))^n@(1,2)","((2*3^n-2^n:ℚ),(2*3^n:ℚ))","n:ℕ"),
	Case("ComplexTriangular","λ(n:ℕ).((ⅈ,1),(0,-ⅈ))^n@(1,2)",""),
	Case("NaturalDiagonal","λ(n:ℕ).((2,0),(0,3))^n@(4,5)","λ(n:ℕ).(4*2^n,5*3^n)"),
	Case("IntegerDiagonal","λ(n:ℕ).(((-2:ℤ),0),(0,3))^n@((4:ℤ),5)","λ(n:ℕ).((4:ℤ)*(-2)^n,(5:ℤ)*3^n)"),
	Case("RationalDiagonal","λ(n:ℕ).((1/2,0),(0,1/3))^n@(4,5)",""),
	Case("RealDiagonal","λ(n:ℕ).(((2:ℝ),0),(0,3))^n@(4,5)",""),
	Case("ComplexDiagonal","λ(n:ℕ).((ⅈ,0),(0,-ⅈ))^n@(1,1)",""),
	Case("RepeatedDiagonal","λ(n:ℕ).((2,0),(0,2))^n@(4,5)","λ(n:ℕ).(4*2^n,5*2^n)"),
	Case("DiagonalThree","λ(n:ℕ).((2,0,0),(0,3,0),(0,0,4))^n@(1,2,3)","λ(n:ℕ).(2^n,2*3^n,3*4^n)"),
	Case("DiagonalParameters","λ(n:ℕ).((a,0),(0,b))^n@(x,y)","λ(n:ℕ).(a^n*x,b^n*y)","a:ℝ,b:ℝ,x:ℝ,y:ℝ"),
	Case("Rational","λ(n:ℕ).(((2:ℚ),1),(0,3))^n@((1:ℚ),2)","λ(n:ℕ).((2*3^n-2^n:ℚ),(2*3^n:ℚ))"),
	Case("RealTwo","λ(n:ℕ).(((0:ℝ),1),(1,1))^n@(0,1)",""),
	Case("RealFibonacci","μ(f:ℕ→ℝ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2)",""),
	Case("FibonacciTen","(μ(f:ℕ→ℝ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2))(10)","(55:ℝ)","",false),
	Case("FibonacciZero","(μ(f:ℕ→ℝ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2))(0)","(0:ℝ)","",false),
	Case("FibonacciOne","(μ(f:ℕ→ℝ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2))(1)","(1:ℝ)","",false),
	Case("ComplexRotation","λ(n:ℕ).((0,-ⅈ*ⅈ*ⅈ*ⅈ),(1,0))^n@(1,0)",""),
	Case("ComplexRotationReal","λ(n:ℕ).(((0:ℂ),-1),(1,0))^n@(1,0)",""),
	Case("ComplexSeeds","λ(n:ℕ).(((0:ℂ),-1),(1,0))^n@(x,y)","","x:ℂ,y:ℂ"),
	Case("RealSeeds","λ(n:ℕ).(((0:ℝ),1),(1,1))^n@(x+1,y*2)","","x:ℝ,y:ℝ"),
	Case("Block","λ(n:ℕ).(((0:ℝ),1,0),(1,1,0),(0,0,3))^n@(0,1,2)",""),
	Case("ZeroEigenvalue","λ(n:ℕ).(((0:ℝ),1),(0,2))^n@(3,4)",""),
	Case("ZeroEigenvalueZero","(λ(n:ℕ).(((0:ℝ),1),(0,2))^n@(3,4))(0)","((3:ℝ),(4:ℝ))","",false),
	Case("ZeroEigenvalueOne","(λ(n:ℕ).(((0:ℝ),1),(0,2))^n@(3,4))(1)","((4:ℝ),(8:ℝ))","",false),
	Case("LargeExponent","(((2:ℚ),1),(0,3))^17@(1,2)","((258149254:ℚ),(258280326:ℚ))"),
	Case("PartialExponent","λ(n:ℕ).((2,0),(0,3))^(n sub 1)@(4,5)",""),
	Case("UndefinedExponent","defined((λ(n:ℕ).((2,0),(0,3))^n@(4,5))(0 sub 1))","false","",false),
	Case("Projection","λ(n:ℕ).get(((2,0),(0,3))^n@(4,5),1)","λ(n:ℕ).5*3^n"),
	Case("PartialProjection","defined(get((1,1/0),0))","false","",false),
	Case("PartialProjectionTail","defined(get((1/0,1),1))","false","",false),
	Case("ProjectionBound","λ(n:ℕ).get((n,n+1),1)","λ(n:ℕ).n+1","",false),
	Case("ProjectionOutOfBounds","defined(get((1,2),2))","false","",false)
]; }
private void run(string directory=""){
	foreach(c;cases()){
		writeln(c.name);
		auto owner=Session.open(); FunctionSyntax s; if(c.variables.length) s.declare(c.variables);
		auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
		enforce(!r.exhausted,c.name~" exhausted");
		if(c.expected.length){ auto expected=s.format(owner.arena,s.run(owner.arena,c.expected)); enforce(text==expected,c.name~": "~text~" expected "~expected); }
		enforce(text.indexOf("@")<0&&text.indexOf("μ(")<0&&text.indexOf("get(")<0,c.name~": "~text);
		auto again=s.run(owner.arena,text),printed=s.format(owner.arena,again);
		if(!r.scalarOnly&&!r.lowered){
			enforce(!again.scalarOnly&&!again.lowered&&r.bindings.type(r.reduction.output)==again.bindings.type(again.reduction.output),c.name~" round-trip type");
			auto next=r; next.reduction=r.bindings.normalize(r.reduction.output,4096,true); enforce(s.format(owner.arena,next)==text,c.name~" not normalized: "~text~" -> "~s.format(owner.arena,next));
		}
		enforce(s.format(owner.arena,s.run(owner.arena,printed))==printed,c.name~" printed normalization");
		auto proof=s.exportCertificate(owner.arena,r);
		if(c.spectral) enforce(proof.indexOf("Spectral.")>=0,c.name~" missing spectral proof");
		if(directory.length) write(buildPath(directory,c.name~".lean"),proof);
	}
	foreach(source;[
		"λ(n:ℕ).(((1:ℝ),1),(0,1))^n@(1,1)",
		"λ(n:ℕ).(((0:ℝ),-1),(1,0))^n@(1,0)",
		"λ(n:ℕ).(((0:ℚ),1),(1,1))^n@(0,1)",
		"λ(n:ℕ).(((1/0:ℝ),0),(0,1))^n@(1,1)",
		"λ(n:ℕ).(((1:ℝ),0),(0,1))^n@(1,1/0)",
		"λ(n:ℕ).(((0:ℝ),1,1),(1,1,0),(0,0,1))^n@(0,1,1)"]){
		auto owner=Session.open(); FunctionSyntax s; auto r=s.run(owner.arena,source);
		enforce(!r.exhausted&&s.exportCertificate(owner.arena,r).indexOf("theorem spectral")<0,"unsupported spectrum replaced: "~source);
	}
}
unittest{ run(); }
int main(string[] args){
	auto dir=args.length>1?args[1]:"build/spectral"; mkdirRecurse(dir); run(dir); writeln(cases().length," spectral certificates; 6 unsupported cases retained"); return 0;
}
