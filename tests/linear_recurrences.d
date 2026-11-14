module linear_recurrence_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected,variables; }
private Case[] cases(){ return [
	Case("Fibonacci","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)",""),
	Case("FibonacciTen","(μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2))(10)","55"),
	Case("FibonacciZero","(μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2))(0)","0"),
	Case("FibonacciOne","(μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2))(1)","1"),
	Case("Reverse","μ(f:ℕ→ℕ).λ(n:ℕ).if 1<n then f(n sub 2)+f(n sub 1) else n",""),
	Case("Tribonacci","μ(f:ℕ→ℕ).λ(n:ℕ).if n<3 then n*n else f(n sub 1)+f(n sub 2)+f(n sub 3)",""),
	Case("TribonacciSix","(μ(f:ℕ→ℕ).λ(n:ℕ).if n<3 then n*n else f(n sub 1)+f(n sub 2)+f(n sub 3))(6)","34"),
	Case("OrderFour","(μ(f:ℕ→ℕ).λ(n:ℕ).if n<4 then n else f(n sub 1)+f(n sub 2)+f(n sub 3)+f(n sub 4))(5)","12"),
	Case("ExtraSeeds","μ(f:ℕ→ℕ).λ(n:ℕ).if n<3 then n*n else f(n sub 1)+f(n sub 2)","λ(n:ℕ). get(((((0,1,0),(0,0,1),(0,1,1))^n)@(0,1,4)),0)"),
	Case("Stride","(μ(f:ℕ→ℕ).λ(n:ℕ).if n<3 then n else 2*f(n sub 3)+1)(7)","7"),
	Case("NestedSeeds","μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then 2 else if n=1 then -1 else 2*f(n sub 1)-3*f(n sub 2)+4",""),
	Case("NestedSeedsFive","(μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then 2 else if n=1 then -1 else 2*f(n sub 1)-3*f(n sub 2)+4)(5)","35"),
	Case("NestedScale","(μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else 2*(f(n sub 1)+f(n sub 2)+3)+1)(4)","79"),
	Case("RightScale","(μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else (f(n sub 1)+f(n sub 2)+3)*2+1)(4)","79"),
	Case("Repeated","μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2)+f(n sub 1)",""),
	Case("ZeroScale","(μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else 0*f(n sub 2)+4)(4)","4"),
	Case("NaturalParameters","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then a else if n=1 then b else c*f(n sub 1)+d*f(n sub 2)+h","","a:ℕ,b:ℕ,c:ℕ,d:ℕ,h:ℕ"),
	Case("IntegerParameters","μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then a else if n=1 then b else c*f(n sub 1)+d*f(n sub 2)+h","","a:ℤ,b:ℤ,c:ℤ,d:ℤ,h:ℤ"),
	Case("RationalParameters","μ(f:ℕ→ℚ).λ(n:ℕ).if n=0 then a else if n=1 then b else c*f(n sub 1)+d*f(n sub 2)+h","","a:ℚ,b:ℚ,c:ℚ,d:ℚ,h:ℚ"),
	Case("RealParameters","μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then a else if n=1 then b else c*f(n sub 1)+d*f(n sub 2)+h","","a:ℝ,b:ℝ,c:ℝ,d:ℝ,h:ℝ"),
	Case("ComplexParameters","μ(f:ℕ→ℂ).λ(n:ℕ).if n=0 then a else if n=1 then b else c*f(n sub 1)+d*f(n sub 2)+h","","a:ℂ,b:ℂ,c:ℂ,d:ℂ,h:ℂ"),
	Case("CompoundParameters","μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then a+1 else if n=1 then b*2 else (c+1)*(f(n sub 1)+f(n sub 2))+d*2","","a:ℤ,b:ℤ,c:ℤ,d:ℤ"),
	Case("Rational","(μ(f:ℕ→ℚ).λ(n:ℕ).if n<2 then n else 2*f(n sub 1)+f(n sub 2))(4)","(12:ℚ)"),
	Case("Real","(μ(f:ℕ→ℝ).λ(n:ℕ).if n<2 then n else 2*f(n sub 1)+f(n sub 2))(4)","(12:ℝ)"),
	Case("Complex","(μ(f:ℕ→ℂ).λ(n:ℕ).if n<2 then 1 else ⅈ*f(n sub 1)+f(n sub 2)+1)(3)","(1+2*ⅈ:ℂ)"),
	Case("InactiveBase","μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 0 else if n<2 then 1/n else f(n sub 1)+f(n sub 2)",""),
	Case("FirstOrderPrefix","μ(f:ℕ→ℕ).λ(n:ℕ).if n<3 then n*n else 2*f(n sub 1)+1",""),
	Case("Domain","domain(μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2))","{n:ℕ|true}"),
	Case("UndefinedInput","defined((μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2))(0 sub 1))","false"),
	Case("InactiveInput","[false]*(μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2))(0 sub 1)","0")
]; }
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(); FunctionSyntax s; if(c.variables.length) s.declare(c.variables);
		auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
		enforce(!r.exhausted,c.name~" exhausted");
		if(c.expected.length){ auto expected=s.format(owner.arena,s.run(owner.arena,c.expected)); enforce(text==expected,c.name~": "~text~" expected "~expected); }
		else enforce(text.indexOf("μ(")<0&&text.indexOf("^n")>=0,c.name~": "~text);
		enforce(s.format(owner.arena,s.run(owner.arena,text))==text,c.name~" round trip");
		auto proof=s.exportCertificate(owner.arena,r);
		if(c.name!="InactiveInput"&&c.name!="Domain"&&c.name!="UndefinedInput") enforce(proof.indexOf("LinearRecurrence.solve_matrix")>=0,c.name~" missing solver proof");
		if(directory.length) write(buildPath(directory,c.name~".lean"),proof);
	}
	foreach(source;[
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else f(n sub 1)+f(n sub 2)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n sub 1)+0*f(n sub 3)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else if n=2 then 1 else f(n sub 1)+f(n sub 2)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n sub 1)*f(n sub 2)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else n*f(n sub 1)+f(n sub 2)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n)+f(n sub 1)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n<2 then n else f(n+1)+f(n sub 1)",
		"μ(f:ℕ→ℝ).λ(n:ℕ).if n<2 then 1/n else f(n sub 1)+f(n sub 2)",
		"μ(f:ℕ→ℝ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2)+1/x",
		"μ(f:ℕ→ℝ).λ(n:ℕ).if n<2∧1/x>0 then n else f(n sub 1)+f(n sub 2)"]){
		auto owner=Session.open(); FunctionSyntax s; auto r=s.run(owner.arena,source);
		enforce(!r.exhausted&&s.format(owner.arena,r).indexOf("μ(")>=0,"unsupported recurrence replaced: "~source);
	}
}
unittest{ run(); }
int main(string[] args){
	auto dir=args.length>1?args[1]:"build/linear-recurrences"; mkdirRecurse(dir); run(dir); writeln(cases().length," linear recurrence certificates; 10 unsupported cases retained"); return 0;
}
