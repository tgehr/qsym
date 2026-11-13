module affine_recurrence_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:
private struct Case{ string name,source,expected,variables; }
private Case[] cases(){ return [
	Case("Natural","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1","λ(n:ℕ). get(((((2,1),(0,1))^n)@(3,1)),0)"),
	Case("NaturalZero","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1)(0)","3"),
	Case("NaturalTen","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1)(10)","4095"),
	Case("Integer","μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then -3 else -2*f(n sub 1)+1",""),
	Case("IntegerFive","(μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then -3 else -2*f(n sub 1)+1)(5)","107"),
	Case("IntegerAdd","(μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then -3 else f(n sub 1)-2)(8)","-19"),
	Case("IntegerMul","(μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then -3 else -2*f(n sub 1))(8)","-768"),
	Case("NaturalParameters","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then a else c*f(n sub 1)+d","","a:ℕ,c:ℕ,d:ℕ"),
	Case("IntegerParameters","μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then a else c*f(n sub 1)+d","","a:ℤ,c:ℤ,d:ℤ"),
	Case("CompoundParameters","μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then a+1 else (c+1)*f(n sub 1)+d*2","","a:ℤ,c:ℤ,d:ℤ"),
	Case("Rational","μ(f:ℕ→ℚ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1",""),
	Case("RationalFour","(μ(f:ℕ→ℚ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1)(4)","(63:ℚ)"),
	Case("Real","μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1",""),
	Case("RealThree","(μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1)(3)","(31:ℝ)"),
	Case("Complex","μ(f:ℕ→ℂ).λ(n:ℕ).if n=0 then 1 else ⅈ*f(n sub 1)+1",""),
	Case("ComplexThree","(μ(f:ℕ→ℂ).λ(n:ℕ).if n=0 then 1 else ⅈ*f(n sub 1)+1)(3)","(0:ℂ)"),
	Case("Repeated","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else f(n sub 1)+f(n sub 1)",""),
	Case("Nested","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else 2*(f(n sub 1)+3)+4)(3)","78"),
	Case("RightScale","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else (f(n sub 1)+3)*2+4)(3)","78"),
	Case("ReverseAdd","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 1+f(n sub 1)*2)(4)","63"),
	Case("ZeroScale","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 0*f(n sub 1)+4)(4)","4"),
	Case("Domain","domain(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1)","{n:ℕ|true}"),
	Case("UndefinedInput","defined((μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1)(0 sub 1))","false"),
	Case("InactiveInput","[false]*(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1)(0 sub 1)","0")
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
		if(c.name!="InactiveInput"&&c.name!="Domain"&&c.name!="UndefinedInput") enforce(proof.indexOf("AffineRecurrence.solve")>=0,c.name~" missing solver proof");
		if(directory.length) write(buildPath(directory,c.name~".lean"),proof);
	}
}
unittest{
	run();
	foreach(source;[
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else f(n sub 1)*f(n sub 1)+2",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else 2*f(n sub 2)+1",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else 2*f(n)+1",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else 2*f(n+1)+1",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else n*f(n sub 1)+1",
		"μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 1 else 2*f(n sub 1)+1/x"]){
		auto owner=Session.open(); FunctionSyntax s; auto r=s.run(owner.arena,source);
		enforce(!r.exhausted&&s.format(owner.arena,r).indexOf("μ(")>=0,"unsupported recurrence replaced: "~source);
	}
	foreach(seed;[0,1,3]) foreach(multiplier;[0,1,2,3]) foreach(offset;[1,2,4]){
		ulong value=seed;
		foreach(n;0..7){
			auto owner=Session.open(); FunctionSyntax s;
			auto source="(μ(f:ℕ→ℕ).λ(k:ℕ).if k=0 then "~to!string(seed)~" else "~to!string(multiplier)~"*f(k sub 1)+"~to!string(offset)~")("~to!string(n)~")";
			auto r=s.run(owner.arena,source); enforce(!r.exhausted&&s.format(owner.arena,r)==to!string(value),source); value=multiplier*value+offset;
		}
	}
}
int main(string[] args){
	auto dir=args.length>1?args[1]:"build/affine-recurrences"; mkdirRecurse(dir); run(dir); writeln(cases().length," affine recurrence certificates"); return 0;
}
