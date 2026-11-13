module real_countdown_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected; bool measure; }
private Case[] cases(){ return [
	Case("User","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else 2*f(x-1))","{x:ℝ | true}",true),
	Case("HalfStep","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x<0 then x else f(x-1/2)+x)","{x:ℝ | true}",true),
	Case("Upward","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if 3≤x then x else f(x+1/3))","{x:ℝ | true}",true),
	Case("Branches","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤2 then x else f(x-1)+f(x-2))","{x:ℝ | true}",true),
	Case("HalvingPositive","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else f(x/2))","{x:ℝ | true}",true),
	Case("HalvingZero","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤0 then x else f(x/2))","{x:ℝ | x≤0}",false),
	Case("NegativeThreshold","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x< -7/3 then x else f(x-2/5))","{x:ℝ | true}",true),
	Case("ContractingAffine","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤0 then x else f((x-1)/2))","{x:ℝ | true}",true),
	Case("Nonlinear","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤0 then x else exp(f(x-1))+f(x-2)^2)","{x:ℝ | true}",true),
	Case("AbsoluteJump","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤0 then x else f(x-abs(x)-1))","{x:ℝ | true}",true),
	Case("BooleanResult","domain(μ(f:ℝ→𝔹).λ(x:ℝ).x≤0∨f(x-1))","{x:ℝ | true}",true),
	Case("ComplexResult","domain(μ(f:ℝ→ℂ).λ(x:ℝ).if x≤0 then x else cexp(f(x-1)))","{x:ℝ | true}",true),
	Case("Self","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else f(x))","{x:ℝ | x≤1}",false),
	Case("WrongDirection","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else f(x+1))","{x:ℝ | x≤1}",false),
	Case("NoBase","domain(μ(f:ℝ→ℝ).λ(x:ℝ).f(x-1))","{x:ℝ | false}",false),
	Case("PartialBase","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then 1/x else f(x-1))","",false),
	Case("InactiveLoop","domain(μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else f(x-1)+[false]*f(x+1))","{x:ℝ | true}",true),
	Case("DefinedZero","defined((μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else 2*f(x-1))(0))","true",true),
	Case("DefinedLarge","defined((μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else 2*f(x-1))(1000000))","true",true),
	Case("DefinedHalf","defined((μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else 2*f(x-1))(1/2))","true",true),
	Case("DefinedUndefined","defined((μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else 2*f(x-1))(1/0))","false",true),
	Case("DefinedSymbolic","defined((μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else 2*f(x-1))(x))","true",true),
	Case("DefinedReciprocal","defined((μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else 2*f(x-1))(1/x))","x≠0",true),
	Case("OffsetLE","(x-2)+1≤x","true",false),
	Case("OffsetPartial","defined(1/x-1≤1/x)","x≠0",false),
	Case("OffsetLT","x+1<x","false",false),
	Case("SelfLE","x≤x-1","false",false),
	Case("SelfLT","x<x+1","true",false),
	Case("OffsetLECommute","-1+x≤x","true",false),
	Case("OffsetLTCommute","1+x<x","false",false),
	Case("SelfLECommute","x≤-1+x","false",false),
	Case("SelfLTCommute","x<1+x","true",false),
	Case("BooleanOffsets","(x≤2 ∨ ((-3<x ∧ (x-1)+1≤x)∧(-3<x ∧ (x-2)+1≤x)))","true",false),
]; }
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(); FunctionSyntax s; s.declare("x:ℝ");
		auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
		enforce(!r.exhausted&&(c.expected.length?text==c.expected:text.indexOf("domain(μ(")==0),c.name~": "~text);
		if(c.expected.length) enforce(s.format(owner.arena,s.run(owner.arena,text))==text,c.name~" round trip");
		auto certificate=s.exportCertificate(owner.arena,r);
		if(c.measure) enforce(certificate.indexOf("SetFixed.Predicate.total_measure")>=0,c.name~" missing measure proof");
		if(directory.length) write(buildPath(directory,c.name~".lean"),certificate);
	}
}
unittest{ run(); }
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/real-countdown"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," real countdown certificates"); return 0;
}
