module recurrence_solver_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:

private struct Case{ string name,source,expected; }
private Case[] cases(){
	return [
		Case("Add","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2","λ(n:ℕ). 2·n+3"),
		Case("AddLeft","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2+f(n sub 1)","λ(n:ℕ). 2·n+3"),
		Case("AddZeroBase","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n sub 1)+2","λ(n:ℕ). 2·n"),
		Case("AddZeroStep","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+0","λ(n:ℕ). 3"),
		Case("AddAtZero","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2)(0)","3"),
		Case("AddAtOne","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2)(1)","5"),
		Case("AddLarge","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2)(10000)","20003"),
		Case("AddSymbolic","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2)(n)","2·n+3"),
		Case("AddParameters","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then a else f(n sub 1)+d","λ(n:ℕ). a+n·d"),
		Case("AddParameterCall","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then a else f(n sub 1)+d)(n)","a+n·d"),
		Case("AddDomain","domain(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2)","{n:ℕ | true}"),
		Case("AddDefined","defined(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2)","true"),
		Case("AddMembership","n∈domain(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2)","true"),
		Case("Mul","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*2","λ(n:ℕ). 3·2^n"),
		Case("MulLeft","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)","λ(n:ℕ). 3·2^n"),
		Case("MulZeroBase","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else f(n sub 1)*2","λ(n:ℕ). 0"),
		Case("MulOneRatio","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*1","λ(n:ℕ). 3"),
		Case("MulZeroRatio","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*0","λ(n:ℕ). ([n=0]·3:ℕ)"),
		Case("MulAtZero","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*2)(0)","3"),
		Case("MulAtOne","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*2)(1)","6"),
		Case("MulLarge","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*2)(100)","3802951800684688204490109616128"),
		Case("MulSymbolic","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*2)(n)","3·2^n"),
		Case("MulParameters","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then a else f(n sub 1)*d","λ(n:ℕ). a·d^n"),
		Case("MulParameterCall","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then a else f(n sub 1)*d)(n)","a·d^n"),
		Case("MulDomain","domain(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*2)","{n:ℕ | true}"),
		Case("UndefinedInput","defined((μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2)(0 sub 1))","false"),
		Case("GuardedInput","(λ(k:{k:ℕ|k<4}).(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2)(k))","λ(k:{k:ℕ | k≤3}). 2·k+3"),
		Case("InactiveGuard","[false]*(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*2)(0 sub 1)","0"),
		Case("NestedUnrelated","λ(k:ℕ).μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2","λ(k:ℕ). λ(n:ℕ). 2·n+3")
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s; s.declare("a:ℕ,d:ℕ,n:ℕ");
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true)),output=s.format(a,r); enforce(!r.exhausted,c.name~" exhausted");
		enforce(output==c.expected,c.name~": "~output);
		auto again=s.run(a,output); enforce(s.format(a,again)==output,c.name~" round trip");
		if(!r.scalarOnly) enforce(r.bindings.normalize(r.reduction.output,4096,true).output==r.reduction.output,c.name~" not normalized");
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
	auto owner=Session.open(); FunctionSyntax s; auto r=s.run(owner.arena,cases()[0].source);
	auto limited=r.bindings.normalize(r.reduction.input,0,true),code=r.bindings.exportLean(limited);
	enforce(limited.exhausted&&limited.output==limited.input&&code.indexOf("solve_nat_step")<0,"recurrence solver ignored its budget");
	if(directory.length) write(buildPath(directory,"Budget.lean"),code);
}
unittest{
	run();
	foreach(source;[
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=1 then 3 else f(n sub 1)+2",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n)+2",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n+1)+2",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 2)+2",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+n",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+(0 sub 1)",
		"μ(f:ℕ→ℕ).λ(n:ℕ|n<5).if n=0 then 3 else f(n sub 1)+2",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+f(n sub 2)"]){
		auto owner=Session.open(); FunctionSyntax s; auto r=s.run(owner.arena,source);
		enforce(!r.exhausted&&s.format(owner.arena,r).indexOf("μ(")>=0,"unsupported recurrence was replaced");
	}
	foreach(seed;[0,1,3]) foreach(delta;[0,1,2,5]) foreach(n;0..8) foreach(op;["+","*"]){
		auto owner=Session.open(); FunctionSyntax s;
		auto definition="μ(f:ℕ→ℕ).λ(k:ℕ).if k=0 then "~to!string(seed)~" else f(k sub 1)"~op~to!string(delta);
		auto r=s.run(owner.arena,"("~definition~")("~to!string(n)~")");
		ulong expected=seed; foreach(i;0..n) expected=op=="+"?expected+delta:expected*delta;
		enforce(!r.exhausted&&s.format(owner.arena,r)==to!string(expected),"recurrence evaluation mismatch");
	}
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/recurrences"; mkdirRecurse(directory); run(directory);
	writeln(cases().length+1," recurrence-solver certificates"); return 0;
}
