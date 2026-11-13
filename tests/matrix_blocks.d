module matrix_block_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source; bool split=true,closed=true; }
private Case[] cases(){ return [
	Case("Natural","((1,1,0,0),(0,2,0,0),(0,0,3,0),(0,0,0,4))^n@(0,1,1,1)"),
	Case("Integer","(((1:ℤ),1,0,0),(0,2,0,0),(0,0,-1,0),(0,0,0,3))^n@((0:ℤ),1,1,1)"),
	Case("Rational","(((1:ℚ),1,0,0),(0,2,0,0),(0,0,1/2,0),(0,0,0,3))^n@((0:ℚ),1,1,1)"),
	Case("Real","(((1:ℝ),1,0,0),(0,2,0,0),(0,0,3,0),(0,0,0,4))^n@((0:ℝ),1,1,1)"),
	Case("Complex","((ⅈ,1,0,0),(0,-ⅈ,0,0),(0,0,2,0),(0,0,0,3))^n@(1,1,1,1)"),
	Case("TwoBlocks","(((1:ℝ),1,0,0),(0,2,0,0),(0,0,3,1),(0,0,0,4))^n@((0:ℝ),1,0,1)"),
	Case("Fibonacci","((0,1,0,0),(1,1,0,0),(0,0,2,0),(0,0,0,3))^n@(0,1,1,1)"),
	Case("LeadingSingleton","((2,0,0,0),(0,1,1,0),(0,0,2,0),(0,0,0,3))^n@(1,0,1,1)"),
	Case("Recurrence","μ(f:ℕ→ℤ). λ(n:ℕ). if n≤2 then n else f(n sub 2)-2*f(n sub 1)",true,false),
	Case("Coupled","((1,1,0,0),(0,2,1,0),(0,0,3,1),(1,0,0,4))^n@(0,1,1,1)",false,false),
	Case("UndefinedSeed","defined(((1,1,0,0),(0,2,0,0),(0,0,3,0),(0,0,0,4))^0@(0 sub 1,1,1,1))",false,false),
	Case("UndefinedMatrix","defined(((0 sub 1,1,0,0),(0,2,0,0),(0,0,3,0),(0,0,0,4))^0@(0,1,1,1))",false,false)
]; }
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/matrix-blocks"; mkdirRecurse(directory);
	foreach(c;cases()){
		auto owner=Session.open(); FunctionSyntax s; s.declare("n:ℕ");
		auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
		enforce(!r.exhausted,c.name~" exhausted");
		auto code=s.exportCertificate(owner.arena,r);
		enforce((code.indexOf("MatrixBlocks.split_value")>=0)==c.split,c.name~" split proof");
		if(c.closed) enforce(text.indexOf("@")<0,c.name~": "~text);
		auto again=s.run(owner.arena,text); enforce(!again.exhausted&&s.format(owner.arena,again)==text,c.name~" round trip: "~text);
		enforce(s.inspectType(owner.arena,text)==s.inspectType(owner.arena,c.source),c.name~" type changed");
		write(buildPath(directory,c.name~".lean"),code); writeln(c.name,": ",text);
	}
	writeln(cases().length," matrix-block cases");
	foreach(i,expected;["0","1","2","-3","8","-19"]){
		import std.conv:to;
		auto owner=Session.open(); FunctionSyntax s;
		auto source="("~cases()[8].source~")("~to!string(i)~")",r=s.run(owner.arena,source);
		enforce(!r.exhausted&&s.format(owner.arena,r)==s.format(owner.arena,s.run(owner.arena,"("~expected~":ℤ)")),source);
	}
	writeln("6 recurrence boundary values"); return 0;
}
