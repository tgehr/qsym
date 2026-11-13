module repeated_spectra_tests;
import qsym;
import std.exception:enforce;
import std.conv:to;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected,variables; bool repeated=true,closed=true; }
private Case[] cases(){ return [
	Case("RealUnit","λ(n:ℕ).(((1:ℝ),1),(0,1))^n@(1,1)","λ(n:ℕ).((n+1:ℝ),(1:ℝ))"),
	Case("NaturalUnit","λ(n:ℕ).((1,1),(0,1))^n@(1,1)","λ(n:ℕ).(n+1,1)"),
	Case("IntegerUnit","λ(n:ℕ).(((1:ℤ),1),(0,1))^n@(1,1)","λ(n:ℕ).((n+1:ℤ),(1:ℤ))"),
	Case("RationalTwo","λ(n:ℕ).(((2:ℚ),3),(0,2))^n@(1,2)","λ(n:ℕ).(((3*n+1)*2^n:ℚ),(2*2^n:ℚ))"),
	Case("RationalHalf","λ(n:ℕ).(((1/2:ℚ),1),(0,1/2))^n@(1,2)",""),
	Case("RealNondiagonal","λ(n:ℕ).(((3:ℝ),1),(-1,1))^n@(1,2)",""),
	Case("IntegerNondiagonal","λ(n:ℕ).(((2:ℤ),1),(-1,0))^n@(1,2)","λ(n:ℕ).((3*n+1:ℤ),-3*n+2)"),
	Case("ComplexImaginary","λ(n:ℕ).((ⅈ,1),(0,ⅈ))^n@(1,2)",""),
	Case("ComplexNondiagonal","λ(n:ℕ).((ⅈ+1,1),(-1,ⅈ-1))^n@(1,2)",""),
	Case("IntegerNegative","λ(n:ℕ).(((-1:ℤ),1),(0,-1))^n@(1,2)",""),
	Case("NaturalBlock","λ(n:ℕ).((2,1,0),(0,2,0),(0,0,3))^n@(1,2,3)",""),
	Case("RationalBlock","λ(n:ℕ).(((2:ℚ),1,0),(0,2,0),(0,0,3))^n@(1,2,3)",""),
	Case("ComplexBlock","λ(n:ℕ).((ⅈ,1,0),(0,ⅈ,0),(0,0,2))^n@(1,2,3)",""),
	Case("NaturalDirectSum","λ(n:ℕ).((1,1,0,0),(0,1,0,0),(0,0,2,1),(0,0,0,2))^n@(1,1,1,2)",""),
	Case("SymbolicSeeds","λ(n:ℕ).(((1:ℝ),1),(0,1))^n@(x,y)","λ(n:ℕ).(x+n*y,y)","x:ℝ,y:ℝ"),
	Case("FreeExponent","(((2:ℚ),3),(0,2))^n@(1,2)","(((3*n+1)*2^n:ℚ),(2*2^n:ℚ))","n:ℕ"),
	Case("IntegerRecurrence","μ(f:ℕ→ℤ).λ(n:ℕ).if n<2 then n else 2*f(n sub 1)-f(n sub 2)","λ(n:ℕ).(n:ℤ)"),
	Case("RealRecurrence","μ(f:ℕ→ℝ).λ(n:ℕ).if n<2 then n else 4*f(n sub 1)-4*f(n sub 2)","λ(n:ℕ).(n*2^n/2:ℝ)"),
	Case("ComplexRecurrence","μ(f:ℕ→ℂ).λ(n:ℕ).if n<2 then n else 2*ⅈ*f(n sub 1)+f(n sub 2)",""),
	Case("NaturalProjection","λ(n:ℕ).get(((1,1),(0,1))^n@(1,1),0)","λ(n:ℕ).n+1"),
	Case("ZeroExponent","((1,1),(0,1))^0@(1,1)","(1,1)","",false),
	Case("UndefinedExponent","defined((λ(n:ℕ).((1,1),(0,1))^n@(1,1))(0 sub 1))","false","",false),
	Case("UndefinedSeed","defined(((1,1),(0,1))^0@(1,0 sub 1))","","",false,false),
	Case("UndefinedMatrix","defined(((1,0 sub 1),(0,1))^0@(1,1))","","",false,false),
	Case("Nilpotent","λ(n:ℕ).(((0:ℝ),1),(0,0))^n@(1,2)","","",false,false),
	Case("PartialExponent","λ(n:ℕ).(((1:ℝ),1),(0,1))^(n sub 1)@(1,2)","","",false,false),
	Case("UnknownEigenvalue","λ(n:ℕ).((r,1),(0,r))^n@(1,2)","","r:ℚ",false,false),
	Case("IntegerSymbolicSeeds","λ(n:ℕ).(((1:ℤ),1),(0,1))^n@(i,j)","","i:ℤ,j:ℤ",false,false)
]; }
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/repeated-spectra";mkdirRecurse(directory);
	foreach(c;cases()){
		auto owner=Session.open();FunctionSyntax s;if(c.variables.length) s.declare(c.variables);
		auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
		enforce(!r.exhausted,c.name~" exhausted");
		if(c.name=="UndefinedSeed"||c.name=="UndefinedMatrix") enforce(text!="true",c.name~" lost partiality");
		if(c.closed) enforce(text.indexOf("@")<0&&text.indexOf("μ(")<0&&text.indexOf("get(")<0,c.name~": "~text);
		if(c.expected.length) enforce(text==s.format(owner.arena,s.run(owner.arena,c.expected)),c.name~": "~text);
		if(c.closed){
			auto again=s.run(owner.arena,text),printed=s.format(owner.arena,again);enforce(!again.exhausted&&s.format(owner.arena,s.run(owner.arena,printed))==printed,c.name~" printed normalization");
			if(!r.scalarOnly&&!r.lowered){
				enforce(!again.scalarOnly&&!again.lowered&&r.bindings.type(r.reduction.output)==again.bindings.type(again.reduction.output),c.name~" changed type");
				auto next=r;next.reduction=r.bindings.normalize(r.reduction.output,4096,true);enforce(s.format(owner.arena,next)==text,c.name~" not normalized");
			}
		}
		auto proof=s.exportCertificate(owner.arena,r);enforce((proof.indexOf("RepeatedSpectra.two_value")>=0||proof.indexOf("RepeatedSpectra.block_value")>=0)==c.repeated,c.name~" proof path");
		enforce(s.format(owner.arena,s.run(owner.arena,c.source,[],Options(DensityMode.preserve,false)))==text,c.name~" tracing changed output");
		write(buildPath(directory,c.name~".lean"),proof);writeln(c.name,": ",text);
	}
	struct Numeric{ string source,sort; long a,b,c,d,x,y; }
	foreach(c;[
		Numeric("λ(n:ℕ).((1,1),(0,1))^n@(1,1)","ℕ",1,1,0,1,1,1),
		Numeric("λ(n:ℕ).(((2:ℚ),3),(0,2))^n@(1,2)","ℚ",2,3,0,2,1,2),
		Numeric("λ(n:ℕ).(((3:ℝ),1),(-1,1))^n@(1,2)","ℝ",3,1,-1,1,1,2),
		Numeric("λ(n:ℕ).(((-1:ℤ),1),(0,-1))^n@(1,2)","ℤ",-1,1,0,-1,1,2)
	]){
		auto owner=Session.open();FunctionSyntax s;auto text=s.format(owner.arena,s.run(owner.arena,c.source));
		auto x=c.x,y=c.y;
		foreach(n;0..6){
			auto r=s.run(owner.arena,"("~text~")("~to!string(n)~")");
			auto expected="(("~to!string(x)~":"~c.sort~"),("~to!string(y)~":"~c.sort~"))";
			enforce(!r.exhausted&&s.format(owner.arena,r)==s.format(owner.arena,s.run(owner.arena,expected)),"numeric "~c.sort~" n="~to!string(n));
			auto next=c.a*x+c.b*y;y=c.c*x+c.d*y;x=next;
		}
	}
	writeln(cases().length," repeated-spectra cases; 24 exact evaluations");return 0;
}
