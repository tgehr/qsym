module integer_spectra_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected,variables; bool lifted; }
private Case[] cases(){ return [
	Case("NaturalFibonacci","λ(n:ℕ).((0,1),(1,1))^n@(0,1)","","",true),
	Case("IntegerFibonacci","λ(n:ℕ).(((0:ℤ),1),(1,1))^n@(0,1)","","",true),
	Case("NaturalTriangular","λ(n:ℕ).((2,1),(0,3))^n@(1,2)","","",true),
	Case("IntegerTriangular","λ(n:ℕ).(((-2:ℤ),1),(0,3))^n@(-1,2)","","",true),
	Case("IntegerRotation","λ(n:ℕ).(((0:ℤ),-1),(1,0))^n@(1,0)","","",true),
	Case("NaturalBlock","λ(n:ℕ).((0,1,0),(1,1,0),(0,0,3))^n@(0,1,2)","","",true),
	Case("IntegerBlock","λ(n:ℕ).(((0:ℤ),-1,0),(1,0,0),(0,0,-2))^n@(1,0,3)","","",true),
	Case("NaturalRecurrence","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)","","",true),
	Case("IntegerRecurrence","μ(f:ℕ→ℤ).λ(n:ℕ).if n<2 then n else f(n sub 1)+f(n sub 2)","","",true),
	Case("FreeExponent","((0,1),(1,1))^n@(0,1)","","n:ℕ",true),
	Case("ZeroEigenvalue","λ(n:ℕ).((0,1),(0,2))^n@(3,4)","","",true),
	Case("NaturalZero","((0,1),(1,1))^0@(0,1)","(0,1)"),
	Case("NaturalOne","((0,1),(1,1))^1@(0,1)","(1,1)"),
	Case("NaturalTen","((0,1),(1,1))^10@(0,1)","(55,89)"),
	Case("IntegerRotationFive","(((0:ℤ),-1),(1,0))^5@(1,0)","((0:ℤ),(1:ℤ))"),
	Case("NaturalRecurrenceTen","(μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2))(10)","55"),
	Case("UndefinedExponent","defined((λ(n:ℕ).((0,1),(1,1))^n@(0,1))(0 sub 1))","false"),
	Case("NaturalFloorZero","floorN(0)","0"),
	Case("NaturalFloorPositive","floorN(7/2)","3"),
	Case("NaturalFloorNegative","floorN(-7/2)","0"),
	Case("NaturalFloorCast","floorN(toℝ(n))","n","n:ℕ"),
	Case("NaturalFloorPartial","defined(floorN(1/0))","false")
]; }
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/integer-spectra"; mkdirRecurse(directory);
	foreach(c;cases()){
		writeln(c.name);
		auto owner=Session.open(); FunctionSyntax s; if(c.variables.length) s.declare(c.variables);
		auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
		enforce(!r.exhausted,c.name~" exhausted");
		if(c.expected.length){ auto expected=s.format(owner.arena,s.run(owner.arena,c.expected)); enforce(text==expected,c.name~": "~text~" expected "~expected); }
		if(c.lifted) enforce(text.indexOf("@")<0&&text.indexOf("μ(")<0&&text.indexOf("get(")<0,c.name~": "~text);
		auto again=s.run(owner.arena,text),printed=s.format(owner.arena,again);
		enforce(text==printed,c.name~" round trip: "~text~" -> "~printed);
		if(!r.scalarOnly&&!r.lowered){
			enforce(!again.scalarOnly&&!again.lowered&&r.bindings.type(r.reduction.output)==again.bindings.type(again.reduction.output),c.name~" round-trip type");
			auto next=r; next.reduction=r.bindings.normalize(r.reduction.output,4096,true); enforce(s.format(owner.arena,next)==text,c.name~" not normalized");
		}
		auto proof=s.exportCertificate(owner.arena,r);
		if(c.lifted) enforce(proof.indexOf("IntegerSpectra.lift")>=0&&proof.indexOf("Spectral.")>=0,c.name~" missing spectral proof");
		enforce(s.format(owner.arena,s.run(owner.arena,c.source,[],Options(DensityMode.preserve,false)))==text,c.name~" tracing changed output");
		write(buildPath(directory,c.name~".lean"),proof);
		writeln(text);
	}
	foreach(source;[
		"defined(((0,1),(1,1))^0@(0 sub 1,1))",
		"defined(((0 sub 1,1),(1,1))^0@(0,1))",
		"λ(n:ℕ).((0,1),(1,1))^(n sub 1)@(0,1)",
		"λ(n:ℕ).((0,1),(1,1))^n@(a,b)",
		"λ(n:ℕ).(((0:ℤ),-1),(1,0))^n@(i,j)",
		"λ(n:ℕ).((1,1),(0,1))^n@(1,1)",
		"λ(n:ℕ).((0,1,1),(1,1,0),(0,0,1))^n@(0,1,1)",
		"λ(n:ℕ).((0,1,0,0),(1,1,0,0),(0,0,1,1),(0,0,0,1))^n@(0,1,0,1)"]){
		auto owner=Session.open(); FunctionSyntax s; s.declare("a:ℕ,b:ℕ,i:ℤ,j:ℤ"); auto r=s.run(owner.arena,source);
		enforce(!r.exhausted&&s.exportCertificate(owner.arena,r).indexOf("IntegerSpectra.lift")<0,"unsupported spectrum replaced: "~source);
	}
	writeln(cases().length," integer spectral certificates; 8 unsupported cases retained"); return 0;
}
