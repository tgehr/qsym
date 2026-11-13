module nilpotent_spectra_tests;
import qsym;
import std.exception:enforce;
import std.conv:to;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected,variables; bool nilpotent=true,closed=true; }
private Case[] cases(){
	Case[] r;
	foreach(i,t;["ℕ","ℤ","ℚ","ℝ","ℂ"]){
		auto matrix="(((0:"~t~"),1),(0,0))";
		r~=Case("Upper"~to!string(i),"λ(n:ℕ)."~matrix~"^n@(1,2)","λ(n:ℕ).(([n=0]+[n=1]*2:"~t~"),([n=0]*2:"~t~"))");
		r~=Case("Lower"~to!string(i),"λ(n:ℕ).(((0:"~t~"),0),(3,0))^n@(2,1)","λ(n:ℕ).(([n=0]*2:"~t~"),([n=0]+[n=1]*6:"~t~"))");
		r~=Case("Block"~to!string(i),"λ(n:ℕ).(((0:"~t~"),1,0),(0,0,0),(0,0,2))^n@(1,2,3)","");
	}
	r~=[
		Case("RationalNondiagonal","λ(n:ℕ).(((1:ℚ),1),(-1,-1))^n@(2,3)","λ(n:ℕ).(([n=0]*2+[n=1]*5:ℚ),([n=0]*3-[n=1]*5:ℚ))"),
		Case("IntegerNondiagonal","λ(n:ℕ).(((1:ℤ),1),(-1,-1))^n@(2,3)",""),
		Case("ComplexNondiagonal","λ(n:ℕ).((ⅈ,1),(1,-ⅈ))^n@(2,3)",""),
		Case("SymbolicSeeds","λ(n:ℕ).(((0:ℝ),1),(0,0))^n@(x,y)","λ(n:ℕ).([n=0]*x+[n=1]*y,[n=0]*y)","x:ℝ,y:ℝ"),
		Case("FreeExponent","(((0:ℚ),1),(0,0))^n@(1,2)","(([n=0]+[n=1]*2:ℚ),([n=0]*2:ℚ))","n:ℕ"),
		Case("DirectSum","λ(n:ℕ).((0,1,0,0),(0,0,0,0),(0,0,0,1),(0,0,0,0))^n@(1,2,3,4)",""),
		Case("Projection","λ(n:ℕ).get(((0,1),(0,0))^n@(1,2),0)","λ(n:ℕ).([n=0]+[n=1]*2:ℕ)"),
		Case("UndefinedExponent","defined((λ(n:ℕ).((0,1),(0,0))^n@(1,2))(0 sub 1))","false","",false),
		Case("UndefinedSeed","defined(((0,1),(0,0))^2@(1,0 sub 1))","false","",false),
		Case("UndefinedMatrix","defined(((0,0 sub 1),(0,0))^0@(1,2))","false","",false),
		Case("PartialExponent","λ(n:ℕ).(((0:ℝ),1),(0,0))^(n sub 1)@(1,2)","","",false,false),
		Case("NotNilpotent","λ(n:ℕ).(((0:ℝ),1),(1,0))^n@(1,2)","","",false),
		Case("HigherNilpotency","λ(n:ℕ).((0,1,0),(0,0,1),(0,0,0))^n@(1,2,3)","","",false,false),
		Case("UnknownMatrix","λ(n:ℕ).((r,1),(0,r))^n@(1,2)","","r:ℚ",false,false),
		Case("IntegerSymbolicSeeds","λ(n:ℕ).(((0:ℤ),1),(0,0))^n@(i,j)","","i:ℤ,j:ℤ",false,false)
	];
	return r;
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/nilpotent-spectra";mkdirRecurse(directory);
	foreach(c;cases()){
		auto owner=Session.open();FunctionSyntax s;if(c.variables.length) s.declare(c.variables);
		auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
		enforce(!r.exhausted,c.name~" exhausted");
		if(c.closed) enforce(text.indexOf("@")<0&&text.indexOf("μ(")<0&&text.indexOf("get(")<0,c.name~": "~text);
		if(c.expected.length){
			auto expected=s.format(owner.arena,s.run(owner.arena,c.expected));
			if(text!=expected) enforce(s.format(owner.arena,s.run(owner.arena,"("~text~")=("~expected~")"))=="true",c.name~": "~text~" expected "~expected);
		}
		if(c.closed){
			auto again=s.run(owner.arena,text),printed=s.format(owner.arena,again);enforce(!again.exhausted&&s.format(owner.arena,s.run(owner.arena,printed))==printed,c.name~" printed normalization");
			if(!r.scalarOnly&&!r.lowered){
				enforce(!again.scalarOnly&&!again.lowered&&r.bindings.type(r.reduction.output)==again.bindings.type(again.reduction.output),c.name~" changed type");
				auto next=r;next.reduction=r.bindings.normalize(r.reduction.output,4096,true);enforce(s.format(owner.arena,next)==text,c.name~" not normalized");
			}
		}
		auto proof=s.exportCertificate(owner.arena,r);enforce((proof.indexOf("NilpotentSpectra.two_value")>=0||proof.indexOf("NilpotentSpectra.block_value")>=0)==c.nilpotent,c.name~" proof path");
		enforce(s.format(owner.arena,s.run(owner.arena,c.source,[],Options(DensityMode.preserve,false)))==text,c.name~" tracing changed output");
		write(buildPath(directory,c.name~".lean"),proof);writeln(c.name,": ",text);
	}
	struct Numeric{ string source,sort; long a,b,c,d,x,y; }
	uint evaluations;
	foreach(c;[
		Numeric("λ(n:ℕ).((0,1),(0,0))^n@(1,2)","ℕ",0,1,0,0,1,2),
		Numeric("λ(n:ℕ).(((0:ℤ),0),(3,0))^n@(2,1)","ℤ",0,0,3,0,2,1),
		Numeric("λ(n:ℕ).(((1:ℚ),1),(-1,-1))^n@(2,3)","ℚ",1,1,-1,-1,2,3),
		Numeric("λ(n:ℕ).(((2:ℝ),4),(-1,-2))^n@(3,1)","ℝ",2,4,-1,-2,3,1),
		Numeric("λ(n:ℕ).(((1:ℂ),1),(-1,-1))^n@(2,3)","ℂ",1,1,-1,-1,2,3)
	]){
		auto owner=Session.open();FunctionSyntax s;auto text=s.format(owner.arena,s.run(owner.arena,c.source));
		auto x=c.x,y=c.y;
		foreach(n;0..7){
			auto r=s.run(owner.arena,"("~text~")("~to!string(n)~")");
			auto expected="(("~to!string(x)~":"~c.sort~"),("~to!string(y)~":"~c.sort~"))";
			enforce(!r.exhausted&&s.format(owner.arena,r)==s.format(owner.arena,s.run(owner.arena,expected)),"numeric "~c.sort~" n="~to!string(n));
			auto next=c.a*x+c.b*y;y=c.c*x+c.d*y;x=next;++evaluations;
		}
	}
	writeln(cases().length," nilpotent-spectra cases; ",evaluations," exact evaluations");return 0;
}
