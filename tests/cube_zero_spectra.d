module cube_zero_spectra_tests;
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
		r~=Case("Upper"~to!string(i),"λ(n:ℕ).(((0:"~t~"),1,0),(0,0,1),(0,0,0))^n@(1,2,3)",i==4?"":"λ(n:ℕ).(([n=0]+[n=1]*2+[n=2]*3:"~t~"),([n=0]*2+[n=1]*3:"~t~"),([n=0]*3:"~t~"))");
		r~=Case("Lower"~to!string(i),"λ(n:ℕ).(((0:"~t~"),0,0),(2,0,0),(1,3,0))^n@(1,2,3)","");
		r~=Case("Symbolic"~to!string(i),"λ(n:ℕ).(((0:"~t~"),1,0),(0,0,1),(0,0,0))^n@(x,y,z)",i<3?"λ(n:ℕ).([n=0]*x+[n=1]*y+[n=2]*z,[n=0]*y+[n=1]*z,[n=0]*z)":"","x:"~t~",y:"~t~",z:"~t,i<3,i<3);
	}
	foreach(i,t;["ℤ","ℚ","ℝ","ℂ"])
		r~=Case("Dense"~to!string(i),"λ(n:ℕ).(((0:"~t~"),2,0),(-1,1,1),(1,1,-1))^n@(1,2,3)","");
	r~=[
		Case("ComplexEntries","λ(n:ℕ).(((0:ℂ),ⅈ,2),(0,0,1+ⅈ),(0,0,0))^n@(1,2,3)","","",false,false),
		Case("RationalEntries","λ(n:ℕ).(((0:ℚ),1/2,0),(0,0,1/3),(0,0,0))^n@(1,2,3)",""),
		Case("FreeExponent","((0,1,0),(0,0,1),(0,0,0))^n@(1,2,3)","","n:ℕ"),
		Case("DirectSum","λ(n:ℕ).((0,1,0,0),(0,0,1,0),(0,0,0,0),(0,0,0,2))^n@(1,2,3,4)",""),
		Case("Projection","λ(n:ℕ).get(((0,1,0),(0,0,1),(0,0,0))^n@(1,2,3),0)","λ(n:ℕ).([n=0]+[n=1]*2+[n=2]*3:ℕ)"),
		Case("SquareZeroDense","λ(n:ℕ).(((1:ℤ),1,1),(-1,-1,-1),(0,0,0))^n@(1,2,3)",""),
		Case("ZeroSeed","λ(n:ℕ).((0,1,0),(0,0,1),(0,0,0))^n@(0,0,0)","λ(n:ℕ).(0,0,0)"),
		Case("UndefinedExponent","defined((λ(n:ℕ).((0,1,0),(0,0,1),(0,0,0))^n@(1,2,3))(0 sub 1))","false","",false),
		Case("UndefinedSeed","defined(((0,1,0),(0,0,1),(0,0,0))^3@(1,2,0 sub 1))","false","",false),
		Case("UndefinedMatrix","defined(((0,1,0 sub 1),(0,0,1),(0,0,0))^0@(1,2,3))","false","",false),
		Case("PartialExponent","λ(n:ℕ).((0,1,0),(0,0,1),(0,0,0))^(n sub 1)@(1,2,3)","","",false,false),
		Case("NonzeroCube","λ(n:ℕ).((0,1,0),(0,0,1),(1,0,0))^n@(1,2,3)","","",false,false),
		Case("SymbolicMatrix","λ(n:ℕ).((0,x,0),(0,0,1),(0,0,0))^n@(1,2,3)","","x:ℝ",false,false),
		Case("FourChain","λ(n:ℕ).((0,1,0,0),(0,0,1,0),(0,0,0,1),(0,0,0,0))^n@(1,2,3,4)","","",false,false)
	];
	return r;
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/cube-zero-spectra";mkdirRecurse(directory);
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
			// Commutative complex sums can reorder after parsing; check type and values, not text order.
			auto again=s.run(owner.arena,text);enforce(!again.exhausted,c.name~" parsed normalization");
			if(!r.scalarOnly&&!r.lowered){
				enforce(!again.scalarOnly&&!again.lowered&&r.bindings.type(r.reduction.output)==again.bindings.type(again.reduction.output),c.name~" changed type");
				auto next=r;next.reduction=r.bindings.normalize(r.reduction.output,4096,true);enforce(s.format(owner.arena,next)==text,c.name~" not normalized");
			}
		}
		auto proof=s.exportCertificate(owner.arena,r);enforce((proof.indexOf("CubeZeroSpectra.three_compact_value")>=0)==c.nilpotent,c.name~" proof path");
		enforce(s.format(owner.arena,s.run(owner.arena,c.source,[],Options(DensityMode.preserve,false)))==text,c.name~" tracing changed output");
		write(buildPath(directory,c.name~".lean"),proof);writeln(c.name,": ",text);
	}
	uint evaluations;
	foreach(t;["ℕ","ℤ","ℚ","ℝ","ℂ"]){
		foreach(dense;0..(t=="ℕ"?1:2)){
			auto source=dense?"λ(n:ℕ).(((0:"~t~"),2,0),(-1,1,1),(1,1,-1))^n@(1,2,3)":"λ(n:ℕ).(((0:"~t~"),1,0),(0,0,1),(0,0,0))^n@(1,2,3)";
			auto owner=Session.open();FunctionSyntax s;auto text=s.format(owner.arena,s.run(owner.arena,source));
			long[3] v=[1,2,3];long[9] m=dense?[0L,2,0,-1,1,1,1,1,-1]:[0L,1,0,0,0,1,0,0,0];
			foreach(n;0..7){
				auto result=s.run(owner.arena,"("~text~")("~to!string(n)~")");
				auto expected="(("~to!string(v[0])~":"~t~"),("~to!string(v[1])~":"~t~"),("~to!string(v[2])~":"~t~"))";
				enforce(!result.exhausted&&s.format(owner.arena,result)==s.format(owner.arena,s.run(owner.arena,expected)),"numeric "~t~" n="~to!string(n));
				long[3] next; foreach(i;0..3) foreach(j;0..3) next[i]+=m[i*3+j]*v[j];v=next;++evaluations;
			}
		}
	}
	writeln(cases().length," cube-zero-spectra cases; ",evaluations," exact evaluations");return 0;
}
