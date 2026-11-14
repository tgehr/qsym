module zero_root_spectra_tests;
import qsym;
import std.exception:enforce;
import std.conv:to;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:
private struct Case{ string name,source,expected,variables; bool closed=true,root=true; }
private Case[] cases(){
 Case[] r;
 foreach(i,t;["ℕ","ℤ","ℝ","ℂ"]){
  r~=Case("Delayed"~to!string(i),"μ(f:ℕ→"~t~").λ(n:ℕ).if n≤2 then n else f(n sub 1)+f(n sub 2)","","",i!=3,i!=3);
  r~=Case("Matrix"~to!string(i),"λ(n:ℕ).(((0:"~t~"),1,0),(0,0,1),(0,1,1))^n@(0,1,2)","","",i!=3,i!=3);
 }
 foreach(i,t;["ℕ","ℤ","ℚ","ℝ","ℂ"])
  r~=Case("RationalRoots"~to!string(i),"λ(n:ℕ).(((0:"~t~"),1,1),(0,1,0),(0,0,2))^n@(3,4,5)");
 foreach(i,t;["ℤ","ℚ","ℝ","ℂ"])
  r~=Case("Dense"~to!string(i),"λ(n:ℕ).(((1:"~t~"),0,-1),(-1,2,1),(0,0,0))^n@(3,4,5)");
 r~=[
  Case("ComplexRoots","λ(n:ℕ).(((0:ℤ),1,0),(0,0,-1),(0,1,0))^n@(1,2,3)","","",false,false),
  Case("AlternateBase","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 7 else if n=1 then 1 else if n=2 then 2 else f(n sub 1)+f(n sub 2)"),
  Case("ZeroSeed","λ(n:ℕ).((0,1,0),(0,0,1),(0,1,1))^n@(0,0,0)"),
  Case("FreeExponent","((0,1,0),(0,0,1),(0,1,1))^n@(0,1,2)","","n:ℕ"),
  Case("DirectSum","λ(n:ℕ).((0,1,0,0),(0,0,1,0),(0,1,1,0),(0,0,0,2))^n@(0,1,2,3)"),
  Case("Fibonacci","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)","","",true,false),
  Case("UndefinedExponent","defined((λ(n:ℕ).((0,1,0),(0,0,1),(0,1,1))^n@(0,1,2))(0 sub 1))","false","",true,false),
  Case("UndefinedSeed","defined(((0,1,0),(0,0,1),(0,1,1))^0@(0 sub 1,1,2))","false","",true,false),
  Case("UndefinedMatrix","defined(((0,1,0 sub 1),(0,0,1),(0,1,1))^0@(0,1,2))","false","",true,false),
  Case("NonzeroDeterminant","λ(n:ℕ).((0,1,0),(0,0,1),(1,1,1))^n@(0,1,2)","","",false,false),
  Case("RepeatedRoot","λ(n:ℕ).((0,1,0),(0,1,1),(0,0,1))^n@(0,1,2)","","",false,false),
  Case("SymbolicSeed","λ(n:ℕ).((0,1,0),(0,0,1),(0,1,1))^n@(x,1,2)","","x:ℕ",false,false),
  Case("PartialExponent","λ(n:ℕ).((0,1,0),(0,0,1),(0,1,1))^(n sub 1)@(0,1,2)","","",false,false)
 ];
 return r;
}
int main(string[] args){
 auto directory=args.length>1?args[1]:"build/zero-root-spectra"; mkdirRecurse(directory);
 uint failures;
 foreach(c;cases()){
  writeln(c.name);
  try{
  auto owner=Session.open(); FunctionSyntax s; if(c.variables.length) s.declare(c.variables);
  auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
  enforce(!r.exhausted,c.name~" exhausted: "~text);
  if(c.expected.length) enforce(text==s.format(owner.arena,s.run(owner.arena,c.expected)),c.name~": "~text);
  if(c.closed) enforce(text.indexOf("@")<0&&text.indexOf("μ(")<0&&text.indexOf("get(")<0,c.name~" not scalar: "~text);
  auto proof=s.exportCertificate(owner.arena,r);
  enforce((proof.indexOf("ZeroRootSpectra.three_value")>=0)==c.root,c.name~" wrong rule path");
  auto roundOwner=Session.open(); FunctionSyntax round; if(c.variables.length) round.declare(c.variables);
  auto again=round.run(roundOwner.arena,text);
  enforce(!again.exhausted,c.name~" round trip exhausted");
  auto plainOwner=Session.open(); FunctionSyntax plain; if(c.variables.length) plain.declare(c.variables);
  auto plainResult=plain.run(plainOwner.arena,c.source,[],Options(DensityMode.preserve,false));
  enforce(!plainResult.exhausted,c.name~" untraced exhausted");
  auto untraced=plain.format(plainOwner.arena,plainResult);
  enforce(untraced==text,c.name~" trace disagreement: "~text~" vs "~untraced);
  write(buildPath(directory,c.name~".lean"),proof); writeln(text);
  }catch(Exception e){ ++failures; writeln("FAIL ",c.name,": ",e.msg); }
 }
 uint evaluations;
 foreach(base;[0,7]){
  auto owner=Session.open(); FunctionSyntax s;
  auto source=base==0?"μ(f:ℕ→ℕ).λ(n:ℕ).if n≤2 then n else f(n sub 1)+f(n sub 2)":"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 7 else if n=1 then 1 else if n=2 then 2 else f(n sub 1)+f(n sub 2)";
  auto result=s.format(owner.arena,s.run(owner.arena,source));
  foreach(i,expected;[base,1,2,3,5,8,13,21,34,55,89]){
   auto x=s.run(owner.arena,"("~result~")("~to!string(i)~")");
   enforce(!x.exhausted&&s.format(owner.arena,x)==to!string(expected),"delayed evaluation "~to!string(i)~": "~s.format(owner.arena,x)); ++evaluations;
  }
 }
 writeln(cases().length," zero-root cases; ",evaluations," exact evaluations; ",failures," failures"); enforce(!failures,"zero-root failures"); return 0;
}
