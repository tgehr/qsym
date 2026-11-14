module product_recursion_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.conv:to;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:

private enum system = "μ(f:ℕ→ℕ×ℕ).λ(n:ℕ).if n=0 then (0,0) else (2*get(f(n sub 1),0)+get(f(n sub 1),1)+1,get(f(n sub 1),1)+1)";
private struct Case { string name,source,expected,variables; }
private Case[] cases(){ return [
 Case("System",system,""),
 Case("SystemUndefined","defined(("~system~")(0 sub 1))","false"),
 Case("ConditionalTrue","if true then (1,2) else (3,4)","(1,2)"),
 Case("ConditionalFalse","if false then (1,2) else (3,4)","(3,4)"),
 Case("InactivePartial","if true then (1,2) else (1/0,3)","((1,2):ℚ^2)"),
 Case("ActivePartial","defined(if true then (1,1/0) else (2,3))","false"),
 Case("StrictProjection","defined(get(if true then (1,1/0) else (2,3),0))","false"),
 Case("PartialCondition","defined(if 1/0>0 then (1,2) else (3,4))","false"),
 Case("Heterogeneous","if false then (1,true) else (2,false)","(2,false)"),
 Case("MixedNumeric","if true then (1,false) else (1/2,true)","((1:ℚ),false)"),
 Case("Nested","if true then ((1,2),false) else ((3,4),true)","((1,2),false)"),
 Case("FreeBranches","λ(p:𝔹).if p then x else y","","x:ℕ^2,y:ℕ^2"),
 Case("Constant","(μ(f:ℕ→ℕ×ℕ).λ(n:ℕ).(3,4))(5)","(3,4)"),
 Case("Identity","defined((μ(f:ℕ→ℕ×ℕ).λ(n:ℕ).f(n))(0))","false"),
 Case("DeadDivergence","(μ(f:ℕ→ℕ×ℕ).λ(n:ℕ).if n=0 then (1,2) else f(n+1))(0)","(1,2)"),
 Case("HeterogeneousRecursion","(μ(f:ℕ→ℕ×𝔹).λ(n:ℕ).if n=0 then (0,false) else (get(f(n sub 1),0)+1,¬get(f(n sub 1),1)))(3)","(3,true)"),
 Case("NestedRecursion","(μ(f:ℕ→(ℕ×ℕ)×𝔹).λ(n:ℕ).if n=0 then ((0,1),false) else ((get(get(f(n sub 1),0),0)+1,get(get(f(n sub 1),0),1)+2),¬get(f(n sub 1),1)))(2)","((2,5),false)"),
 Case("PartialSeed","defined((μ(f:ℕ→ℕ×ℕ).λ(n:ℕ).if n=0 then (0,0 sub 1) else f(n sub 1))(1))","false"),
 Case("OutOfBounds","defined((μ(f:ℕ→ℕ×ℕ).λ(n:ℕ).if n=0 then (1,2) else (get(f(n sub 1),2),0))(1))","false"),
 Case("Capture","(λ(x:ℕ).μ(f:ℕ→ℕ×ℕ).λ(n:ℕ).if n=0 then (x,0) else (get(f(n sub 1),0)+1,get(f(n sub 1),1)+1))(7)(2)","(9,2)")
]; }
int main(string[] args){
 auto directory=args.length>1?args[1]:"build/product-recursion"; mkdirRecurse(directory);
 uint certificates,evaluations;
 foreach(c;cases()){
  writeln(c.name);
  auto owner=Session.open(); FunctionSyntax s; if(c.variables.length) s.declare(c.variables);
  auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
  enforce(!r.exhausted,c.name~" exhausted: "~text);
  if(c.expected.length) enforce(text==s.format(owner.arena,s.run(owner.arena,c.expected)),c.name~": "~text);
  auto again=s.run(owner.arena,text); enforce(!again.exhausted&&s.format(owner.arena,again)==text,c.name~" round trip");
  auto proof=s.exportCertificate(owner.arena,r);
  if(c.name=="System") enforce(proof.indexOf("Recursion.Program")>=0,"missing product recursion proof");
  write(buildPath(directory,c.name~".lean"),proof); ++certificates;
 }
 ulong x,y;
 foreach(n;0..11){
  auto owner=Session.open(); FunctionSyntax s;
  auto source="("~system~")("~to!string(n)~")",expected="("~to!string(x)~","~to!string(y)~")";
  foreach(trace;[true,false]){
   auto r=s.run(owner.arena,source,[],Options(DensityMode.preserve,trace));
   enforce(!r.exhausted&&s.format(owner.arena,r)==expected,"system evaluation "~to!string(n)~": "~s.format(owner.arena,r)); ++evaluations;
   if(trace){ write(buildPath(directory,"System"~to!string(n)~".lean"),s.exportCertificate(owner.arena,r)); ++certificates; }
  }
  x=2*x+y+1; ++y;
 }
 auto owner=Session.open(); FunctionSyntax s;
 foreach(source;["if true then (1,2) else (3,4,5)","if true then (1,2) else (true,false)",
  "μ(f:ℕ→ℕ×ℕ).λ(n:ℕ).if defined(f(n)) then (0,0) else (1,1)"])
  assertThrown(s.run(owner.arena,source));
 writeln(certificates," product recursion certificates; ",evaluations," exact evaluations; 3 invalid programs rejected"); return 0;
}
