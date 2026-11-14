module indexed_recurrence_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:
private enum example="μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else 2*f(n sub 1)+n";
private struct Case {string name,source,vars; bool solved=true;}
private Case[] cases(){return [
 Case("User",example),
 Case("Scaled","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 3*f(n sub 1)+2*n+4"),
 Case("Right","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 2 else f(n sub 1)*2+n*3"),
 Case("Nested","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else 2*(f(n sub 1)+n)+1"),
 Case("Integer","μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then -3 else -2*f(n sub 1)+n-1"),
 Case("Rational","μ(f:ℕ→ℚ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+(3:ℚ)*n+1"),
 Case("Real","μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 0 else 2*f(n sub 1)+n"),
 Case("Complex","μ(f:ℕ→ℂ).λ(n:ℕ).if n=0 then 1 else ⅈ*f(n sub 1)+n"),
 Case("Parameters","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then a else c*f(n sub 1)+b*n+d","a:ℕ,b:ℕ,c:ℕ,d:ℕ"),
 Case("PartialSeed","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 sub 1 else 2*f(n sub 1)+n","",false),
 Case("WrongLag","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else 2*f(n sub 2)+n","",false),
 Case("NonlinearState","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else f(n sub 1)*f(n sub 1)+n","",false),
 Case("VariableCoefficient","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 1 else n*f(n sub 1)+n","",false),
 Case("QuadraticForcing","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else 2*f(n sub 1)+n*n"),
 Case("PartialForcing","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else 2*f(n sub 1)+(n sub 1)","",false)
];}
int main(string[] args){
 auto dir=args.length>1?args[1]:"build/indexed-recurrences";mkdirRecurse(dir);
 uint certificates,evaluations;
 foreach(c;cases()){
  auto owner=Session.open();FunctionSyntax s;if(c.vars.length)s.declare(c.vars);
  auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
  writeln(c.name,": ",text);
  enforce(!r.exhausted,c.name~" exhausted");enforce((text.indexOf("μ(")<0)==c.solved,c.name~" eligibility");
  auto again=s.run(owner.arena,text);enforce(!again.exhausted&&s.format(owner.arena,again)==text,c.name~" round trip");
  if(c.name=="User")enforce(text==s.format(owner.arena,s.run(owner.arena,"λ(n:ℕ).floorN(2*2^n-n-2)")),"user closed form");
  auto proof=s.exportCertificate(owner.arena,r);
  if(c.solved)enforce((proof.indexOf("IndexedRecurrence.solve_matrix")>=0||proof.indexOf("CFiniteRecurrence.solve_matrix")>=0),c.name~" solver proof");
  write(buildPath(dir,c.name~".lean"),proof);++certificates;
 }
 ulong expected;
 foreach(n;0..13){
  foreach(trace;[false,true]){
   auto owner=Session.open();FunctionSyntax s;
   auto r=s.run(owner.arena,"("~example~")("~to!string(n)~")",[],Options(DensityMode.preserve,trace));
   enforce(!r.exhausted&&s.format(owner.arena,r)==to!string(expected),"user value "~to!string(n));++evaluations;
   if(trace&&(n==0||n==1||n==12)){write(buildPath(dir,"User"~to!string(n)~".lean"),s.exportCertificate(owner.arena,r));++certificates;}
  }
  expected=2*expected+n+1;
 }
 // Evaluate the symbolic answer against an independent recurrence oracle.
 foreach(k;0..16){
  ulong a=k%4,b=(k/4)%3,c=(k+1)%3,x=k%3;
  auto source="μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then "~to!string(x)~" else "~to!string(a)~"*f(n sub 1)+"~to!string(b)~"*n+"~to!string(c);
  auto owner=Session.open();FunctionSyntax s;auto result=s.run(owner.arena,source),text=s.format(owner.arena,result);
  enforce(!result.exhausted&&text.indexOf("μ(")<0,"grid solution "~to!string(k));
  foreach(n;0..9){
   auto r=s.run(owner.arena,"("~text~")("~to!string(n)~")");
   enforce(!r.exhausted&&s.format(owner.arena,r)==to!string(x),"grid value "~to!string(k)~"/"~to!string(n));++evaluations;
   x=a*x+b*(n+1)+c;
  }
 }
 auto owner=Session.open();FunctionSyntax s;auto partial=s.run(owner.arena,"defined(("~example~")(0 sub 1))",[],Options(DensityMode.preserve,true));
 enforce(s.format(owner.arena,partial)=="false","partial index");write(buildPath(dir,"PartialIndex.lean"),s.exportCertificate(owner.arena,partial));++certificates;
 writeln(certificates," indexed recurrence certificates; ",evaluations," exact evaluations");return 0;
}
