module coupled_recurrence_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:
private enum system="μ(f:ℕ→ℕ^2).λ(n:ℕ).if n=0 then (0,0) else (2*get(f(n sub 1),0)+get(f(n sub 1),1)+1,get(f(n sub 1),1)+1)";
private struct Case {string name,source,vars; bool solved=true;}
private Case[] cases(){ return [
 Case("User",system),
 Case("Diagonal","μ(f:ℕ→ℕ^2).λ(n:ℕ).if n=0 then (1,2) else (2*get(f(n sub 1),0),3*get(f(n sub 1),1))"),
 Case("Swapped","μ(f:ℕ→ℕ^2).λ(n:ℕ).if n=0 then (1,2) else (get(f(n sub 1),1),get(f(n sub 1),0))"),
 Case("Singleton","μ(f:ℕ→ℕ^1).λ(n:ℕ).if n=0 then (1,) else (2*get(f(n sub 1),0)+1,)"),
 Case("Three","μ(f:ℕ→ℕ^3).λ(n:ℕ).if n=0 then (0,1,2) else (get(f(n sub 1),1)+1,get(f(n sub 1),2)+1,get(f(n sub 1),0)+1)"),
 Case("Integer","μ(f:ℕ→ℤ^2).λ(n:ℕ).if n=0 then ((0:ℤ),0) else (2*get(f(n sub 1),0)+get(f(n sub 1),1)-1,get(f(n sub 1),1)+1)"),
 Case("Rational","μ(f:ℕ→ℚ^2).λ(n:ℕ).if n=0 then ((0:ℚ),0) else (2*get(f(n sub 1),0)+get(f(n sub 1),1)+1/2,get(f(n sub 1),1)+1/2)"),
 Case("Real","μ(f:ℕ→ℝ^2).λ(n:ℕ).if n=0 then ((0:ℝ),0) else (2*get(f(n sub 1),0)+get(f(n sub 1),1)+1,get(f(n sub 1),1)+1)"),
 Case("Complex","μ(f:ℕ→ℂ^2).λ(n:ℕ).if n=0 then ((0:ℂ),0) else (2*get(f(n sub 1),0)+get(f(n sub 1),1)+1,get(f(n sub 1),1)+1)"),
 Case("Parameters","μ(f:ℕ→ℕ^2).λ(n:ℕ).if n=0 then (a,b) else (c*get(f(n sub 1),0)+get(f(n sub 1),1)+d,get(f(n sub 1),1)+1)","a:ℕ,b:ℕ,c:ℕ,d:ℕ"),
 Case("PartialSeed","μ(f:ℕ→ℕ^2).λ(n:ℕ).if n=0 then (0 sub 1,0) else (get(f(n sub 1),0)+1,get(f(n sub 1),1)+1)","",false),
 Case("Nonlinear","μ(f:ℕ→ℕ^2).λ(n:ℕ).if n=0 then (1,1) else (get(f(n sub 1),0)*get(f(n sub 1),1),get(f(n sub 1),1)+1)","",false),
 Case("WrongLag","μ(f:ℕ→ℕ^2).λ(n:ℕ).if n=0 then (0,0) else (get(f(n sub 2),0)+1,get(f(n sub 1),1)+1)","",false),
 Case("OutOfBounds","μ(f:ℕ→ℕ^2).λ(n:ℕ).if n=0 then (0,0) else (get(f(n sub 1),2)+1,get(f(n sub 1),1)+1)","",false)
];}
int main(string[] args){
 auto directory=args.length>1?args[1]:"build/coupled-recurrences";mkdirRecurse(directory);
 uint certificates,evaluations;
 foreach(c;cases()){
  auto owner=Session.open();FunctionSyntax s;if(c.vars.length)s.declare(c.vars);
  auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);writeln(c.name,": ",text);
  enforce(!r.exhausted,c.name~" exhausted");enforce((text.indexOf("μ(")<0)==c.solved,c.name~" solver eligibility");
  auto again=s.run(owner.arena,text);enforce(!again.exhausted&&s.format(owner.arena,again)==text,c.name~" round trip");
  if(c.name=="User"){
   auto expected=s.format(owner.arena,s.run(owner.arena,"λ(n:ℕ).(floorN(2*2^n-n-2),n)"));enforce(text==expected,"user closed form");
  }
  auto proof=s.exportCertificate(owner.arena,r);if(c.solved)enforce(proof.indexOf("CoupledRecurrence.solve_matrix")>=0,c.name~" missing solver proof");
  write(buildPath(directory,c.name~".lean"),proof);++certificates;
 }
 ulong x,y;
 foreach(n;0..13){
  foreach(trace;[false,true]){
   auto owner=Session.open();FunctionSyntax s;
   auto r=s.run(owner.arena,"("~system~")("~to!string(n)~")",[],Options(DensityMode.preserve,trace));
   enforce(!r.exhausted&&s.format(owner.arena,r)=="("~to!string(x)~","~to!string(y)~")","user evaluation "~to!string(n));++evaluations;
   if(trace){write(buildPath(directory,"User"~to!string(n)~".lean"),s.exportCertificate(owner.arena,r));++certificates;}
  }
  x=2*x+y+1;++y;
 }
 foreach(k;0..16){
  ulong a=k%4,b=k/4,c=(k+1)%3,d=(k/3)%3,u=k%2,v=(k+1)%2,x0=k%3,y0=(k+2)%3;
  auto source="μ(f:ℕ→ℕ^2).λ(n:ℕ).if n=0 then ("~to!string(x0)~","~to!string(y0)~") else ("~to!string(a)~"*get(f(n sub 1),0)+"~to!string(b)~"*get(f(n sub 1),1)+"~to!string(u)~","~to!string(c)~"*get(f(n sub 1),0)+"~to!string(d)~"*get(f(n sub 1),1)+"~to!string(v)~")";
  foreach(n;0..7){
   auto owner=Session.open();FunctionSyntax s;
   auto r=s.run(owner.arena,"("~source~")("~to!string(n)~")",[],Options(DensityMode.preserve,false));
   enforce(!r.exhausted&&s.format(owner.arena,r)=="("~to!string(x0)~","~to!string(y0)~")","matrix oracle "~to!string(k)~"/"~to!string(n));++evaluations;
   auto next=a*x0+b*y0+u;y0=c*x0+d*y0+v;x0=next;
  }
 }
 // Exercise the Jordan formula independently of recurrence recognition,
 // including nonunit, negative, zero and complex eigenvalues.
 foreach(k, source;[
  "λ(n:ℕ).((3,2,1),(0,2,4),(0,0,2))^n@(1,2,3)",
  "λ(n:ℕ).(((2:ℤ),-1,3),(0,-1,2),(0,0,-1))^n@(-2,1,3)",
  "λ(n:ℕ).(((1/3:ℚ),2,1),(0,1/2,1),(0,0,1/2))^n@(1,2,3)",
  "λ(n:ℕ).(((0:ℝ),1,2),(0,1,3),(0,0,1))^n@(1,2,3)",
  "λ(n:ℕ).((2*ⅈ,1,2),(0,ⅈ,3),(0,0,ⅈ))^n@(1,2,3)"
 ]){
  auto owner=Session.open();FunctionSyntax s;auto r=s.run(owner.arena,source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
  enforce(!r.exhausted&&text.indexOf("@")<0,"Jordan formula "~to!string(k)~": "~text);
  auto proof=s.exportCertificate(owner.arena,r);enforce(proof.indexOf("JordanSpectra.three_value")>=0,"Jordan proof");
  write(buildPath(directory,"Jordan"~to!string(k)~".lean"),proof);++certificates;
  foreach(n;0..7){
   auto argument="("~to!string(n)~")";
   auto original=s.run(owner.arena,"("~source~")"~argument),solved=s.run(owner.arena,"("~text~")"~argument);
   enforce(!original.exhausted&&!solved.exhausted&&s.format(owner.arena,original)==s.format(owner.arena,solved),"Jordan evaluation "~to!string(k)~"/"~to!string(n));evaluations+=2;
  }
 }
 auto owner=Session.open();FunctionSyntax s;
 auto partial=s.run(owner.arena,"defined(("~system~")(0 sub 1))",[],Options(DensityMode.preserve,true));enforce(s.format(owner.arena,partial)=="false","partial index");
 write(buildPath(directory,"PartialIndex.lean"),s.exportCertificate(owner.arena,partial));++certificates;
 writeln(certificates," coupled recurrence certificates; ",evaluations," exact evaluations");return 0;
}
