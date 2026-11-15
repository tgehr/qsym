module mixed_recurrence_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:
private struct Case {string name,step,seed="n",vars;uint toll=1;bool solved=true,numeric=true,inclusive=false;}
private ulong charge(uint kind,uint n){switch(kind){case 0:return 1;case 1:return n;case 2:return cast(ulong)n*n;case 3:uint v;while(n>=2){n/=2;++v;}return v;default:assert(0);}}
int main(string[] args){
 auto dir=args.length>1?args[1]:"build/mixed-recurrences";mkdirRecurse(dir);uint certificates,evaluations;
 foreach(c;[
 Case("Linear","f(divN(n,2))+f(divN(n+1,2))+n"),
 Case("Unit","f(divN(n,2))+f(divN(n+1,2))+1","1","",0),
 Case("Quadratic","f(divN(n,2))+f(divN(n+1,2))+n*n","n","",2),
 Case("Logarithmic","f(divN(n,2))+f(divN(n+1,2))+logN(2,n)","n","",3),
 Case("DistinctSeeds","f(divN(n,2))+f(divN(n+1,2))+n","n+7"),
 Case("ReorderedInclusive","n+f(divN(n+1,2))+f(divN(n,2))","n","",1,true,true,true),
 Case("Symbolic","f(divN(n,2))+f(divN(n+1,2))+a*n+b","c","a:ℕ,b:ℕ,c:ℕ",1,true,false),
 Case("MissingFloor","f(divN(n+1,2))+n","n","",1,false,false),
 Case("ExtraFloor","f(divN(n,2))+f(divN(n,2))+f(divN(n+1,2))+n","n","",1,false,false),
 Case("OtherSplit","f(divN(n,2))+f(divN(n+1,3))+n","n","",1,false,false),
 Case("Nonlinear","f(divN(n,2))*f(divN(n+1,2))+n","n","",1,false,false),
 Case("PartialToll","f(divN(n,2))+f(divN(n+1,2))+divN(n,0)","n","",1,false,false)
 ]){
  auto owner=Session.open();FunctionSyntax s;if(c.vars.length)s.declare(c.vars);
  auto source="μ(f:ℕ→ℕ).λ(n:ℕ).if n"~(c.inclusive?"≤1":"<2")~" then "~c.seed~" else "~c.step;
  auto r=s.run(owner.arena,source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
  writeln(c.name,": ",text);enforce(!r.exhausted,c.name~" exhausted");enforce((text.indexOf("μ(")<0)==c.solved,c.name~" eligibility");
  auto again=s.run(owner.arena,text);enforce(!again.exhausted&&s.format(owner.arena,again)==text,c.name~" round trip: "~s.format(owner.arena,again));
  auto proof=s.exportCertificate(owner.arena,r);if(c.solved)enforce(proof.indexOf("MixedDivide.solve_sum")>=0,c.name~" proof");write(buildPath(dir,c.name~".lean"),proof);++certificates;
  if(!c.numeric)continue;
  ulong[1026] want;want[0]=c.seed=="1"?1:c.seed=="n+7"?7:0;want[1]=c.seed=="n+7"?8:1;
  foreach(n;2..want.length)want[n]=want[n/2]+want[(n+1)/2]+charge(c.toll,cast(uint)n);
  uint[] samples;foreach(n;0..17)samples~=n; samples~=[31u,32u,33u,63u,64u,65u,127u,128u,129u,255u,256u,257u,1023u,1024u,1025u];
  foreach(n;samples)foreach(trace;[false,true]){
   auto value=s.run(owner.arena,"("~text~")("~to!string(n)~")",[],Options(DensityMode.preserve,trace));
   enforce(!value.exhausted&&s.format(owner.arena,value)==to!string(want[n]),c.name~" at "~to!string(n)~": "~s.format(owner.arena,value));++evaluations;
  }
 }
 writeln(certificates," mixed-split certificates; ",evaluations," exact evaluations");return 0;
}
