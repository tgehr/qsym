module divide_recurrence_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:
private struct Case{string name,source,vars;uint radix=2,coefficient=2;int toll=1;uint seed=0;bool seedIndex=true,solved=true,numeric=true;}
private string recurrence(string step,string base="n",uint radix=2,bool inclusive=false){return "μ(f:ℕ→ℕ).λ(n:ℕ).if n"~(inclusive?"≤"~to!string(radix-1):"<"~to!string(radix))~" then "~base~" else "~step;}
private Case[] cases(){return [
 Case("LinearToll",recurrence("2*f(divN(n,2))+n")),
 Case("Inclusive",recurrence("2*f(divN(n,2))+n","n",2,true)),
 Case("BinarySearch",recurrence("f(divN(n,2))+1","1"),"",2,1,0,1,false),
 Case("Ternary",recurrence("3*f(divN(n,3))+n","n",3),"",3,3),
 Case("QuadraticToll",recurrence("2*f(divN(n,2))+n*n"),"",2,2,2),
 Case("TwoCalls",recurrence("f(divN(n,2))+f(divN(n,2))+n")),
 Case("RightCoefficient",recurrence("f(divN(n,2))*3+n"),"",2,3),
 Case("ZeroCoefficient",recurrence("0*f(divN(n,2))+n"),"",2,0),
 Case("Homogeneous",recurrence("2*f(divN(n,2))"),"",2,2,3),
 Case("QuotientToll",recurrence("2*f(divN(n,2))+divN(n,3)"),"",2,2,4),
 Case("LogarithmicToll",recurrence("2*f(divN(n,2))+logN(2,n)"),"",2,2,5),
 Case("Symbolic",recurrence("a*f(divN(n,2))+c*n","d"),"a:ℕ,c:ℕ,d:ℕ",2,2,1,0,false,true,false),
 Case("MissingBase",recurrence("2*f(divN(n,3))+n"),"",2,2,1,0,true,false,false),
 Case("Nonshrinking",recurrence("f(divN(n,1))+n"),"",2,2,1,0,true,false,false),
 Case("Nonlinear",recurrence("f(divN(n,2))*f(divN(n,2))+n"),"",2,2,1,0,true,false,false),
 Case("ChangingCoefficient",recurrence("n*f(divN(n,2))+n"),"",2,2,1,0,true,false,false),
 Case("PartialSeed",recurrence("2*f(divN(n,2))+n","0 sub 1"),"",2,2,1,0,true,false,false),
 Case("PartialToll",recurrence("2*f(divN(n,2))+divN(n,0)"),"",2,2,1,0,true,false,false)
];}
private ulong cost(int kind,uint n){switch(kind){case 0:return 1;case 1:return n;case 2:return cast(ulong)n*n;case 3:return 0;case 4:return n/3;case 5:uint r;while(n>=2){n/=2;++r;}return r;default:assert(0);}}
int main(string[] args){
 auto dir=args.length>1?args[1]:"build/divide-recurrences";mkdirRecurse(dir);uint certificates,evaluations;
 foreach(c;cases()){
  auto owner=Session.open();FunctionSyntax s;if(c.vars.length)s.declare(c.vars);
  auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
  writeln(c.name,": ",text);enforce(!r.exhausted,c.name~" exhausted");enforce((text.indexOf("μ(")<0)==c.solved,c.name~" eligibility");
  auto again=s.run(owner.arena,text);enforce(!again.exhausted&&s.format(owner.arena,again)==text,c.name~" round trip: "~s.format(owner.arena,again));
  auto proof=s.exportCertificate(owner.arena,r);if(c.solved)enforce(proof.indexOf("DivideConquer.solve_sum")>=0,c.name~" solver proof");
  write(buildPath(dir,c.name~".lean"),proof);++certificates;
  if(!c.numeric)continue;
  ulong[1026] expected;
  foreach(n;0..expected.length)expected[n]=n<c.radix?(c.seedIndex?n:c.seed):c.coefficient*expected[n/c.radix]+cost(c.toll,cast(uint)n);
  uint[] samples;foreach(n;0..17)samples~=n;foreach(n;[31u,32u,33u,63u,64u,65u,80u,81u,82u,255u,256u,257u,1023u,1024u,1025u])samples~=n;
  foreach(n;samples)foreach(trace;[false,true]){
   auto value=s.run(owner.arena,"("~text~")("~to!string(n)~")",[],Options(DensityMode.preserve,trace));
   enforce(!value.exhausted&&s.format(owner.arena,value)==to!string(expected[n]),c.name~" at "~to!string(n)~": "~s.format(owner.arena,value));++evaluations;
  }
 }
 struct Scalar{string name,source,want;}
 foreach(c;[Scalar("IntegerDivision","divN(1000000000000000000000000000001,3)","333333333333333333333333333333"),Scalar("IntegerLog","logN(2,1023)","9"),Scalar("PowerLog","logN(2,1024)","10"),Scalar("AfterPower","logN(2,1025)","10"),Scalar("ZeroLog","logN(3,0)","0"),Scalar("ZeroDivisor","defined(divN(7,0))","false"),Scalar("InvalidBase","defined(logN(1,8))","false"),Scalar("PartialArgument","defined(logN(2,0 sub 1))","false")]){
  auto owner=Session.open();FunctionSyntax s;auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true));enforce(!r.exhausted&&s.format(owner.arena,r)==c.want,c.name);write(buildPath(dir,c.name~".lean"),s.exportCertificate(owner.arena,r));++certificates;
 }
 writeln(certificates," divide-and-conquer certificates; ",evaluations," exact evaluations");return 0;
}
