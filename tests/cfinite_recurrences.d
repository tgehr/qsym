module cfinite_recurrence_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:
private enum fib="((0,1),(1,1))^n@(0,1)";
private struct Case{ string name,forcing,sort="ℕ",vars; int oracle=-1; long coefficient=2,seed=0; bool solved=true; }
private Case[] cases(){ return [
 Case("Quadratic","n*n","ℕ","",0),
 Case("Cube","n^3","ℕ","",1),
 Case("Geometric","3^n","ℕ","",2),
 Case("WeightedGeometric","n*2^n","ℕ","",3),
 Case("PolynomialProduct","(n+1)*(n+2)","ℕ","",4),
 Case("GeometricProduct","2^n*3^n","ℕ","",5),
 Case("Fibonacci","get("~fib~",0)","ℕ","",6),
 Case("FibonacciProduct","get("~fib~",0)*get("~fib~",1)","ℕ","",7),
 Case("Integer","n*n","ℤ","",0,-2,-3),
 Case("RationalCast","3*n*n","ℚ","",8),
 Case("RealCast","n*n","ℝ","",0),
 Case("ComplexCast","n*n","ℂ","",0),
 Case("ZeroCoefficient","n*n","ℕ","",0,0),
 Case("UnitCoefficient","n*n","ℕ","",0,1),
 Case("Symbolic","a*n*n+b^n","ℕ","a:ℕ,b:ℕ"),
 Case("NegativeGeometric","(-2)^n","ℤ","",9),
 Case("ZeroGeometric","0^n","ℕ","",10),
 Case("PartialForcing","n sub 1","ℕ","",-1,2,0,false),
 Case("VariableCoefficient","n*f(n sub 1)+n*n","ℕ","",-1,2,0,false),
 Case("NonlinearFeedback","f(n sub 1)*f(n sub 1)+n*n","ℕ","",-1,2,1,false),
 Case("ZeroRootTransient","get(((0,1),(0,0))^n@(0,1),0)","ℕ","",11),
 Case("SquarePower","n^2","ℕ","",0),
 Case("SymbolicReal","a*n*n+b^n","ℝ","a:ℝ,b:ℝ"),
 Case("Reciprocal","1/(n+1)","ℚ","",-1,2,0,false),
 Case("StateBudget","n^5","ℕ","",-1,2,0,false)
]; }
private long power(long a,uint n){long r=1;foreach(i;0..n)r*=a;return r;}
private long force(int which,uint n){
 long a=0,b=1;foreach(i;0..n){auto c=a+b;a=b;b=c;}
 switch(which){
  case 0:return cast(long)n*n;
  case 1:return power(n,3);
  case 2:return power(3,n);
  case 3:return n*power(2,n);
  case 4:return (cast(long)n+1)*(n+2);
  case 5:return power(2,n)*power(3,n);
  case 6:return a;
  case 7:return a*b;
  case 8:return 3*cast(long)n*n;
  case 9:return power(-2,n);
  case 10:return n==0?1:0;
  case 11:return n==1?1:0;
  default:assert(0);
 }
}
int main(string[] args){
 auto dir=args.length>1?args[1]:"build/cfinite-recurrences";mkdirRecurse(dir);
 uint certificates,evaluations;
 foreach(c;cases()){
  auto owner=Session.open();FunctionSyntax s;if(c.vars.length)s.declare(c.vars);
  auto source="μ(f:ℕ→"~c.sort~").λ(n:ℕ).if n=0 then "~to!string(c.seed)~" else "~to!string(c.coefficient)~"*f(n sub 1)+("~c.forcing~")";
  auto r=s.run(owner.arena,source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
  writeln(c.name,": ",text);
  enforce(!r.exhausted,c.name~" exhausted");enforce((text.indexOf("μ(")<0)==c.solved,c.name~" eligibility");
  auto again=s.run(owner.arena,text);enforce(!again.exhausted&&s.format(owner.arena,again)==text,c.name~" round trip");
  auto proof=s.exportCertificate(owner.arena,r);
  if(c.solved&&c.coefficient!=0&&c.name!="ZeroGeometric")enforce(proof.indexOf("CFiniteRecurrence.solve_matrix")>=0,c.name~" solver proof");
  write(buildPath(dir,c.name~".lean"),proof);++certificates;
  if(c.oracle>=0){
   long expected=c.seed;
   foreach(n;0..7){
    foreach(trace;[false,true]){
     auto value=s.run(owner.arena,"("~text~")("~to!string(n)~")",[],Options(DensityMode.preserve,trace));
     auto want=s.run(owner.arena,"("~to!string(expected)~":"~c.sort~")");
     enforce(!value.exhausted&&s.format(owner.arena,value)==s.format(owner.arena,want),c.name~" value "~to!string(n)~": "~s.format(owner.arena,value));++evaluations;
    }
    expected=c.coefficient*expected+force(c.oracle,n+1);
   }
  }
 }
 auto owner=Session.open();FunctionSyntax s;
 auto partial=s.run(owner.arena,"defined((μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else 2*f(n sub 1)+n*n)(0 sub 1))",[],Options(DensityMode.preserve,true));
 enforce(!partial.exhausted&&s.format(owner.arena,partial)=="false","partial argument");
 write(buildPath(dir,"PartialArgument.lean"),s.exportCertificate(owner.arena,partial));++certificates;
 writeln(certificates," C-finite recurrence certificates; ",evaluations," exact evaluations");return 0;
}
