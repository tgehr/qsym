module polynomial_summation_tests;
import qsym;
import qsym.polynomial:polynomialZero,polynomialAntidifference;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
import std.datetime.stopwatch:StopWatch,AutoStart;
@safe:

private Number power(long x,uint k){auto r=Number(1);foreach(i;0..k)r=r*Number(x);return r;}
private struct Case{string name,source;uint degree;uint kind;}
int main(string[] args){
 enforce(args.length==2);mkdirRecurse(args[1]);uint certificates,checks;
 Case[] cases=[
  Case("Natural6","∑(i:ℕ). [i<n]·i^6",6),
  Case("Fresh6","∑(i:ℕ). [i<n]·i^6",6,5),
  Case("Fresh10","∑(i:ℕ). [i<n]·i^10",10,5),
  Case("Natural10","∑(i:ℕ). [i<n]·i^10",10),
  Case("Natural40","∑(i:ℕ). [i<n]·i^40",40),
  Case("Natural64","∑(i:ℕ). [i<n]·i^64",64),
  Case("Shifted10","∑(i:ℕ). [i<n]·(2*i+1)^10",10,1),
  Case("Rational10","∑(i:ℕ). [i<n]·(i:ℚ)^10",10),
  Case("Complex6","∑(i:ℕ). [i<n]·((ⅈ*(i:ℂ))^6+(2+ⅈ)*(i:ℂ)^4)",6,2),
  Case("Symbolic10","∑(i:ℕ). [i<n]·(a*i^10+b*i^6)",10,3),
  Case("IntegerInterval6","∑(i:ℤ). [-3≤i]·[i<n]·i^6",6,4)
 ];
 foreach(c;cases){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;s.declare(c.kind==5?"a:ℝ,b:ℝ":"n:ℕ,a:ℝ,b:ℝ");
  auto watch=StopWatch(AutoStart.yes);
  auto result=s.run(a,c.source,[],Options(DensityMode.preserve,true));auto ms=watch.peek.total!"msecs";
  auto formula=s.format(a,result);
  enforce(!result.exhausted&&formula.indexOf("∑(")<0,c.name~": unresolved "~formula);
  auto fast=s.run(a,c.source);enforce(!fast.exhausted&&s.format(a,fast)==formula,c.name~" tracing");
  auto code=s.exportCertificate(a,result);
  enforce(code.indexOf("ring_nf")>=0&&code.indexOf("Summation.range_solution_partial")>=0,c.name~" missing polynomial certificate");
  write(buildPath(args[1],c.name~".lean"),code);++certificates;
  foreach(n;[0,1,2,5,10]){
   auto expression="(λ(a:ℝ). (λ(b:ℝ). (λ(n:"~(c.kind==5?"ℝ":"ℕ")~"). "~formula~")("~to!string(n)~"))(-2))(3)";
   auto actual=s.run(a,expression);Number expected;
   foreach(long i;c.kind==4?-3:0..n){
    auto term=power(c.kind==1?2*i+1:i,c.degree);
    if(c.kind==2)term=-power(i,6)+Number(2,1)*power(i,4);
    if(c.kind==3)term=Number(3)*power(i,10)-Number(2)*power(i,6);
    expected=expected+term;
   }
   enforce(!actual.exhausted&&(actual.scalarOnly||actual.lowered)&&a.isNumber(actual.scalar.output)&&a.number(actual.scalar.output)==expected,c.name~" prefix "~to!string(n)~": "~s.format(a,actual));++checks;
  }
  if(c.kind==5){
   auto bounds=["-1","-1/2","1/2","3/2","5/2","11/2"];
   foreach(k,count;[0,0,1,2,3,6]){
    auto r=s.run(a,"(λ(n:ℝ). "~formula~")("~bounds[k]~")");Number expected;
    foreach(i;0..count)expected=expected+power(i,c.degree);
    enforce(!r.exhausted&&(r.scalarOnly||r.lowered)&&a.isNumber(r.scalar.output)&&a.number(r.scalar.output)==expected,"fresh real bound "~bounds[k]);++checks;
   }
  }
  writeln(c.name,": solved in ",ms," ms; checked five exact prefixes");
 }
 // Cross the old cutoff in several places, rather than merely moving it to
 // the degree of a single regression example. Verify with independent sums.
 foreach(degree;[4u,5,8,16,31,32,33,50,80,100]){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;s.declare("n:ℕ");
  auto watch=StopWatch(AutoStart.yes);
  auto closed=s.run(a,"∑(i:ℕ). [i<n]·i^"~to!string(degree));
  auto ms=watch.peek.total!"msecs",formula=s.format(a,closed);
  enforce(!closed.exhausted&&formula.indexOf("∑(")<0,"degree "~to!string(degree)~": "~formula);
  foreach(n;[0,1,3,7]){
   auto result=s.run(a,"(λ(n:ℕ). "~formula~")("~to!string(n)~")");Number expected;
   foreach(i;0..n)expected=expected+power(i,degree);
   enforce(!result.exhausted&&(result.scalarOnly||result.lowered)&&a.isNumber(result.scalar.output)&&a.number(result.scalar.output)==expected,"degree "~to!string(degree)~" evaluation");++checks;
  }
  writeln("Degree ",degree,": ",ms," ms");
 }
 foreach(c;[
  ["Pole","defined(∑(i:ℕ). [i<5]·i^6/(i-2))","false"],
  ["EmptyPartial","∑(i:ℕ). [i<0]·(i sub 1)^6","0"],
  ["PartialSubtraction","defined(∑(i:ℕ). [i<1]·(i sub 1)^6)","false"]
 ]){
  auto owner=Session.open();FunctionSyntax s;auto r=s.run(owner.arena,c[1],[],Options(DensityMode.preserve,true));
  enforce(!r.exhausted&&s.format(owner.arena,r)==c[2],c[0]);
  write(buildPath(args[1],c[0]~".lean"),s.exportCertificate(owner.arena,r));++certificates;
 }
 auto owner=Session.open(),a=owner.arena;Syntax s;s.declare("n:ℕ,a:ℝ");
 foreach(source;["0*(1/0)","1/n-1/n","n^6-n^5","(n sub 1)-(n sub 1)"])
  enforce(!polynomialZero(a,s.parse(a,source,Sort.real_)),"unsafe polynomial zero: "~source);
 enforce(polynomialZero(a,s.parse(a,"(a+1)^2-a^2-2*a-1",Sort.real_)),"multivariate polynomial check");
 auto n=s.parse(a,"n");
 enforce(polynomialAntidifference(a,s.parse(a,"n^4294967295",Sort.real_),n)==Term.init,"work budget ignored");
 enforce(polynomialAntidifference(a,s.parse(a,"n^6",Sort.real_),n)!=Term.init,"budget failure escaped");
 writeln(certificates," certificates; ",checks," exact prefix checks; 4 invalid-identity rejections; 1 work-budget check");
 return 0;
}
