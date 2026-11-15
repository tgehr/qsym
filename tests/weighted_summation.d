module weighted_summation_tests;
import qsym;
import qsym.rational_identity:rationalIdentityZero;
import qsym.proof:exportRationalZeroLean;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
import std.datetime.stopwatch:StopWatch,AutoStart;
@safe:
private Number power(Number x,uint n){auto r=Number(1);foreach(i;0..n)r=r*x;return r;}
private struct Case{string name,source,type="ℝ";uint degree=1,kind;}
int main(string[] args){
 enforce(args.length==2);mkdirRecurse(args[1]);uint certificates,checks;
 Case[] cases=[
  Case("Linear","∑(i:ℕ). [i<n]·i*q^i"),
  Case("Quadratic","∑(i:ℕ). [i<n]·i^2*q^i","ℝ",2),
  Case("Degree6","∑(i:ℕ). [i<n]·i^6*q^i","ℝ",6),
  Case("AffineExponent","∑(i:ℕ). [i<n]·i*q^(2*i+3)","ℝ",1,1),
  Case("SumRatio","∑(i:ℕ). [i<n]·i*(q+r)^i","ℝ",1,2),
  Case("TwoRatios","∑(i:ℕ). [i<n]·i*(q^i+r^i)","ℝ",1,3),
  Case("Coefficient","∑(i:ℕ). [i<n]·a*i*q^i","ℝ",1,4),
  Case("Rational","∑(i:ℕ). [i<n]·(i:ℚ)^2*q^i","ℚ",2),
  Case("Complex","∑(i:ℕ). [i<n]·(i:ℂ)*q^i","ℂ"),
  Case("Natural","∑(i:ℕ). [i<n]·i*q^i","ℕ"),
  Case("FreshBound","∑(i:ℕ). [i<n]·i*q^i","ℝ",1,5)
 ];
 foreach(c;cases){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;s.declare((c.kind==5?"":"n:ℕ,")~"q:"~c.type~",r:"~c.type~",a:ℝ");
  auto watch=StopWatch(AutoStart.yes),result=s.run(a,c.source,[],Options(DensityMode.preserve,true));
  auto ms=watch.peek.total!"msecs",formula=s.format(a,result);
  enforce(!result.exhausted&&formula.indexOf("∑(")<0,c.name~": "~formula);
  auto fast=s.run(a,c.source);auto fastFormula=s.format(a,fast);enforce(!fast.exhausted&&fastFormula.indexOf("∑(")<0,c.name~" untraced");
  auto code=s.exportCertificate(a,result);enforce(code.indexOf("field_simp")>=0,c.name~" missing field certificate");
  write(buildPath(args[1],c.name~".lean"),code);++certificates;
  string[] qs=c.type=="ℕ"?["0","1","2","3"]:c.type=="ℂ"?["0","1","-1","ⅈ","(1+ⅈ)/2","2"]:["-2","-1","0","1/2","1","2"];
  Syntax numeric;numeric.declare("q:"~c.type);
  foreach(qtext;qs){
   auto q=numeric.parse(a,qtext);auto value=simplify(a,q);enforce(a.isNumber(value.output));auto qv=a.number(value.output);
   foreach(rv;c.kind==3?[1,2]:[2])foreach(n;[0,1,2,5]){
    foreach(evaluated;[formula,fastFormula]){
    auto source="(λ(a:ℝ). (λ(r:"~c.type~"). (λ(q:"~c.type~"). (λ(n:"~(c.kind==5?"ℝ":"ℕ")~"). "~evaluated~")("~to!string(n)~"))("~qtext~"))("~to!string(rv)~"))(3)";
    auto actual=s.run(a,source);Number expected;
    foreach(i;0..n){
     auto ratio=c.kind==2?qv+Number(rv):qv;
     auto term=power(Number(i),c.degree)*power(ratio,c.kind==1?2*i+3:i);
     if(c.kind==3)term=term+Number(i)*power(Number(rv),i);
     if(c.kind==4)term=Number(3)*term;
     expected=expected+term;
    }
    enforce(!actual.exhausted&&(actual.scalarOnly||actual.lowered)&&a.isNumber(actual.scalar.output)&&a.number(actual.scalar.output)==expected,c.name~" q="~qtext~" n="~to!string(n)~": "~s.format(a,actual));++checks;
    }
   }
  }
  writeln(c.name,": ",ms," ms; exact ratio and endpoint checks passed");
 }
 auto owner=Session.open(),a=owner.arena;Syntax s;s.declare("q:ℝ,n:ℕ");Term[] conditions;
 foreach(source;["0*(1/q)","1/q-1/q","(1/q)^0-1","[q=1]*(n^2-n)","[q≠1]*(q/q-1)","exp(1/q)-exp(1/q)","creal(cis(1/q))-creal(cis(1/q))"])
  enforce(!rationalIdentityZero(a,s.parse(a,source,Sort.real_),conditions),"unsafe field identity: "~source);
 auto safe=s.parse(a,"[q≠0]*(q/q-1)",Sort.real_);
 enforce(rationalIdentityZero(a,safe,conditions),"masked cancellation");
 write(buildPath(args[1],"MaskedCancellation.lean"),exportRationalZeroLean(a,safe,conditions));++certificates;
 Syntax guards;guards.declare("x:ℝ,y:ℝ");
 string[] guardInputs=["[x*y=0]*x*y","[x=0∨y=0]*x*y","[x^2=1]*(x^2-1)","[x≤0∧0≤x]*x"];
 foreach(i,source;guardInputs){
  auto result=simplify(a,guards.parse(a,source),[],Options(DensityMode.preserve,true));
  enforce(!result.exhausted&&a.isNumber(result.output)&&a.number(result.output).zero,"guarded zero: "~source);
  write(buildPath(args[1],"GuardZero"~to!string(i)~".lean"),exportLean(a,result));++certificates;
 }
 writeln(certificates," certificates; ",checks," exact checks; 7 invalid-identity rejections");return 0;
}
