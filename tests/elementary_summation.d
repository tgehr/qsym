module elementary_summation_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:
int main(string[] args){
 enforce(args.length==2);mkdirRecurse(args[1]);uint certificates,checks;
 struct Case {string name,term,values="log(2)",decl="a:ℝ,b:ℝ";}
 foreach(c;[
  Case("Exp","exp(i)"),Case("ComplexExpIndex","cexp(i)"),Case("ComplexExpiIndex","cexpi(i)"),Case("ExpNegative","exp(-i)"),
  Case("ExpFractional","exp(i/2)"),Case("ExpMultiple","exp(2*i)"),
  Case("ExpAffine","exp(a*i+b)"),Case("Exp2","exp2(a*i)","2"),
  Case("WeightedExp","i*exp(a*i)"),Case("WeightedPhase","i*cis(a*i)","π/2"),Case("ExpComplex","cexp(a*i)","log(2)","a:ℂ,b:ℝ"),
  Case("Phase","cis(a*i)","π/2"),Case("PhaseAffine","cis(a*i+b)","π/2"),
  Case("Expi","cexpi(a*i)","π/2","a:ℂ,b:ℝ"),
  Case("Sin","sin(a*i)","π/2"),Case("Cos","cos(a*i)","π/2"),
  Case("ComplexSin","csin(a*i)","π/2","a:ℂ,b:ℝ"),
  Case("ComplexCos","ccos(a*i)","π/2","a:ℂ,b:ℝ"),
  Case("Sinh","sinh(a*i)"),Case("Cosh","cosh(a*i)"),
  Case("ComplexSinh","csinh(a*i)","log(2)","a:ℂ,b:ℝ"),
  Case("ComplexCosh","ccosh(a*i)","log(2)","a:ℂ,b:ℝ"),
  Case("RealPower","powerR(a,i)","-2"),
  Case("ComplexPower","powerC(a,i)","ⅈ","a:ℂ,b:ℝ")
 ]){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;s.declare("n:ℕ,"~c.decl);
  auto input="∑(i:ℕ). [i<n]*("~c.term~")";
  auto r=s.run(a,input,[],Options(DensityMode.preserve,true)),formula=s.format(a,r);
  enforce(!r.exhausted&&formula.indexOf("∑(")<0,c.name~": "~formula);
  auto fast=s.run(a,input);enforce(!fast.exhausted&&s.format(a,fast)==formula,c.name~" untraced");
  write(buildPath(args[1],c.name~".lean"),s.exportCertificate(a,r));++certificates;
  foreach(value;["0",c.values])foreach(n;c.term.indexOf("a")>=0?[0,1,2,4]:[0,1]){
   auto ty=c.decl.indexOf("a:ℂ")>=0?"ℂ":"ℝ";
   string instantiate(string text){return "(λ(b:ℝ). (λ(a:"~ty~"). (λ(n:ℕ). ("~text~"))("~to!string(n)~"))("~value~"))(0)";}
   // Use the defining exponentials for the independent hyperbolic
   // evaluation: scalar sinh(k*log(2)) is not always reduced yet.
   auto term=c.term;
   if(c.name=="Sinh"||c.name=="ComplexSinh")term="(exp(a*i)-exp(-a*i))/2";
   if(c.name=="Cosh"||c.name=="ComplexCosh")term="(exp(a*i)+exp(-a*i))/2";
   string explicit="0";foreach(i;0..n)explicit~="+((λ(i:ℕ). "~term~")("~to!string(i)~"))";
   auto actual=s.run(a,instantiate(formula)),expected=s.run(a,instantiate(explicit));
   enforce(!actual.exhausted&&!expected.exhausted,c.name~" evaluation exhausted");
   if(s.format(a,actual)!=s.format(a,expected)){
    enforce((actual.scalarOnly||actual.lowered)&&(expected.scalarOnly||expected.lowered),c.name~" not scalar");
    auto sort=a.sort(actual.scalar.output)==Sort.complex||a.sort(expected.scalar.output)==Sort.complex?Sort.complex:Sort.real_;
    auto opts=Options.init;opts.expandPowers=true;opts.expandScalarEmbeddings=true;
    auto delta=simplify(a,a.sub(a.castTo(actual.scalar.output,sort),a.castTo(expected.scalar.output,sort)),[],opts);
    enforce(!delta.exhausted&&a.isNumber(delta.output)&&a.number(delta.output).zero,c.name~" n="~to!string(n)~" a="~value~": "~s.format(a,actual)~" versus "~s.format(a,expected));
   }
   ++checks;
  }
  writeln(c.name,": ",formula);
 }
 // The imaginary unit in the reported example is not the bound index.
 foreach(c;[
  ["ConstantPhase","cis(2*π/n)"], ["ConstantComplexExp","exp(2*π*ⅈ/n)"],
  ["ConstantPole","1/n"], ["ConstantLog","log(n)"], ["ConstantRoot","sqrt(n)"]
 ]){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;
  auto r=s.run(a,"∑(i:ℕ). [0≤i<n]*("~c[1]~")",[],Options(DensityMode.preserve,true)),formula=s.format(a,r);
  enforce(!r.exhausted&&formula.indexOf("∑(")<0,c[0]~": "~formula);
  write(buildPath(args[1],c[0]~".lean"),s.exportCertificate(a,r));++certificates;
  foreach(value;["-1","0","1/2","1","2"]){
   auto source="(λ(n:ℝ). "~formula~")("~value~")";
   auto direct="(λ(n:ℝ). ∑(i:ℕ). [0≤i<n]*("~c[1]~"))("~value~")";
   auto x=s.run(a,source),y=s.run(a,direct);
   enforce(!x.exhausted&&!y.exhausted&&s.format(a,x)==s.format(a,y),c[0]~" n="~value~": "~s.format(a,x)~" versus "~s.format(a,y));++checks;
  }
 }
 foreach(c;[
  ["DivergentExp","∑(i:ℕ). exp(i)","undefined(ℝ)"],
  ["DivergentPhase","∑(i:ℕ). cis(i)","undefined(ℂ)"],
  ["ConvergentExp","∑(i:ℕ). exp(-i)","1/(1-exp(-1))"],
  ["ConvergentFractional","∑(i:ℕ). exp(-i/2)","1/(1-exp(-1/2))"],
  ["ZeroPhase","∑(i:ℕ). cis(0)","undefined(ℂ)"]
 ]){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;
  auto r=s.run(a,c[1],[],Options(DensityMode.preserve,true)),expected=s.run(a,c[2]);
  enforce(!r.exhausted&&s.format(a,r)==s.format(a,expected),c[0]~": "~s.format(a,r));
  write(buildPath(args[1],c[0]~".lean"),s.exportCertificate(a,r));++certificates;
 }
 writeln(certificates," certificates; ",checks," finite evaluations");return 0;
}
