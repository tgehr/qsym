module roots_unity_tests;
import qsym;
import std.exception:enforce;
import std.file:mkdirRecurse,write;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:

int main(string[] args){
 enforce(args.length==2);mkdirRecurse(args[1]);uint certificates,checks;
 struct Case{string name,source,want="([n=1]:ℂ)";}
 foreach(c;[
  Case("Cis","∑(i:ℕ). cis(2*π*i/n)*[i<n]"),
  Case("Exp","∑(i:ℕ). exp(2*π*ⅈ*i/n)*[i<n]"),
  Case("Reordered","∑(i:ℕ). cis((i/n)*(2*π))*[i<n]"),
  Case("RealDenominator","∑(i:ℕ). cis(2*π*i/(n:ℝ))*[i<n]"),
  Case("Power","∑(i:ℕ). cis(2*π/n)^i*[i<n]"),
  Case("RealPower","∑(i:ℕ). cis(2*π/(n:ℝ))^i*[i<n]"),
  Case("Cos","∑(i:ℕ). cos(2*π*i/n)*[i<n]","([n=1]:ℝ)"),
  Case("Sin","∑(i:ℕ). sin(2*π*i/n)*[i<n]","(0:ℝ)"),
  Case("Successor","∑(i:ℕ). cis(2*π*i/(n+1))*[i<n+1]","([n+1=1]:ℂ)"),
  Case("PartialCount","∑(i:ℕ). cis(2*π*i/(n sub 1))*[i<n sub 1]","([n sub 1=1]:ℂ)"),
  Case("Lambda","λ(n:ℕ). ∑(i:ℕ). cis(2*π*i/n)*[i<n]","λ(n:ℕ). ([n=1]:ℂ)")
 ]){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;s.declare("n:ℕ");
  auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true)),want=s.run(a,c.want);
  auto text=s.format(a,r);writeln(c.name,": ",text);
  enforce(!r.exhausted&&text==s.format(a,want),c.name~" expected "~s.format(a,want));
  auto fast=s.run(a,c.source);enforce(!fast.exhausted&&s.format(a,fast)==text,c.name~" tracing");
  write(buildPath(args[1],c.name~".lean"),s.exportCertificate(a,r));++certificates;
  foreach(n;[0,1,2,3,7,64,100]){
   string apply(string t){return c.name=="Lambda"?"("~t~")("~to!string(n)~")":"(λ(n:ℕ). ("~t~"))("~to!string(n)~")";}
   auto x=s.run(a,apply(text)),y=s.run(a,apply(c.want));
   enforce(!x.exhausted&&!y.exhausted&&s.format(a,x)==s.format(a,y),c.name~" n="~to!string(n));++checks;
  }
 }
 // Independent explicit sums at the empty, singleton and quarter-turn cases.
 foreach(n;[0,1,2,4]){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;string terms="(0:ℂ)";
  foreach(i;0..n)terms~="+cis(2*π*"~to!string(i)~"/"~to!string(n)~")";
  auto r=s.run(a,terms);enforce(!r.exhausted&&s.format(a,r)==(n==1?"1":"0"),"explicit roots");++checks;
 }
 // A real bound does not mean a whole number of phase periods. Nor may
 // cancellation erase a pole in a coefficient of a nonempty sum.
 foreach(c;[
  ["RealBound","∑(i:ℕ). cis(2*π*i/(3/2))*[i<3/2]","1+cis(4*π/3)"],
  ["DifferentCount","∑(i:ℕ). cis(2*π*i/4)*[i<2]","1+ⅈ"],
  ["PartialCoefficient","defined(∑(i:ℕ). cis(2*π*i/2)*(1/0)*[i<2])","false"],
  ["EmptyPartialCoefficient","∑(i:ℕ). cis(2*π*i/0)*(1/0)*[i<0]","(0:ℂ)"],
  ["PartialCountDomain","defined((λ(n:ℕ). ∑(i:ℕ). cis(2*π*i/(n sub 1))*[i<n sub 1])(0))","false"]
 ]){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;
  auto r=s.run(a,c[1],[],Options(DensityMode.preserve,true)),want=s.run(a,c[2]);
  enforce(!r.exhausted&&s.format(a,r)==s.format(a,want),c[0]~": "~s.format(a,r));
  write(buildPath(args[1],c[0]~".lean"),s.exportCertificate(a,r));++certificates;
 }
 writeln(certificates," roots-of-unity certificates; ",checks," evaluations");return 0;
}
