module summation_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:
private struct Case { string name,input,expected,proof; }
private Case[] cases(){ return [
 Case("Example","∑(i:ℕ). [i<n]·i","floorN(n*(1/2*n-1/2))","Summation.range_solution_partial"),
 Case("Ascii","sum(i:ℕ). [i<5]*i","10"),
 Case("FiniteInclusive","∑(i:ℕ). [i≤5]·i","15"),
 Case("Empty","∑(i:ℕ). [i<0]·(1/0)","0"),
 Case("Singleton","∑(i:ℕ). [i<1]·(i+7)","7"),
 Case("LargeFinite","∑(i:ℕ). [i<100]·i","4950"),
 Case("Squares","∑(i:ℕ). [i<n]·(i:ℝ)^2","n*(n-1)*(2*n-1)/6"),
 Case("Cubes","∑(i:ℕ). [i<n]·(i:ℝ)^3","n^2*(n-1)^2/4"),
 Case("PolynomialGeometric","∑(i:ℕ). [i<n]·(i:ℝ)*(1/2)^i","2-(2*n+2)*(1/2)^n"),
 Case("FiniteGeometric","∑(i:ℕ). [i<n]·(2:ℝ)^i","2^n-1"),
 Case("SymbolicFinite","∑(i:ℕ). [i<n]·q^i","[n≠0]·([q≠1]·((q^n-1)/(q-1))+[q=1]·n)","Summation.range_geometric_value"),
 Case("FiniteRatioOne","∑(i:ℕ). [i<n]·(1:ℝ)^i","(n:ℝ)"),
 Case("FiniteRatioZero","∑(i:ℕ). [i<n]·(0:ℝ)^i","[0<n]·(1:ℝ)"),
 Case("NaturalInterval","∑(i:ℕ). [2≤i∧i<5]·i","9","Summation.interval_convertN"),
 Case("IntegerInterval","∑(i:ℤ). [-2≤i∧i<4]·i","3","Summation.interval_convertZ"),
 Case("StrictInterval","∑(i:ℤ). [-2<i∧i<4]·i","5","Summation.boundsZ"),
 Case("ClosedInterval","∑(i:ℤ). [-2≤i∧i≤4]·i","7"),
 Case("OpenClosedInterval","∑(i:ℕ). [2<i∧i≤5]·i","12","Summation.boundsN"),
 Case("ReversedInterval","∑(i:ℤ). [4≤i∧i<2]·(1/0)","0"),
 Case("NaturalDelta","∑(i:ℕ). [i=n]·i","n","Summation.deltaN"),
 Case("IntegerDelta","∑(i:ℤ). [i=-2]·i","-2","Summation.deltaZ_offset"),
 Case("DeltaPartial","defined(∑(i:ℕ). [i=n]·(1/(i-n)))","false"),
 Case("ZeroN","∑(i:ℕ). 0","0"),
 Case("ZeroZ","∑(i:ℤ). (0:ℤ)","0"),
 Case("ZeroQ","∑(i:ℕ). (0:ℚ)","0"),
 Case("ZeroR","∑(i:ℕ). (0:ℝ)","0"),
 Case("ZeroC","∑(i:ℤ). (0:ℂ)","(0:ℂ)"),
 Case("ConstantDiverges","defined(∑(i:ℕ). 1)","false"),
 Case("IntegerConstantDiverges","defined(∑(i:ℤ). (2:ℤ))","false"),
 Case("RationalConstantDiverges","defined(∑(i:ℕ). (1:ℚ))","false"),
 Case("RealConstantDiverges","defined(∑(i:ℕ). (1:ℝ))","false"),
 Case("ComplexConstantDiverges","defined(∑(i:ℕ). (1:ℂ))","false"),
 Case("Geometric","∑(i:ℕ). (1/2)^i","2","Summation.geometric"),
 Case("GeometricQ","∑(i:ℕ). (1/2:ℚ)^i","(2:ℚ)","Summation.geometricQ_literals"),
 Case("GeometricC","∑(i:ℕ). (1/2:ℂ)^i","(2:ℂ)","Summation.geometricC_literals"),
 Case("NegativeRatio","∑(i:ℕ). (-1/2)^i","2/3"),
 Case("GeometricDiverges","defined(∑(i:ℕ). (2:ℝ)^i)","false"),
 Case("AlternatingDiverges","defined(∑(i:ℕ). (-1:ℝ)^i)","false"),
 Case("SymbolicGeometric","∑(i:ℕ). q^i","guard(-1<q∧q<1,1/(1-q))"),
 Case("LinearGeometric","∑(i:ℕ). (i:ℝ)*(1/2)^i","2","Summation.tail_solution"),
 Case("SquareGeometric","∑(i:ℕ). (i:ℝ)^2*(1/2)^i","6"),
 Case("CubicGeometric","∑(i:ℕ). (i:ℝ)^3*(1/2)^i","26"),
 Case("WeightedQ","∑(i:ℕ). (i:ℚ)*(1/2:ℚ)^i","(2:ℚ)"),
 Case("WeightedC","∑(i:ℕ). (i:ℂ)*(1/2:ℂ)^i","(2:ℂ)"),
 Case("TwoRatios","∑(i:ℕ). (i:ℝ)*(1/2)^i+(1/3)^i","7/2"),
 Case("PoleSelected","defined(∑(i:ℕ). [i<5]·(1/(i-2)))","false"),
 Case("PoleMasked","∑(i:ℕ). [i<2]·(1/(i-2))","-3/2"),
 Case("UndefinedBound","defined(∑(i:ℕ). [i<(0 sub 1)]·i)","false"),
 Case("UndefinedGeometric","defined(∑(i:ℕ). (1/0)^i)","false"),
 Case("UndefinedEmptyRatio","∑(i:ℕ). [i<0]·(1/0)^i","0"),
 Case("Lambda","λ(k:ℕ). ∑(i:ℕ). [i<k]·i","λ(k:ℕ). floorN(k*(1/2*k-1/2))"),
 Case("Shadowing","(λ(i:ℕ). ∑(i:ℕ). [i<3]·i)(20)","3"),
 Case("NestedFinite","∑(i:ℕ). [i<3]·(∑(j:ℕ). [j<i]·j)","1"),
 Case("AdditiveRecurrence","μ(f:ℕ→ℕ).λ(k:ℕ).if k=0 then 3 else f(k sub 1)+k","λ(k:ℕ). floorN(k*(1/2*k+1/2))+3","Summation.solve_prefix"),
 Case("HarmonicRecurrence","(μ(f:ℕ→ℝ).λ(k:ℕ).if k=0 then 3 else 1/k+f(k sub 1))(3)","29/6","Summation.solve_prefix"),
 Case("PartialRecurrenceBase","(μ(f:ℕ→ℝ).λ(k:ℕ).if k=0 then 3 else f(k sub 1)+1/(k-2))(0)","3"),
 Case("PartialRecurrenceStep","defined((μ(f:ℕ→ℝ).λ(k:ℕ).if k=0 then 3 else f(k sub 1)+1/(k-2))(3))","false")
 ]; }
int main(string[] args){
 enforce(args.length==2); mkdirRecurse(args[1]);
 uint failed;
 foreach(c;cases()) try{
  auto session=Session.open(),a=session.arena; FunctionSyntax s; s.declare("n:ℕ,m:ℕ,q:ℝ,a:ℤ,b:ℤ");
  auto r=s.run(a,c.input,[],Options(DensityMode.preserve,true)),expected=s.run(a,c.expected);
  auto text=s.format(a,r),want=s.format(a,expected);
  bool equivalent(FunctionResult x,FunctionResult y){
   if(s.format(a,x)==s.format(a,y)) return true;
   if(!(x.scalarOnly||x.lowered)||!(y.scalarOnly||y.lowered)) return false;
   auto tx=x.scalar.output,ty=y.scalar.output;
   if(a.sort(tx)==Sort.boolean||a.sort(ty)==Sort.boolean) return false;
   auto target=a.sort(tx)==Sort.complex||a.sort(ty)==Sort.complex?Sort.complex:Sort.real_;
   auto opts=Options(DensityMode.preserve,true); opts.expandPowers=true;opts.expandScalarEmbeddings=true;
   auto check=simplify(a,a.equal(a.castTo(tx,target),a.castTo(ty,target)),[],opts);
   return !check.exhausted&&check.output==a.boolean(true);
  }
  enforce(!r.exhausted&&!expected.exhausted,c.name~" exhausted");
  enforce(equivalent(r,expected),c.name~": "~text~"; expected "~want);
  auto fast=s.run(a,c.input); enforce(!fast.exhausted&&s.format(a,fast)==text,c.name~" trace differs");
  auto roundtrip=s.run(a,text); enforce(!roundtrip.exhausted&&equivalent(r,roundtrip),c.name~" round trip: "~s.format(a,roundtrip));
  auto code=s.exportCertificate(a,r); if(c.proof.length) enforce(code.indexOf(c.proof)>=0,c.name~" missing proof");
  write(buildPath(args[1],c.name~".lean"),code);
  writeln(c.name,": ",text);
 } catch(Exception e){++failed;writeln("FAILED ",c.name,": ",e.msg);}
 enforce(failed==0,to!string(failed)~" summation cases failed");
 foreach(source;["∑(i:ℝ). i","∑(i:ℕ). true","∑(i:ℕ). λ(j:ℕ).j"]){
  bool rejected;try{auto session=Session.open();FunctionSyntax s;s.run(session.arena,source);}catch(Exception){rejected=true;}
  enforce(rejected,"invalid summation accepted: "~source);
 }
 foreach(source;[
  "μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n)+n",
  "μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n+1)+n",
  "μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 2)+n",
  "μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)*n"]){
  auto session=Session.open();FunctionSyntax s;auto r=s.run(session.arena,source);
  enforce(!r.exhausted&&s.format(session.arena,r).indexOf("μ(")>=0,"unsupported recurrence rewritten");
 }
 foreach(source;["∑(i:ℕ). 1/(i+1)","∑(i:ℕ). (-1:ℝ)^i/(i+1)"]){
  auto session=Session.open();FunctionSyntax s;auto r=s.run(session.arena,source);
  enforce(!r.exhausted&&s.format(session.arena,r).indexOf("∑(")>=0,"unknown series given an unchecked value");
 }
 foreach(ratio;[Rational(-1)/Rational(2),Rational(0),Rational(1)/Rational(2),Rational(1),Rational(2)]) foreach(degree;0..4){
  auto session=Session.open(),a=session.arena;FunctionSyntax s;
  auto source="λ(n:ℕ). ∑(i:ℕ). [i<n]·(i:ℝ)^"~to!string(degree)~"*("~to!string(ratio)~")^i";
  auto closed=s.run(a,source);auto formula=s.format(a,closed);
  enforce(!closed.exhausted&&formula.indexOf("∑(")<0,"polynomial-geometric formula missing: "~formula);
  foreach(count;[0,1,2,5,20]){
   Rational expected=Rational(0),power=Rational(1);
   foreach(i;0..count){ auto coefficient=Rational(1);foreach(j;0..degree) coefficient=coefficient*Rational(i);expected=expected+coefficient*power;power=power*ratio; }
   auto actual=s.run(a,"("~formula~")("~to!string(count)~")");
   enforce(!actual.exhausted&&(actual.scalarOnly||actual.lowered)&&a.isNumber(actual.scalar.output)&&a.number(actual.scalar.output)==Number(expected),"finite sum disagrees with independent iteration: "~source);
  }
 }
 auto session=Session.open();FunctionSyntax s;auto r=s.run(session.arena,"∑(i:ℕ). [i<5]·i",[],Options(DensityMode.preserve,true));
 auto limited=r.bindings.normalize(r.reduction.input,0,true);
 enforce(limited.exhausted&&limited.output==limited.input,"sum budget ignored");
 write(buildPath(args[1],"Budget.lean"),r.bindings.exportLean(limited));
 writeln(cases().length+1," summation certificates; 100 independent numeric checks; 3 invalid binders rejected");return 0;
}
