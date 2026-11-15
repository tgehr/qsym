module summation_abel_tests;
import qsym;
import qsym.summation:sumAbelAntidifference,AbelSearchStats;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:

private Term substitute(Arena a,Term t,Term variable,Term value){
 if(t==variable)return value;
 auto n=a.view(t);Term[] children;
 foreach(i;0..n.arity)children~=substitute(a,a.viewChild(t,i),variable,value);
 return children.length?a.viewRebuild(t,children,true):t;
}

int main(string[] args){
 enforce(args.length==2,"usage: summation-abel-tests DIRECTORY");mkdirRecurse(args[1]);
 uint certificates,numeric,cycles;
 struct Primitive {string name,input;Sort sort;bool cycle;}
 // These call the recursive search directly: the coefficient fast path in
 // binding.d must not hide an unused or broken cycle-solving implementation.
 foreach(c;[
  Primitive("LinearCycle","n",Sort.real_,true),
  Primitive("CubicCycles","n^3",Sort.real_,true),
  Primitive("RationalCycles","(n:ℚ)^4",Sort.rational,true),
  Primitive("ComplexCycles","(n:ℂ)",Sort.complex,true),
  Primitive("WeightedSquare","n^2*(1/2)^n",Sort.real_,true),
  Primitive("MixedRatios","n*(1/2)^n+n^2*(-1/2)^n",Sort.real_,true),
  Primitive("SymbolicCoefficient","a*n^2",Sort.real_,true),
  Primitive("ShiftedPolynomial","(n+2)^3",Sort.real_,true)
 ]){
  auto owner=Session.open(),a=owner.arena;Syntax s;s.declare("n:ℕ,a:ℝ,q:ℝ");
  auto n=s.parse(a,"n"),parameter=s.parse(a,"a"),input=s.parse(a,c.input,c.sort);
  // Allocate a variable outside the input to check arena-wide freshness.
  a.variable(Sort.real_,900);
  AbelSearchStats stats;auto result=sumAbelAntidifference(a,input,n,stats);
  enforce(result!=Term.init&&!stats.exhausted,c.name~" candidate missing");
  enforce(!c.cycle||stats.cycles>0&&stats.hits>0,c.name~" did not close a cycle");cycles+=stats.cycles;
  foreach(id;a.viewPostorder(result)){
   auto v=a.view(a.at(id));enforce(v.op!=Op.variable||v.value<3,c.name~" leaked placeholder");
  }
  auto initial=substitute(a,result,n,a.natural_(0));
  auto step=a.sub(substitute(a,result,n,a.add(n,a.natural_(1),true)),a.add(result,input,true));
  auto opts=Options(DensityMode.preserve,true);opts.expandPowers=true;opts.expandScalarEmbeddings=true;
  opts.maxRewrites=2048;opts.maxAlgebraWork=32768;
  foreach(t;[initial,step]){
   auto checked=c.sort==Sort.rational?a.castTo(t,Sort.real_):t;
   auto d=simplifyDomain(a,checked,[],opts),v=simplify(a,checked,[],opts);
   enforce(!d.exhausted&&!v.exhausted&&d.output==a.boolean(true)&&a.isNumber(v.output)&&a.number(v.output).zero,c.name~" identity/domain");
   if(t==step){
    write(buildPath(args[1],c.name~"Step.lean"),exportLean(a,v));
    write(buildPath(args[1],c.name~"Domain.lean"),exportLean(a,d));certificates+=2;
   }
  }
  auto total=Number(0);
  foreach(k;0..10){
   Term evaluate(Term t){return simplify(a,substitute(a,substitute(a,t,parameter,a.real_(3)),n,a.natural_(k)),[],opts).output;}
   auto value=evaluate(result);enforce(a.isNumber(value)&&a.number(value)==total,c.name~" prefix "~to!string(k));++numeric;
   auto term=evaluate(input);enforce(a.isNumber(term),c.name~" summand");total=total+a.number(term);
  }
  writeln(c.name,": ",stats.cycles," cycles; ",stats.calls," recursive calls");
 }

 // These families were outside the old polynomial-geometric parser. Check
 // the symbolic result, independent finite sums, and emitted range proofs.
 foreach(c;[
  ["FractionalSlope","(i:ℝ)*powerR(2,i/2)"],
  ["FractionalSquare","(i:ℝ)^2*powerR(4,i/2)"],
  ["NegativeSlope","(i:ℝ)*powerR(4,-i/2)"],
  ["ShiftedFractional","(i:ℝ)^2*powerR(4,i/2+1/2)"],
  ["NonmonomialFactor","((i:ℝ)+1)^2*powerR(4,i/2)"],
  ["PolynomialCoefficient","a*(i:ℝ)*powerR(4,i/2)"]
 ]){
  auto owner=Session.open(),a=owner.arena;FunctionSyntax s;s.declare("n:ℕ,a:ℝ");
  auto source="∑(i:ℕ). [i<n]*("~c[1]~")";
  auto r=s.run(a,source,[],Options(DensityMode.preserve,true)),out_=s.format(a,r);
  enforce(!r.exhausted&&out_.indexOf("∑(")<0,c[0]~": "~out_);
  auto fast=s.run(a,source);enforce(!fast.exhausted&&s.format(a,fast)==out_,c[0]~" tracing");
  auto code=s.exportCertificate(a,r);enforce(code.indexOf("Summation.range_solution_partial")>=0,c[0]~" missing checked range proof");
  write(buildPath(args[1],c[0]~".lean"),code);++certificates;
  // Instantiate the already derived closed form, then compare it with an
  // explicit sum; this also checks empty and singleton prefixes.
  foreach(k;0..5){
   string explicit="0";
   foreach(j;0..k)explicit~="+((λ(i:ℕ). "~c[1]~")("~to!string(j)~"))";
   auto expression="(λ(a:ℝ). (λ(n:ℕ). ("~out_~"))("~to!string(k)~"))(3)";
   auto expected="(λ(a:ℝ). ("~explicit~"))(3)";
   auto u=s.run(a,expression),v=s.run(a,expected);
   enforce(!u.exhausted&&!v.exhausted&&(u.scalarOnly||u.lowered)&&(v.scalarOnly||v.lowered),c[0]~" evaluation");
   auto opts=Options.init;opts.expandPowers=true;opts.expandScalarEmbeddings=true;
   auto delta=simplify(a,a.sub(a.castTo(u.scalar.output,Sort.real_),a.castTo(v.scalar.output,Sort.real_)),[],opts);
   Syntax text;
   enforce(!delta.exhausted&&a.isNumber(delta.output)&&a.number(delta.output).zero,c[0]~" explicit sum "~to!string(k)~": "~s.format(a,u)~" versus "~s.format(a,v)~"; residual "~text.format(a,delta.output));++numeric;
  }
  writeln(c[0],": ",out_);
 }

 // Failed searches cannot poison the next invocation or introduce a
 // division across a singular ratio, a pole, or a real-power branch cut.
 auto owner=Session.open(),a=owner.arena;Syntax scalar;scalar.declare("n:ℕ");auto n=scalar.parse(a,"n");
 foreach(source;["1/(n+1)","sin(n)","powerR(n,1/2)"]){
  AbelSearchStats stats;auto r=sumAbelAntidifference(a,scalar.parse(a,source,Sort.real_),n,stats);
  enforce(r==Term.init,"unsupported primitive accepted");
  enforce(sumAbelAntidifference(a,scalar.parse(a,"n^2",Sort.real_),n)!=Term.init,"failed memo escaped");
 }
 AbelSearchStats budget;
 enforce(sumAbelAntidifference(a,scalar.parse(a,"n^32",Sort.real_),n,budget)==Term.init&&budget.exhausted,"Abel work budget");
 enforce(sumAbelAntidifference(a,scalar.parse(a,"n^2",Sort.real_),n)!=Term.init,"exhausted memo escaped");
 foreach(source;[
  "∑(i:ℕ). [i<n]*(i:ℝ)*q^i",
  "∑(i:ℕ). [i<n]*(i:ℝ)*powerR(-2,i/2)",
  "∑(i:ℕ). [i<n]*(i:ℝ)*exp(a*i)",
  "∑(i:ℕ). (i:ℝ)*powerR(4,-i/2)"
 ]){
  auto o=Session.open();FunctionSyntax s;s.declare("n:ℕ,q:ℝ,a:ℝ");auto r=s.run(o.arena,source);
  enforce(!r.exhausted&&s.format(o.arena,r).indexOf("∑(")>=0,"unchecked candidate: "~source);
 }
 writeln(certificates," certificates; ",numeric," independent prefix checks; ",cycles," closed cycles; 7 rejection checks; 1 budget check");
 return 0;
}
