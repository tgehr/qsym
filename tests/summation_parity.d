module summation_parity_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
import std.conv:to;
@safe:
private struct Case{string name,input,expected,proof;}
private Case[] cases(){return [
 Case("AffineTail","∑(i:ℤ). [-3≤i]*(1/2)^(3*i+2)","1024/7"),
 Case("AffineLinearTail","∑(i:ℤ). [-3≤i]*(i+2)*(1/2)^(2*i+1)","-256/9"),
 Case("AffineFinite","∑(i:ℤ). [-3≤i]*[i≤5]*(1/2)^(3*i+2)","19173961/131072"),
 Case("RationalAffineTail","∑(i:ℤ). [-3≤i]*(1/2:ℚ)^(3*i+2)","(1024/7:ℚ)"),
 Case("ComplexAffineTail","∑(i:ℤ). [-3≤i]*(1/2:ℂ)^(3*i+2)","(1024/7:ℂ)"),
 Case("RealLowerBound","∑(i:ℤ). [a≤i]*(1/2)^i","2*(1/2)^ceil(a)"),
 Case("RepeatedExclusions","∑(i:ℤ). [-3≤i]*[i≠2]*[i≠4]*i/2^i","-131/4"),
 Case("ProductMasks","∑(i:ℤ). ([0≤i]*[i≤2]+[4≤i]*[i≤5])*i","12"),
 Case("ProductMasksRight","∑(i:ℤ). i*([0≤i]*[i≤2]+[4≤i]*[i≤5])","12"),
 Case("PiecewiseTail","∑(i:ℕ). ([i<4]*i+[4≤i]*i^2)*(1/2)^i","19/4"),
 Case("ExcludedNoninteger","∑(i:ℤ). [0≤i]*[i≠3/2]*(1/2)^i","2"),
 Case("ExcludedInteger","∑(i:ℤ). [0≤i]*[i≠2]*(1/2)^i","7/4"),
 Case("EmptyRealInterval","∑(i:ℤ). [3/2≤i]*[i≤7/4]*i","(0:ℤ)"),
 Case("UndefinedBound","defined(∑(i:ℤ). [1/0≤i]*[i≤5]*i)","false"),
 Case("UndefinedSelector","defined(∑(i:ℤ). [i=1/0]*i)","false"),
 Case("ZeroBaseFinite","∑(i:ℕ). [i<n]*(i:ℝ)^0*(0:ℝ)^i","[n≠0]"),
 Case("DivergentCancellation","∑(i:ℕ). (2:ℝ)^i-(2:ℝ)^i","0")
];}
int main(string[] args){
	enforce(args.length==2);mkdirRecurse(args[1]);uint failed;
	foreach(c;cases())try{
		auto owner=Session.open(),a=owner.arena;FunctionSyntax s;s.declare("n:ℕ,a:ℝ,b:ℝ,x:ℝ,q:ℝ,f:ℤ→ℝ");
		auto r=s.run(a,c.input,[],Options(DensityMode.preserve,true)),e=s.run(a,c.expected),out_=s.format(a,r),want=s.format(a,e);
		bool equal(FunctionResult x,FunctionResult y){
			if(s.format(a,x)==s.format(a,y))return true;
			if(!(x.scalarOnly||x.lowered)||!(y.scalarOnly||y.lowered))return false;
			auto u=x.scalar.output,v=y.scalar.output;if(a.sort(u)==Sort.boolean||a.sort(v)==Sort.boolean)return false;
			auto sort=a.sort(u)==Sort.complex||a.sort(v)==Sort.complex?Sort.complex:Sort.real_;
			auto opts=Options(DensityMode.preserve,true);opts.expandPowers=true;opts.expandScalarEmbeddings=true;
			auto check=simplify(a,a.equal(a.castTo(u,sort),a.castTo(v,sort)),[],opts);return !check.exhausted&&check.output==a.boolean(true);
		}
		enforce(!r.exhausted&&!e.exhausted&&equal(r,e),c.name~": "~out_~"; expected "~want);
		auto fast=s.run(a,c.input),again=s.run(a,out_);enforce(!fast.exhausted&&!again.exhausted&&s.format(a,fast)==out_&&equal(r,again),c.name~" repeat");
		auto code=s.exportCertificate(a,r);if(c.proof.length)enforce(code.indexOf(c.proof)>=0,c.name~" missing proof");
		write(buildPath(args[1],c.name~".lean"),code);writeln(c.name,": ",out_);
	}catch(Exception e){++failed;writeln("FAILED ",c.name,": ",e.msg);}
	enforce(failed==0,to!string(failed)~" parity cases failed");

 uint symbolic;
 string[2][] shapes=[
  ["RealInterval","∑(i:ℤ). [a≤i]*[i≤b]*i"],
  ["AffineInterval","∑(i:ℤ). [a≤3*i+2]*[3*i+2≤b]*i"],
  ["RealSelector","∑(i:ℤ). [i=x]*(i+1)"],
  ["AffineSelector","∑(i:ℤ). [2*i=x]*(i+1)"],
  ["RealExclusion","∑(i:ℤ). [0≤i]*[i≠x]*(1/2)^i"]];
 foreach(c;shapes){
  auto o=Session.open();FunctionSyntax s;s.declare("a:ℝ,b:ℝ,x:ℝ");
  auto r=s.run(o.arena,c[1],[],Options(DensityMode.preserve,true));
  enforce(!r.exhausted&&s.format(o.arena,r).indexOf("∑(")<0,c[0]~": "~s.format(o.arena,r));
  write(buildPath(args[1],c[0]~".lean"),s.exportCertificate(o.arena,r));++symbolic;
 }
 foreach(c;[["PartialLinearityRight","∑(i:ℤ). [0≤i]*f(i)+[0≤i]*(1/2)^i"],
            ["PartialLinearity","∑(i:ℤ). [0≤i]*(1/2)^i+[0≤i]*f(i)"],
            ["PartialFiniteLinearity","∑(i:ℤ). [0≤i]*[i<n]*i+[0≤i]*[i<n]*f(i)"]]){
  auto o=Session.open();FunctionSyntax s;s.declare("n:ℕ,f:ℤ→ℝ");
  auto r=s.run(o.arena,c[1],[],Options(DensityMode.preserve,true));
  auto code=s.exportCertificate(o.arena,r);
  enforce(!r.exhausted&&code.indexOf("SummationLinearity.add_known")>=0,c[0]);
  write(buildPath(args[1],c[0]~".lean"),code);
 }
 uint checks;
 void numeric(string source,Rational expected){
  auto o=Session.open();FunctionSyntax s;auto r=s.run(o.arena,source);
  enforce(!r.exhausted&&(r.scalarOnly||r.lowered)&&o.arena.isNumber(r.scalar.output)&&o.arena.number(r.scalar.output)==Number(expected),source~": "~s.format(o.arena,r));++checks;
 }
 foreach(lo;-5..6)foreach(hi;-5..6){
  long total;
  foreach(i;-8..9)if(lo<=2*i&&2*i<=hi)total+=i;
  numeric("∑(i:ℤ). ["~to!string(lo)~"/2≤i]*[i≤"~to!string(hi)~"/2]*i",Rational(total));
 }
 foreach(x;-8..9){
  auto value=x%2==0?Rational(x/2+1):Rational(0);
  numeric("∑(i:ℤ). [i="~to!string(x)~"/2]*(i+1)",value);
  value=x%4==0?Rational(x/4+1):Rational(0);
  numeric("∑(i:ℤ). [2*i="~to!string(x)~"/2]*(i+1)",value);
 }
 // Infinite symbolic ratios still require a convergence proof. Finite
 // weighted symbolic ratios are covered by weighted_summation.d.
 foreach(source;["∑(i:ℕ). (i:ℝ)*q^i","∑(i:ℤ). [-3≤i]*[i^2+1<n]*i"]){
  auto o=Session.open();FunctionSyntax s;s.declare("n:ℕ,q:ℝ");auto r=s.run(o.arena,source);
  enforce(!r.exhausted&&s.format(o.arena,r).indexOf("∑(")>=0,"unchecked symbolic ratio");
 }
 writeln(cases().length," exact cases; ",symbolic," symbolic families; 3 partial linearity certificates; ",checks," independent numeric checks; 1 unsupported-ratio check; 1 nonlinear-bound check");return 0;
}
