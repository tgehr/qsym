module summation_tail_tests;
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
	Case("SymbolicRatio","∑(i:ℕ). [3≤i]*q^i","guard(-1<q∧q<1,q^3/(1-q))","Summation.geometric_shift_guard"),
	Case("DivergentTail","defined(∑(i:ℕ). [3≤i]*(2:ℝ)^i)","false"),
	Case("AlternatingTail","defined(∑(i:ℕ). [3≤i]*(-1:ℝ)^i)","false"),
	Case("RealTail","∑(i:ℕ). [3≤i]*(1/2)^i","1/4","Summation.tailN_value"),
	Case("StrictTail","∑(i:ℕ). [3<i]*(1/2)^i","1/8","Summation.tailN_value"),
	Case("ReversedComparison","∑(i:ℕ). [i≥3]*(1/2)^i","1/4"),
	Case("ZeroCutoff","∑(i:ℕ). [0≤i]*(1/2)^i","2"),
	Case("RationalTail","∑(i:ℕ). [3≤i]*(1/2:ℚ)^i","(1/4:ℚ)"),
	Case("ComplexTail","∑(i:ℕ). [3≤i]*(1/2:ℂ)^i","(1/4:ℂ)"),
	Case("NonrealTail","∑(i:ℕ). [2≤i]*(ⅈ/2)^i","-1/5-ⅈ/10"),
	Case("NegativeRatio","∑(i:ℕ). [3≤i]*(-1/2)^i","-1/12"),
	Case("LinearTail","∑(i:ℕ). [3≤i]*(i:ℝ)*(1/2)^i","1"),
	Case("SquareTail","∑(i:ℕ). [3≤i]*(i:ℝ)^2*(1/2)^i","9/2"),
	Case("CubicTail","∑(i:ℕ). [3≤i]*(i:ℝ)^3*(1/2)^i","47/2"),
	Case("TwoRatios","∑(i:ℕ). [3≤i]*((1/2)^i+(1/3)^i)","11/36"),
	Case("SymbolicCutoff","∑(i:ℕ). [n≤i]*(1/2)^i","2*(1/2)^n"),
	Case("SymbolicStrict","∑(i:ℕ). [n<i]*(1/2)^i","(1/2)^n"),
	Case("LambdaCutoff","λ(k:ℕ). ∑(i:ℕ). [k≤i]*(1/2)^i","λ(k:ℕ). (2*(1/2)^k:ℝ)"),
	Case("UndefinedBound","defined(∑(i:ℕ). [(0 sub 1)≤i]*(1/2)^i)","false"),
	Case("UndefinedStrictBound","defined(∑(i:ℕ). [(0 sub 1)<i]*(1/2)^i)","false"),
	Case("UndefinedBoundZero","defined(∑(i:ℕ). [(0 sub 1)≤i]*(0:ℝ))","false"),
	Case("UndefinedSelected","defined(∑(i:ℕ). [3≤i]*(1/0))","false"),
	Case("FalseMask","[false]*(∑(i:ℕ). [(0 sub 1)≤i]*(1/2)^i)","0"),
	Case("ConstantDivergence","defined(∑(i:ℕ). [3≤i]*(1:ℝ))","false"),
	Case("ZeroNatural","∑(i:ℕ). [3≤i]*(0:ℕ)","0"),
	Case("ZeroInteger","∑(i:ℕ). [3≤i]*(0:ℤ)","(0:ℤ)"),
	Case("ZeroComplex","∑(i:ℕ). [3≤i]*(0:ℂ)","(0:ℂ)"),
	Case("ZeroRatio","∑(i:ℕ). [3≤i]*(0:ℝ)^i","0"),
	Case("ZeroRatioOrigin","∑(i:ℕ). [0≤i]*(0:ℝ)^i","1"),
	Case("ZeroRatioStrict","∑(i:ℕ). [0<i]*(0:ℝ)^i","0"),
	Case("UndefinedBelow","∑(i:ℕ). [1≤i]*(0:ℝ)^i/(i:ℝ)","0"),
	Case("OpaqueFunction","∑(i:ℕ). [n≤i]*f(i)","∑(i:ℕ). f(i+n)","Summation.tailN_value"),
	Case("OpaqueStrict","∑(i:ℕ). [n<i]*f(i)","∑(i:ℕ). f(i+(n+1))","Summation.tailN_value")
];}
int main(string[] args){
	enforce(args.length==2);mkdirRecurse(args[1]);uint failed;
	foreach(c;cases())try{
		auto owner=Session.open(),a=owner.arena;FunctionSyntax s;s.declare("n:ℕ,q:ℝ,f:ℕ→ℝ");
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
	enforce(failed==0,to!string(failed)~" tail cases failed");
	foreach(source;["∑(i:ℕ). [3≤i]/(i+1)","∑(i:ℕ). [3≤i]*(-1:ℝ)^i/(i+1)"]){
		auto o=Session.open();FunctionSyntax s;s.declare("q:ℝ");auto r=s.run(o.arena,source);enforce(!r.exhausted&&s.format(o.arena,r).indexOf("∑(")>=0,"unchecked convergence");
	}
	uint checks;
	foreach(q;[Rational(1)/Rational(2),-Rational(1)/Rational(2)])foreach(d;0..4)foreach(k;[0,1,3,6]){
		auto one=Rational(1),den=one-q,total=one/den;
		if(d==1)total=q/(den*den);if(d==2)total=q*(one+q)/(den*den*den);if(d==3)total=q*(one+Rational(4)*q+q*q)/(den*den*den*den);
		auto power=one;foreach(i;0..k){auto c=one;foreach(j;0..d)c=c*Rational(i);total=total-c*power;power=power*q;}
		auto o=Session.open();FunctionSyntax s;auto source="∑(i:ℕ). ["~to!string(k)~"≤i]*(i:ℝ)^"~to!string(d)~"*("~to!string(q)~")^i";auto r=s.run(o.arena,source);
		enforce(!r.exhausted&&(r.scalarOnly||r.lowered)&&o.arena.isNumber(r.scalar.output)&&o.arena.number(r.scalar.output)==Number(total),"numeric tail: "~source~" -> "~s.format(o.arena,r));++checks;
	}
	writeln(cases().length," tail cases; ",checks," exact numeric checks; 2 unresolved convergence checks");return 0;
}
