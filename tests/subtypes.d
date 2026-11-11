module subtype_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce,assertThrown;
import std.algorithm:canFind;
@safe:

private Syntax syntax(){ Syntax s; s.declare("n:ℕ,m:ℕ,k:ℤ,j:ℤ,q:ℚ,r:ℚ,x:ℝ,y:ℝ,z:ℂ,p:𝔹"); return s; }
struct Example{ string name,input,expected; Sort sort; }
Example[] examples(){
	return [
		Example("NaturalHalfBound","n<1/2","n=0",Sort.boolean),
		Example("NaturalHalfIndicator","[n<1/2]=[n=0]","true",Sort.boolean),
		Example("NaturalHalfInterval","1/2<n<3/2","n=1",Sort.boolean),
		Example("NaturalHalfIntervalReverse","n<3/2∧1/2<n","n=1",Sort.boolean),
		Example("NaturalSecondInterval","3/2<n<5/2","n=2",Sort.boolean),
		Example("NaturalClosedInterval","2≤n∧n≤2","n=2",Sort.boolean),
		Example("NaturalClosedIntervalReverse","n≤2∧2≤n","n=2",Sort.boolean),
		Example("NaturalHalfClosedInterval","3/2≤n∧n≤5/2","n=2",Sort.boolean),
		Example("NaturalOneUpper","n<1","n=0",Sort.boolean),
		Example("NaturalOneLower","1≤n","n≠0",Sort.boolean),
		Example("NaturalThirdBound","n<1/3","n=0",Sort.boolean),
		Example("NaturalZeroClosed","0≤n∧n≤0","n=0",Sort.boolean),
		Example("IntegerHalfInterval","1/2<k<3/2","k=1",Sort.boolean),
		Example("IntegerNegativeInterval","-5/2<k<-3/2","k=-2",Sort.boolean),
		Example("IntegerClosedInterval","j≤k∧k≤j","k=j",Sort.boolean),
		Example("IntegerClosedIntervalReverse","k≤j∧j≤k","j=k",Sort.boolean),
		Example("IntegerStrictUpper","k<3","k≤2",Sort.boolean),
		Example("IntegerStrictLower","-3<k","-2≤k",Sort.boolean),
		Example("NaturalStrictUpper","n<3","n≤2",Sort.boolean),
		Example("NaturalStrictLower","2<n","3≤n",Sort.boolean),
		Example("PositiveRealLiteral","real(3)","3",Sort.natural),
		Example("NegativeRealLiteral","real(-3)","-3",Sort.integer),
		Example("RationalRealLiteral","real(3,2)","3/2",Sort.rational),
		Example("PositiveIntegerLiteral","int(3)","3",Sort.natural),
		Example("IntegerRationalLiteral","rat(-3,1)","-3",Sort.integer),
		Example("RealComplexLiteral","complex(3,0)","3",Sort.natural),
		Example("ImaginaryComplexLiteral","complex(0,3)","3*ⅈ",Sort.complex),
		Example("NaturalEmbedding","toℂ(n)","n",Sort.natural),
		Example("IntegerEmbedding","toℂ(k)","k",Sort.integer),
		Example("RationalEmbedding","toℂ(q)","q",Sort.rational),
		Example("RealEmbedding","toℂ(x)","x",Sort.real_),
		Example("NaturalEmbeddedSum","toℝ(n)+toℝ(m)","n+m",Sort.natural),
		Example("IntegerEmbeddedSum","toℝ(k)+toℝ(j)","k+j",Sort.integer),
		Example("RationalEmbeddedSum","toℂ(q)+toℂ(r)","q+r",Sort.rational),
		Example("RealEmbeddedSum","toℂ(x)+toℂ(y)","x+y",Sort.real_),
		Example("NaturalEmbeddedProduct","toℝ(n)*toℝ(m)","n*m",Sort.natural),
		Example("IntegerEmbeddedProduct","toℂ(k)*toℂ(j)","k*j",Sort.integer),
		Example("RationalEmbeddedProduct","toℂ(q)*toℂ(r)","q*r",Sort.rational),
		Example("RealEmbeddedProduct","toℂ(x)*toℂ(y)","x*y",Sort.real_),
		Example("NaturalEmbeddedPower","toℝ(n)^3","n^3",Sort.natural),
		Example("IntegerEmbeddedPower","toℂ(k)^3","k^3",Sort.integer),
		Example("RationalEmbeddedPower","toℂ(q)^3","q^3",Sort.rational),
		Example("RealEmbeddedPower","toℂ(x)^3","x^3",Sort.real_),
		Example("RationalEmbeddedInverse","toℂ(q)⁻¹","q⁻¹",Sort.rational),
		Example("RealEmbeddedInverse","toℂ(x)⁻¹","x⁻¹",Sort.real_),
		Example("NaturalIndexedBase","powCN(3,n)","3^n",Sort.natural),
		Example("IntegerIndexedBase","powCN(k,n)","k^n",Sort.integer),
		Example("RationalIndexedBase","powCN(q,n)","q^n",Sort.rational),
		Example("RealIndexedBase","powCN(x,n)","x^n",Sort.real_),
		Example("RationalIntegerPower","powCZ(q,k)","q^k",Sort.rational),
		Example("RealIntegerPower","powCZ(x,k)","x^k",Sort.real_),
		Example("LiteralIntegerPower","powRZ(3,k)","3^k",Sort.rational),
		Example("NaturalMask","[p]","([p]:ℕ)",Sort.natural),
		Example("IntegerMask","maskR(p,toℝ(k))","[p]*k",Sort.integer),
		Example("RationalMask","maskC(p,toℂ(q))","[p]*q",Sort.rational),
		Example("RealMask","maskC(p,toℂ(x))","[p]*x",Sort.real_),
		Example("EmbeddedNaturalMask","toℂ(([p]:ℕ))","([p]:ℕ)",Sort.natural),
		Example("ComplexMask","maskC(p,z)","[p]*z",Sort.complex),
		Example("EmptyMask","[false]*log(0)","0",Sort.natural),
		Example("MaskedPole","[p]*toℝ(q⁻¹)","[p]*q⁻¹",Sort.rational),
		Example("StrictIndicator","mulC(ⅈ,toℂ([p]))","[p]*ⅈ",Sort.complex),
		Example("ComplexPowerOverload","cpow(z,toℂ(n))","cpow(z,n)",Sort.complex),
		Example("NegativeComplexRoot","cpow(-2,1/3)","cpow(-2,1/3)",Sort.complex),
		Example("NegativeRealRoot","pow(-2,1/3)","pow(-2,1/3)",Sort.real_),
		Example("RealPowerOverload","pow(-2,toℝ(n))","pow(-2,n)",Sort.real_),
		Example("RealPowerArgument","sin(powRN(3,n))","sin(powRN(3,n))",Sort.real_),
		Example("MixedPowerArgument","z*toℂ(powRN(3,n))","z*powRN(3,n)",Sort.complex),
		Example("MixedIntegerPowerArgument","z*toℂ(powRZ(3,k))","z*powRZ(3,k)",Sort.complex),
		Example("RealPartialArgument","sin(toℝ(q⁻¹))","sin(q⁻¹)",Sort.real_),
		Example("ComplexPartialArgument","csqrt(toℂ(sqrt(x)))","csqrt(sqrt(x))",Sort.real_),
		Example("NestedRationalSum","sin(toℝ(q)+toℝ(r))","sin(q+r)",Sort.real_),
		Example("NestedNaturalSum","sin(toℝ(n)+toℝ(m))","sin(n+m)",Sort.real_),
		Example("NestedNaturalDifference","sin(toℝ(n)-toℝ(m))","sin(n-m)",Sort.real_),
		Example("NestedRationalInverse","sin(toℝ(q)⁻¹)","sin(q⁻¹)",Sort.real_),
		Example("NestedComplexRoot","csqrt(toℂ(toℝ(q)+toℝ(r)))","csqrt(q+r)",Sort.complex),
		Example("NestedPartialLog","log(toℝ(q)⁻¹)","-log(q)",Sort.real_),
		Example("NestedMaskedSum","[p]*sin(toℝ(q)+toℝ(r))","[p]*sin(q+r)",Sort.real_),
		Example("NestedComplexSum","z+toℂ(toℝ(q)+toℝ(r))","z+toℂ(q+r)",Sort.complex),
		Example("LargeIntegerPower","int(-2)^16000","2^16000",Sort.natural),
		Example("LargeRationalPower","rat(1,2)^16000","1/(2^16000)",Sort.rational),
		Example("LargePrintableInteger","2^16000","2^16000",Sort.natural),
		Example("LargePositive","10^30","1000000000000000000000000000000",Sort.natural),
		Example("LargeNegative","-(10^30)","-1000000000000000000000000000000",Sort.integer),
		Example("LargeRational","1/(10^30+1)","1/1000000000000000000000000000001",Sort.rational),
		Example("LargeComplex","(10^30)*ⅈ","1000000000000000000000000000000*ⅈ",Sort.complex)
	];
}
unittest{
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=s.parse(a,c.input),want=simplify(a,s.parse(a,c.expected)).output;
		auto fast=simplify(a,input),checked=simplify(a,input,Options(DensityMode.preserve,true));
		enforce(!fast.exhausted&&!checked.exhausted,c.name~" exhausted");
		enforce(fast.output==want,c.name~": "~s.format(a,fast.output)~" != "~s.format(a,want));
		enforce(a.sort(fast.output)==c.sort,c.name~" result sort");
		enforce(fast.output==checked.output,c.name~" traced result");
		enforce(checked.certificate.after==a.castTo(checked.output,a.sort(input)),c.name~" checked embedding");
		enforce(simplify(a,fast.output).output==fast.output,c.name~" idempotence");
		auto printed=s.format(a,fast.output),parsed=s.parse(a,printed);
		foreach(injection;["real(","int(","rat(","nat(","complex(","toℕ(","toℤ(","toℚ(","toℝ(","toℂ("])
			enforce(!printed.canFind(injection),c.name~" printed injection: "~printed);
		enforce(simplify(a,parsed).output==fast.output,c.name~" round-trip: "~printed);
		enforce(simplifyDomain(a,parsed).output==simplifyDomain(a,fast.output).output,c.name~" printed domain: "~printed);
		exportLean(a,checked);
	}
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	auto r=simplify(a,s.parse(a,"real(3)"),Options(DensityMode.preserve,true));
	r.output=a.natural_(4); assertThrown(exportLean(a,r));
	r.output=a.complex(3); assertThrown(exportLean(a,r));
	r.output=a.natural_(3); r.certificate.after=r.output; assertThrown(exportLean(a,r));
	Options options; options.trace=true; options.maxRewrites=0;
	auto t=s.parse(a,"toℂ(n+n)"); r=simplify(a,t,options);
	assert(r.exhausted&&r.output==t); exportLean(a,r);
}
int main(string[] args){
	enforce(args.length==2,"expected certificate directory"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),Options(DensityMode.preserve,true))));
	}
	writeln("Exported ",examples().length," subtype certificates."); return 0;
}
