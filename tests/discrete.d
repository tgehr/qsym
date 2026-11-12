module discrete_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
import std.algorithm:startsWith;
@safe:

struct Example{ string name,input,expected; }
Example[] examples(){
	Example[] result;
	foreach(vars;[["Natural","n","m","l","nat(0)","nat(1)"],
		["Integer","i","j","k","int(0)","int(1)"],
		["Rational","q","r","s","rat(0,1)","rat(1,1)"]]){
		auto x=vars[1],y=vars[2],z=vars[3];
		void add(string name,string input,string expected){ result~=Example(vars[0]~name,input,expected); }
		add("Double",x~"+"~x,"2*"~x);
		add("Collect","2*"~x~"+3*"~x,"5*"~x);
		add("CollectLeft",x~"+3*"~x,"4*"~x);
		add("CollectRight","3*"~x~"+"~x,"4*"~x);
		add("NestedCoefficient","2*(3*"~x~")","6*"~x);
		add("RepeatedCoefficient","2*(3*(4*"~x~"))","24*"~x);
		add("CommutedDouble",x~"*"~y~"+"~y~"*"~x,"2*("~x~"*"~y~")");
		add("FactorLeft",x~"*"~y~"+"~x~"*"~z,x~"*("~y~"+"~z~")");
		add("FactorRight",x~"*"~z~"+"~y~"*"~z,"("~x~"+"~y~")*"~z);
		add("FactorCrossLeft",x~"*"~y~"+"~z~"*"~x,x~"*("~y~"+"~z~")");
		add("FactorCrossRight",x~"*"~y~"+"~y~"*"~z,"("~x~"+"~z~")*"~y);
		add("FactorMasked","[p]*("~x~"*"~y~"+"~x~"*"~z~")","[p]*("~x~"*("~y~"+"~z~"))");
		add("FactorMaskedZero","[false]*("~x~"*"~y~"+"~x~"*"~z~")",vars[4]);
		add("NewProductSquare","("~x~"*"~y~")^2",x~"^2*"~y~"^2");
		add("NewProductCube","("~x~"*"~y~")^3",x~"^3*"~y~"^3");
		add("NewProductNested","("~x~"*("~y~"*"~z~"))^4",x~"^4*("~y~"^4*"~z~"^4)");
		add("NewProductCoefficient","(2*"~x~")^3","8*"~x~"^3");
		add("NewProductMasked","[p]*(("~x~"*"~y~")^2)","[p]*("~x~"^2*"~y~"^2)");
		add("NewProductFalseMask","[false]*(("~x~"*"~y~")^3)",vars[4]);
		add("NewProductZeroExponent","("~x~"*"~y~")^0",vars[5]);
		add("Square",x~"*"~x,x~"^2");
		add("PowerProduct",x~"^3*"~x~"^4",x~"^7");
		add("PowerLeft",x~"*"~x~"^3",x~"^4");
		add("PowerRight",x~"^3*"~x,x~"^4");
		add("PowerChain","("~x~"^2)^3",x~"^6");
		add("PowerRepeated","("~x~"*"~x~")*("~x~"*"~x~")",x~"^4");
		add("ZeroPowerProduct",x~"^0*"~x~"^3",x~"^3");
		add("NonzeroProduct",x~"*"~y~"≠0",x~"≠0∧"~y~"≠0");
		add("NonzeroPower",x~"^3≠0",x~"≠0");
		add("StrictSelf",x~"<"~x,"false");
		add("WeakSelf",x~"≤"~x,"true");
		add("StrictCommon",x~"+"~y~"<"~x~"+"~z,y~"<"~z);
		add("WeakCommon",x~"+"~y~"≤"~x~"+"~z,y~"≤"~z);
		add("StrictCommonConstants",x~"+1<"~x~"+2","true");
		add("WeakCommonConstants",x~"+2≤"~x~"+1","false");
		add("MaskedCollection","[p]*(2*"~x~"+3*"~x~")","[p]*(5*"~x~")");
		add("MaskedZero","[false]*("~x~"^3*"~x~"^4)",vars[4]);
		add("GuardZero","[p]*"~vars[4],vars[4]);
		add("PartialGuardZero","[log(x)<0]*"~vars[4],vars[4]);
		add("UndefinedGuardZero","[log(0)<0]*"~vars[4],vars[4]);
		add("ZeroPower","("~x~"^2)^0",vars[5]);
	}
	result~=[
		Example("OffsetNaturalZeroDifference","2*n-1=-1","n=0"),
		Example("OffsetNaturalZeroReversed","0=-2*n","n=0"),
		Example("OffsetNaturalZeroPositive","2*n+3=3","n=0"),
		Example("OffsetNaturalProductZero","n*m+1=1","n=0∨m=0"),
		Example("OffsetNaturalPowerZero","n^3+1=1","n=0"),
		Example("OffsetNaturalSumZero","n+m+1=1","n=0∧m=0"),
		Example("OffsetNaturalProductNonzero","n*m+1≠1","n≠0∧m≠0"),
		Example("OffsetNaturalPowerNonzero","n^3+1≠1","n≠0"),
		Example("OffsetNaturalSumNonzero","n+m+1≠1","n≠0∨m≠0"),
		Example("OffsetNaturalZeroNe","2*n-1≠-1","n≠0"),
		Example("DirectNaturalProduct","nonzeroN(n*m)","n≠0∧m≠0"),
		Example("DirectNaturalPower","nonzeroN(n^3)","n≠0"),
		Example("DirectNaturalSum","nonzeroN(n+m)","n≠0∨m≠0"),
		Example("DirectNaturalZeroPower","nonzeroN(n^0)","true"),
		Example("DirectNaturalZeroFactor","nonzeroN(n*0)","false"),
		Example("DirectNaturalPositiveSum","nonzeroN(n+m+1)","true"),
		Example("DirectNaturalPositiveProduct","nonzeroN(n*m+1)","true"),
		Example("DirectNaturalMaskedUndefined","false∧nonzeroN([log(0)<0]*(n*m))","false"),
		Example("OffsetInteger0","2*i+1=5","i=2"),
		Example("OffsetInteger1","1+2*i=5","i=2"),
		Example("OffsetInteger2","5=2*i+1","i=2"),
		Example("OffsetInteger3","5=1+2*i","i=2"),
		Example("OffsetInteger4","2*i+1=4","false"),
		Example("OffsetInteger5","1+2*i=4","false"),
		Example("OffsetInteger6","2*i+2=4","i=1"),
		Example("OffsetInteger7","(2*i+1)+2=7","i=2"),
		Example("OffsetInteger8","(1+2*i)+2=7","i=2"),
		Example("OffsetInteger9","2*(i+1)=4","i=1"),
		Example("OffsetInteger10","2*(1+i)=4","i=1"),
		Example("OffsetInteger11","2*i+1≠5","i≠2"),
		Example("OffsetInteger12","2*i+1≠4","true"),
		Example("OffsetInteger13","0*i+1=1","true"),
		Example("OffsetInteger14","0*i+1=2","false"),
		Example("OffsetInteger15","2*i+3=1","i=-1"),
		Example("OffsetNatural0","2*n+1=5","n=2"),
		Example("OffsetNatural1","1+2*n=5","n=2"),
		Example("OffsetNatural2","5=2*n+1","n=2"),
		Example("OffsetNatural3","5=1+2*n","n=2"),
		Example("OffsetNatural4","2*n+1=4","false"),
		Example("OffsetNatural5","1+2*n=4","false"),
		Example("OffsetNatural6","2*n+2=4","n=1"),
		Example("OffsetNatural7","(2*n+1)+2=7","n=2"),
		Example("OffsetNatural8","(1+2*n)+2=7","n=2"),
		Example("OffsetNatural9","2*(n+1)=4","n=1"),
		Example("OffsetNatural10","2*(1+n)=4","n=1"),
		Example("OffsetNatural11","2*n+1≠5","n≠2"),
		Example("OffsetNatural12","2*n+1≠4","true"),
		Example("OffsetNatural13","0*n+1=1","true"),
		Example("OffsetNatural14","0*n+1=2","false"),
		Example("OffsetNatural15","2*n+3=1","false"),
		Example("OffsetFloor","2*floor(x)+1=5","2≤x∧x<3"),
		Example("OffsetFloorImpossible","2*floor(x)+1=4","false"),
		Example("OffsetFloorCommuted","1+2*floor(x)=5","2≤x∧x<3"),
		Example("OffsetCeiling","2*ceil(x)+1=5","1<x∧x≤2"),
		Example("OffsetRound","2*round(x)+1=5","3/2≤x∧x<5/2"),
		Example("OffsetNegativeCoefficient","-2*i+1=5","i=-2"),
		Example("OffsetPartial","2*floor(log(x))+1=5","2≤log(x)∧log(x)<3"),
		Example("OffsetMaskedUndefined","false∧(2*floor(log(0))+1=5)","false"),

		Example("LinearNaturalDivisible","2*n=4","n=2"),
		Example("LinearNaturalNondivisible","2*n=5","false"),
		Example("LinearNaturalRightCoeff","n*2=4","n=2"),
		Example("LinearNaturalReversed","4=2*n","n=2"),
		Example("LinearNaturalNegative","2*n=-4","false"),

		Example("LinearIntegerDivisible","2*i=4","i=2"),
		Example("LinearIntegerNondivisible","2*i=5","false"),
		Example("LinearIntegerKnownOne","2*i=2","i=1"),
		Example("LinearIntegerNegativeCoeff","-2*i=4","i=-2"),
		Example("LinearIntegerNegativeRhs","2*i=-4","i=-2"),
		Example("LinearIntegerRightCoeff","i*2=4","i=2"),
		Example("LinearIntegerReversed","4=2*i","i=2"),
		Example("LinearIntegerUnequal","2*i≠5","true"),
		Example("LinearFloorDivisible","2*floor(x)=4","2≤x∧x<3"),
		Example("LinearFloorNondivisible","2*floor(x)=3","false"),
		Example("LinearFloorKnownOne","2*floor(x)=2","1≤x∧x<2"),
		Example("LinearFloorPartial","2*floor(log(x))=4","2≤log(x)∧log(x)<3"),
		Example("LinearIntegerZero","0*i=4","false"),
		Example("LinearIntegerZeroBoth","0*i=0","true"),

		Example("NaturalCollectNested","n+(m+n)","2*n+m"),
		Example("IntegerCollectNested","i+(j+i)","2*i+j"),
		Example("IntegerCommutedSum","(i+j)-(j+i)","int(0)"),
		Example("IntegerOppositeDifference","(i-j)+(j-i)","int(0)"),
		Example("RationalCollectNested","q+(r+q)","2*q+r"),
		Example("RationalCommutedSum","(q+r)-(r+q)","rat(0,1)"),
		Example("RationalOppositeDifference","(q-r)+(r-q)","rat(0,1)"),
		Example("PartialNestedCollection","q⁻¹+(r+q⁻¹)","2*q⁻¹+r"),
		Example("PartialCommutedSum","(floor(log(x))+i)-(i+floor(log(x)))","int(0)"),
		Example("PartialOppositeDifference","(q⁻¹-r)+(r-q⁻¹)","rat(0,1)"),
		Example("MaskedCommutedSum","[false]*((q⁻¹+r)-(r+q⁻¹))","rat(0,1)"),
		Example("RationalDenominatorLeft","q/(q*r)","r⁻¹"),
		Example("RationalDenominatorRight","q/(r*q)","r⁻¹"),
		Example("RationalCommutedQuotient","(q*r)/(r*q)","rat(1,1)"),
		Example("RationalReciprocalQuotients","(q/r)*(r/q)","rat(1,1)"),
		Example("RationalPartialDenominator","q⁻¹/(q⁻¹*r)","r⁻¹"),
		Example("RationalPartialCommutedQuotient","(q⁻¹*r)/(r*q⁻¹)","rat(1,1)"),
		Example("RationalGuardedDenominator","[q≠0]*(q/(q*r))","[q≠0]*r⁻¹"),
		Example("RationalGuardedReciprocal","[q≠0∧r≠0]*((q/r)*(r/q))","[q≠0∧r≠0]*rat(1,1)"),
		Example("RationalMaskedDenominator","[false]*(q/(q*r))","rat(0,1)"),
		Example("RationalZeroDenominatorNumerator","rat(0,1)/(rat(0,1)*r)","rat(0,1)"),
		Example("RationalMaskedReciprocal","[false]*((q/r)*(r/q))","rat(0,1)"),
		Example("RationalUnequalDenominator","q/(r*s)","q*(r⁻¹*s⁻¹)"),
		Example("FactorPartialRational","q⁻¹*r+q⁻¹*s","q⁻¹*(r+s)"),
		Example("FactorPartialInteger","floor(log(x))*i+floor(log(x))*j","floor(log(x))*(i+j)"),
		Example("FactorPartialNatural","denominator(qfromnd(i,0))*n+denominator(qfromnd(i,0))*m","denominator(qfromnd(i,0))*(n+m)"),
		Example("FactorGuardedRational","[q≠0]*(q⁻¹*r+q⁻¹*s)","[q≠0]*(q⁻¹*(r+s))"),
		Example("FactorDifferentProducts","n*m+l*l","n*m+l^2"),

		Example("NewIntegerNegativePower2","(-i)^2","i^2"),
		Example("NewIntegerNegativePower3","(-i)^3","-i^3"),
		Example("NewIntegerNegativePower4","(-i)^4","i^4"),
		Example("NewIntegerNegativePower5","(-i)^5","-i^5"),
		Example("NewRationalNegativePower2","(-q)^2","q^2"),
		Example("NewRationalNegativePower3","(-q)^3","-q^3"),
		Example("NewRationalNegativePower4","(-q)^4","q^4"),
		Example("NewRationalNegativePower5","(-q)^5","-q^5"),
		Example("NewRationalInverseProduct","(q*r)⁻¹","q⁻¹*r⁻¹"),
		Example("NewRationalInverseCube","(q^3)⁻¹","(q⁻¹)^3"),
		Example("NewRationalPowerDivBase","q^4/q","q^3"),
		Example("NewRationalBaseDivPower","q/q^4","(q⁻¹)^3"),
		Example("NewRationalPowerDivPartial","(q⁻¹)^4/q⁻¹","(q⁻¹)^3"),
		Example("NewRationalInverseProductGuard","[q≠0∧r≠0]*((q*r)⁻¹)","[q≠0∧r≠0]*(q⁻¹*r⁻¹)"),
		Example("NewRationalPowerDivGuard","[q≠0]*(q^4/q)","[q≠0]*q^3"),
		Example("NewRationalMaskedPole","[false]*((q*rat(0,1))⁻¹)","rat(0,1)"),
		Example("NewRationalProductPartial","(q⁻¹*r)^2","(q⁻¹)^2*r^2"),
		Example("NewIntegerProductPartial","(floor(log(x))*i)^2","floor(log(x))^2*i^2"),
		Example("NewNaturalProductPartial","(denominator(qfromnd(i,0))*n)^2","denominator(qfromnd(i,0))^2*n^2"),
		Example("NewRationalDifferentPower","q^3/r","q^3/r"),

		Example("IntegerCancelLast","(i+j)-j","i"),
		Example("IntegerCancelFirst","(i+j)-i","j"),
		Example("IntegerSubAdd","(i-j)+j","i"),
		Example("IntegerAddSub","i+(j-i)","j"),
		Example("RationalCancelLast","(q+r)-r","q"),
		Example("RationalCancelFirst","(q+r)-q","r"),
		Example("RationalSubAdd","(q-r)+r","q"),
		Example("RationalAddSub","q+(r-q)","r"),
		Example("PartialFloorCancelLast","(floor(log(x))+floor(x))-floor(x)","floor(log(x))"),
		Example("PartialFloorCancelFirst","(floor(log(x))+floor(x))-floor(log(x))","floor(x)"),
		Example("PartialFloorSubAdd","(floor(log(x))-floor(x))+floor(x)","floor(log(x))"),
		Example("PartialFloorAddSub","floor(log(x))+(floor(x)-floor(log(x)))","floor(x)"),
		Example("PartialRationalCancelLast","(q⁻¹+r)-r","q⁻¹"),
		Example("PartialRationalCancelFirst","(q⁻¹+r)-q⁻¹","r"),
		Example("PartialRationalSubAdd","(q⁻¹-r)+r","q⁻¹"),
		Example("PartialRationalAddSub","q⁻¹+(r-q⁻¹)","r"),
		Example("RationalNestedLeft","q*(r/q)","r"),
		Example("RationalNestedRight","q*(q⁻¹*r)","r"),
		Example("RationalInverseNested","q⁻¹*(q*r)","r"),
		Example("RationalInverseNestedRight","q⁻¹*(r*q)","r"),
		Example("RationalPartialNested","q⁻¹*(r/q⁻¹)","r"),
		Example("RationalGuardedNested","[q≠0]*(q*(r/q))","[q≠0]*r"),
		Example("RationalMaskedNested","[false]*(q*(r/q))","rat(0,1)"),
		Example("RationalZeroNested","rat(0,1)*(r/rat(0,1))","rat(0,1)"),
		Example("FloorUnitDifference","floor(x+1)-floor(x)","int(1)"),
		Example("CeilingUnitDifference","ceil(x+1)-ceil(x)","int(1)"),
		Example("FloorPartialShiftDifference","floor(log(x)+3)-floor(log(x))","int(3)"),
		Example("CeilingNegativeShiftDifference","ceil(x-2)-ceil(x)","int(-2)"),
		Example("IntegerCancellation","i-i","int(0)"),
		Example("IntegerNegativeCancellation","-i+i","int(0)"),
		Example("IntegerDoubleNegation","-(-i)","i"),
		Example("IntegerNegativeCollection","2*i-3*i","-i"),
		Example("RationalCancellation","q-q","rat(0,1)"),
		Example("RationalNegativeCancellation","-q+q","rat(0,1)"),
		Example("RationalDoubleNegation","-(-q)","q"),
		Example("RationalFractionalCollection","rat(1,2)*q+rat(1,3)*q","rat(5,6)*q"),
		Example("RationalSelfDivision","q/q","rat(1,1)"),
		Example("RationalInverseProduct","q⁻¹*q","rat(1,1)"),
		Example("RationalInverseNonzero","q⁻¹≠0","true"),
		Example("RationalCancelFactor","(q*r)/q","r"),
		Example("RationalCancelRightFactor","(q*r)/r","q"),
		Example("RationalGuardedCancellation","[q≠0]*(q/q)","[q≠0]*rat(1,1)"),
		Example("RationalMaskedUndefined","[false]*(q/rat(0,1))","rat(0,1)"),
		Example("RationalPartialCancellation","q⁻¹-q⁻¹","rat(0,1)"),
		Example("RationalPartialPower","(q⁻¹)^3*(q⁻¹)^4","(q⁻¹)^7"),
		Example("FloorCeilingCancellation","floor(x)+ceil(-x)","int(0)"),
		Example("CeilingFloorCancellation","ceil(x)+floor(-x)","int(0)"),
		Example("FloorCollection","2*floor(x)+3*floor(x)","5*floor(x)"),
		Example("FloorPartialCancellation","floor(log(x))-floor(log(x))","int(0)"),
		Example("FloorPartialComparison","floor(log(x))<floor(log(x))","false"),
		Example("FloorPowerProduct","floor(x)^2*floor(x)^3","floor(x)^5"),
		Example("NaturalPartialCancellation","denominator(qfromnd(i,0))<denominator(qfromnd(i,0))","false"),
		Example("NaturalPartialPower","denominator(qfromnd(i,0))^3*denominator(qfromnd(i,0))^4","denominator(qfromnd(i,0))^7"),
		Example("GuardedFloorPartial","[x>0]*(floor(log(x))-floor(log(x)))","int(0)"),
		Example("IntegerWrongPowerUnchanged","i^2","i^2"),
		Example("RationalPoleUnchanged","rat(0,1)⁻¹","rat(0,1)⁻¹")
	];
	return result;
}
private Syntax syntax(){ Syntax s; s.declare("n:ℕ,m:ℕ,l:ℕ,i:ℤ,j:ℤ,k:ℤ,q:ℚ,r:ℚ,s:ℚ,x:ℝ,p:𝔹"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=s.parse(a,c.input),expected=c.input==c.expected?input:simplify(a,s.parse(a,c.expected,a.sort(input))).output;
		auto fast=simplify(a,input),checked=simplify(a,input,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected),fast.exhausted?" (exhausted)":""); ++failures;
		}
		assert(promotes(a.sort(fast.output),a.sort(input)),c.name~" changed type");
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output).output==fast.output,c.name~" is not idempotent");
		if(c.name.startsWith("Offset","DirectNatural")){
			auto roundtrip=simplify(a,s.parse(a,s.format(a,fast.output)));
			assert(!roundtrip.exhausted&&roundtrip.output==fast.output,c.name~" round trip");
		}
		exportLean(a,checked);
	}
	assert(!failures,"discrete scalar regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena;
	foreach(s;[Sort.natural,Sort.integer,Sort.rational]){
		auto x=a.variable(s,0),large=a.pow(x,uint.max);
		foreach(t;[a.mul(large,x),a.mul(x,large),a.mul(large,large),a.pow(large,2)]){
			auto fast=simplify(a,t),checked=simplify(a,t,Options(DensityMode.preserve,true));
			assert(fast.exhausted&&fast.output==t,"oversized exponent must leave the term intact");
			assert(checked.exhausted&&checked.output==t);
			exportLean(a,checked);
		}
		auto boundary=a.mul(a.pow(x,uint.max-1),x);
		auto r=simplify(a,boundary);
		assert(!r.exhausted&&r.output==large,"largest supported exponent");
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: discrete-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length," discrete scalar certificates.");
}
