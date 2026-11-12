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
	foreach(vars;[["Natural","n"],["Integer","i"],["Rational","q"],["Complex","z"]]){
		auto x=vars[1];
		void add(string name,string input,string expected){ result~=Example("MaskZero"~vars[0]~name,input,expected); }
		add("Zero","[p]*"~x~"=0","¬p∨"~x~"=0");
		add("Nonzero","[p]*"~x~"≠0","p∧"~x~"≠0");
		add("Negated","[¬p]*"~x~"≠0","¬p∧"~x~"≠0");
		add("Nested","[p]*([p]*"~x~")≠0","p∧"~x~"≠0");
		add("False","[false]*"~x~"≠0","false");
		add("True","[true]*"~x~"≠0",x~"≠0");
		add("ZeroOperand","[p]*(0*"~x~")≠0","false");
		add("ZeroEquality","[false]*"~x~"=0","true");
		add("UndefinedGuardZero","[log(0)<0]*(0*"~x~")≠0","false");
		add("FalseUndefined","false∧([log(0)<0]*"~x~"≠0)","false");
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
	result~=Example("ComplexMasksinArg0","sin([p]*(z))","[p]*sin(z)");
	result~=Example("ComplexMasksinArg1","sin([p]*(complex(0,0)))","[p]*sin(complex(0,0))");
	result~=Example("ComplexMasksinArg2","sin([p]*(complex(1,0)))","[p]*sin(complex(1,0))");
	result~=Example("ComplexMasksinArg3","sin([p]*(complex(-1,0)))","[p]*sin(complex(-1,0))");
	result~=Example("ComplexMasksinArg4","sin([p]*(complex(0,1)))","[p]*sin(complex(0,1))");
	result~=Example("ComplexMasksinArg5","sin([p]*(complex(1,-1)))","[p]*sin(complex(1,-1))");
	result~=Example("ComplexMasksinArg6","sin([p]*(1/z))","[p]*sin(1/z)");
	result~=Example("ComplexMasksinArg7","sin([p]*(1/complex(0,0)))","[p]*sin(1/complex(0,0))");
	result~=Example("ComplexMasksinArg8","sin([p]*((complex(0,1)*pi/2)))","[p]*sin((complex(0,1)*pi/2))");
	result~=Example("ComplexMasksinArg9","sin([p]*((-complex(0,1)*pi/2)))","[p]*sin((-complex(0,1)*pi/2))");
	result~=Example("ComplexMasksinGuard0","sin([false]*(1/z))","[false]*sin(1/z)");
	result~=Example("ComplexMasksinGuard1","sin([true]*(1/z))","[true]*sin(1/z)");
	result~=Example("ComplexMasksinGuard2","sin([z=0]*(1/z))","[z=0]*sin(1/z)");
	result~=Example("ComplexMasksinGuard3","sin([log(x)<0]*(1/z))","[log(x)<0]*sin(1/z)");
	result~=Example("ComplexMasksinhArg0","sinh([p]*(z))","[p]*sinh(z)");
	result~=Example("ComplexMasksinhArg1","sinh([p]*(complex(0,0)))","[p]*sinh(complex(0,0))");
	result~=Example("ComplexMasksinhArg2","sinh([p]*(complex(1,0)))","[p]*sinh(complex(1,0))");
	result~=Example("ComplexMasksinhArg3","sinh([p]*(complex(-1,0)))","[p]*sinh(complex(-1,0))");
	result~=Example("ComplexMasksinhArg4","sinh([p]*(complex(0,1)))","[p]*sinh(complex(0,1))");
	result~=Example("ComplexMasksinhArg5","sinh([p]*(complex(1,-1)))","[p]*sinh(complex(1,-1))");
	result~=Example("ComplexMasksinhArg6","sinh([p]*(1/z))","[p]*sinh(1/z)");
	result~=Example("ComplexMasksinhArg7","sinh([p]*(1/complex(0,0)))","[p]*sinh(1/complex(0,0))");
	result~=Example("ComplexMasksinhArg8","sinh([p]*((complex(0,1)*pi/2)))","[p]*sinh((complex(0,1)*pi/2))");
	result~=Example("ComplexMasksinhArg9","sinh([p]*((-complex(0,1)*pi/2)))","[p]*sinh((-complex(0,1)*pi/2))");
	result~=Example("ComplexMasksinhGuard0","sinh([false]*(1/z))","[false]*sinh(1/z)");
	result~=Example("ComplexMasksinhGuard1","sinh([true]*(1/z))","[true]*sinh(1/z)");
	result~=Example("ComplexMasksinhGuard2","sinh([z=0]*(1/z))","[z=0]*sinh(1/z)");
	result~=Example("ComplexMasksinhGuard3","sinh([log(x)<0]*(1/z))","[log(x)<0]*sinh(1/z)");
	result~=Example("ComplexMasktanhArg0","tanh([p]*(z))","[p]*tanh(z)");
	result~=Example("ComplexMasktanhArg1","tanh([p]*(complex(0,0)))","[p]*tanh(complex(0,0))");
	result~=Example("ComplexMasktanhArg2","tanh([p]*(complex(1,0)))","[p]*tanh(complex(1,0))");
	result~=Example("ComplexMasktanhArg3","tanh([p]*(complex(-1,0)))","[p]*tanh(complex(-1,0))");
	result~=Example("ComplexMasktanhArg4","tanh([p]*(complex(0,1)))","[p]*tanh(complex(0,1))");
	result~=Example("ComplexMasktanhArg5","tanh([p]*(complex(1,-1)))","[p]*tanh(complex(1,-1))");
	result~=Example("ComplexMasktanhArg6","tanh([p]*(1/z))","[p]*tanh(1/z)");
	result~=Example("ComplexMasktanhArg7","tanh([p]*(1/complex(0,0)))","[p]*tanh(1/complex(0,0))");
	result~=Example("ComplexMasktanhArg8","tanh([p]*((complex(0,1)*pi/2)))","[p]*tanh((complex(0,1)*pi/2))");
	result~=Example("ComplexMasktanhArg9","tanh([p]*((-complex(0,1)*pi/2)))","[p]*tanh((-complex(0,1)*pi/2))");
	result~=Example("ComplexMasktanhGuard0","tanh([false]*(1/z))","[false]*tanh(1/z)");
	result~=Example("ComplexMasktanhGuard1","tanh([true]*(1/z))","[true]*tanh(1/z)");
	result~=Example("ComplexMasktanhGuard2","tanh([z=0]*(1/z))","[z=0]*tanh(1/z)");
	result~=Example("ComplexMasktanhGuard3","tanh([log(x)<0]*(1/z))","[log(x)<0]*tanh(1/z)");
	result~=Example("ComplexUnitcosArg0","cos([p]*(z))","[p]*cos(z)+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosArg1","cos([p]*(complex(0,0)))","[p]*cos(complex(0,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosArg2","cos([p]*(complex(1,0)))","[p]*cos(complex(1,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosArg3","cos([p]*(complex(-1,0)))","[p]*cos(complex(-1,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosArg4","cos([p]*(complex(0,1)))","[p]*cos(complex(0,1))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosArg5","cos([p]*(complex(1,-1)))","[p]*cos(complex(1,-1))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosArg6","cos([p]*(1/z))","[p]*cos(1/z)+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosArg7","cos([p]*(1/complex(0,0)))","[p]*cos(1/complex(0,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosArg8","cos([p]*((complex(0,1)*pi/2)))","[p]*cos((complex(0,1)*pi/2))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosArg9","cos([p]*((-complex(0,1)*pi/2)))","[p]*cos((-complex(0,1)*pi/2))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcosGuard0","cos([false]*(1/z))","[false]*cos(1/z)+[¬(false)]*complex(1,0)");
	result~=Example("ComplexUnitcosGuard1","cos([true]*(1/z))","[true]*cos(1/z)+[¬(true)]*complex(1,0)");
	result~=Example("ComplexUnitcosGuard2","cos([z=0]*(1/z))","[z=0]*cos(1/z)+[¬(z=0)]*complex(1,0)");
	result~=Example("ComplexUnitcosGuard3","cos([log(x)<0]*(1/z))","[log(x)<0]*cos(1/z)+[¬(log(x)<0)]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg0","cosh([p]*(z))","[p]*cosh(z)+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg1","cosh([p]*(complex(0,0)))","[p]*cosh(complex(0,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg2","cosh([p]*(complex(1,0)))","[p]*cosh(complex(1,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg3","cosh([p]*(complex(-1,0)))","[p]*cosh(complex(-1,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg4","cosh([p]*(complex(0,1)))","[p]*cosh(complex(0,1))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg5","cosh([p]*(complex(1,-1)))","[p]*cosh(complex(1,-1))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg6","cosh([p]*(1/z))","[p]*cosh(1/z)+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg7","cosh([p]*(1/complex(0,0)))","[p]*cosh(1/complex(0,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg8","cosh([p]*((complex(0,1)*pi/2)))","[p]*cosh((complex(0,1)*pi/2))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshArg9","cosh([p]*((-complex(0,1)*pi/2)))","[p]*cosh((-complex(0,1)*pi/2))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitcoshGuard0","cosh([false]*(1/z))","[false]*cosh(1/z)+[¬(false)]*complex(1,0)");
	result~=Example("ComplexUnitcoshGuard1","cosh([true]*(1/z))","[true]*cosh(1/z)+[¬(true)]*complex(1,0)");
	result~=Example("ComplexUnitcoshGuard2","cosh([z=0]*(1/z))","[z=0]*cosh(1/z)+[¬(z=0)]*complex(1,0)");
	result~=Example("ComplexUnitcoshGuard3","cosh([log(x)<0]*(1/z))","[log(x)<0]*cosh(1/z)+[¬(log(x)<0)]*complex(1,0)");
	result~=Example("ComplexUnitexpArg0","exp([p]*(z))","[p]*exp(z)+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpArg1","exp([p]*(complex(0,0)))","[p]*exp(complex(0,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpArg2","exp([p]*(complex(1,0)))","[p]*exp(complex(1,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpArg3","exp([p]*(complex(-1,0)))","[p]*exp(complex(-1,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpArg4","exp([p]*(complex(0,1)))","[p]*exp(complex(0,1))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpArg5","exp([p]*(complex(1,-1)))","[p]*exp(complex(1,-1))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpArg6","exp([p]*(1/z))","[p]*exp(1/z)+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpArg7","exp([p]*(1/complex(0,0)))","[p]*exp(1/complex(0,0))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpArg8","exp([p]*((complex(0,1)*pi/2)))","[p]*exp((complex(0,1)*pi/2))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpArg9","exp([p]*((-complex(0,1)*pi/2)))","[p]*exp((-complex(0,1)*pi/2))+[¬p]*complex(1,0)");
	result~=Example("ComplexUnitexpGuard0","exp([false]*(1/z))","[false]*exp(1/z)+[¬(false)]*complex(1,0)");
	result~=Example("ComplexUnitexpGuard1","exp([true]*(1/z))","[true]*exp(1/z)+[¬(true)]*complex(1,0)");
	result~=Example("ComplexUnitexpGuard2","exp([z=0]*(1/z))","[z=0]*exp(1/z)+[¬(z=0)]*complex(1,0)");
	result~=Example("ComplexUnitexpGuard3","exp([log(x)<0]*(1/z))","[log(x)<0]*exp(1/z)+[¬(log(x)<0)]*complex(1,0)");
	foreach(vars;[["Natural","n"],["Integer","i"],["Rational","q"],["Real","x"],["Complex","z"]]){
		auto v=vars[1];
		void add(string name,string input,string expected){ result~=Example("MaskOffset"~vars[0]~name,input,expected); }
		add("Eq","[p]*"~v~"=2","p∧"~v~"=2");
		add("EqReversed","2=[p]*"~v,"p∧"~v~"=2");
		add("Ne","[p]*"~v~"≠2","¬p∨"~v~"≠2");
		add("NeReversed","2≠[p]*"~v,"¬p∨"~v~"≠2");
		add("NegatedGuard","[¬p]*"~v~"=2","¬p∧"~v~"=2");
		add("True","[true]*"~v~"=2",v~"=2");
		add("False","[false]*"~v~"=2","false");
		add("FalseNe","[false]*"~v~"≠2","true");
		add("Add","[p]*"~v~"+2≠0",vars[0]=="Natural"?"true":"¬p∨"~v~"≠-2");
		add("AddCommuted","2+[p]*"~v~"≠0",vars[0]=="Natural"?"true":"¬p∨"~v~"≠-2");
		add("Indicator","[[p]*"~v~"=2]","[p∧"~v~"=2]");
		add("ZeroBoundary","[p]*"~v~"=0",vars[0]=="Real"?"¬p∨"~v~"=0":"([p]*"~v~")=0");
	}
	foreach(vars;[["Natural","n"],["Integer","i"],["Real","x"]]){
		auto v=vars[1];
		foreach(k;[-2,-1,0,1,2]) foreach(strict;[false,true]) foreach(reverse;[false,true]){
			import std.conv:to;
			auto c=to!string(k),op=strict?"<":"≤";
			auto relation=reverse?c~op~v:v~op~c;
			auto input=reverse?c~op~"[p]*"~v:"[p]*"~v~op~c;
			bool zero=reverse?(strict?k<0:k<=0):(strict?0<k:0<=k);
			auto expected=(zero?"¬p∨":"p∧")~relation;
			if(vars[0]=="Natural"&&((!reverse&&((strict&&k==1)||(!strict&&k==0)))||(reverse&&((strict&&k==0)||(!strict&&k==1))))) expected="([p]*n)"~(reverse?"≠":"=")~"0";
			result~=Example("MaskBound"~vars[0]~to!string(k+2)~(strict?"Lt":"Le")~(reverse?"Lower":"Upper"),input,expected);
		}
	}
	result~=Example("MaskFunctionsignVariable","sign([p]*(x))","[p]*sign(x)");
	result~=Example("MaskFunctionsignPositive","sign([p]*(3/2))","[p]*sign(3/2)");
	result~=Example("MaskFunctionsignNegative","sign([p]*(-3/2))","[p]*sign(-3/2)");
	result~=Example("MaskFunctionsignZero","sign([p]*(0))","[p]*sign(0)");
	result~=Example("MaskFunctionsignInverse","sign([p]*(1/x))","[p]*sign(1/x)");
	result~=Example("MaskFunctionsignLog","sign([p]*(log(x)))","[p]*sign(log(x))");
	result~=Example("MaskFunctionsignUndefined","sign([p]*(1/0))","[p]*sign(1/0)");
	result~=Example("MaskFunctionsignBoundary","sign([p]*(-1))","[p]*sign(-1)");
	result~=Example("MaskFunctionsignGuard0","sign([true]*(1/x))","[true]*sign(1/x)");
	result~=Example("MaskFunctionsignGuard1","sign([false]*(1/x))","[false]*sign(1/x)");
	result~=Example("MaskFunctionsignGuard2","sign([x=0]*(1/x))","[x=0]*sign(1/x)");
	result~=Example("MaskFunctionsignGuard3","sign([log(x)<0]*(1/x))","[log(x)<0]*sign(1/x)");
	result~=Example("MaskFunctionfloorVariable","floor([p]*(x))","[p]*floor(x)");
	result~=Example("MaskFunctionfloorPositive","floor([p]*(3/2))","[p]*floor(3/2)");
	result~=Example("MaskFunctionfloorNegative","floor([p]*(-3/2))","[p]*floor(-3/2)");
	result~=Example("MaskFunctionfloorZero","floor([p]*(0))","[p]*floor(0)");
	result~=Example("MaskFunctionfloorInverse","floor([p]*(1/x))","[p]*floor(1/x)");
	result~=Example("MaskFunctionfloorLog","floor([p]*(log(x)))","[p]*floor(log(x))");
	result~=Example("MaskFunctionfloorUndefined","floor([p]*(1/0))","[p]*floor(1/0)");
	result~=Example("MaskFunctionfloorBoundary","floor([p]*(-1))","[p]*floor(-1)");
	result~=Example("MaskFunctionfloorGuard0","floor([true]*(1/x))","[true]*floor(1/x)");
	result~=Example("MaskFunctionfloorGuard1","floor([false]*(1/x))","[false]*floor(1/x)");
	result~=Example("MaskFunctionfloorGuard2","floor([x=0]*(1/x))","[x=0]*floor(1/x)");
	result~=Example("MaskFunctionfloorGuard3","floor([log(x)<0]*(1/x))","[log(x)<0]*floor(1/x)");
	result~=Example("MaskFunctionceilVariable","ceil([p]*(x))","[p]*ceil(x)");
	result~=Example("MaskFunctionceilPositive","ceil([p]*(3/2))","[p]*ceil(3/2)");
	result~=Example("MaskFunctionceilNegative","ceil([p]*(-3/2))","[p]*ceil(-3/2)");
	result~=Example("MaskFunctionceilZero","ceil([p]*(0))","[p]*ceil(0)");
	result~=Example("MaskFunctionceilInverse","ceil([p]*(1/x))","[p]*ceil(1/x)");
	result~=Example("MaskFunctionceilLog","ceil([p]*(log(x)))","[p]*ceil(log(x))");
	result~=Example("MaskFunctionceilUndefined","ceil([p]*(1/0))","[p]*ceil(1/0)");
	result~=Example("MaskFunctionceilBoundary","ceil([p]*(-1))","[p]*ceil(-1)");
	result~=Example("MaskFunctionceilGuard0","ceil([true]*(1/x))","[true]*ceil(1/x)");
	result~=Example("MaskFunctionceilGuard1","ceil([false]*(1/x))","[false]*ceil(1/x)");
	result~=Example("MaskFunctionceilGuard2","ceil([x=0]*(1/x))","[x=0]*ceil(1/x)");
	result~=Example("MaskFunctionceilGuard3","ceil([log(x)<0]*(1/x))","[log(x)<0]*ceil(1/x)");
	result~=Example("MaskTranssinArg0","sin([p]*(x))","[p]*sin(x)");
	result~=Example("MaskTranssinArg1","sin([p]*(1/2))","[p]*sin(1/2)");
	result~=Example("MaskTranssinArg2","sin([p]*(-1/2))","[p]*sin(-1/2)");
	result~=Example("MaskTranssinArg3","sin([p]*(0))","[p]*sin(0)");
	result~=Example("MaskTranssinArg4","sin([p]*(1/x))","[p]*sin(1/x)");
	result~=Example("MaskTranssinArg5","sin([p]*(log(x)))","[p]*sin(log(x))");
	result~=Example("MaskTranssinArg6","sin([p]*(1/0))","[p]*sin(1/0)");
	result~=Example("MaskTranssinArg7","sin([p]*(-1))","[p]*sin(-1)");
	result~=Example("MaskTranssinArg8","sin([p]*(1))","[p]*sin(1)");
	result~=Example("MaskTranssinArg9","sin([p]*(2))","[p]*sin(2)");
	result~=Example("MaskTranssinArg10","sin([p]*(-2))","[p]*sin(-2)");
	result~=Example("MaskTranssinGuard0","sin([false]*(1/x))","[false]*sin(1/x)");
	result~=Example("MaskTranssinGuard1","sin([true]*(1/x))","[true]*sin(1/x)");
	result~=Example("MaskTranssinGuard2","sin([x=0]*(1/x))","[x=0]*sin(1/x)");
	result~=Example("MaskTranssinGuard3","sin([log(x)<0]*(1/x))","[log(x)<0]*sin(1/x)");
	result~=Example("MaskTranssinhArg0","sinh([p]*(x))","[p]*sinh(x)");
	result~=Example("MaskTranssinhArg1","sinh([p]*(1/2))","[p]*sinh(1/2)");
	result~=Example("MaskTranssinhArg2","sinh([p]*(-1/2))","[p]*sinh(-1/2)");
	result~=Example("MaskTranssinhArg3","sinh([p]*(0))","[p]*sinh(0)");
	result~=Example("MaskTranssinhArg4","sinh([p]*(1/x))","[p]*sinh(1/x)");
	result~=Example("MaskTranssinhArg5","sinh([p]*(log(x)))","[p]*sinh(log(x))");
	result~=Example("MaskTranssinhArg6","sinh([p]*(1/0))","[p]*sinh(1/0)");
	result~=Example("MaskTranssinhArg7","sinh([p]*(-1))","[p]*sinh(-1)");
	result~=Example("MaskTranssinhArg8","sinh([p]*(1))","[p]*sinh(1)");
	result~=Example("MaskTranssinhArg9","sinh([p]*(2))","[p]*sinh(2)");
	result~=Example("MaskTranssinhArg10","sinh([p]*(-2))","[p]*sinh(-2)");
	result~=Example("MaskTranssinhGuard0","sinh([false]*(1/x))","[false]*sinh(1/x)");
	result~=Example("MaskTranssinhGuard1","sinh([true]*(1/x))","[true]*sinh(1/x)");
	result~=Example("MaskTranssinhGuard2","sinh([x=0]*(1/x))","[x=0]*sinh(1/x)");
	result~=Example("MaskTranssinhGuard3","sinh([log(x)<0]*(1/x))","[log(x)<0]*sinh(1/x)");
	result~=Example("MaskTranstanhArg0","tanh([p]*(x))","[p]*tanh(x)");
	result~=Example("MaskTranstanhArg1","tanh([p]*(1/2))","[p]*tanh(1/2)");
	result~=Example("MaskTranstanhArg2","tanh([p]*(-1/2))","[p]*tanh(-1/2)");
	result~=Example("MaskTranstanhArg3","tanh([p]*(0))","[p]*tanh(0)");
	result~=Example("MaskTranstanhArg4","tanh([p]*(1/x))","[p]*tanh(1/x)");
	result~=Example("MaskTranstanhArg5","tanh([p]*(log(x)))","[p]*tanh(log(x))");
	result~=Example("MaskTranstanhArg6","tanh([p]*(1/0))","[p]*tanh(1/0)");
	result~=Example("MaskTranstanhArg7","tanh([p]*(-1))","[p]*tanh(-1)");
	result~=Example("MaskTranstanhArg8","tanh([p]*(1))","[p]*tanh(1)");
	result~=Example("MaskTranstanhArg9","tanh([p]*(2))","[p]*tanh(2)");
	result~=Example("MaskTranstanhArg10","tanh([p]*(-2))","[p]*tanh(-2)");
	result~=Example("MaskTranstanhGuard0","tanh([false]*(1/x))","[false]*tanh(1/x)");
	result~=Example("MaskTranstanhGuard1","tanh([true]*(1/x))","[true]*tanh(1/x)");
	result~=Example("MaskTranstanhGuard2","tanh([x=0]*(1/x))","[x=0]*tanh(1/x)");
	result~=Example("MaskTranstanhGuard3","tanh([log(x)<0]*(1/x))","[log(x)<0]*tanh(1/x)");
	result~=Example("MaskTransatanArg0","atan([p]*(x))","[p]*atan(x)");
	result~=Example("MaskTransatanArg1","atan([p]*(1/2))","[p]*atan(1/2)");
	result~=Example("MaskTransatanArg2","atan([p]*(-1/2))","[p]*atan(-1/2)");
	result~=Example("MaskTransatanArg3","atan([p]*(0))","[p]*atan(0)");
	result~=Example("MaskTransatanArg4","atan([p]*(1/x))","[p]*atan(1/x)");
	result~=Example("MaskTransatanArg5","atan([p]*(log(x)))","[p]*atan(log(x))");
	result~=Example("MaskTransatanArg6","atan([p]*(1/0))","[p]*atan(1/0)");
	result~=Example("MaskTransatanArg7","atan([p]*(-1))","[p]*atan(-1)");
	result~=Example("MaskTransatanArg8","atan([p]*(1))","[p]*atan(1)");
	result~=Example("MaskTransatanArg9","atan([p]*(2))","[p]*atan(2)");
	result~=Example("MaskTransatanArg10","atan([p]*(-2))","[p]*atan(-2)");
	result~=Example("MaskTransatanGuard0","atan([false]*(1/x))","[false]*atan(1/x)");
	result~=Example("MaskTransatanGuard1","atan([true]*(1/x))","[true]*atan(1/x)");
	result~=Example("MaskTransatanGuard2","atan([x=0]*(1/x))","[x=0]*atan(1/x)");
	result~=Example("MaskTransatanGuard3","atan([log(x)<0]*(1/x))","[log(x)<0]*atan(1/x)");
	result~=Example("MaskTransasinArg0","asin([p]*(x))","[p]*asin(x)");
	result~=Example("MaskTransasinArg1","asin([p]*(1/2))","[p]*asin(1/2)");
	result~=Example("MaskTransasinArg2","asin([p]*(-1/2))","[p]*asin(-1/2)");
	result~=Example("MaskTransasinArg3","asin([p]*(0))","[p]*asin(0)");
	result~=Example("MaskTransasinArg4","asin([p]*(1/x))","[p]*asin(1/x)");
	result~=Example("MaskTransasinArg5","asin([p]*(log(x)))","[p]*asin(log(x))");
	result~=Example("MaskTransasinArg6","asin([p]*(1/0))","[p]*asin(1/0)");
	result~=Example("MaskTransasinArg7","asin([p]*(-1))","[p]*asin(-1)");
	result~=Example("MaskTransasinArg8","asin([p]*(1))","[p]*asin(1)");
	result~=Example("MaskTransasinArg9","asin([p]*(2))","[p]*asin(2)");
	result~=Example("MaskTransasinArg10","asin([p]*(-2))","[p]*asin(-2)");
	result~=Example("MaskTransasinGuard0","asin([false]*(1/x))","[false]*asin(1/x)");
	result~=Example("MaskTransasinGuard1","asin([true]*(1/x))","[true]*asin(1/x)");
	result~=Example("MaskTransasinGuard2","asin([x=0]*(1/x))","[x=0]*asin(1/x)");
	result~=Example("MaskTransasinGuard3","asin([log(x)<0]*(1/x))","[log(x)<0]*asin(1/x)");
	return result;
}
private Syntax syntax(){ Syntax s; s.declare("n:ℕ,m:ℕ,l:ℕ,i:ℤ,j:ℤ,k:ℤ,q:ℚ,r:ℚ,s:ℚ,x:ℝ,z:ℂ,p:𝔹"); return s; }
unittest{
	foreach(f;["cos","cosh","exp"])
	foreach(g;["false","true","1/0=0"])
	foreach(x;["z","complex(0,0)","1/complex(0,0)","(complex(0,1)*pi/2)"]){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=f~"(["~g~"]*("~x~"))";
		auto expected=g=="false"?"true":g!="true"||x=="1/complex(0,0)"?"false":"true";
		auto want=simplify(a,s.parse(a,expected));
		auto domain=simplifyDomain(a,s.parse(a,input));
		assert(!domain.exhausted&&domain.output==want.output,input~" domain");
	}
}
unittest{
	foreach(f;["sin","sinh","tanh"])
	foreach(g;["false","true","1/0=0"])
	foreach(x;["z","complex(0,0)","1/complex(0,0)","(complex(0,1)*pi/2)"]){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=f~"(["~g~"]*("~x~"))";
		auto expected=g=="false"?"true":g!="true"||x=="1/complex(0,0)"?"false":
			f=="tanh"?"cosh("~x~")≠complex(0,0)":"true";
		auto want=simplify(a,s.parse(a,expected));
		auto domain=simplifyDomain(a,s.parse(a,input));
		assert(!domain.exhausted&&domain.output==want.output,input~" domain");
	}
}
unittest{
	foreach(f;["sin","sinh","tanh","atan","asin"])
	foreach(g;["false","true","1/0=0"])
	foreach(x;["-2","-1","-1/2","0","1/2","1","2","1/0","log(0)"]){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=f~"(["~g~"]*("~x~"))";
		auto valid=x!="1/0"&&x!="log(0)"&&!(f=="asin"&&(x=="-2"||x=="2"));
		auto expected=s.parse(a,g=="false"||(g=="true"&&valid)?"true":"false");
		auto domain=simplifyDomain(a,s.parse(a,input));
		assert(!domain.exhausted&&domain.output==expected,input~" domain");
	}
}
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
		if(c.name.startsWith("Offset","DirectNatural","ComplexMask","ComplexUnit","MaskFunction","MaskTrans")){
			auto roundtrip=simplify(a,s.parse(a,s.format(a,fast.output)));
			assert(!roundtrip.exhausted&&roundtrip.output==fast.output,c.name~" round trip");
		}
		if(c.name.startsWith("MaskZero")){
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
