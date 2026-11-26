module order_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("QuadraticClosed","[x^2-3x+1≤0]","[(3-sqrt(5))/2≤x∧x≤(3+sqrt(5))/2]"),
		Example("QuadraticOpen","x^2-3x+1<0","(3-sqrt(5))/2<x∧x<(3+sqrt(5))/2"),
		Example("QuadraticOutsideClosed","-x^2+3x-1≤0","x≤(3-sqrt(5))/2∨(3+sqrt(5))/2≤x"),
		Example("QuadraticOutsideOpen","-x^2+3x-1<0","x<(3-sqrt(5))/2∨(3+sqrt(5))/2<x"),
		Example("QuadraticNonmonic","4*x^2≤3","-sqrt(3)/2≤x∧x≤sqrt(3)/2"),
		Example("QuadraticReversed","2<x^2","x<-sqrt(2)∨sqrt(2)<x"),
		Example("QuadraticStrictBoundary","[x^2≤2]*[x<sqrt(2)]","[-sqrt(2)≤x∧x<sqrt(2)]"),
		Example("QuadraticPartial","log(x)^2<2","-sqrt(2)<log(x)∧log(x)<sqrt(2)"),
		Example("QuadraticFact","x<2", "true",["x^2≤2"]),
		Example("FactoredCubic","(x-1)*(x-2)*(x-3)=0","x=1∨(x=2∨x=3)"),
		Example("FactoredDifference","(x-y)*(x+y)=0","x=-y∨x=y"),
		Example("IndicatorSumZero","[[x=0]+[x=1]=0]","[x≠0∧x≠1]"),
		Example("IndicatorWeightedSum","[2*[x=0]+3*[x=1]=0]","[x≠0∧x≠1]"),
		Example("IndicatorNonnegative","[0≤[x=0]+[x=1]]","1"),
		Example("IndicatorUpper","[p]≤1","true"),
		Example("IndicatorPositive","0<[p]+[q]","p∨q"),
		Example("IndicatorPartial","[[log(x)=0]+[x=1]=0]","[x≠1∧log(x)≠0]"),
		Example("SquareSumZero","[x^2+y^2=0]","[x=0∧y=0]"),
		Example("WeightedSquareSumZero","[2*x^2+y^2=0]","[x=0∧y=0]"),
		Example("SquareSumNonpositive","x^2+y^2≤0","x=0∧y=0"),
		Example("SquareSumPositive","0<x^2+y^2","x≠0∨y≠0"),
		Example("ThreeSquares","x^2+y^2+t^2=0","x=0∧(y=0∧t=0)"),
		Example("NegativeSquareSum","-x^2-y^2=0","x=0∧y=0"),
		Example("ConditionalSum","x+y=0","x=0∧y=0",["0≤x","0≤y"]),
		Example("ConditionalSumScope","[0≤x]*[0≤y]*[x+y=0]","[x=0∧y=0]"),
		Example("AssumedSquareSum","x","0",["x^2+y^2=0"]),
		Example("AssumedIndicators","[p]","0",["[p]+[q]=0"]),
		Example("SquareSumScope","[x^2+y^2=0]*x+x","x"),
		Example("PartialSquareSum","log(x)^2+y^2=0","y=0∧log(x)=0"),
		Example("PositiveProduct","[x*y≤0]*[0<x]","[y≤0∧0<x]"),
		Example("PositiveProductReverse","[x*y≤0]*[0<y]","[x≤0∧0<y]"),
		Example("NegativeProduct","x*y<0","0<y",["x<0"]),
		Example("PositiveProductFact","0<x*y","0<y",["0<x"]),
		Example("ProductStrictBoundary","x*y<0","x*y<0",["0≤x"]),
		Example("ExpIncreasing","exp(x)<exp(y)","x<y"),
		Example("ExpIncreasingClosed","exp(x)≤exp(y)","x≤y"),
		Example("ExpInjective","exp(x)=exp(y)","x=y"),
		Example("ExpUnit","exp(x)=1","x=0"),
		Example("LogIncreasing","log(x)<log(y)","x<y"),
		Example("LogIncreasingClosed","log(x)≤log(y)","x≤y"),
		Example("LogInjective","log(x)=log(y)","x=y"),
		Example("LogNonpositive","log(x)≤0","x≤1"),
		Example("LogEquation","x","exp(y)",["log(x)=y"]),
		Example("SqrtIncreasing","sqrt(x)<sqrt(y)","x<y"),
		Example("SqrtIncreasingClosed","sqrt(x)≤sqrt(y)","x≤y"),
		Example("SqrtInjective","sqrt(x)=sqrt(y)","x=y"),
		Example("SqrtBound","sqrt(x)<2","x<4"),
		Example("SqrtNegativeBound","sqrt(x)<-2","false"),
		Example("OddPowerIncreasing","x^3<y^3","x<y"),
		Example("OddPowerIncreasingClosed","x^5≤y^5","x≤y"),
		Example("OddPowerInjective","x^3=y^3","x=y"),
		Example("EvenPowerNonnegative","x^4<y^4","x<y",["0≤x","0≤y"]),
		Example("EvenPowerNonnegativeClosed","x^2≤y^2","x≤y",["0≤x","0≤y"]),
		Example("EvenPowerUnrestricted","x^4<y^4","x^4<y^4"),
		Example("PowerBaseIncreasing","2^x<2^y","x<y"),
		Example("PowerBaseIncreasingClosed","2^x≤2^y","x≤y"),
		Example("PowerBaseDecreasing","(1/2)^x<(1/2)^y","y<x"),
		Example("PowerBaseDecreasingClosed","(1/2)^x≤(1/2)^y","y≤x"),
		Example("PowerBaseConditional","t^x<t^y","x<y",["1<t"]),
		Example("PowerBaseUnknown","t^x<t^y","t^x<t^y"),
		Example("AbsEquality","abs(x)=2","x=-2∨x=2"),
		Example("AbsOpen","abs(x)<2","-2<x∧x<2"),
		Example("AbsClosed","abs(x)≤2","-2≤x∧x≤2"),
		Example("AbsNegative","abs(x)=-2","false"),
		Example("AbsSymbolic","abs(x)=y","0≤y∧(x=-y∨x=y)"),
		Example("AbsOutside","2<abs(x)","x<-2∨2<x"),
		Example("AbsOutsideClosed","2≤abs(x)","x≤-2∨2≤x"),
		Example("PiRoundDown","floor(π)","3"),
		Example("PiRoundUp","ceil(π)","4"),
		Example("PiRoundInverse","floor(8/π)","2"),
		Example("PiRoundNegative","floor(-8/π)","-3"),
		Example("PiCeilNegative","ceil(-8/π)","-2"),
		Example("PiFloorAffine","floor(3*π+1/2)","9"),
		Example("PiFloorNatural","floorN(-π)","0"),
		Example("PiEnclosureOpenFloor","floor(1000000*π)","3141592"),
		Example("PiEnclosureOpenCeil","ceil(1000000*π)","3141593"),
		Example("PiEnclosureWide","floor(10000000*π)","floor(10000000*π)"),
		Example("PiEnclosureFree","floor(x*π)","floor(x*π)"),
		Example("PiEnclosureOpenLower","3141592/1000000<π","true"),
		Example("PiEnclosureOpenUpper","π<3141593/1000000","true"),
		Example("PiEnclosureFalse","π≤3141592/1000000","false"),
		Example("PiEnclosureAffineOrder","π+1<2*π-4","false"),
		Example("PiEnclosureMixedUnknown","π-3<π⁻¹","π-3<π⁻¹"),
		Example("CosPositiveUnit","0<cos(x)","true",["-1≤x","x≤1"]),
		Example("CosNonzeroUnit","cos(x)≠0","true",["-1≤x","x≤1"]),
		Example("CosPositiveSine","0<cos(sin(x))","true"),
		Example("CosNonzeroCosine","cos(cos(x))≠0","true"),
		Example("CosUnitEndpoint","cos(1)≠0","true"),
		Example("CosPartialBound","cos(x)≠0","cos(x)≠0",["x≤1"]),
		Example("CosOutsideUnit","cos(2*sin(x))≠0","cos(2*sin(x))≠0"),
		Example("MaskPartialBody","[p]*log(-1)≠0","p∧log(-1)≠0"),
		// Bounds that differ by a constant: a premise about one asks for the
		// same about the other, moved by that constant, without end. A chain
		// of premises takes a known fact once, so it does not go around such
		// a cycle of facts, of two or of three, with an offset or a factor,
		// and with other facts to branch at.
		Example("OffsetChain","[0≤y]*[y≤x]*[x-1≤y]","[0≤y∧(y≤x∧x-1≤y)]"),
		Example("OffsetChainUpper","[y≤1]*[y≤x]*[x-1≤y]","[y≤1∧(y≤x∧x-1≤y)]"),
		Example("OffsetChainThree","[0≤t]*[t≤y]*[y≤x]*[x-1≤t]","[0≤t∧(t≤y∧(y≤x∧x-1≤t))]"),
		Example("ScaledChain","[0≤y]*[y≤x]*[x/2≤y]","[0≤y∧(y≤x∧x·(1/2)≤y)]"),
		Example("OffsetChainBranching","[0≤y]*[y≤x]*[x-1≤y]*[y≤2*x]*[x/3≤y]","[0≤y∧(y≤x∧(x-1≤y∧x·(1/3)≤y))]"),
		// A chain through different facts stays: it shows a bound that the
		// others imply, with the offsets added, and one that they refute. A
		// cycle of facts that contradict each other shows without a second
		// round.
		Example("ChainImplied","[0≤y]*[y≤x]*[x≤t]*[0≤t]","[0≤y∧(y≤x∧x≤t)]"),
		Example("ChainImpliedOffset","[x≤y+1]*[y≤x+1]*[0≤x]*[x≤1]*[y≤2]","[x≤y+1∧(y≤x+1∧(0≤x∧x≤1))]"),
		Example("ChainRefuted","[0≤y]*[y≤x]*[x≤t]*[t<0]","0"),
		Example("ChainRefutedOffset","[x≤y+1]*[y≤x+1]*[0≤x]*[x≤1]*[2<y]","0"),
		Example("ChainContradiction","[0≤y]*[y≤x]*[x+1≤y]","0"),
		Example("ChainContradictionThree","[x≤y]*[y≤t]*[t≤x]*[x<t]","0"),
		// Two terms that are known to be distinct: a bound by one of the
		// other is strict, and the exclusion written again adds nothing,
		// whichever of the two it has on the left and however their
		// difference is split between its sides. Nor does it add to a
		// strict bound.
		Example("PunctureTerm","[x≤y]*[x≠y]","[x<y]"),
		Example("PunctureTermSwapped","[x≤y]*[y≠x]","[x<y]"),
		Example("PunctureTermLower","[y≤x]*[x≠y]","[y<x]"),
		Example("PunctureTermFirst","[y≠x]*[x≤y]","[x<y]"),
		Example("PunctureOffset","[x≤y+1]*[y+1≠x]","[x<y+1]"),
		Example("PunctureOffsetSplit","[x≤y+1]*[x-y≠1]","[x<y+1]"),
		Example("PunctureScaled","[2*x≤y]*[y≠2*x]","[2*x<y]"),
		Example("PunctureSum","[x+y≤t]*[t-x≠y]","[x+y<t]"),
		Example("PunctureBoth","[0≤x]*[0≠x]*[x≤y]*[y≠x]","[0<x∧x<y]"),
		Example("DistinctBelow","[x<y]*[x≠y]","[x<y]"),
		Example("DistinctAbove","[x<y]*[y≠x]","[x<y]"),
		Example("DistinctOffset","[x-1<y]*[x≠y+1]","[x-1<y]"),
		Example("DistinctSwapped","[x≠y]*[y≠x]","[x≠y]"),
		Example("DistinctNegated","[x≠0]*[-x≠0]","[x≠0]"),
		Example("DistinctSplit","[x≠y+1]*[y-x≠-1]","[x≠y+1]"),
		Example("DistinctEqual","[x<y]*[y=x]","0"),
		Example("DistinctEqualSwapped","[x≠y]*[y=x]","0"),
		// Two terms in the order that a known bound gives, where the bound
		// is not written with the same two sides: the difference of the
		// sides of the comparison is a positive multiple of that of the
		// known bound, and the comparison holds, or a negative multiple,
		// and it fails. A strict comparison does not follow from a bound
		// that is not strict, nor does a weak one fail against it; the two
		// together are the strict bound and the equation. So the absolute
		// value of a difference is the difference or its opposite, also in
		// an exponent, and so is the square root of its square.
		Example("OrderedDifference","[y≤x]*[0≤x-y]","[y≤x]"),
		Example("OrderedDifferenceStrict","[y<x]*[0<x-y]","[y<x]"),
		Example("OrderedDifferenceWeak","[y<x]*[0≤x-y]","[y<x]"),
		Example("OrderedDifferenceFirst","[0≤x-y]*[y≤x]","[0≤x-y]"),
		Example("OrderedOpposite","[x<y]*[0≤x-y]","0"),
		Example("OrderedOppositeWeak","[y≤x]*[x-y<0]","0"),
		Example("OrderedOppositeStrict","[y<x]*[x-y≤0]","0"),
		Example("OrderedOppositeBoth","[y<x]*[x-y<0]","0"),
		Example("OrderedTightened","[y≤x]*[0<x-y]","[y<x]"),
		Example("OrderedBoundary","[y≤x]*[x-y≤0]","[x=y]"),
		Example("OrderedScaled","[y≤3*x]*[0≤x-y/3]","[y≤3*x]"),
		Example("OrderedScaledOpposite","[2*y<3*x]*[x/2≤y/3]","0"),
		Example("OrderedShifted","[x<y]*[x-y+1<1]","[x<y]"),
		Example("OrderedSum","[x+y≤t]*[y≤t-x]","[x+y≤t]"),
		Example("OrderedProduct","[x*y<1]*[0<1-x*y]","[x*y<1]"),
		Example("OrderedPartial","[log(y)≤x]*[0≤x-log(y)]","[log(y)≤x]"),
		Example("OrderedFact","0≤x-y","true",["y≤x"]),
		Example("OrderedFactStrict","0<2*x-2*y","true",["y<x"]),
		Example("OrderedFactOpposite","x-y<0","false",["y≤x"]),
		Example("OrderedFactTightened","0<x-y","x≠y",["y≤x"]),
		Example("OrderedAbs","[y≤x]*abs(x-y)","[y≤x]*(x-y)"),
		Example("OrderedAbsBelow","[x<y]*abs(x-y)","[x<y]*(y-x)"),
		Example("OrderedAbsScaled","[y/2≤x]*abs(2*x-y)","[y/2≤x]*(2*x-y)"),
		Example("OrderedAbsExponent","[y≤x]*exp(-abs(x-y))","[y≤x]*exp(y-x)"),
		Example("OrderedAbsProduct","[y≤x]*[x<t]*abs(x-y)*abs(x-t)","[y≤x]*[x<t]*((x-y)*(t-x))"),
		Example("OrderedAbsPartial","[log(y)≤x]*abs(x-log(y))","[log(y)≤x]*(x-log(y))"),
		Example("OrderedAbsOther","[y≤x]*abs(x-t)","[y≤x]*abs(x-t)"),
		Example("OrderedRoot","[y≤x]*sqrt((x-y)^2)","[y≤x]*(x-y)"),
		Example("OrderedMaximum","[y≤x]*max(x-y,0)","[y≤x]*(x-y)"),
		// A comparison with a square root whose argument has the square of a
		// sum. Where powers are multiplied out the square is split into two
		// first powers, and it is met again in a premise while one half is
		// normalized. There the halves come back as they are, and the two
		// first powers are joined again, which ended in an internal error.
		// The comparisons stay as they are written.
		Example("FirstPowerRoot","[0≤y+sqrt((y+1)^2+1)]","[0≤y+sqrt((y+1)^2+1)]"),
		Example("FirstPowerSum","[0≤y+sqrt((y+t)^2+x)]","[0≤y+sqrt((y+t)^2+x)]"),
		Example("FirstPowerBounds","[0≤x]*[y-sqrt((y+1)^2+t)≤x]*[x≤y+sqrt((y+1)^2+t)]","[0≤x]*[y-sqrt((y+1)^2+t)≤x]*[x≤y+sqrt((y+1)^2+t)]")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,t:ℝ,z:ℂ,p:𝔹,q:𝔹"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected,a.sort(input))).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected),fast.exhausted?" (exhausted)":""); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"ordered guard regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	foreach(work;[size_t(0),1,100]){
		auto options=Options(DensityMode.preserve,true); options.maxAlgebraWork=work;
		auto r=simplify(a,s.parse(a,"[x^2-3*x+1≤0]*[x<2]"),options);
		assert(r.exhausted); exportLean(a,r);
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: order-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ordered guard certificates.");
}
