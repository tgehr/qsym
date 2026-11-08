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
		Example("MaskPartialBody","[p]*log(-1)≠0","p∧log(-1)≠0")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,t:ℝ,z:ℂ,p:𝔹,q:𝔹"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected)).output;
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
