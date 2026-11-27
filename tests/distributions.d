module distribution_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,type,expected; }
private Case[] cases(){
	string scaledSteps(string rate,string k="k",string seed="δ((3:ℝ))"){
		return "(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then "~seed~" else scaleD("~rate~",f(n sub 1)))("~k~")";
	}
	string emittedSteps(string seed,string emission,string rate,string k,bool tailFirst=false){
		auto tail=rate.length?"scaleD("~rate~",f(n sub 1))":"f(n sub 1)";
		auto step=tailFirst?tail~","~emission:emission~","~tail;
		return "(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then "~seed~" else addD("~step~"))("~k~")";
	}
	enum growing="(n+1:ℝ)/(n:ℝ)",shrinking="(n:ℝ)/(n+1:ℝ)";
	string discountedAtoms(string k,string rate="1/2",string seed="zeroD(ℝ)",bool tailFirst=false){
		auto tail="scaleD("~rate~",f(n sub 1))",atom="δ((n:ℝ))";
		return "(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then "~seed~" else addD("~
			(tailFirst?tail~","~atom:atom~","~tail)~"))("~k~")";
	}
	enum uniformCountdown="(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else addD(scaleD(1/(n+1),δ((n:ℝ))),scaleD(n/(n+1),f(n sub 1))))";
	enum indexedAtoms="(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then zeroD(ℝ) else addD(δ((n:ℝ)),f(n sub 1)))";
	enum mixedLoop="(μ(d:Distribution(ℝ)).addD(addD(δ(0),δ(2)),d))";
	enum retry="(μ(d:Distribution(ℝ)).addD(addD(scaleD(1/4,δ(0)),scaleD(1/4,δ(2))),scaleD(1/2,d)))";
	string shift(string start,string step="n+1",string mass="1/2",string ratio="1/2"){
		auto seed="δ(("~start~":ℕ))";
		if(mass.length) seed="scaleD("~mass~","~seed~")";
		return "(μ(d:Distribution(ℕ)).addD("~seed~",scaleD("~ratio~",bindD(d,λ(n:ℕ).δ("~step~")))))";
	}
	string flip(string seed="δ(false)",string rate="1/2"){
		return "(μ(d:Distribution(𝔹)).addD("~seed~",scaleD("~rate~",bindD(d,λ(b:𝔹).δ(¬b)))))";
	}
	string reflectAcross(string expression="5-x",string seed="δ((1:ℝ))",string ratio="1/2"){
		return "(μ(d:Distribution(ℝ)).addD("~seed~",scaleD("~ratio~",bindD(d,λ(x:ℝ).δ("~expression~")))))";
	}
	string reflect(string seed="δ((2:ℝ))",string rate="1/2"){
		return "(μ(d:Distribution(ℝ)).addD("~seed~",scaleD("~rate~",bindD(d,λ(x:ℝ).δ(-x)))))";
	}
	auto counter=shift("0");
	enum endless="(μ(d:Distribution(ℝ)).addD(δ(0),d))";
	enum twoArms="(μ(d:Distribution(ℝ)).addD(scaleD(1/4,addD(δ(0),d)),scaleD(1/4,addD(d,δ(2)))))";
	return [
	Case("Dirac","δ(2)","Distribution(ℕ)"),
	Case("NaturalDirac","(δ(2):Distribution(ℕ))","Distribution(ℕ)"),
	Case("FunctionDirac","δ(λ(n:ℕ).n)","Distribution(ℕ→ℕ)"),
	Case("TypeDirac","δ(Distribution(ℝ))","Distribution(Type)"),
	Case("NestedDirac","δ(δ(2))","Distribution(Distribution(ℕ))"),
	Case("SetDirac","δ({x:ℝ|x≠0})","Distribution(Set(ℝ))"),
	Case("DistributionIdentity","λ(d:Distribution(ℝ)).Λ(x:ℝ).d[x]","Distribution(ℝ)→Distribution(ℝ)"),
	Case("DistributionFunction","λ(p:Distribution(ℝ)).δ(p)","Distribution(ℝ)→Distribution(Distribution(ℝ))"),
	Case("Lebesgue","Λ(x:ℝ).λ[x]","Distribution(ℝ)"),
	Case("UntypedLebesgue","Λx.λ[x]","Distribution(ℝ)"),
	Case("UntypedIntegral","∫dx x*δ(2)[x]","ℝ"),
	Case("Marginal","Λ(x:ℝ).∫(y:ℝ).δ(y)[x]*λ[y]","Distribution(ℝ)"),
	Case("BarePuncture","[x≠0]·λ[x]","Distribution(ℝ)"),
	Case("BareLebesgue","λ[x]","Distribution(ℝ)"),
	Case("Interval","∫dx [-1≤x≤1]·λ[x]","ℝ"),
	Case("PuncturedInterval","∫dx [x≠0]·λ[x]·[-1≤x≤1]","ℝ"),
	Case("UnboundedPuncture","∫dx [x≠0]·λ[x]","ℝ"),
	Case("ZeroIntegral","∫dx 0","ℝ","0"),
	Case("StrictInterval","∫dx [-1<x<1]·λ[x]","ℝ","2"),
	Case("EmptyInterval","∫dx [2≤x≤1]·λ[x]","ℝ","0"),
	Case("SingletonIntegral","∫dx [x=0]·λ[x]","ℝ","0"),
	Case("ShiftedPuncture","∫dx [2*x≠1]·[-1≤x≤1]·λ[x]","ℝ","2"),
	Case("IntersectedIntervals","∫dx [0≤x≤3]·λ[x]·[-1≤x≤1]","ℝ","1"),
	Case("SignedInterval","∫dx (-3)*[-1≤x≤1]·λ[x]","ℝ","-6"),
	Case("LinearInterval","∫dx [0≤2*x+1]·[3*x≤6]·λ[x]","ℝ","5/2"),
	Case("AtomDensityAway","densityAtD(δ((2:ℝ)),0)","ℝ","0"),
	Case("AtomDensityAt","densityAtD(δ((2:ℝ)),2)","ℝ","undefined(ℝ)"),
	Case("MixedDensityFunction","λ(x:ℝ).(δ(0)[x]+[0≤x≤1]*λ[x])//λ[x]","ℝ→ℝ","λ(x:{x:ℝ | x≠0}). [0≤x∧x≤1]"),
	Case("MixedDensityAtAtom","densityAtD(Λ(x:ℝ).δ(0)[x]+[0≤x≤1]*λ[x],0)","ℝ","undefined(ℝ)"),
	Case("MixedDensityInside","densityAtD(Λ(x:ℝ).δ(0)[x]+[0≤x≤1]*λ[x],1/2)","ℝ","1"),
	Case("MixedDensityEndpoint","densityAtD(Λ(x:ℝ).[0≤x≤1]*λ[x]+δ(0)[x],1)","ℝ","1"),
	Case("MixedDensityOutside","densityAtD(Λ(x:ℝ).δ(0)[x]+[0≤x≤1]*λ[x],2)","ℝ","0"),
	Case("MixedDensityHole","densityAtD(Λ(x:ℝ).δ(0)[x]+(1/(x-1))*λ[x],1)","ℝ","0⁻¹"),
	Case("MixedDensityNestedWeights","densityAtD(addD(δ((0:ℝ)),weightD(λ(x:ℝ).x,weightD(λ(x:ℝ).(-2),lebesgueD()))),3)","ℝ","-6"),
	Case("MixedDensityPartialAtom","densityAtD(addD(δ(undefined(ℝ)),lebesgueD()),1)","ℝ"),
	Case("MixedDensityPartialQuery","densityAtD(addD(lebesgueD(),δ((2:ℝ))),undefined(ℝ))","ℝ"),
	Case("SignedFibreCancel","densityAtD(Λ(x:ℝ).δ(0)[x]+(-δ(0)[x])+[0≤x≤1]*λ[x],0)","ℝ","1"),
	Case("SignedFibreResidual","densityAtD(Λ(x:ℝ).2*δ(0)[x]+(-δ(0)[x])+λ[x],0)","ℝ","undefined(ℝ)"),
	Case("SignedFibreDistinct","densityAtD(Λ(x:ℝ).δ(0)[x]+(-δ(2)[x])+λ[x],2)","ℝ","undefined(ℝ)"),
	Case("SignedFibreAway","densityAtD(Λ(x:ℝ).δ(0)[x]+(-δ(2)[x])+λ[x],1)","ℝ","1"),
	Case("SignedFibreZeroScale","densityAtD(scaleD(0,δ((3:ℝ))),3)","ℝ","0"),
	Case("SignedFibrePartialWeight","densityAtD(Λ(x:ℝ).(1/x)*δ(0)[x]+λ[x],1)","ℝ","undefined(ℝ)"),
	Case("SignedFibreRegularHole","densityAtD(Λ(x:ℝ).δ(0)[x]+((1/x)*λ[x]+(-δ(0)[x])),0)","ℝ","0⁻¹"),
	Case("SignedFibreSymbolic","λ(a:ℝ).densityAtD(Λ(x:ℝ).δ(a)[x]+(λ[x]+(-δ(a)[x])),a)","ℝ→ℝ","λ(a:ℝ). (1:ℝ)"),
	Case("CubicGraph","(λ[x]·δ(x^3)[y])//λ[y]","Distribution(ℝ)","(3·cbrt(y)^2)⁻¹·δ(cbrt(y))[x]"),
	Case("CubicNegativeFibre","(λ(y:ℝ). (λ[x]·δ(x^3)[y])//λ[y])(-8)","Distribution(ℝ)","Λ(x:ℝ). 1/12·δ(-2)[x]"),
	Case("FifthNegativeFibre","(λ(y:ℝ). (λ[x]·δ(x^5)[y])//λ[y])(-32)","Distribution(ℝ)","Λ(x:ℝ). 1/80·δ(-2)[x]"),
	Case("SeventhPositiveMass","(λ(y:ℝ). ∫dx λ[x]·δ(x^7)[y]//λ[y])(128)","ℝ","1/448"),
	Case("FifthSymbolicFibre","λ[x]·δ(x^5)[y]//λ[y]","Distribution(ℝ)"),
	Case("CubicExcludedFibre","(λ(y:ℝ). [0<x]·λ[x]·δ(x^3)[y]//λ[y])(0)","Distribution(ℝ)","Λ(x:ℝ). 0·δ(0)[x]"),
	Case("CubicCriticalDefined","defined(graphFibreD(λ(x:ℝ).x^3,0))","𝔹","false"),
	Case("FifthMissingQuery","(λ(y:ℝ). [0<x]·λ[x]·δ(x^5)[y]//λ[y])(undefined(ℝ))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("CubicCriticalDensity","densityAtD(Λy. ∫dx λ[x]·δ(x³)[y],0)","ℝ","0⁻¹"),
	Case("CubicExcludedDensity","densityAtD(Λy. ∫dx λ[x]·δ(x³)[y]·[x≠0],0)","ℝ","0"),
	Case("CubicPartialDensity","densityAtD(pushforwardOnD(λ(x:ℝ).0<x⁻¹,λ(x:ℝ).x^3),0)","ℝ","undefined(ℝ)"),
	Case("CubicSymbolicPartialDensity","densityAtD(pushforwardOnD(λ(x:ℝ).0<(x-2)⁻¹,λ(x:ℝ).x^3),y)","ℝ"),
	Case("CubicRegularHole","densityAtD(pushforwardOnD(λ(x:ℝ).0<(x-2)⁻¹,λ(x:ℝ).x^3),8)","ℝ","undefined(ℝ)"),
	Case("CubicPartialComparison","0<densityAtD(pushforwardOnD(λ(x:ℝ).0<(x-2)⁻¹,λ(x:ℝ).x^3),8)","𝔹","undefined(𝔹)"),
	Case("CubicRegularDensity","densityAtD(pushforwardOnD(λ(x:ℝ).0<x⁻¹,λ(x:ℝ).x^3),8)","ℝ","1/12"),
	Case("CubicMissingDensity","densityAtD(pushforwardOnD(λ(x:ℝ).false,λ(x:ℝ).x^3),undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("CubicPredicateParameter","λ(p:ℝ→𝔹).densityAtD(pushforwardOnD(p,λ(x:ℝ).x^3),-8)","(ℝ→𝔹)→ℝ"),
	Case("CubicMissingPredicate","densityAtD(pushforwardOnD(undefined(ℝ→𝔹),λ(x:ℝ).x^3),8)","ℝ","undefined(ℝ)"),
	Case("FifthChart","Λy. ∫dx λ[x]·δ(x^5)[y]·[x≠0]","Distribution(ℝ)"),
	Case("CubicCriticalSource","Λy. ∫dx λ[x]·δ(x³)[y]·[0≤x]","Distribution(ℝ)"),
	Case("CubicPartialSource","pushforwardOnD(λ(x:ℝ).0<x⁻¹,λ(x:ℝ).x^3)","Distribution(ℝ)"),
	Case("WeightedFibreCancel","densityAtD(Λy. ∫dx λ[x]·δ(x²)[y]·x,4)","ℝ","0"),
	Case("WeightedFibreZero","densityAtD(Λy. ∫dx λ[x]·δ(x²)[y]·x,0)","ℝ","0"),
	Case("WeightedFibreCritical","densityAtD(integralD(λ(x:ℝ).scaleD(1+x²,δ(x*x))),0)","ℝ","undefined(ℝ)"),
	Case("WeightedFibreGap","densityAtD(integralD(λ(x:ℝ).scaleD(1+x²,δ(x*x))),-1)","ℝ","0"),
	Case("WeightedFibreMissing","densityAtD(bindD(weightD(λ(x:ℝ).x,lebesgueD()),λ(x:ℝ).δ(x²)),undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("WeightedSquareAbs","Λy. ∫dx λ[x]·δ(x²)[y]·abs(x)","Distribution(ℝ)","Λ(y:ℝ). [0<y]·λ[y]"),
	Case("BareCriticalGraph","Λy. ∫dx λ[x]·δ((1-2*x)^2)[y]","Distribution(ℝ)","Λ(y:ℝ). λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)]"),
	Case("RadiusRational","Λy. ∫dx λ[x]·δ((x/3-1)*(x/3-1))[y]","Distribution(ℝ)","Λ(y:ℝ). λ[3-3·sqrt(y), 3+3·sqrt(y)]"),
	Case("RadiusUnit","Λy. ∫dx λ[x]·δ(x²)[y]","Distribution(ℝ)","Λ(y:ℝ). λ[-sqrt(y), sqrt(y)]"),
	Case("ScaledSquare","Λy. ∫dx λ[x]·δ((2*x)^2)[y]","Distribution(ℝ)","Λ(y:ℝ). λ[-(1/2·sqrt(y)), 1/2·sqrt(y)]"),
	Case("ScaledFour","Λy. ∫dx λ[x]·δ(4*x²)[y]","Distribution(ℝ)","Λ(y:ℝ). λ[-(1/2·sqrt(y)), 1/2·sqrt(y)]"),
	Case("ExpandedSquare","Λy. ∫dx λ[x]·δ(4*x²-4*x+1)[y]","Distribution(ℝ)","Λ(y:ℝ). λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)]"),
	Case("SymmetricBand","Λy. ∫dx [0≤x≤1]·λ[x]·δ((1-2*x)^2)[y]","Distribution(ℝ)","Λ(y:ℝ). [y≤1]·λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)]"),
	Case("OpenSquareWindow","Λy. ∫dx [0<x<1]·λ[x]·δ((1-2*x)^2)[y]","Distribution(ℝ)","Λ(y:ℝ). [y<1]·λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)]"),
	Case("OpenSquareExpanded","Λy. ∫dx [-1<x<1]·λ[x]·δ(4*x²)[y]","Distribution(ℝ)","Λ(y:ℝ). [y<4]·λ[-(1/2·sqrt(y)), 1/2·sqrt(y)]"),
	Case("OpenSquareArgument","λ(k:Distribution(ℝ)→𝔹). k(Λy. ∫dx [0<x<1]·λ[x]·δ((1-2*x)^2)[y])","(Distribution(ℝ)→𝔹)→𝔹"),
	Case("OpenSquareAtCritical","densityAtD(Λy. [y<1]·λ[1/2-1/2·sqrt(y),1/2+1/2·sqrt(y)],0)","ℝ","undefined(ℝ)"),
	Case("OpenSquareAtEdge","densityAtD(Λy. [y<1]·λ[1/2-1/2·sqrt(y),1/2+1/2·sqrt(y)],1)","ℝ","0"),
	Case("OpenSquareInside","densityAtD(Λy. [y<1]·λ[1/2-1/2·sqrt(y),1/2+1/2·sqrt(y)],1/4)","ℝ","1"),
	Case("OpenSquareExcludedCritical","densityAtD(Λy. [y<0]·λ[-sqrt(y),sqrt(y)],0)","ℝ","0"),
	Case("OpenSquareMass","∫dy [y<1]·λ[1/2-1/2·sqrt(y),1/2+1/2·sqrt(y)]","ℝ","1"),
	Case("OpenSquareEmptyMass","∫dy [y<0]·λ[-sqrt(y),sqrt(y)]","ℝ","0"),
	Case("OpenSquareMissingBound","∫dy [y<undefined(ℝ)]·λ[-sqrt(y),sqrt(y)]","ℝ","undefined(ℝ)"),
	Case("HalfOpenSquareEdge","densityAtD(Λy. ∫dx [0≤x<1]·λ[x]·δ((1-2*x)^2)[y],1)","ℝ","1/4"),
	Case("ExpandedBand","Λy. ∫dx [-1≤x≤1]·λ[x]·δ(4*x²)[y]","Distribution(ℝ)","Λ(y:ℝ). [y≤4]·λ[-(1/2·sqrt(y)), 1/2·sqrt(y)]"),
	Case("ScaledSquareAtFour","densityAtD(Λy. ∫dx λ[x]·δ(4*x²)[y],4)","ℝ","1/4"),
	Case("PointBand","Λy. ∫dx [1≤x≤1]·λ[x]·δ((x-1)^2)[y]","Distribution(ℝ)","Λ(y:ℝ). [y≤0]·λ[1-sqrt(y), 1+sqrt(y)]"),
	Case("BandCutBelow","densityAtD(Λy. [y≤-1]·λ[-sqrt(y), sqrt(y)],0)","ℝ","0"),
	Case("ChartSumRadius","Λy. λ[±(y+1)]","Distribution(ℝ)","radiusImageD(0,λ(y:ℝ). y+1)"),
	Case("ChartWeightedSource","bindD(Λs. [s≤1]·λ[±(1/2·sqrt(s))],λ(t:ℝ).δ(t))","Distribution(ℝ)"),
	Case("CoverDensityZero","densityAtD(Λy. λ[-sqrt(y),sqrt(y)],0)","ℝ","undefined(ℝ)"),
	Case("CoverDensityPositive","densityAtD(Λy. λ[-sqrt(y),sqrt(y)],4)","ℝ","1/2"),
	Case("CoverDensityGap","densityAtD(Λy. λ[-sqrt(y),sqrt(y)],-2)","ℝ","0"),
	Case("CoverAsymmetric","Λy. λ[y+1,y²]","Distribution(ℝ)"),
	Case("CoverScaled","Λy. λ[-1/2·sqrt(y),1/2·sqrt(y)]","Distribution(ℝ)","Λ(y:ℝ). λ[-(1/2·sqrt(y)), 1/2·sqrt(y)]"),
	Case("CoverShifted","Λy. λ[3-3·sqrt(y),3+3·sqrt(y)]","Distribution(ℝ)","Λ(y:ℝ). λ[3-3·sqrt(y), 3+3·sqrt(y)]"),
	Case("CoverDuplicate","Λy. λ[y,y]","Distribution(ℝ)"),
	Case("CoverNested","bindD(Λs. λ[s+1,s²],λ(t:ℝ).δ(t))","Distribution(ℝ)"),
	Case("CoverThree","Λy. λ[y-1,y,y+1]","Distribution(ℝ)"),
	Case("CoordinateRayOpenLeft","Λx. λ[[x<0]·x²]","Distribution(ℝ)","Λ(x:ℝ). ([x<0]·(-2·x))·λ[x]"),
	Case("CoordinateRayClosedLeft","Λt. λ[[t≤0]·t⁴]","Distribution(ℝ)","Λ(t:ℝ). ([t≤0]·(-4·t^3))·λ[t]"),
	Case("CoordinateRayOpenRight","Λv. λ[[0<v]·v²]","Distribution(ℝ)","Λ(v:ℝ). ([0<v]·(2·v))·λ[v]"),
	Case("CoordinateRayClosedRight","Λu. λ[[0≤u]·u³]","Distribution(ℝ)","Λ(u:ℝ). ([0≤u]·(3·u^2))·λ[u]"),
	Case("CoordinateRayDensity","densityAtD(Λx. λ[[x<0]·x²],-2)","ℝ","4"),
	Case("CoordinateRayCut","densityAtD(Λx. λ[[x≤0]·x²],0)","ℝ","0"),
	Case("CoordinateRayMass","∫dx [-1≤x≤1]·λ[[x<0]·x²]","ℝ","1"),
	Case("CoordinateRayArgument","λ(k:Distribution(ℝ)→𝔹). k(Λx. λ[[x<0]·x²])","(Distribution(ℝ)→𝔹)→𝔹"),
	Case("CoordinateCorner","Λx. λ[[0<x]·x]","Distribution(ℝ)","Λ(y:ℝ). (∫dx λ[x]·δ(x^2)[y]·[x=0])+[0<y]·λ[y]"),
	Case("CoordinateCornerAt","densityAtD(Λx. λ[[0<x]·x],0)","ℝ","undefined(ℝ)"),
	Case("CoordinateCornerClosedAt","densityAtD(Λx. λ[[0≤x]·x],0)","ℝ","undefined(ℝ)"),
	Case("CoordinateCornerOff","densityAtD(Λx. λ[[0<x]·x],-2)","ℝ","0"),
	Case("CoordinateCornerOn","densityAtD(Λx. λ[[0<x]·x],2)","ℝ","1"),
	Case("CoordinateCornerLeft","densityAtD(Λx. λ[[x≤0]·x],-2)","ℝ","1"),
	Case("CoordinateCornerMass","∫dx [-1≤x≤1]·λ[[x>0]·x]","ℝ","1"),
	Case("CoordinateCornerPartial","∫dx [-1≤x≤1]·λ[[x>0]·x]·(1/x)","ℝ"),
	Case("CoordinateCornerArgument","λ(k:Distribution(ℝ)→𝔹). k(Λx. λ[[0<x]·x])","(Distribution(ℝ)→𝔹)→𝔹"),
	Case("CoordinateJumps","Λx. λ[[x<-1]·x²+[x>1]·x]","Distribution(ℝ)","Λ(x:ℝ). δ(-1)[x]+(δ(1)[x]+([x<-1]·(-2·x)+[1<x])·λ[x])"),
	Case("CoordinateJumpsSwapped","Λx. λ[[2<x]·x+[x<-1/2]·x²]","Distribution(ℝ)","Λ(x:ℝ). 1/4·δ(-1/2)[x]+(2·δ(2)[x]+([x<-1/2]·(-2·x)+[2<x])·λ[x])"),
	Case("CoordinateJumpsAt","densityAtD(Λx. λ[[x<-1]·x²+[1<x]·x],1)","ℝ","undefined(ℝ)"),
	Case("CoordinateJumpsOff","densityAtD(Λx. λ[[x<-1]·x²+[1<x]·x],-2)","ℝ","4"),
	Case("CoordinateJumpsClosed","∫dx [-1≤x≤1]·λ[[x<-1]·x²+[x>1]·x]","ℝ","2"),
	Case("CoordinateJumpsOpen","∫dx [-1<x<1]·λ[[x<-1]·x²+[x>1]·x]","ℝ","0"),
	Case("CoordinateJumpsBoth","∫dx [-2≤x≤2]·λ[[x<-1]·x²+[x>1]·x]","ℝ","6"),
	Case("GridPolynomial","Λx. λ[x³-x]","Distribution(ℝ)","Λ(x:ℝ). (abs(3·x^2-1))·λ[x]"),
	Case("GridSmoothJoin","densityAtD(Λx. λ[x+[0<x]·x²],0)","ℝ","1"),
	Case("GridArgument","λ(k:Distribution(ℝ)→𝔹). k(Λx. λ[x³-x])","(Distribution(ℝ)→𝔹)→𝔹"),
	Case("GridMixed","Λx. λ[[0<x]·x-[1<x]·(x-1)+2·[2≤x]]","Distribution(ℝ)"),
	Case("GridMixedClosed","∫dx [0≤x≤2]·λ[[0<x]·x-[1<x]·(x-1)+2·[2≤x]]","ℝ","3"),
	Case("GridMixedOpen","∫dx [0<x<2]·λ[[0<x]·x-[1<x]·(x-1)+2·[2≤x]]","ℝ","1"),
	Case("GridCornerDensity","densityAtD(Λx. λ[[0<x]·x-[1<x]·(x-1)+2·[2≤x]],1)","ℝ","undefined(ℝ)"),
	Case("GridJumpDensity","densityAtD(Λx. λ[[0<x]·x-[1<x]·(x-1)+2·[2≤x]],2)","ℝ","undefined(ℝ)"),
	Case("GridRegularDensity","densityAtD(Λx. λ[[0<x]·x-[1<x]·(x-1)+2·[2≤x]],1/2)","ℝ","1"),
	Case("GridRationalCorner","densityAtD(Λx. λ[abs(2*x-3)],3/2)","ℝ","undefined(ℝ)"),
	Case("GridDownwardJump","∫dx [0≤x≤1]·λ[[x<1/2]·3]","ℝ","3"),
	Case("GridPartialTest","∫dx [0≤x≤2]·λ[abs(2*x-3)]·(2*x-3)⁻¹","ℝ"),
	Case("GridSpike","Λx. λ[[x=0]]","Distribution(ℝ)","Λ(x:ℝ). λ[([x=0])]"),
	Case("CoordinateSquare","Λx. λ[x²]","Distribution(ℝ)","Λ(x:ℝ). (2·abs(x))·λ[x]"),
	Case("CoordinateSquareProduct","Λx. λ[x*x]","Distribution(ℝ)","Λ(x:ℝ). (2·abs(x))·λ[x]"),
	Case("CoordinateSquareNegative","densityAtD(Λx. λ[x²],-2)","ℝ","4"),
	Case("CoordinateSquarePositive","densityAtD(Λx. λ[x²],2)","ℝ","4"),
	Case("CoordinateSquareZero","densityAtD(Λx. λ[x²],0)","ℝ","0"),
	Case("CoordinateSquareLeftMass","∫dx [-1≤x≤0]·λ[x²]","ℝ","1"),
	Case("CoordinateSquareRightMass","∫dx [0≤x≤1]·λ[x²]","ℝ","1"),
	Case("CoordinateSquareZeroTest","∫dx 0·λ[x²]","ℝ","0"),
	Case("CoordinateSquareArgument","λ(k:Distribution(ℝ)→𝔹). k(Λx. λ[x²])","(Distribution(ℝ)→𝔹)→𝔹"),
	Case("CoverSingle","Λy. λ[1+y]","Distribution(ℝ)","Λ(x:ℝ). λ[x]"),
	Case("CoverAffineDensity","densityAtD(Λy. λ[3-2*y],1)","ℝ","2"),
	Case("CoverRegularSum","Λy. λ[sinh(y)]+λ[asinh(y)]","Distribution(ℝ)","Λ(y:ℝ). (cosh(y))·λ[y]+(sqrt(y^2+1)⁻¹)·λ[y]"),
	Case("CoverPairing","λ(t:ℝ→ℝ). ∫dy t(y)·λ[-sqrt(y),sqrt(y)]","(ℝ→ℝ)→ℝ"),
	Case("CoverPairingMissingEndpoint","∫dy y⁻¹·λ[-sqrt(y),sqrt(y)]","ℝ","undefined(ℝ)"),
	Case("CoverPairingGap","∫dy [0<y]·[y<0]·λ[-sqrt(y),sqrt(y)]","ℝ","0"),
	Case("CoverPairingShifted","λ(t:ℝ→ℝ). ∫dy t(y)·λ[3-3·sqrt(y),3+3·sqrt(y)]","(ℝ→ℝ)→ℝ"),
	Case("CoordinateSin","Λy. λ[sin(y)]","Distribution(ℝ)","Λ(y:ℝ). (abs(cos(y)))·λ[y]"),
	Case("CoordinateGaussian","Λy. λ[exp(-y²)]","Distribution(ℝ)","Λ(y:ℝ). (2·abs(y)·exp(-y^2))·λ[y]"),
	Case("CoordinateCosAffine","Λy. λ[cos(2*y+1)]","Distribution(ℝ)","Λ(y:ℝ). (2·abs(sin(2·y+1)))·λ[y]"),
	Case("CoordinateSmoothProduct","Λy. λ[sin(y)*exp(y)]","Distribution(ℝ)","Λ(y:ℝ). (abs(exp(y)·sin(y)+exp(y)·cos(y)))·λ[y]"),
	Case("CoordinateSmoothPower","densityAtD(Λy. λ[(1+sin(y))^3],0)","ℝ","3"),
	Case("CoordinateHyperbolic","densityAtD(Λy. λ[cosh(sinh(y))+sinh(2*y)],0)","ℝ","2"),
	Case("CoordinateRestrictedSin","Λy. λ[sin(y) | x. 0<x]","Distribution(ℝ)","Λ(y:ℝ). ([0<sin(y)]·abs(cos(y)))·λ[y]"),
	Case("CoordinateRestrictedSinAtZero","densityAtD(Λy. λ[sin(y) | x. 0<x],0)","ℝ","0"),
	Case("PositiveCoordinateLog","densityAtD(Λx. λ[log(1+x²)],1)","ℝ","1"),
	Case("PositiveCoordinateStationary","densityAtD(Λx. λ[log(1+x²)],0)","ℝ","0"),
	Case("PositiveCoordinateRoot","densityAtD(Λx. λ[sqrt(9+16*x²)],1)","ℝ","16/5"),
	Case("PositiveCoordinateInverse","densityAtD(Λx. λ[(1+x²)⁻¹],1)","ℝ","1/2"),
	Case("PositiveCoordinateMixed","densityAtD(Λx. λ[log(exp(sin(x))+cosh(x))],0)","ℝ","1/2"),
	Case("PositiveCoordinateNestedRoot","densityAtD(Λx. λ[log(sqrt(9+16*x²))],1)","ℝ","16/25"),
	Case("PositiveCoordinateNestedInverse","densityAtD(Λx. λ[log((1+x²)⁻¹)],1)","ℝ","1"),
	Case("PositiveCoordinatePower","densityAtD(Λx. λ[log((exp(x)+1)^3)],0)","ℝ","3/2"),
	Case("PositiveCoordinateRestricted","densityAtD(Λx. λ[sqrt(9+16*x²) | u. 0<u<5],1)","ℝ","0"),
	Case("PositiveCoordinateClosed","densityAtD(Λx. λ[sqrt(9+16*x²) | u. 0<u≤5],1)","ℝ","16/5"),
	Case("CenteredCoordinateLog","densityAtD(Λx. λ[log(x^2+x+1)],0)","ℝ","1"),
	Case("CenteredCoordinateStationary","densityAtD(Λx. λ[log(x^2+x+1)],-1/2)","ℝ","0"),
	Case("CenteredCoordinateRoot","densityAtD(Λx. λ[sqrt(x^2-6*x+25)],0)","ℝ","3/5"),
	Case("CenteredCoordinateSquares","densityAtD(Λx. λ[log(x^2+(x-1)^2)],0)","ℝ","2"),
	Case("CenteredCoordinateQuartic","densityAtD(Λx. λ[log(x^4-4*x^3+7*x^2-6*x+4)],0)","ℝ","3/2"),
	Case("CenteredCoordinateNested","densityAtD(Λx. λ[log((x^2-2*x+1)*exp(x)+1)],0)","ℝ","1/2"),
	Case("CoordinateTouchingLog","Λx. λ[log(x^2-2*x+1)]","Distribution(ℝ)"),
	Case("CoordinateSignChangeLog","Λx. λ[log(x^2-3*x+1)]","Distribution(ℝ)"),
	Case("FlatCoordinateUnitJump","∫dx λ[exp([0≤x]·1)]","ℝ","e-1"),
	Case("FlatCoordinateReversed","∫dx λ[exp([x<0]·1)]","ℝ","e-1"),
	Case("FlatCoordinateClosed","massD(Λx. λ[exp([x≤0]·1)])","ℝ","e-1"),
	Case("FlatCoordinateTwoJumps","∫dx λ[exp([x<0]·2+[1<x]·3)]","ℝ","exp(2)+exp(3)-2"),
	Case("FlatCoordinateLog","∫dx λ[log(1+[0≤x]·2)]","ℝ","log(3)"),
	Case("FlatCoordinateRoot","∫dx λ[sqrt(1+[0≤x]·3)]","ℝ","1"),
	Case("FlatCoordinateReciprocal","∫dx λ[(1+[0≤x]·1)⁻¹]","ℝ","1/2"),
	Case("FlatCoordinateSinh","∫dx λ[sinh([0≤x]·1)]","ℝ","sinh(1)"),
	Case("FlatCoordinateArsinh","∫dx λ[asinh([0≤x]·1)]","ℝ","asinh(1)"),
	Case("FlatCoordinateGrowing","∫dx λ[exp(x+[0≤x]·2)]","ℝ"),
	Case("FlatCoordinateBoundary","∫dx λ[log([0≤x]·2)]","ℝ"),
	Case("TraceCoordinateExpJump","densityAtD(Λx. λ[exp([0≤x]·2)],0)","ℝ","undefined(ℝ)"),
	Case("TraceCoordinateExpRight","densityAtD(Λx. λ[exp(x+[0≤x]·2)],1)","ℝ","exp(3)"),
	Case("TraceCoordinateExpLeft","densityAtD(Λx. λ[exp(x+[0≤x]·2)],-1)","ℝ","exp(-1)"),
	Case("TraceCoordinateTwo","densityAtD(Λx. λ[exp([x<0]·2+[1<x]·3)],1)","ℝ","undefined(ℝ)"),
	Case("TraceCoordinateLog","densityAtD(Λx. λ[log(1+abs(x)+[0≤x]·2)],1)","ℝ","1/4"),
	Case("TraceCoordinateLogJump","densityAtD(Λx. λ[log(1+abs(x)+[0≤x]·2)],0)","ℝ","undefined(ℝ)"),
	Case("TraceCoordinateRoot","densityAtD(Λx. λ[sqrt(1+[0≤x]·3)],1)","ℝ","0"),
	Case("TraceCoordinateReciprocal","densityAtD(Λx. λ[(1+abs(x)+[0≤x]·2)⁻¹],1)","ℝ","1/16"),
	Case("TraceCoordinateMixed","densityAtD(Λx. λ[log(1+abs(x)+[1≤x]·2)],0)","ℝ","undefined(ℝ)"),
	Case("TraceCoordinateDomain","densityAtD(Λx. λ[([0≤x]·2)⁻¹],1)","ℝ"),
	Case("ProbeGridJump","densityAtD(Λx. λ[x+[1≤x]·3],1)","ℝ","undefined(ℝ)"),
	Case("ProbeGridJumpAway","densityAtD(Λx. λ[x+[1≤x]·3],2)","ℝ","1"),
	Case("ProbeGridCorners","densityAtD(Λx. λ[abs(x-1)+abs(x+1)],-1)","ℝ","undefined(ℝ)"),
	Case("ProbeGridMiddle","densityAtD(Λx. λ[abs(x-1)+abs(x+1)],0)","ℝ","0"),
	Case("ProbeGridAffine","densityAtD(Λx. λ[2*abs(x-1)],2/3)","ℝ","2"),
	Case("DecreasingSmoothJoin","Λx. λ[[x<0]·(-2*x)+[0≤x]·(-2*x+x^2)]","Distribution(ℝ)","Λ(x:ℝ). ([0≤x]·abs(2·x-2)+[x<0]·2)·λ[x]"),
	Case("DecreasingSmoothFraction","Λx. λ[[x<1]·(-x/2)+[1≤x]·((x-1)^2-x/2)]","Distribution(ℝ)"),
	Case("BoundNeutralMass","λ(f:ℝ→ℝ).λ(x:ℝ). massD(zeroD(ℝ))+f(x)","(ℝ→ℝ)→ℝ→ℝ","λ(f:ℝ→ℝ). λ(x:ℝ). f(x)"),
	Case("BoundNeutralOne","λ(f:ℝ→ℝ).λ(x:ℝ). f(x)*massD(δ((3:ℝ)))","(ℝ→ℝ)→ℝ→ℝ","λ(f:ℝ→ℝ). λ(x:ℝ). f(x)"),
	Case("BoundNeutralPowers","λ(r:ℝ).λ(k:ℕ). ∑(i:ℕ). [i<k]·r^i","ℝ→ℕ→ℝ","λ(r:ℝ). λ(k:ℕ). [k≠0]·([r≠1]·((r^k-1)·(r-1)⁻¹)+[r=1]·k)"),
	Case("BoundNeutralBoth","λ(f:ℝ→ℝ).λ(x:ℝ). massD(δ((3:ℝ)))*f(x)+massD(zeroD(ℝ))","(ℝ→ℝ)→ℝ→ℝ","λ(f:ℝ→ℝ). λ(x:ℝ). f(x)"),
	Case("BoundStrictZero","λ(f:ℝ→ℝ).λ(x:ℝ). massD(zeroD(ℝ))*f(x)","(ℝ→ℝ)→ℝ→ℝ","λ(f:ℝ→ℝ). λ(x:ℝ). 0·f(x)"),
	Case("ImageWindowInterior","Λx. λ[(1+[0≤x]·1)⁻¹ | u. 1/2<u<3/4]","Distribution(ℝ)","Λ(x:ℝ). 1/4·δ(0)[x]+0·λ[x]"),
	Case("ImageWindowMass","∫dx λ[(1+[0≤x]·1)⁻¹ | u. 1/2<u<3/4]","ℝ","1/4"),
	Case("ImageWindowUnit","Λx. λ[sqrt(1+[0≤x]·3) | u. 1≤u≤2]","Distribution(ℝ)","Λ(x:ℝ). δ(0)[x]+0·λ[x]"),
	Case("ImageWindowReverse","Λx. λ[sqrt(4+[x<0]·5) | u. 9/4<u<11/4]","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(0)[x]+0·λ[x]"),
	Case("ImageWindowTwo","Λx. λ[(1+[x<0]·1+[1<x]·3)⁻¹ | u. 1/4<u<3/4]","Distribution(ℝ)","Λ(x:ℝ). 1/4·δ(0)[x]+(1/2·δ(1)[x]+0·λ[x])"),
	Case("ImageWindowDisjoint","Λx. λ[(1+[0≤x]·1)⁻¹ | u. 2<u]","Distribution(ℝ)","Λ(x:ℝ). 0·δ(0)[x]+0·λ[x]"),
	Case("ImageWindowMixed","Λx. λ[(1+abs(x)+[1≤x]·2)⁻¹ | u. 0<u]","Distribution(ℝ)"),
	Case("ImageWindowCornerExcluded","densityAtD(Λx. λ[(1+abs(x)+[1≤x]·2)⁻¹ | u. u<1],0)","ℝ","0"),
	Case("ImageWindowCornerIncluded","densityAtD(Λx. λ[(1+abs(x)+[1≤x]·2)⁻¹ | u. u≤1],0)","ℝ","undefined(ℝ)"),
	Case("WindowProbeRegular","densityAtD(Λx. λ[(1+abs(x)+[1≤x]·2)⁻¹ | u. 0<u],2)","ℝ","1/25"),
	Case("WindowProbeEmpty","densityAtD(Λx. λ[(1+abs(x)+[1≤x]·2)⁻¹ | u. 2<u],1)","ℝ","0"),
	Case("WindowProbeJump","densityAtD(Λx. λ[(1+[0≤x]·1)⁻¹ | u. u<1],0)","ℝ","undefined(ℝ)"),
	Case("WindowProbeTwo","densityAtD(Λx. λ[(1+[x<0]·1+[1<x]·3)⁻¹ | u. 1/4<u<3/4],1)","ℝ","undefined(ℝ)"),
	Case("WindowProbeRoot","densityAtD(Λx. λ[sqrt(4+[x<0]·5) | u. 3<u],0)","ℝ","0"),
	Case("ImageWindowPartial","λ(k:ℝ→𝔹). Λx. λ[(1+[0≤x]·1)⁻¹ | u. k(u)]","(ℝ→𝔹)→Distribution(ℝ)"),
	Case("ImageWindowEndpoint","Λx. λ[(1+[0≤x]·1)⁻¹ | u. (u-1/2)⁻¹<2]","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("SymbolicJumpLong","λ(k:ℝ→𝔹). Λx. λ[2·[0≤x] | u. k(u)]","(ℝ→𝔹)→Distribution(ℝ)"),
	Case("SymbolicJumpReversed","λ(k:ℝ→𝔹). Λx. λ[sqrt(4+5·[x<0]) | u. k(u)]","(ℝ→𝔹)→Distribution(ℝ)"),
	Case("SymbolicJumpDistant","densityAtD(Λx. λ[(1+[0≤x]·1)⁻¹ | u. (u-1/2)⁻¹<2],2)","ℝ","undefined(ℝ)"),
	Case("TraversalHoleInterior","Λx. λ[2·[0≤x] | u. (u-1)⁻¹<2]","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("TraversalHoleReversed","Λx. λ[sqrt(4+[x<0]·5) | u. (u-3)⁻¹<0]","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("TraversalHoleCell","Λx. λ[2·[0≤x] | u. sqrt((u-1/4)*(u-3/4))<2]","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("TraversalHoleMasked","Λx. λ[3·[0≤x] | u. if u=1 then true else (u-1)⁻¹<0]","Distribution(ℝ)","Λ(x:ℝ). δ(0)[x]+0·λ[x]"),
	Case("TraversalHoleShortCircuit","Λx. λ[2·[0≤x] | u. u<1 ∨ (u-1/2)⁻¹<0]","Distribution(ℝ)","Λ(x:ℝ). δ(0)[x]+0·λ[x]"),
	Case("SymbolicJumpOutside","Λx. λ[(1+[0≤x]·1)⁻¹ | u. (u-2)⁻¹<0]","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(0)[x]+0·λ[x]"),
	Case("ImageCoordinateReciprocal","Λx. λ[(1+[0≤x]·1)⁻¹]","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(0)[x]+0·λ[x]"),
	Case("ImageCoordinateUnit","Λx. λ[sqrt(1+[0≤x]·3)]","Distribution(ℝ)","Λ(x:ℝ). δ(0)[x]+0·λ[x]"),
	Case("ImageCoordinateReverse","Λx. λ[sqrt(4+[x<0]·5)]","Distribution(ℝ)","Λ(x:ℝ). δ(0)[x]+0·λ[x]"),
	Case("ImageCoordinateTwo","Λx. λ[(1+[x<0]·1+[1<x]·3)⁻¹]","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(0)[x]+(3/4·δ(1)[x]+0·λ[x])"),
	Case("ImageCoordinateRegular","Λx. λ[(1+abs(x)+[0≤x]·2)⁻¹]","Distribution(ℝ)","Λ(x:ℝ). 2/3·δ(0)[x]+(((abs(x)+[0≤x]·2+1)^2)⁻¹·([x<0]+[0<x]))·λ[x]"),
	Case("ImageCoordinateMixed","Λx. λ[(1+abs(x)+[1≤x]·2)⁻¹]","Distribution(ℝ)"),
	Case("ImageCoordinateHigher","λ(k:Distribution(ℝ)→ℝ). k(Λx. λ[(1+[0≤x]·1)⁻¹])","(Distribution(ℝ)→ℝ)→ℝ"),
	Case("RootImageDescending","Λx. λ[sqrt(2+[x<0]·1)]","Distribution(ℝ)","Λ(x:ℝ). (-sqrt(2)+sqrt(3))·δ(0)[x]+0·λ[x]"),
	Case("RootImageFraction","Λx. λ[sqrt(1/4+[0≤x]·1/4)]","Distribution(ℝ)","Λ(x:ℝ). (1/2·sqrt(2)-1/2)·δ(0)[x]+0·λ[x]"),
	Case("RootImageTwo","Λx. λ[sqrt(2+[x<0]·2+[1<x]·3)]","Distribution(ℝ)","Λ(x:ℝ). (-sqrt(2)+2)·δ(0)[x]+((-sqrt(2)+sqrt(5))·δ(1)[x]+0·λ[x])"),
	Case("RootImagePartial","Λx. λ[sqrt(1+[0≤x]·1) | u. 1<u<2]","Distribution(ℝ)","Λ(x:ℝ). λ[sqrt([0≤x]+1) | u. 1<u∧u<2]"),
	Case("ImageCoordinateIrrational","Λx. λ[sqrt(1+[0≤x]·1)]","Distribution(ℝ)","Λ(x:ℝ). (sqrt(2)-1)·δ(0)[x]+0·λ[x]"),
	Case("ChangedCoordinateExp","Λx. λ[exp(abs(x))]","Distribution(ℝ)","Λ(y:ℝ). (∫dx λ[x]·δ(x^2)[y]·[x=0])+(([y<0]+[0<y])·exp(abs(y)))·λ[y]"),
	Case("ChangedCoordinateExpLeft","densityAtD(Λx. λ[exp(abs(x))],-1)","ℝ","e"),
	Case("ChangedCoordinateLogLeft","densityAtD(Λx. λ[log(1+abs(x))],-3)","ℝ","1/4"),
	Case("ChangedCoordinateLogCorner","densityAtD(Λx. λ[log(1+abs(x))],0)","ℝ","undefined(ℝ)"),
	Case("ChangedCoordinateRoot","densityAtD(Λx. λ[sqrt(1+abs(x))],3)","ℝ","1/4"),
	Case("ChangedCoordinateReciprocal","densityAtD(Λx. λ[(1+abs(x))⁻¹],-1)","ℝ","1/4"),
	Case("ChangedCoordinateSinh","densityAtD(Λx. λ[sinh(abs(x-2))],2)","ℝ","undefined(ℝ)"),
	Case("DensityHoleBefore","λ(h:ℝ→ℝ).massD(weightD(h,weightD(λ(x:ℝ).(x²-2)⁻¹,lebesgueD())))","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). undefined(ℝ)"),
	Case("DensityHoleAfter","λ(h:ℝ→ℝ).massD(weightD(λ(x:ℝ).(x²-2)⁻¹,weightD(h,lebesgueD())))","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). undefined(ℝ)"),
	Case("DensityHoleBoth","λ(h:ℝ→ℝ).λ(g:ℝ→ℝ).massD(weightD(h,weightD(λ(x:ℝ).(x²-2)⁻¹,weightD(g,lebesgueD()))))","(ℝ→ℝ)→(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). λ(g:ℝ→ℝ). undefined(ℝ)"),
	Case("DensityHoleCaptures","λ(h:ℝ→ℝ→ℝ).λ(t:ℝ).massD(weightD(h(t),weightD(λ(x:ℝ).(x²-2)⁻¹,lebesgueD())))","(ℝ→ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ→ℝ). λ(t:ℝ). undefined(ℝ)"),
	Case("DensityHoleMissing","defined(massD(weightD(undefined(ℝ→ℝ),weightD(λ(x:ℝ).(x²-2)⁻¹,lebesgueD()))))","𝔹","false"),
	Case("DensityHoleDirac","massD(weightD(λ(x:ℝ).(x²-2)⁻¹,δ((0:ℝ))))","ℝ","-1/2"),
	Case("DensityHoleAbstract","λ(d:Distribution(ℝ)).massD(weightD(λ(x:ℝ).(x²-2)⁻¹,d))","Distribution(ℝ)→ℝ"),
	Case("DensityHoleUnknown","λ(h:ℝ→ℝ).massD(weightD(h,lebesgueD()))","(ℝ→ℝ)→ℝ"),
	Case("DensityHoleMasked","λ(h:ℝ→ℝ).massD(weightD(h,weightD(λ(x:ℝ).[false]·(x²-2)⁻¹,lebesgueD())))","(ℝ→ℝ)→ℝ"),
	Case("MissingQuadraticPositive","∫dx (x²-2)⁻¹·λ[x]","ℝ","undefined(ℝ)"),
	Case("MissingQuadraticTranslated","∫dx ((2*x-3)^2-2)⁻¹·λ[x]","ℝ","undefined(ℝ)"),
	Case("MissingQuadraticNegative","∫dx (2-x²)⁻¹·λ[x]","ℝ","undefined(ℝ)"),
	Case("MissingQuadraticTouch","∫dx (1-2*x+x²)⁻¹·λ[x]","ℝ","undefined(ℝ)"),
	Case("MissingQuadraticAffine","∫dx (2*x+3)⁻¹·λ[x]","ℝ","undefined(ℝ)"),
	Case("MissingQuadraticStrictZero","∫dx 0*(x²-2)⁻¹·λ[x]","ℝ","undefined(ℝ)"),
	Case("MissingQuadraticStrictSum","∫dx (1+(x²-2)⁻¹)·λ[x]","ℝ","undefined(ℝ)"),
	Case("MissingQuadraticHigher","λ(h:ℝ→ℝ).∫dx h(x)*(x²-2)⁻¹·λ[x]","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). undefined(ℝ)"),
	Case("MissingQuadraticFactor","λ(a:ℝ).∫dx a*(x²-1)⁻¹·λ[x]","ℝ→ℝ","λ(a:ℝ). undefined(ℝ)"),
	Case("MissingQuadraticMask","λ(p:𝔹).∫dx [p]·(x²-2)⁻¹·λ[x]","𝔹→ℝ","λ(p:𝔹). [p]·(undefined(ℝ))"),
	Case("MissingQuadraticInactive","∫dx [false]·(x²-2)⁻¹·λ[x]","ℝ","0"),
	Case("MissingQuadraticOutside","∫dx [2<x<3]·(x²-2)⁻¹·λ[x]","ℝ"),
	Case("MissingQuadraticHoleHidden","∫dx [x²≠2]·(x²-2)⁻¹·λ[x]","ℝ"),
	Case("MissingQuadraticSafe","∫dx (2+x²)⁻¹·λ[x]","ℝ","1/2·sqrt(2)·π"),
	Case("MissingQuadraticBottom","defined(∫dx undefined(ℝ)·λ[x])","𝔹","false"),
	Case("MissingQuadraticZeroArg","defined((λ(a:ℝ).∫dx a⁻¹*(1+x²)⁻¹·λ[x])(0))","𝔹","false"),
	Case("StrictBoundPartial","λ(h:ℝ→ℝ).λ(t:ℝ).defined(h(t)<undefined(ℝ))","(ℝ→ℝ)→ℝ→𝔹","λ(h:ℝ→ℝ). λ(t:ℝ). false"),
	Case("StrictBoundMask","[false]·undefined(ℝ)","ℝ","0"),
	Case("StrictBoundAnd","false∧undefined(𝔹)","𝔹","false"),
	Case("StrictBoundOr","true∨undefined(𝔹)","𝔹","true"),
	Case("DirectedTotalLogistic","∫dx λ[(1+exp(-x))⁻¹]","ℝ","1"),
	Case("DirectedTotalReflected","∫dx λ[(1+exp(x))⁻¹]","ℝ","1"),
	Case("DirectedTotalSteep","∫dx λ[(1+exp(-7*x+3))⁻¹]","ℝ","1"),
	Case("DirectedTotalScaled","∫dx λ[-3*(1+exp(-x))⁻¹]","ℝ","3"),
	Case("DirectedTotalAtanExp","∫dx λ[atan(exp(x))]","ℝ","1/2·π"),
	Case("DirectedTotalAtanReflected","∫dx λ[atan(exp(-x))]","ℝ","1/2·π"),
	Case("DirectedTotalHalfRange","∫dx λ[atan((1+exp(-x))⁻¹)]","ℝ","1/4·π"),
	Case("DirectedTotalAdd","∫dx λ[(1+exp(-x))⁻¹+atan(x)]","ℝ","π+1"),
	Case("DirectedTotalShift","∫dx λ[atan(exp(x))+7]","ℝ","1/2·π"),
	Case("DirectedTotalLog","∫dx λ[log(1+(1+exp(-x))⁻¹)]","ℝ","log(2)"),
	Case("DirectedTotalRoot","∫dx λ[sqrt(1+(1+exp(-x))⁻¹)]","ℝ","sqrt(2)-1"),
	Case("DirectedTotalNested","∫dx λ[(2+(1+exp(x))⁻¹)⁻¹]","ℝ","1/6"),
	Case("DirectedTotalConstant","∫dx λ[3]","ℝ","0"),
	Case("DirectedTotalPole","∫dx λ[x⁻¹]","ℝ","∫dx λ[(x⁻¹)]"),
	Case("DirectedTotalOneEnd","∫dx λ[exp(-x)]","ℝ","∫dx (exp(-x))·λ[x]"),
	Case("DirectedTotalOscillation","∫dx λ[sin(x)]","ℝ","∫dx (abs(cos(x)))·λ[x]"),
	Case("DirectedTotalTurning","∫dx λ[exp(-(x²))]","ℝ","2"),
	Case("DirectedRayCDF","λ(u:ℝ).∫dx [x≤u]·λ[(1+exp(-x))⁻¹]","ℝ→ℝ","λ(u:ℝ). (exp(-u)+1)⁻¹"),
	Case("DirectedRaySurvival","λ(l:ℝ).∫dx [l<x]·λ[(1+exp(-x))⁻¹]","ℝ→ℝ","λ(l:ℝ). 1-(exp(-l)+1)⁻¹"),
	Case("DirectedRayDecreasingCDF","λ(u:ℝ).∫dx [x<u]·λ[(exp(x)+1)⁻¹]","ℝ→ℝ","λ(u:ℝ). 1-(exp(u)+1)⁻¹"),
	Case("DirectedRayDecreasingSurvival","λ(l:ℝ).∫dx [l≤x]·λ[(exp(x)+1)⁻¹]","ℝ→ℝ","λ(l:ℝ). (exp(l)+1)⁻¹"),
	Case("DirectedRayAtZero","∫dx [x≤0]·λ[(1+exp(-x))⁻¹]","ℝ","1/2"),
	Case("DirectedRayReverseAtZero","∫dx [0<x]·λ[(exp(x)+1)⁻¹]","ℝ","1/2"),
	Case("DirectedRayNested","∫dx [0<x]·λ[atan(exp(x))]","ℝ","1/4·π"),
	Case("DirectedRayArctanLeft","∫dx [x<0]·λ[atan(exp(x))]","ℝ","1/4·π"),
	Case("DirectedRayReflected","∫dx [x<0]·λ[atan(exp(-x))]","ℝ","1/4·π"),
	Case("DirectedRayDecaying","λ(l:ℝ).∫dx [l<x]·λ[exp(-2*x)]","ℝ→ℝ","λ(l:ℝ). exp(-2·l)"),
	Case("DirectedRayOppositeEnd","λ(u:ℝ).∫dx [x≤u]·λ[exp(3*x-1)]","ℝ→ℝ","λ(u:ℝ). exp(3·u-1)"),
	Case("DirectedRayScaled","∫dx [0≤x]·λ[2*atan(exp(x))]","ℝ","1/2·π"),
	Case("DirectedRayLogPath","∫dx [x≤0]·λ[log(1+exp(x))]","ℝ","log(2)"),
	Case("DirectedRayComposite","∫dx [x≤0]·λ[atan((1+exp(-x))⁻¹)]","ℝ","atan(1/2)"),
	Case("DirectedRayPartial","λ(h:ℝ→ℝ).λ(t:ℝ).∫dx [x<h(t)]·λ[(1+exp(-x))⁻¹]","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(t:{t:ℝ | holds((t∈domain(h)))}). (exp(-h(t))+1)⁻¹"),
	Case("DirectedRayMissingUpper","defined(∫dx [x≤undefined(ℝ)]·λ[(1+exp(-x))⁻¹])","𝔹","false"),
	Case("DirectedRayMissingLower","defined(∫dx [undefined(ℝ)<x]·λ[(exp(x)+1)⁻¹])","𝔹","false"),
	Case("DirectedRayPole","∫dx [x<1]·λ[x⁻¹]","ℝ","∫dx [x<1]·λ[(x⁻¹)]"),
	Case("DirectedRayUnbounded","∫dx [0<x]·λ[exp(x)]","ℝ","∫dx ([0<x]·exp(x))·λ[x]"),
	Case("DirectedRangeRoot","∫dx [0≤x≤1]·λ[sqrt(exp(x)+1)]","ℝ","-sqrt(2)+sqrt(e+1)"),
	Case("DirectedRangeLog","λ(l:ℝ).λ(u:ℝ).∫dx [l<x≤u]·λ[log(1+exp(x))]","ℝ→ℝ→ℝ","λ(l:ℝ). λ(u:ℝ). [l<u]·(-log(exp(l)+1)+log(exp(u)+1))"),
	Case("DirectedRangeInverse","λ(u:ℝ).∫dx [0<x≤u]·λ[(1+exp(x))⁻¹]","ℝ→ℝ","λ(u:ℝ). [0<u]·(1/2-(exp(u)+1)⁻¹)"),
	Case("DirectedRangeInverseDown","∫dx [0≤x≤1]·λ[(1+exp(-x))⁻¹]","ℝ","-1/2+(exp(-1)+1)⁻¹"),
	Case("DirectedRangeInverseNegative","∫dx [0≤x≤1]·λ[(-2*exp(x))⁻¹]","ℝ","-1/2·exp(-1)+1/2"),
	Case("DirectedRangeTwice","∫dx [0≤x≤1]·λ[(sqrt(exp(-x)+1))⁻¹]","ℝ","-1/2·sqrt(2)+sqrt(exp(-1)+1)⁻¹"),
	Case("DirectedRangeNested","λ(u:ℝ).∫dx [0≤x<u]·λ[atan(log(1+exp(-x)))]","ℝ→ℝ","λ(u:ℝ). [0<u]·(atan(log(2))-atan(log(exp(-u)+1)))"),
	Case("DirectedRangeScaled","∫dx [-1≤x≤1]·λ[(-3/2)*atan(x)]","ℝ","3/4·π"),
	Case("DirectedRangeScaleRight","∫dx [0≤x≤1]·λ[exp(-x)*(-2)]","ℝ","-2·exp(-1)+2"),
	Case("DirectedRangeSquare","∫dx [0≤x≤1]·λ[(sqrt(1+exp(x))-2)^2]","ℝ","(sqrt(e+1)-2)·abs(sqrt(e+1)-2)-4·sqrt(2)+6"),
	Case("DirectedRangeCosh","∫dx [-1≤x≤1]·λ[cosh(log(1+exp(x)))]","ℝ","-1/2·exp(-1)+1/2·e+(e+1)⁻¹·(1/2)-(exp(-1)+1)⁻¹·(1/2)"),
	Case("DirectedRangePartial","λ(h:ℝ→ℝ).λ(t:ℝ).∫dx [0≤x<h(t)]·λ[(1+exp(-x))⁻¹]","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(t:ℝ). [0<h(t)]·(-1/2+(exp(-h(t))+1)⁻¹)"),
	Case("DirectedRangeMissing","defined(∫dx [0<x<undefined(ℝ)]·λ[log(1+exp(x))])","𝔹","false"),
	Case("DirectedRangePole","∫dx [-1≤x≤1]·λ[x⁻¹]","ℝ"),
	Case("DirectedRangeTouch","∫dx [-1≤x≤1]·λ[sqrt(x²)]","ℝ","2"),
	Case("DirectedRangeGap","∫dx [1≤x≤2]·λ[log(x)]","ℝ"),
	Case("VariationSquareCross","∫dx [-1≤x≤1]·λ[x²]","ℝ","2"),
	Case("VariationSquareShift","∫dx [0≤x≤1]·λ[(1-2*x)^2]","ℝ","2"),
	Case("VariationSquareDown","∫dx [1<x≤3]·λ[(2-x)^2]","ℝ","2"),
	Case("VariationSixth","∫dx [-1≤x≤2]·λ[x^6]","ℝ","65"),
	Case("PeriodicSpanSine","∫dx [0≤x≤2*π]·λ[sin(x)]","ℝ","4"),
	Case("PeriodicSpanCosine","∫dx [-π≤x≤π]·λ[cos(x)]","ℝ","4"),
	Case("PeriodicSpanQuarter","∫dx [0<x<π/2]·λ[sin(x)]","ℝ","1"),
	Case("PeriodicSpanCrest","∫dx [π/2≤x<3*π/2]·λ[sin(x)]","ℝ","2"),
	Case("PeriodicSpanNegative","∫dx [-3*π/2<x≤-π/2]·λ[sin(x)]","ℝ","2"),
	Case("PeriodicSpanMillion","∫dx [0≤x≤1000000*π]·λ[cos(x)]","ℝ","2000000"),
	Case("PeriodicSpanAffine","∫dx [0≤x≤π]·λ[sin(-3*x)]","ℝ","6"),
	Case("PeriodicSpanInside","∫dx [π/3≤x≤2*π/3]·λ[sin(x)]","ℝ","-sqrt(3)+2"),
	Case("PeriodicSpanReverse","∫dx [π≤x<0]·λ[cos(x)]","ℝ","0"),
	Case("PeriodicSpanPoint","∫dx [π/2≤x≤π/2]·λ[sin(x)]","ℝ","0"),
	Case("PeriodicSpanMissing","defined(∫dx [0<x≤undefined(ℝ)]·λ[cos(x)])","𝔹","false"),
	Case("PeriodicSpanSymbolic","λ(u:ℝ).∫dx [0<x≤u]·λ[cos(x)]","ℝ→ℝ"),
	Case("PeriodicSpanSineSymbolic","λ(l:ℝ).λ(u:ℝ).∫dx [l≤x≤u]·λ[sin(x)]","ℝ→ℝ→ℝ"),
	Case("PeriodicSpanWhole","∫dx λ[sin(atan(x))]","ℝ","2"),
	Case("PeriodicSpanWholeCos","∫dx λ[cos(atan(x))]","ℝ","2"),
	Case("PeriodicSpanRay","∫dx [x≤0]·λ[cos(atan(x))]","ℝ","1"),
	Case("PeriodicSpanRayDown","∫dx [0≤x]·λ[sin(atan(-x))]","ℝ","1"),
	Case("PeriodicSpanUnbounded","∫dx λ[cos(x)]","ℝ"),
	Case("PeriodicSpanNonmonotone","∫dx [-π≤x≤π]·λ[sin(sin(x))]","ℝ","4·sin(1)"),
	Case("AffineTurnScale","∫dx [0≤x≤2*π]·λ[3*sin(x)+4]","ℝ","12"),
	Case("AffineTurnNegative","∫dx [0≤x≤2*π]·λ[7-2*cos(x)]","ℝ","8"),
	Case("AffineTurnMillion","∫dx [0≤x≤1000000*π]·λ[3*cos(x)+7]","ℝ","6000000"),
	Case("AffineTurnRight","∫dx [0≤x≤π]·λ[(cos(x)+4)*(-3)]","ℝ","6"),
	Case("AffineTurnSquare","∫dx [-2≤x≤1]·λ[3*x²+7]","ℝ","15"),
	Case("AffineTurnSymbolic","∫dx [0≤x≤2*π]·λ[a*sin(x)+b]","ℝ","4·abs(a)"),
	Case("AffineTurnPi","∫dx [0≤x≤2*π]·λ[π*cos(x)+e]","ℝ","4·π"),
	Case("AffineTurnFraction","∫dx [0≤x≤2*π]·λ[1/3*cos(x)-2/3]","ℝ","4/3"),
	Case("AffineTurnWhole","∫dx λ[7-3*sin(atan(x))]","ℝ","6"),
	Case("AffineTurnRay","∫dx [0≤x]·λ[5-3*cos(atan(x))]","ℝ","3"),
	Case("AffineTurnDescending","∫dx λ[6-2*cos(atan(-x))]","ℝ","4"),
	Case("AffineTurnCosh","∫dx [-1≤x≤1]·λ[3*cosh(x)+2]","ℝ","6·cosh(1)-6"),
	Case("AffineTurnOffset","∫dx [-1≤x≤1]·λ[atan(x)^2+b]","ℝ","1/8·π^2"),
	Case("AffineTurnEmpty","∫dx [1<x≤0]·λ[7-2*cos(x)]","ℝ","0"),
	Case("AffineTurnMissingEndpoint","defined(∫dx [0≤x<undefined(ℝ)]·λ[a*cos(x)+b])","𝔹","false"),
	Case("AffineTurnNonlinear","∫dx [0≤x≤2*π]·λ[x*sin(x)]","ℝ"),
	Case("AffineTurnMissingCoefficient","∫dx [0≤x≤2*π]·λ[undefined(ℝ)*cos(x)+1]","ℝ","undefined(ℝ)"),
	Case("AffineTurnOpaque","λ(h:ℕ→ℝ).∫dx [0≤x≤2*π]·λ[h(0)+sin(x)]","(ℕ→ℝ)→ℝ"),
	Case("AffineTurnHolder","λ(u:ℝ).∫dx [0≤x≤u]·λ[7-2*cos(x)]","ℝ→ℝ"),
	Case("AffineTurnClosedZero","∫dx [0≤x≤2*π]·λ[0*cos(x)+4]","ℝ","0"),
	Case("PowerWaveRationalEndpoints","∫dx [-4≤x≤4]·λ[sin(x)^2]","ℝ","sin(-4)^2+sin(4)^2+4"),
	Case("PowerWaveBeyondCrest","∫dx [0≤x≤2]·λ[sin(x)^2]","ℝ","cos(2)^2+1"),
	Case("PeriodicSpanSeveralTurns","∫dx [0≤x≤7]·λ[cos(x)]","ℝ","-cos(7)+5"),
	Case("PowerWaveSquare","∫dx [-π≤x≤π]·λ[sin(x)^2]","ℝ","4"),
	Case("PowerWaveOdd","∫dx [0<x≤π]·λ[sin(x)^3]","ℝ","2"),
	Case("PowerWaveCrest","∫dx [π/3≤x≤2*π/3]·λ[sin(x)^2]","ℝ","1/2"),
	Case("PowerWaveQuarter","∫dx [0≤x≤π/3]·λ[cos(x)^3]","ℝ","7/8"),
	Case("PowerWaveNegative","∫dx [-π/2≤x≤0]·λ[cos(x)^4]","ℝ","1"),
	Case("PowerWaveHalfTurn","∫dx [π/2≤x≤3*π/2]·λ[sin(x)^4]","ℝ","2"),
	Case("PowerWaveMillion","∫dx [-1000000*π≤x≤0]·λ[cos(x)^7]","ℝ","2000000"),
	Case("PowerWavePower","∫dx [0≤x≤2*π]·λ[sin(x)^32]","ℝ","4"),
	Case("PowerWaveScaled","∫dx [0≤x≤π]·λ[a*cos(x)^5+b]","ℝ","2·abs(a)"),
	Case("PowerWaveReverseInner","∫dx [0≤x≤π]·λ[cos(-3*x)^5]","ℝ","6"),
	Case("PowerWaveWhole","∫dx λ[sin(atan(x))^2]","ℝ","2"),
	Case("PowerWaveWholeOdd","∫dx λ[cos(atan(x))^3]","ℝ","2"),
	Case("PowerWaveRay","∫dx [0≤x]·λ[cos(atan(-x))^4]","ℝ","1"),
	Case("PowerWaveSymbolic","λ(l:ℝ).λ(u:ℝ).∫dx [l<x≤u]·λ[sin(x)^4]","ℝ→ℝ→ℝ"),
	Case("PowerWavePartial","defined(∫dx [0≤x<undefined(ℝ)]·λ[cos(x)^5])","𝔹","false"),
	Case("PowerWaveReverse","∫dx [π<x≤0]·λ[sin(x)^2]","ℝ","0"),
	Case("PowerWavePoint","∫dx [π/2≤x≤π/2]·λ[cos(x)^6]","ℝ","0"),
	Case("PowerWaveUnknownVelocity","λ(h:ℝ→ℝ).∫dx [0≤x<1]·λ[sin(h(x))^2]","(ℝ→ℝ)→ℝ"),
	Case("PowerWaveInfinite","∫dx λ[cos(x)^3]","ℝ"),
	Case("SmoothWaveSineCosine","∫dx [0≤x≤π]·λ[sin(cos(x))]","ℝ","2·sin(1)"),
	Case("SmoothWaveTangent","∫dx [0≤x≤π/2]·λ[tan(sin(x))]","ℝ","tan(1)"),
	Case("SmoothWaveTangentMillion","∫dx [0≤x≤1000000*π]·λ[tan(cos(x))]","ℝ","2000000·tan(1)"),
	Case("SmoothWaveCosh","∫dx [-π≤x≤π]·λ[cosh(sin(x))]","ℝ","4·cosh(1)-4"),
	Case("SmoothWaveTanh","∫dx [0≤x≤2*π]·λ[tanh(cos(x))]","ℝ","4·tanh(1)"),
	Case("SmoothWaveSinh","∫dx [-π/2≤x≤π/2]·λ[sinh(sin(x))]","ℝ","2·sinh(1)"),
	Case("SmoothWaveArctan","∫dx [-π≤x≤π]·λ[atan(cos(x))]","ℝ","π"),
	Case("SmoothWaveArsinh","∫dx [0≤x≤π]·λ[asinh(sin(x))]","ℝ","2·asinh(1)"),
	Case("SmoothWaveCrest","∫dx [π/3≤x≤2*π/3]·λ[atan(sin(x))]","ℝ","-2·atan(1/2·sqrt(3))+1/2·π"),
	Case("SmoothWaveRay","∫dx [x≤0]·λ[tan(cos(atan(x)))]","ℝ","tan(1)"),
	Case("SmoothWaveWhole","∫dx λ[cosh(sin(atan(x)))]","ℝ","2·cosh(1)-2"),
	Case("SmoothWaveAffine","∫dx [-π≤x≤π]·λ[3*sin(cos(2*x))-7]","ℝ","24·sin(1)"),
	Case("TangentSineDomain","defined(tan(sin(x)))","𝔹","true"),
	Case("TangentCosineDomain","defined(tan(cos(x)))","𝔹","true"),
	Case("TangentPartialInput","defined(tan(sin(x⁻¹)))","𝔹","x≠0"),
	Case("TangentAtPole","defined(tan(π/2))","𝔹","false"),
	Case("SmoothWaveMissing","defined(∫dx [undefined(ℝ)≤x≤1]·λ[tan(sin(x))])","𝔹","false"),
	Case("SmoothWaveSymbolic","λ(u:ℝ).∫dx [0≤x≤u]·λ[tan(sin(x))]","ℝ→ℝ"),
	Case("SmoothWaveReciprocal","∫dx [0≤x≤π]·λ[(sin(x))⁻¹]","ℝ"),
	Case("SmoothWavePole","∫dx [0≤x≤π]·λ[tan(2*sin(x))]","ℝ"),
	Case("SmoothWaveUnknown","λ(h:ℝ→ℝ).∫dx [0≤x≤π]·λ[h(sin(x))]","(ℝ→ℝ)→ℝ"),
	Case("VariationSquareSinh","∫dx [-1≤x≤1]·λ[sinh(x)^2]","ℝ","2·sinh(1)^2"),
	Case("VariationSquareAtan","∫dx [-1≤x≤1]·λ[atan(x)^2]","ℝ","1/8·π^2"),
	Case("VariationSquareExp","λ(u:ℝ).∫dx [0≤x<u]·λ[(exp(x)-2)^2]","ℝ→ℝ","λ(u:ℝ). [0<u]·((exp(u)-2)·abs(exp(u)-2)+1)"),
	Case("VariationSquareGeneral","λ(l:ℝ).λ(u:ℝ).∫dx [l<x≤u]·λ[x²]","ℝ→ℝ→ℝ","λ(l:ℝ). λ(u:ℝ). [l<u]·(-l·abs(l)+u·abs(u))"),
	Case("VariationSquarePartial","λ(h:ℝ→ℝ).λ(t:ℝ).∫dx [-1≤x<h(t)]·λ[x²]","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(t:ℝ). [-1<h(t)]·(h(t)·abs(h(t))+1)"),
	Case("VariationCoshCross","∫dx [-1≤x≤1]·λ[cosh(x)]","ℝ","2·cosh(1)-2"),
	Case("VariationCoshDown","∫dx [0≤x<2]·λ[cosh(2-2*x)]","ℝ","cosh(-2)+cosh(2)-2"),
	Case("VariationCoshExp","∫dx [0≤x≤1]·λ[cosh(exp(x))]","ℝ","-cosh(1)+cosh(e)"),
	Case("VariationCoshSymbolic","λ(u:ℝ).∫dx [0<x≤u]·λ[cosh(x)]","ℝ→ℝ","λ(u:ℝ). [0<u]·(cosh(u)-1)"),
	Case("VariationEmpty","∫dx [2≤x<1]·λ[cosh(x)]","ℝ","0"),
	Case("VariationMissing","defined(∫dx [undefined(ℝ)<x<1]·λ[x²])","𝔹","false"),
	Case("VariationOscillating","∫dx [-4≤x≤4]·λ[sin(x)^2]","ℝ"),
	Case("VariationJump","∫dx [-1≤x≤1]·λ[([0≤x]·2)^2]","ℝ"),
	Case("MissingOutputInverseMass","∫dx λ[(undefined(ℝ))]","ℝ","undefined(ℝ)"),
	Case("MissingOutputInverseDensity","densityAtD(Λx.λ[(undefined(ℝ))],z)","ℝ","undefined(ℝ)"),
	Case("MissingOutputInverseTest","∫dx [0<x<1]·λ[(undefined(ℝ))]","ℝ","undefined(ℝ)"),
	Case("MissingOutputInverseZero","massD(weightD(λ(x:ℝ).(0:ℝ),Λz.λ[(undefined(ℝ))]))","ℝ","undefined(ℝ)"),
	Case("MissingOutputPart","massD(inversePartD(λ(x:ℝ).false,(λ(y:ℝ).undefined(ℝ),)))","ℝ","undefined(ℝ)"),
	Case("MissingOutputPartDensity","densityAtD(inversePartD(λ(x:ℝ).x>0,(λ(y:ℝ).undefined(ℝ),)),a)","ℝ","undefined(ℝ)"),
	Case("MissingOutputForwardPole","massD(pushforwardOnD(λ(x:ℝ).true,λ(x:ℝ).x⁻¹))","ℝ","undefined(ℝ)"),
	Case("MissingOutputForwardPoleDensity","densityAtD(pushforwardOnD(λ(x:ℝ).true,λ(x:ℝ).x⁻¹),3)","ℝ","undefined(ℝ)"),
	Case("MissingOutputOutside","massD(pushforwardOnD(λ(x:ℝ).1<x,λ(x:ℝ).(2*x-1)⁻¹))","ℝ","undefined(ℝ)"),
	Case("MissingOutputZeroGuard","densityAtD(pushforwardOnD(λ(x:ℝ).false,λ(x:ℝ).(x^2-2)⁻¹),5)","ℝ","undefined(ℝ)"),
	Case("MissingOutputWeighted","densityAtD(weightD(λ(x:ℝ).x,pushforwardOnD(λ(x:ℝ).true,λ(x:ℝ).(x^2-3)⁻¹)),y)","ℝ","undefined(ℝ)"),
	Case("MissingOutputMaskedPole","massD(pushforwardOnD(λ(x:ℝ).true,λ(x:ℝ).[x≠0]·x⁻¹))","ℝ","∫dx 1·λ[x]"),
	Case("MissingOutputNoRealRoot","densityAtD(pushforwardOnD(λ(x:ℝ).true,λ(x:ℝ).(x^2+1)⁻¹),0)","ℝ","(λ(x:ℝ). (∫dx1 λ[x1]·δ((x1^2+1)⁻¹)[x])//λ[x])((0:ℝ))"),
	Case("MissingOutputInversePartial","densityAtD(Λx.λ[x⁻¹],1)","ℝ","(λ(x:ℝ). (λ[(x⁻¹)])//λ[x])((1:ℝ))"),
	Case("MissingOutputAtom","massD(δ((2:ℝ)))","ℝ","1"),
	Case("MissingOutputUnknown","λ(h:ℝ→ℝ).massD(pushforwardOnD(λ(x:ℝ).true,h))","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). ∫dy (pushforwardOnD(λ(x:ℝ). true,h))[y]"),
	Case("IversonParameterBoolean","λ(p:𝔹).Λx.λ[sin(x+[p])]","𝔹→Distribution(ℝ)","λ(p:𝔹). Λ(x:ℝ). (abs(cos(x+[p])))·λ[x]"),
	Case("IversonParameterCompare","Λx.λ[sin(x+[a<b])]","Distribution(ℝ)","Λ(x:ℝ). (abs(cos(x+[a<b])))·λ[x]"),
	Case("IversonParameterWeak","Λx.λ[sin(x+[a≤b])]","Distribution(ℝ)","Λ(x:ℝ). (abs(cos(x+[a≤b])))·λ[x]"),
	Case("IversonParameterAnd","Λx.λ[exp(([a<b∧b<c]+1)*x)]","Distribution(ℝ)","Λ(x:ℝ). (([a<b∧b<c]+1)·exp(x·([a<b∧b<c]+1)))·λ[x]"),
	Case("IversonParameterOr","Λx.λ[sin(([a<b∨c≤a]+1)*x)]","Distribution(ℝ)","Λ(x:ℝ). (abs(cos(x·([a<b∨c≤a]+1)))·([a<b∨c≤a]+1))·λ[x]"),
	Case("IversonParameterNegated","Λx.λ[sin(x+[a=0])]","Distribution(ℝ)","Λ(x:ℝ). (abs(cos(x+[a=0])))·λ[x]"),
	Case("IversonParameterMasked","Λx.λ[sin(x+[a<0]*a)]","Distribution(ℝ)","Λ(x:ℝ). (abs(cos(x+[a<0]·a)))·λ[x]"),
	Case("IversonParameterGuardedInverse","Λx.λ[sin(x+[a≠0]·a⁻¹)]","Distribution(ℝ)","Λ(x:ℝ). (abs(cos(x+[a≠0]·a⁻¹)))·λ[x]"),
	Case("IversonParameterInverseMagnitude","Λx.λ[sin(([a≠0]·a⁻¹)*x)]","Distribution(ℝ)","Λ(x:ℝ). λ[([a≠0]·sin(x·a⁻¹))]"),
	Case("IversonParameterInverseMass","∫dx [0≤x≤1]·λ[exp(x+[a≠0]·a⁻¹)]","ℝ","exp([a≠0]·a⁻¹+1)-exp([a≠0]·a⁻¹)"),
	Case("IversonParameterBooleanMass","λ(p:𝔹).∫dx [0≤x≤1]·λ[(x+[p])^3]","𝔹→ℝ","λ(p:𝔹). ([p]+1)^3+[p]·-1"),
	Case("IversonParameterOtherGuard","Λx.λ[sin(x+[b≠0]·a⁻¹)]","Distribution(ℝ)","Λ(x:ℝ). λ[(sin(x+[b≠0]·a⁻¹))]"),
	Case("IversonParameterPartialGuard","λ(h:ℕ→𝔹).Λx.λ[sin(x+[h(0)])]","(ℕ→𝔹)→Distribution(ℝ)","λ(h:ℕ→𝔹). Λ(x:ℝ). λ[(sin(x+[h(0)]))]"),
	Case("IversonParameterPartialValue","λ(h:ℕ→ℝ).Λx.λ[sin(x+[a<0]·h(0))]","(ℕ→ℝ)→Distribution(ℝ)","λ(h:ℕ→ℝ). Λ(x:ℝ). λ[(sin(x+[a<0]·h(0)))]"),
	Case("IversonParameterApplied","(λ(p:𝔹).Λx.λ[sin(x+[p])])(false)","Distribution(ℝ)","Λ(x:ℝ). (abs(cos(x)))·λ[x]"),
	Case("ScalarBinderNatural","λ(n:ℕ).Λx.λ[sin(x+(n:ℝ))]","ℕ→Distribution(ℝ)","λ(n:ℕ). Λ(x:ℝ). (abs(cos(x+n)))·λ[x]"),
	Case("ScalarBinderInteger","λ(k:ℤ).Λx.λ[sin((k:ℝ)*x)]","ℤ→Distribution(ℝ)","λ(k:ℤ). Λ(x:ℝ). (abs(k)·abs(cos(x·k)))·λ[x]"),
	Case("ScalarBinderRational","λ(q:ℚ).Λx.λ[exp((q:ℝ)*x)]","ℚ→Distribution(ℝ)","λ(q:ℚ). Λ(x:ℝ). (abs(q)·exp(x·q))·λ[x]"),
	Case("ScalarBinderComplex","λ(z:ℂ).Λx.λ[sin(x+creal(z))]","ℂ→Distribution(ℝ)","λ(z:ℂ). Λ(x:ℝ). (abs(cos(x+creal(z))))·λ[x]"),
	Case("ScalarBinderHigherOrder","λ(h:ℕ→ℝ).λ(n:ℕ).Λx.λ[sin(x+h(n))]","(ℕ→ℝ)→ℕ→Distribution(ℝ)","λ(h:ℕ→ℝ). λ(n:ℕ). Λ(x:ℝ). λ[(sin(x+h(n)))]"),
	Case("ScalarBinderNaturalMass","λ(n:ℕ).∫dx [0≤x≤1]·λ[exp(x+(n:ℝ))]","ℕ→ℝ","λ(n:ℕ). -exp(n)+exp(n+1)"),
	Case("ScalarBinderMixed","λ(n:ℕ).λ(a:ℝ).Λx.λ[sin(a*x+(n:ℝ))]","ℕ→ℝ→Distribution(ℝ)","λ(n:ℕ). λ(a:ℝ). Λ(x:ℝ). (abs(a)·abs(cos(a·x+n)))·λ[x]"),
	Case("ScalarBinderSameType","λ(n:ℕ).λ(m:ℕ).Λx.λ[sin((n:ℝ)*x+(m:ℝ))]","ℕ→ℕ→Distribution(ℝ)","λ(n:ℕ). λ(m:ℕ). Λ(x:ℝ). (abs(cos(x·n+m))·n)·λ[x]"),
	Case("ScalarBinderFree","λ(n:ℕ).Λx.λ[sin(x+(n:ℝ)+a)]","ℕ→Distribution(ℝ)","λ(n:ℕ). Λ(x:ℝ). (abs(cos(a+x+n)))·λ[x]"),
	Case("ScalarBinderSpecialized","(λ(n:ℕ).Λx.λ[sin(x+(n:ℝ))])(2)","Distribution(ℝ)","Λ(x:ℝ). (abs(cos(x+2)))·λ[x]"),
	Case("ScalarBinderPartial","λ(k:ℤ).Λx.λ[sin(x+(k:ℝ)⁻¹)]","ℤ→Distribution(ℝ)","λ(k:ℤ). Λ(x:ℝ). λ[(sin(x+k⁻¹))]"),
	Case("ScalarBinderIntegerMass","λ(k:ℤ).∫dx [0≤x≤1]·λ[(x+(k:ℝ))^3]","ℤ→ℝ","λ(k:ℤ). ((k+1)^3-k^3:ℝ)"),
	Case("ScalarBinderComplexMass","λ(z:ℂ).∫dx [0≤x≤1]·λ[exp(x+creal(z))]","ℂ→ℝ","λ(z:ℂ). exp(creal(z)+1)-exp(creal(z))"),
	Case("CoordinateParameterOffset","Λx.λ[sin(x+a)]","Distribution(ℝ)","Λ(x:ℝ). (abs(cos(a+x)))·λ[x]"),
	Case("CoordinateParameterFrequency","Λx.λ[sin(a*x)]","Distribution(ℝ)","Λ(x:ℝ). (abs(a)·abs(cos(a·x)))·λ[x]"),
	Case("CoordinateParameterScale","Λx.λ[(exp(a)+cos(b))*x]","Distribution(ℝ)","Λ(x:ℝ). (abs(exp(a)+cos(b)))·λ[x]"),
	Case("CoordinateParameterConstant","Λx.λ[exp(a)+cos(b)]","Distribution(ℝ)","Λ(x:ℝ). 0·λ[x]"),
	Case("CoordinateParameterPolynomial","Λx.λ[a*x²+b*x+c]","Distribution(ℝ)","Λ(x:ℝ). (abs(2·a·x+b))·λ[x]"),
	Case("CoordinateParameterExponential","Λx.λ[exp(a*x+b)]","Distribution(ℝ)","Λ(x:ℝ). (abs(a)·exp(a·x+b))·λ[x]"),
	Case("CoordinateParameterNegative","Λx.λ[cos(b-a*x)]","Distribution(ℝ)","Λ(x:ℝ). (abs(a)·abs(sin(-a·x+b)))·λ[x]"),
	Case("CoordinateParameterShared","Λx.λ[sin((a+b)*x+(a+b))]","Distribution(ℝ)","Λ(x:ℝ). (abs(a+b)·abs(cos(x·(a+b)+a+b)))·λ[x]"),
	Case("CoordinateParameterBound","λ(a:ℝ).Λx.λ[sin(x+a)]","ℝ→Distribution(ℝ)","λ(a:ℝ). Λ(x:ℝ). (abs(cos(a+x)))·λ[x]"),
	Case("CoordinateParameterIntegral","∫dx [0≤x≤1]·λ[exp(x+a)]","ℝ","-exp(a)+exp(a+1)"),
	Case("CoordinateParameterIncreasing","∫dx [0≤x≤1]·λ[(x+a)^3]","ℝ","-a^3+(a+1)^3"),
	Case("CoordinateParameterDecreasing","∫dx [0≤x≤1]·λ[(a-x)^3]","ℝ","a^3-(a-1)^3"),
	Case("CoordinateParameterConstantMass","∫dx [0≤x≤1]·λ[exp(a)]","ℝ","0"),
	Case("CoordinateParameterSingular","Λx.λ[sin(x+a⁻¹)]","Distribution(ℝ)","Λ(x:ℝ). λ[(sin(x+a⁻¹))]"),
	Case("CoordinateParameterMissing","Λx.λ[sin(x+undefined(ℝ))]","Distribution(ℝ)","Λ(x:ℝ). λ[(undefined(ℝ))]"),
	Case("CoordinateParameterLookup","λ(h:ℕ→ℝ).Λx.λ[sin(x+h(0))]","(ℕ→ℝ)→Distribution(ℝ)","λ(h:ℕ→ℝ). Λ(x:ℝ). λ[(sin(x+h(0)))]"),
	Case("CoordinateParameterMagnitude","Λx.λ[sin(abs(a)*x)]","Distribution(ℝ)","Λ(x:ℝ). (abs(a)·abs(cos(x·abs(a))))·λ[x]"),
	Case("IntervalFactorSigned","∫dx [0≤x≤2*π]·(-3/2*abs(cos(x)))·λ[x]","ℝ","-6"),
	Case("IntervalFactorPositive","∫dx [0≤x≤2*π]·(3/2*abs(cos(x)))·λ[x]","ℝ","6"),
	Case("IntervalFactorSymbolic","λ(c:ℝ).∫dx [0≤x≤2*π]·(c*abs(cos(x)))·λ[x]","ℝ→ℝ","λ(c:ℝ). 4·c"),
	Case("IntervalFactorConstantRight","λ(c:ℝ).∫dx [0≤x≤2*π]·mulR(abs(cos(x)),c)·λ[x]","ℝ→ℝ","λ(c:ℝ). 4·c"),
	Case("IntervalFactorSignedSine","λ(c:ℝ).∫dx [0≤x≤π]·mulR(c,sin(x))·λ[x]","ℝ→ℝ","λ(c:ℝ). 2·c"),
	Case("IntervalFactorHigherOrder","λ(h:ℕ→ℝ).λ(n:ℕ).∫dx [0≤x≤2*π]·(abs(sin(x))*h(n))·λ[x]","(ℕ→ℝ)→ℕ→ℝ","λ(h:ℕ→ℝ). λ(n:ℕ). 4·h(n)"),
	Case("IntervalFactorSum","λ(c:ℝ).∫dx [0≤x≤1]·(c*(abs(sin(x))+cos(x)))·λ[x]","ℝ→ℝ","λ(c:ℝ). c·(sin(1)-cos(1)+1)"),
	Case("IntervalFactorTwoCoefficients","λ(c:ℝ).λ(d:ℝ).∫dx [0≤x≤π]·mulR(c,mulR(sin(x),d))·λ[x]","ℝ→ℝ→ℝ","λ(c:ℝ). λ(d:ℝ). 2·d·c"),
	Case("IntervalFactorInsideSum","λ(c:ℝ).λ(d:ℝ).∫dx [0≤x≤π]·(c*abs(sin(x))+d*cos(x))·λ[x]","ℝ→ℝ→ℝ","λ(c:ℝ). λ(d:ℝ). 2·c"),
	Case("IntervalFactorCauchy","λ(c:ℝ).∫dx [0≤x≤1]·mulR(c,(1+x²)⁻¹)·λ[x]","ℝ→ℝ","λ(c:ℝ). c·(1/4)·π"),
	Case("IntervalFactorCauchySine","λ(c:ℝ).∫dx [0≤x≤1]·mulR(c,(1+x²)⁻¹+sin(x))·λ[x]","ℝ→ℝ","λ(c:ℝ). c·(-cos(1)+1/4·π+1)"),
	Case("IntervalFactorBounds","λ(l:ℝ).λ(u:ℝ).λ(c:ℝ).∫dx [l<x<u]·mulR(sin(x),c)·λ[x]","ℝ→ℝ→ℝ→ℝ","λ(l:ℝ). λ(u:ℝ). λ(c:ℝ). [l<u]·(c·(cos(l)-cos(u)))"),
	Case("IntervalFactorEmptyMissing","defined(∫dx [1≤x≤0]·mulR(undefined(ℝ),abs(cos(x)))·λ[x])","𝔹","true"),
	Case("IntervalFactorClosedSingletonMissing","defined(∫dx [0≤x≤0]·mulR(undefined(ℝ),abs(cos(x)))·λ[x])","𝔹","false"),
	Case("IntervalFactorOpenSingletonMissing","defined(∫dx [0<x≤0]·mulR(undefined(ℝ),abs(cos(x)))·λ[x])","𝔹","true"),
	Case("IntervalFactorZeroAreaPartial","λ(h:ℕ→ℝ).∫dx [0≤x≤π]·mulR(h(0),cos(x))·λ[x]","(ℕ→ℝ)→ℝ","λ(h:ℕ→ℝ). 0·h(0)"),
	Case("IntervalFactorActiveMissing","defined(∫dx [0≤x≤1]·mulR(undefined(ℝ),abs(cos(x)))·λ[x])","𝔹","false"),
	Case("IntervalFactorActiveMissingZeroArea","defined(∫dx [-π≤x≤π]·mulR(undefined(ℝ),sin(x))·λ[x])","𝔹","false"),
	Case("IntervalFactorSingular","defined(∫dx [0≤x≤1]·mulR(0,x⁻¹)·λ[x])","𝔹"),
	Case("IntervalFactorOpaque","λ(c:ℝ).∫dx [0≤x≤1]·mulR(c,sin(x²))·λ[x]","ℝ→ℝ"),
	Case("IntervalFactorImproper","λ(c:ℝ).∫dx [0≤x]·mulR(c,abs(sin(x)))·λ[x]","ℝ→ℝ"),
	Case("PromotedLiteralGuard","λ(h:ℕ→𝔹).[h(0)]·toℝ(floor(3/2))","(ℕ→𝔹)→ℝ","λ(h:ℕ→𝔹). [h(0)]"),
	Case("PromotedLiteralProduct","λ(h:ℕ→ℝ).mulR(h(0),toℝ(floor(9/2)))","(ℕ→ℝ)→ℝ","λ(h:ℕ→ℝ). 4·h(0)"),
	Case("PromotedLiteralStrict","λ(h:ℕ→𝔹).λ(k:ℕ→ℝ).mulR([h(0)]·toℝ(floor(3/2)),k(0))","(ℕ→𝔹)→(ℕ→ℝ)→ℝ","λ(h:ℕ→𝔹). λ(k:ℕ→ℝ). mulR(k(0),[h(0)])"),
	Case("TrigParameterCosine","λ(a:ℝ).∫dx [0≤x≤1]·cos(a*x)·λ[x]","ℝ→ℝ","λ(a:ℝ). [a≠0]·(a⁻¹·sin(a))+[a=0]"),
	Case("TrigParameterSine","λ(a:ℝ).∫dx [0≤x≤1]·sin(a*x)·λ[x]","ℝ→ℝ","λ(a:ℝ). [a≠0]·(-a⁻¹·cos(a)+a⁻¹)"),
	Case("TrigParameterShift","λ(a:ℝ).∫dx [0≤x≤π]·sin(x+a)·λ[x]","ℝ→ℝ","λ(a:ℝ). 2·cos(a)"),
	Case("TrigParameterNegativeShift","λ(a:ℝ).∫dx [0≤x≤π]·sin(a-x)·λ[x]","ℝ→ℝ","λ(a:ℝ). -2·cos(a)"),
	Case("TrigParameterCompound","λ(a:ℝ).λ(b:ℝ).∫dx [0≤x≤2]·sin(a*(2*x+b))·λ[x]","ℝ→ℝ→ℝ"),
	Case("TrigParameterCosineShift","λ(a:ℝ).λ(b:ℝ).∫dx [0≤x≤2]·cos(b+a*x)·λ[x]","ℝ→ℝ→ℝ"),
	Case("TrigParameterAbsSine","λ(a:ℝ).∫dx [0≤x≤1]·abs(sin(a*x))·λ[x]","ℝ→ℝ"),
	Case("TrigParameterAbsTranslated","λ(b:ℝ).∫dx [0≤x≤π]·abs(sin(x+b))·λ[x]","ℝ→ℝ"),
	Case("TrigParameterPartial","λ(h:ℕ→ℝ).λ(n:ℕ).∫dx [0≤x≤1]·cos(h(n)*x)·λ[x]","(ℕ→ℝ)→ℕ→ℝ"),
	Case("TrigParameterPartialShift","λ(h:ℕ→ℝ).∫dx [0≤x≤π]·sin(x+h(0))·λ[x]","(ℕ→ℝ)→ℝ","λ(h:ℕ→ℝ). cos(h(0))-cos(h(0)+π)"),
	Case("TrigParameterOnBounds","λ(l:ℝ).λ(u:ℝ).λ(a:ℝ).∫dx [l<x≤u]·sin(a*x)·λ[x]","ℝ→ℝ→ℝ→ℝ"),
	Case("TrigParameterZero","∫dx [0≤x≤2]·cos(0*x)·λ[x]","ℝ","2"),
	Case("TrigParameterFree","∫dx [-1≤x≤1]·sin(a*x+b)·λ[x]","ℝ"),
	Case("TrigParameterFactor","λ(c:ℝ).λ(a:ℝ).∫dx [0≤x≤1]·mulR(c,cos(a*x))·λ[x]","ℝ→ℝ→ℝ"),
	Case("TrigParameterUndefined","defined(∫dx [0≤x≤2]·cos(undefined(ℝ)*x)·λ[x])","𝔹","false"),
	Case("TrigParameterUndefinedShift","defined(∫dx [0≤x≤1]·cos(x+undefined(ℝ))·λ[x])","𝔹","false"),
	Case("TrigParameterClosedSingleton","defined(∫dx [0≤x≤0]·cos(undefined(ℝ)*x)·λ[x])","𝔹","false"),
	Case("TrigParameterOpenSingleton","defined(∫dx [0<x≤0]·cos(undefined(ℝ)*x)·λ[x])","𝔹","true"),
	Case("TrigParameterQuadratic","λ(a:ℝ).∫dx [0≤x≤1]·cos(a*x²)·λ[x]","ℝ→ℝ"),
	Case("TrigParameterRay","λ(a:ℝ).∫dx [0≤x]·sin(a*x)·λ[x]","ℝ→ℝ"),
	Case("TrigParameterCancellation","λ(a:ℝ).∫dx [-1≤x≤1]·sin(a*x)·λ[x]","ℝ→ℝ","λ(a:ℝ). (0:ℝ)"),
	Case("TrigIntegralCosinePeriod","∫dx [0≤x≤2*π]·abs(cos(x))·λ[x]","ℝ","4"),
	Case("TrigIntegralSinePeriod","∫dx [0≤x≤2*π]·abs(sin(x))·λ[x]","ℝ","4"),
	Case("TrigIntegralAffinePeriod","∫dx [0≤x≤π]·abs(cos(2*x+1))·λ[x]","ℝ","2"),
	Case("TrigIntegralNegativeSlope","∫dx [0≤x≤π]·abs(sin(1-2*x))·λ[x]","ℝ","2"),
	Case("TrigIntegralFractionalSlope","∫dx [0≤x≤4*π]·abs(cos((x+1)/2))·λ[x]","ℝ","8"),
	Case("TrigIntegralMillion","∫dx [0≤x≤2000000*π]·abs(cos(x))·λ[x]","ℝ","4000000"),
	Case("TrigIntegralSignedSine","∫dx [0≤x≤π]·sin(x)·λ[x]","ℝ","2"),
	Case("TrigIntegralSignedCosine","∫dx [0≤x≤π/2]·cos(x)·λ[x]","ℝ","1"),
	Case("TrigIntegralSignedCancellation","∫dx [-π≤x≤π]·sin(3*x+1)·λ[x]","ℝ","0"),
	Case("TrigIntegralMixed","∫dx [0≤x≤1]·(abs(cos(x))+abs(sin(x)))·λ[x]","ℝ","sin(1)-cos(1)+1"),
	Case("TrigIntegralPartialPeriod","∫dx [0≤x≤2]·abs(cos(x))·λ[x]","ℝ","-sin(2)+2"),
	Case("TrigIntegralPunctured","∫dx [0≤x≤2*π]·abs(cos(x))·[x≠a]·λ[x]","ℝ","4"),
	Case("TrigIntegralFromSquare","∫dx [0≤x≤1]·sqrt(1-sin(x)^2)·λ[x]","ℝ","sin(1)"),
	Case("TrigIntegralSymbolic","λ(l:ℝ).λ(u:ℝ).∫dx [l<x≤u]·abs(cos(x))·λ[x]","ℝ→ℝ→ℝ"),
	Case("TrigIntegralBounds","∫dx [1≤x≤0]·abs(sin(x))·λ[x]","ℝ","0"),
	Case("TrigIntegralMissing","defined(∫dx [0≤x≤undefined(ℝ)]·cos(x)·λ[x])","𝔹"),
	Case("TrigIntegralNonlinear","∫dx [0≤x≤1]·abs(cos(x²))·λ[x]","ℝ"),
	Case("TrigIntegralHalfLine","∫dx [0≤x]·abs(sin(x))·λ[x]","ℝ"),
	Case("TrigIntegralUnknownFrequency","λ(t:ℝ).∫dx [0≤x≤1]·abs(cos(t*x))·λ[x]","ℝ→ℝ"),
	Case("RepeatedIversonAdjacent","λ(p:𝔹).λ(h:ℕ→ℝ).[p]·([p]·h(0))","𝔹→(ℕ→ℝ)→ℝ","λ(p:𝔹). λ(h:ℕ→ℝ). [p]·h(0)"),
	Case("RepeatedIversonBetween","λ(p:𝔹).λ(q:𝔹).λ(h:ℕ→ℝ).[p]·([q]·([p]·h(0)))","𝔹→𝔹→(ℕ→ℝ)→ℝ","λ(p:𝔹). λ(q:𝔹). λ(h:ℕ→ℝ). [p]·([q]·h(0))"),
	Case("RepeatedIversonThreeGuards","λ(p:𝔹).λ(q:𝔹).λ(r:𝔹).λ(h:ℕ→ℝ).[p]·([q]·([r]·([p]·h(0))))","𝔹→𝔹→𝔹→(ℕ→ℝ)→ℝ","λ(p:𝔹). λ(q:𝔹). λ(r:𝔹). λ(h:ℕ→ℝ). [p]·([q]·([r]·h(0)))"),
	Case("RepeatedIversonNatural","λ(p:𝔹).λ(q:𝔹).λ(h:ℕ→ℕ).[p]·([q]·([p]·h(0)))","𝔹→𝔹→(ℕ→ℕ)→ℕ","λ(p:𝔹). λ(q:𝔹). λ(h:ℕ→ℕ). [p]·([q]·h(0))"),
	Case("RepeatedIversonOpaquePredicate","λ(h:ℕ→𝔹).λ(k:ℕ).λ(f:ℕ→ℝ).[h(k)]·([h(k)]·f(k))","(ℕ→𝔹)→ℕ→(ℕ→ℝ)→ℝ","λ(h:ℕ→𝔹). λ(k:ℕ). λ(f:ℕ→ℝ). [h(k)]·f(k)"),
	Case("RepeatedIversonDistinct","λ(p:𝔹).λ(q:𝔹).λ(h:ℕ→ℝ).[p]·([q]·h(0))","𝔹→𝔹→(ℕ→ℝ)→ℝ","λ(p:𝔹). λ(q:𝔹). λ(h:ℕ→ℝ). [p]·([q]·h(0))"),
	Case("RepeatedIversonDifferentOrder","λ(p:𝔹).λ(q:𝔹).λ(h:ℕ→ℝ).[p∨q]·([q∨p]·h(0))","𝔹→𝔹→(ℕ→ℝ)→ℝ","λ(p:𝔹). λ(q:𝔹). λ(h:ℕ→ℝ). [p∨q]·([q∨p]·h(0))"),
	Case("RepeatedIversonMissing","defined([undefined(𝔹)]·([undefined(𝔹)]·(1:ℝ)))","𝔹","false"),
	Case("RepeatedIversonHidden","defined([false]·([undefined(𝔹)]·([false]·undefined(ℝ))))","𝔹","true"),
	Case("RepeatedIversonCoordinate","λ(l:ℝ).λ(u:ℝ).∫dx [l≤x<u]·[x≠a]·λ[sinh(exp(x))]","ℝ→ℝ→ℝ","λ(l:ℝ). λ(u:ℝ). [l<u]·(-sinh(exp(l))+sinh(exp(u)))"),
	Case("CombinedMassJump","∫dx [0≤x≤1]·[x=a]·λ[[0≤x]·1]","ℝ","[a=0]"),
	Case("CombinedMassJumpPeriod","∫dx [0≤x≤2*π]·[x≠0]·λ[[0≤x]·1]","ℝ","0"),
	Case("CombinedMassJumpHit","∫dx [0≤x≤1]·[x=0]·λ[[0≤x]·1]","ℝ","1"),
	Case("CombinedMassZero","massD(weightD(λ(x:ℝ). [x≠a],weightD(λ(x:ℝ). 0,lebesgueD())))","ℝ","0"),
	Case("CombinedMassThree","massD(weightD(λ(x:ℝ). [0≤x≤1],weightD(λ(x:ℝ). (1+x²)⁻¹,weightD(λ(x:ℝ). 2,lebesgueD()))))","ℝ","1/2·π"),
	Case("CombinedMassFour","massD(weightD(λ(x:ℝ). [0≤x≤1],weightD(λ(x:ℝ). (1+x²)⁻¹,weightD(λ(x:ℝ). 2,weightD(λ(x:ℝ). -3,lebesgueD())))))","ℝ","-3/2·π"),
	Case("CombinedMassAfterMask","massD(weightD(λ(x:ℝ). 2,weightD(λ(x:ℝ). (1+x²)⁻¹,weightD(λ(x:ℝ). [0≤x≤1],lebesgueD()))))","ℝ","1/2·π"),
	Case("CombinedMassSignedInterval","massD(weightD(λ(x:ℝ). [a≤x≤b],weightD(λ(x:ℝ). (1+x²)⁻¹,weightD(λ(x:ℝ). -3/2,lebesgueD()))))","ℝ","[a≤b]·(3/2·atan(a)-3/2·atan(b))"),
	Case("CombinedMassWhole","massD(weightD(λ(x:ℝ). (1+x²)⁻¹,weightD(λ(x:ℝ). -3/2,lebesgueD())))","ℝ","-3/2·π"),
	Case("CombinedMassPole","defined(massD(weightD(λ(x:ℝ). 0,weightD(λ(x:ℝ). x⁻¹,lebesgueD()))))","𝔹","false"),
	Case("CombinedMassFalseOuter","defined(massD(weightD(λ(x:ℝ). [2≤x≤1],weightD(λ(x:ℝ). x⁻¹,lebesgueD()))))","𝔹","false"),
	Case("CombinedMassMissingGuard","defined(massD(weightD(λ(x:ℝ). [x≤undefined(ℝ)],weightD(λ(x:ℝ). 0,lebesgueD()))))","𝔹","false"),
	Case("CombinedMassOpaque","λ(h:ℝ→ℝ).massD(weightD(h,weightD(λ(x:ℝ). 0,lebesgueD())))","(ℝ→ℝ)→ℝ"),
	Case("CombinedMassDensity","densityAtD(weightD(λ(x:ℝ). [x≠0],weightD(λ(x:ℝ). 2,lebesgueD())),0)","ℝ","0"),
	Case("CombinedMassOtherBase","massD(weightD(λ(x:ℝ). [x=0],weightD(λ(x:ℝ). 2,δ((0:ℝ)))))","ℝ","2"),
	Case("CoordinatePuncturePeriod","∫dx [0≤x≤2*π]·[x≠a]·λ[sin(x)]","ℝ","4"),
	Case("CoordinatePunctureFront","∫dx [x≠a]·[0≤x≤2*π]·λ[sin(x)]","ℝ","4"),
	Case("CoordinatePunctureClosedPoint","∫dx [0≤x≤2*π]·[x≠1]·λ[sin(x)]","ℝ","4"),
	Case("CoordinatePunctureBetween","∫dx [0≤x]·[x≠a]·[x≤2*π]·λ[sin(x)]","ℝ","4"),
	Case("CoordinatePunctureAffine","∫dx [0≤x≤2*π]·[2*x+a≠0]·λ[sin(x)]","ℝ","4"),
	Case("CoordinatePunctureCrest","∫dx [0≤x≤2]·[x≠1]·λ[sin(x)^2]","ℝ","cos(2)^2+1"),
	Case("CoordinatePunctureSigned","∫dx [0≤x≤2*π]·[x≠a]·(-3/2)·λ[sin(x)]","ℝ","-6"),
	Case("CoordinatePunctureRay","∫dx [x≤0]·[x≠a]·λ[atan(x)]","ℝ","1/2·π"),
	Case("CoordinatePunctureSymbolic","λ(l:ℝ).λ(u:ℝ).∫dx [l≤x<u]·[x≠a]·λ[sinh(exp(x))]","ℝ→ℝ→ℝ"),
	Case("CoordinatePuncturePartial","λ(h:ℝ→ℝ).λ(t:ℝ).∫dx [0≤x≤2*π]·[x≠h(t)]·λ[sin(x)]","(ℝ→ℝ)→ℝ→ℝ"),
	Case("CoordinatePunctureMissing","defined(∫dx [0≤x≤1]·[x≠undefined(ℝ)]·λ[sin(x)])","𝔹","false"),
	Case("CoordinatePunctureEmpty","∫dx [1<x≤0]·[x≠undefined(ℝ)]·λ[sin(x)]","ℝ","0"),
	Case("CoordinatePunctureFirstMissing","defined(∫dx [x≠undefined(ℝ)]·[1<x≤0]·λ[sin(x)])","𝔹","false"),
	Case("CoordinatePuncturePointDensity","densityAtD(Λx. [x≠0]·λ[sin(x)],0)","ℝ","0"),
	Case("CoordinatePunctureJumpHit","∫dx [-1≤x≤1]·λ[[0≤x]·1]","ℝ","1"),
	Case("CoordinatePunctureJumpExcluded","∫dx [-1≤x≤1]·[x≠0]·λ[[0≤x]·1]","ℝ","0"),
	Case("CoordinatePunctureHiddenPole","∫dx [0≤x≤1]·[x≠0]·x⁻¹·λ[sin(x)]","ℝ"),
	Case("CoordinateWeightPeriod","∫dx [0≤x≤2*π]·2·λ[sin(x)]","ℝ","8"),
	Case("CoordinateWeightSigned","∫dx [0≤x≤2*π]·(-3/2)·λ[sin(x)]","ℝ","-6"),
	Case("CoordinateWeightCrest","∫dx [0≤x≤2]·(-3/2)·λ[sin(x)^2]","ℝ","-3/2·cos(2)^2-3/2"),
	Case("CoordinateWeightMonotone","∫dx [0≤x≤1]·(3/4)·λ[exp(x)]","ℝ","3/4·e-3/4"),
	Case("CoordinateWeightTangent","∫dx [0≤x≤π/2]·(-3/2)·λ[tan(sin(x))]","ℝ","-3/2·tan(1)"),
	Case("CoordinateWeightRay","∫dx [x≤1]·(2/3)·λ[atan(x)]","ℝ","1/2·π"),
	Case("CoordinateWeightNatural","∫dx toℝ(maskN(0≤x∧x≤2*π,3))·λ[sin(x)]","ℝ","12"),
	Case("CoordinateWeightInteger","∫dx toℝ(maskZ(0≤x∧x≤2*π,(-3:ℤ)))·λ[sin(x)]","ℝ","-12"),
	Case("CoordinateWeightRational","∫dx toℝ(maskQ(0≤x∧x≤2*π,(3/2:ℚ)))·λ[sin(x)]","ℝ","6"),
	Case("CoordinateWeightMissing","defined(∫dx [0≤x≤undefined(ℝ)]·2·λ[sin(x)])","𝔹","false"),
	Case("CoordinateWeightEmpty","∫dx [2<x≤1]·(-3/2)·λ[sin(x)]","ℝ","0"),
	Case("CoordinateWeightSymbolic","λ(l:ℝ).λ(u:ℝ).∫dx ([l<x]·[x≤u]·(-3/2:ℝ))·λ[sinh(exp(x))]","ℝ→ℝ→ℝ"),
	Case("CoordinateWeightInfinite","∫dx [-π≤x]·2·λ[sin(x)]","ℝ"),
	Case("CoordinateWeightZero","∫dx [0≤x≤1]·0·λ[sin(x)]","ℝ","0"),
	Case("CoordinateIntervalSinhExp","∫dx [0≤x≤1]·λ[sinh(exp(x))]","ℝ","-sinh(1)+sinh(e)"),
	Case("CoordinateIntervalArsinhExp","∫dx [-1≤x≤1]·λ[asinh(exp(2*x-3))]","ℝ","-asinh(exp(-5))+asinh(exp(-1))"),
	Case("CoordinateIntervalDecreasing","λ(l:ℝ).λ(u:ℝ).∫dx [l<x≤u]·λ[atan(exp(-x))]","ℝ→ℝ→ℝ","λ(l:ℝ). λ(u:ℝ). [l<u]·(atan(exp(-l))-atan(exp(-u)))"),
	Case("CoordinateIntervalOdd","λ(u:ℝ).∫dx [0≤x≤u]·λ[atan(x)^3]","ℝ→ℝ","λ(u:ℝ). [0≤u]·atan(u)^3"),
	Case("CoordinateIntervalSum","∫dx [0≤x≤1]·λ[sinh(x)+atan(x)]","ℝ","sinh(1)+1/4·π"),
	Case("CoordinateIntervalSumDown","∫dx [0≤x≤1]·λ[atan(-x)+exp(-x)]","ℝ","-exp(-1)+1/4·π+1"),
	Case("CoordinateIntervalTranslated","∫dx [0≤x≤1]·λ[2+sinh(exp(x))]","ℝ","-sinh(1)+sinh(e)"),
	Case("CoordinateIntervalStrict","∫dx [x<1∧0<x]·λ[sinh(exp(x))]","ℝ","-sinh(1)+sinh(e)"),
	Case("CoordinateIntervalReverse","∫dx [1≤x<0]·λ[atan(exp(-x))]","ℝ","0"),
	Case("CoordinateIntervalEqual","∫dx [1≤x≤1]·λ[sinh(exp(x))]","ℝ","0"),
	Case("CoordinateIntervalPartial","λ(h:ℝ→ℝ).λ(t:ℝ).∫dx [0<x≤h(t)]·λ[sinh(exp(x))]","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(t:ℝ). [0<h(t)]·(-sinh(1)+sinh(exp(h(t))))"),
	Case("CoordinateIntervalMissing","defined(∫dx [undefined(ℝ)<x<1]·λ[sinh(exp(x))])","𝔹","false"),
	Case("CoordinateIntervalTurning","∫dx [-1≤x≤1]·λ[exp(sin(x))]","ℝ"),
	Case("CoordinateIntervalOpposite","∫dx [-2≤x≤2]·λ[exp(x)+exp(-x)]","ℝ"),
	Case("CoordinateIntervalJump","∫dx [-1≤x≤1]·λ[[0≤x]·1]","ℝ","1"),
	Case("CauchyRayLower","∫dx [1≤x]·(1+x²)⁻¹·λ[x]","ℝ","1/4·π"),
	Case("CauchyRayUpper","∫dx [x<1]·(1+x²)⁻¹·λ[x]","ℝ","3/4·π"),
	Case("CauchyRayLowerNegative","∫dx [-1<x]·(-1-x²)⁻¹·λ[x]","ℝ","-3/4·π"),
	Case("CauchyRayUpperNegative","∫dx [x≤-1]·(-1-x²)⁻¹·λ[x]","ℝ","-1/4·π"),
	Case("CauchyRayUpperZero","∫dx [x≤0]·λ[atan(x)]","ℝ","1/2·π"),
	Case("CauchyRayTranslate","∫dx [3/2<x]·(1+(2*x-3)^2)⁻¹·λ[x]","ℝ","1/4·π"),
	Case("CauchyRayScaledAtan","∫dx [x≤3/2]·λ[atan(2*x-3)]","ℝ","1/2·π"),
	Case("CauchyRaySymbolic","λ(u:ℝ).∫dx [x≤u]·(1+x²)⁻¹·λ[x]","ℝ→ℝ","λ(u:ℝ). atan(u)+1/2·π"),
	Case("CauchyRayNormalized","λ(u:ℝ).∫dx [x≤u]·π⁻¹*(1+x²)⁻¹·λ[x]","ℝ→ℝ","λ(u:ℝ). (atan(u)+1/2·π)·π⁻¹"),
	Case("CauchyRayPartialFactor","λ(h:ℝ→ℝ).λ(t:ℝ).∫dx [1<x]·(h(t)*(1+x²)⁻¹)·λ[x]","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(t:ℝ). h(t)·(1/4)·π"),
	Case("CauchyRayBoth","λ(z:ℝ).(∫dx [x<z]·(1+x²)⁻¹·λ[x])+(∫dx [z≤x]·(1+x²)⁻¹·λ[x])","ℝ→ℝ","λ(z:ℝ). π"),
	Case("CauchyRayMissing","defined(∫dx [undefined(ℝ)<x]·(1+x²)⁻¹·λ[x])","𝔹","false"),
	Case("CauchyRayPole","∫dx [2<x]·(x²-2)⁻¹·λ[x]","ℝ"),
	Case("CauchyWindowUnit","∫dx [-1≤x≤1]·(1+x²)⁻¹·λ[x]","ℝ","1/2·π"),
	Case("CauchyWindowAtan","∫dx [-1≤x≤1]·λ[atan(x)]","ℝ","1/2·π"),
	Case("CauchyWindowAtanScaled","∫dx [1<x<2]·λ[atan(2*x-3)]","ℝ","1/2·π"),
	Case("CauchyWindowShift","∫dx [1≤x≤2]·(1+(2*x-3)^2)⁻¹·λ[x]","ℝ","1/4·π"),
	Case("CauchyWindowNegative","∫dx [0≤x≤1]·(-1-x²)⁻¹·λ[x]","ℝ","-1/4·π"),
	Case("CauchyWindowRational","∫dx [0<x<1/2]·(x²+1/4)⁻¹·λ[x]","ℝ","1/2·π"),
	Case("CauchyWindowUnknown","λ(l:ℝ).λ(u:ℝ).∫dx [l<x≤u]·(1+x²)⁻¹·λ[x]","ℝ→ℝ→ℝ","λ(l:ℝ). λ(u:ℝ). [l<u]·(-atan(l)+atan(u))"),
	Case("CauchyWindowReverse","∫dx [2≤x≤1]·(1+x²)⁻¹·λ[x]","ℝ","0"),
	Case("CauchyWindowSingleton","∫dx [1≤x≤1]·(1+x²)⁻¹·λ[x]","ℝ","0"),
	Case("CauchyWindowMean","∫dx [0≤x≤1]·(1+(1+x²)⁻¹)·λ[x]","ℝ","1/4·π+1"),
	Case("CauchyWindowFactor","λ(h:ℝ→ℝ).λ(t:ℝ).∫dx [-1<x<1]·(h(t)*(1+x²)⁻¹)·λ[x]","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(t:ℝ). h(t)·(1/2)·π"),
	Case("CauchyWindowZeroMask","∫dx [1<x<0]·undefined(ℝ)*(1+x²)⁻¹·λ[x]","ℝ","0"),
	Case("CauchyWindowMissing","defined(∫dx [undefined(ℝ)<x<1]·(1+x²)⁻¹·λ[x])","𝔹","false"),
	Case("CauchyWindowIrrational","∫dx [0≤x≤1]·(2*x²+2*x+3)⁻¹·λ[x]","ℝ","-1/5·sqrt(5)·atan(1/5·sqrt(5))+1/5·sqrt(5)·atan(3/5·sqrt(5))"),
	Case("CauchyWindowPole","∫dx [2<x<3]·(x²-2)⁻¹·λ[x]","ℝ"),
	Case("CauchyScaledAtan","∫dx λ[atan(2*x-3)]","ℝ","π"),
	Case("CauchyScaleNormal","∫dx (π⁻¹)·(1+x²)⁻¹·λ[x]","ℝ","1"),
	Case("CauchyScaleQuotient","∫dx 1/(π*(1+x²))·λ[x]","ℝ","1"),
	Case("CauchyScaleLeft","λ(a:ℝ).∫dx a*(1+x²)⁻¹·λ[x]","ℝ→ℝ","λ(a:ℝ). a·π"),
	Case("CauchyScaleRight","λ(a:ℝ).∫dx (1+x²)⁻¹*a·λ[x]","ℝ→ℝ","λ(a:ℝ). a·π"),
	Case("CauchyScaleSigned","λ(a:ℝ).∫dx a*(-2*x²-2*x-3)⁻¹·λ[x]","ℝ→ℝ","λ(a:ℝ). -a·(1/5)·sqrt(5)·π"),
	Case("CauchyScalePartial","λ(a:ℝ).∫dx a⁻¹*(1+x²)⁻¹·λ[x]","ℝ→ℝ","λ(a:ℝ). a⁻¹·π"),
	Case("CauchyScaleProbe","λ(h:ℝ→ℝ).λ(t:ℝ).∫dx h(t)*(1+x²)⁻¹·λ[x]","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(t:ℝ). h(t)·π"),
	Case("CauchyScaleZero","∫dx 0*(1+x²)⁻¹·λ[x]","ℝ","0"),
	Case("CauchyScalePole","λ(a:ℝ).∫dx a*(x²-1)⁻¹·λ[x]","ℝ→ℝ"),
	Case("CauchyScaleInner","λ(a:ℝ).massD(weightD(λ(x:ℝ).a,weightD(λ(x:ℝ).(1+x²)⁻¹,lebesgueD())))","ℝ→ℝ","λ(a:ℝ). a·π"),
	Case("CauchyScaleOuter","λ(a:ℝ).massD(weightD(λ(x:ℝ).(1+x²)⁻¹,weightD(λ(x:ℝ).a,lebesgueD())))","ℝ→ℝ","λ(a:ℝ). a·π"),
	Case("CauchyWhole","∫dx (1+x²)⁻¹·λ[x]","ℝ","π"),
	Case("CauchyScaledAxis","∫dx (1+4*x²)⁻¹·λ[x]","ℝ","1/2·π"),
	Case("CauchyTranslated","∫dx (1+(2*x-3)^2)⁻¹·λ[x]","ℝ","1/2·π"),
	Case("CauchyIrrationalWidth","∫dx (2*x²+2*x+3)⁻¹·λ[x]","ℝ","1/5·sqrt(5)·π"),
	Case("CauchyNegative","∫dx (-2*x²-2*x-3)⁻¹·λ[x]","ℝ","-1/5·sqrt(5)·π"),
	Case("CauchyRational","∫dx ((x-1)^2+1/4)⁻¹·λ[x]","ℝ","2·π"),
	Case("CauchyAtanWhole","∫dx λ[atan(x)]","ℝ","π"),
	Case("CauchyGuard","λ(p:𝔹).∫dx [p]·(1+x²)⁻¹·λ[x]","𝔹→ℝ","λ(p:𝔹). [p]·π"),
	Case("CauchyPole","∫dx (x²-1)⁻¹·λ[x]","ℝ"),
	Case("CauchyTouch","∫dx (1-2*x+x²)⁻¹·λ[x]","ℝ"),
	Case("CauchyQuartic","∫dx (1+x^4)⁻¹·λ[x]","ℝ"),
	Case("CauchyAffine","∫dx (1+x)⁻¹·λ[x]","ℝ"),
	Case("CauchyMeasure","Λx. (1+x²)⁻¹·λ[x]","Distribution(ℝ)","Λ(x:ℝ). ((x^2+1)⁻¹)·λ[x]"),
	Case("TurningWholeSquare","∫dx λ[atan(x)^2]","ℝ","1/2·π^2"),
	Case("TurningWholeFourth","∫dx λ[tanh(x)^4]","ℝ","2"),
	Case("TurningWholeCosh","∫dx λ[cosh(atan(x))]","ℝ","cosh(-1/2·π)+cosh(1/2·π)-2"),
	Case("TurningWholeReflected","∫dx λ[cosh(tanh(-2*x))]","ℝ","2·cosh(1)-2"),
	Case("TurningWholeShift","∫dx λ[(tanh(x)+1)^2]","ℝ","4"),
	Case("TurningWholeOffCentre","∫dx λ[(tanh(x)+2)^4]","ℝ","80"),
	Case("TurningWholeNonnegative","∫dx λ[atan(exp(x))^2]","ℝ","1/4·π^2"),
	Case("TurningRayCDF","λ(u:ℝ). ∫dx [x≤u]·λ[atan(x)^2]","ℝ→ℝ","λ(u:ℝ). atan(u)·atan(abs(u))+1/4·π^2"),
	Case("TurningRayRight","λ(l:ℝ). ∫dx [l<x]·λ[tanh(x)^4]","ℝ→ℝ","λ(l:ℝ). -tanh(abs(l))^3·tanh(l)+1"),
	Case("TurningRayReverse","∫dx [x≤0]·λ[tanh(-3*x)^2]","ℝ","1"),
	Case("TurningRayCosh","∫dx [0≤x]·λ[cosh(atan(x))]","ℝ","cosh(1/2·π)-1"),
	Case("TurningRayCoshCross","∫dx [x≤1]·λ[cosh(tanh(x))]","ℝ","[tanh(1)<0]·(-cosh(tanh(1))+1)+[0≤tanh(1)]·(cosh(tanh(1))-1)+cosh(1)-1"),
	Case("TurningRayDecay","∫dx [x≤0]·λ[cosh(exp(x))]","ℝ","cosh(1)-1"),
	Case("TurningRayPartial","λ(u:ℝ). ∫dx [x≤u⁻¹]·λ[tanh(x)^2]","ℝ→ℝ","λ(u:ℝ). (guard(u≠0,tanh(u⁻¹)·tanh(abs(u)⁻¹)))+1"),
	Case("TurningRayMissing","∫dx [x<undefined(ℝ)]·λ[tanh(x)^2]","ℝ","undefined(ℝ)"),
	Case("TurningRayHigher","λ(h:ℕ→ℝ). λ(n:ℕ). ∫dx [h(n)≤x]·λ[tanh(x)^2]","(ℕ→ℝ)→ℕ→ℝ","λ(h:ℕ→ℝ). λ(n:ℕ). -(guard(holds((n∈domain(h))),abs(tanh(h(n)))·tanh(h(n))))+1"),
	Case("TurningControlOpaque","λ(h:ℝ→ℝ). ∫dx λ[cosh(h(x))]","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). ∫dx λ[(cosh(h(x)))]"),
	Case("TurningControlInfinite","∫dx λ[x^2]","ℝ","∫dx (2·abs(x))·λ[x]"),
	Case("TurningControlOscillating","∫dx λ[cosh(sin(x))]","ℝ","∫dx (abs(cos(x))·sinh(abs(sin(x))))·λ[x]"),
	Case("TurningControlOneEnd","∫dx λ[cosh(exp(x))]","ℝ","∫dx (exp(x)·sinh(exp(x)))·λ[x]"),
	Case("TanhCoordinateMeasure","Λx. λ[tanh(x)]","Distribution(ℝ)","Λ(x:ℝ). ((cosh(x)^2)⁻¹)·λ[x]"),
	Case("TanhCoordinateSmooth","Λx. λ[tanh(x^2+1)]","Distribution(ℝ)","Λ(x:ℝ). (2·(cosh(x^2+1)^2)⁻¹·abs(x))·λ[x]"),
	Case("TanhCoordinatePoint","densityAtD(Λx.λ[tanh(2*x)],0)","ℝ","2"),
	Case("TanhCoordinateNestedPoint","densityAtD(Λx.λ[tanh(atan(3*x))],0)","ℝ","3"),
	Case("TanhCoordinateCDF","λ(u:ℝ).∫dx [x≤u]·λ[tanh(x)]","ℝ→ℝ","λ(u:ℝ). tanh(u)+1"),
	Case("TanhCoordinateSurvival","λ(l:ℝ).∫dx [l<x]·λ[tanh(-x)]","ℝ→ℝ","λ(l:ℝ). -tanh(l)+1"),
	Case("TanhCoordinateWhole","∫dx λ[tanh(3*x+2)]","ℝ","2"),
	Case("TanhCoordinateNested","∫dx λ[tanh(atan(x))]","ℝ","-tanh(-1/2·π)+tanh(1/2·π)"),
	Case("TanhCoordinateWindow","∫dx [-1≤x≤1]·λ[tanh(-2*x)]","ℝ","-tanh(-2)+tanh(2)"),
	Case("TanhCoordinateSquareWindow","∫dx [-1≤x≤1]·λ[tanh(x)^2]","ℝ","2·tanh(1)^2"),
	Case("TanhCoordinateCorner","densityAtD(Λx.λ[tanh(abs(x))],0)","ℝ","undefined(ℝ)"),
	Case("TanhCoordinateBesideCorner","densityAtD(Λx.λ[tanh(abs(x))],-1)","ℝ","(cosh(1)^2)⁻¹"),
	Case("TanhCoordinateJump","∫dx λ[tanh([0≤x])]","ℝ","tanh(1)"),
	Case("TanhCoordinateJumpPoint","densityAtD(Λx.λ[tanh([0≤x])],0)","ℝ","undefined(ℝ)"),
	Case("TanhCoordinateJumpAway","densityAtD(Λx.λ[tanh([0≤x])],1)","ℝ","0"),
	Case("TanhCoordinateRemovable","∫dx λ[tanh([x=0])]","ℝ","∫dx λ[([x=0]·tanh(1))]"),
	Case("TanhCoordinateHole","defined(densityAtD(Λx.λ[tanh(x)],undefined(ℝ)))","𝔹","false"),
	Case("TanhCoordinateUnsupported","λ(h:ℝ→ℝ).∫dx λ[tanh(h(x))]","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). ∫dx λ[(tanh(h(x)))]"),
	Case("TanhCoordinatePole","∫dx λ[tanh(x⁻¹)]","ℝ","∫dx λ[(tanh(x⁻¹))]"),
	Case("AtanMeasure","Λx. λ[atan(x)]","Distribution(ℝ)","Λ(x:ℝ). ((x^2+1)⁻¹)·λ[x]"),
	Case("AtanPoint","densityAtD(Λx. λ[atan(2*x+1)],0)","ℝ","1"),
	Case("AtanAbs","densityAtD(Λx. λ[atan(abs(x))],1)","ℝ","1/2"),
	Case("AtanCorner","densityAtD(Λx. λ[atan(abs(x))],0)","ℝ","undefined(ℝ)"),
	Case("AtanAtom","∫dx λ[atan([0≤x]·1)]","ℝ","1/4·π"),
	Case("AtanJump","densityAtD(Λx. λ[atan(x+[0≤x]·1)],0)","ℝ","undefined(ℝ)"),
	Case("AtanLeft","densityAtD(Λx. λ[atan(x+[0≤x]·1)],-1)","ℝ","1/2"),
	Case("AtanRight","densityAtD(Λx. λ[atan(x+[0≤x]·1)],1)","ℝ","1/5"),
	Case("AtanWindow","densityAtD(Λx. λ[atan(abs(x)) | u. u<0],0)","ℝ","0"),
	Case("AtanNested","densityAtD(Λx. λ[atan(sin(x)+x)],0)","ℝ","2"),
	Case("AtanNestedDown","densityAtD(Λx. λ[atan(exp(-x))],0)","ℝ","1/2"),
	Case("AtanAsinh","densityAtD(Λx. λ[asinh(atan(-x))],0)","ℝ","1"),
	Case("AtanComposite","densityAtD(Λx. λ[atan(exp(-x))+2*x],0)","ℝ","3/2"),
	Case("ChangedCoordinateArsinh","densityAtD(Λx. λ[asinh(abs(x))],3/4)","ℝ","4/5"),
	Case("ChangedCoordinateMany","densityAtD(Λx. λ[log(1+abs(x-1)+abs(x+1))],2)","ℝ","2/5"),
	Case("ChangedCoordinateIverson","densityAtD(Λx. λ[exp([0<x]·x)],-1)","ℝ","0"),
	Case("ChangedCoordinateInactive","densityAtD(Λx. λ[exp(abs(x)) | u. u<1],0)","ℝ","0"),
	Case("ChangedCoordinateActive","densityAtD(Λx. λ[exp(abs(x)) | u. 1≤u],0)","ℝ","undefined(ℝ)"),
	Case("ChangedCoordinatePredicate","λ(k:ℝ→𝔹). Λx. λ[log(1+abs(x)) | u. k(u)]","(ℝ→𝔹)→Distribution(ℝ)"),
	Case("UnchangedCoordinateLogZero","densityAtD(Λx. λ[log(abs(x))],0)","ℝ"),
	Case("NegativeCoordinateQuadratic","densityAtD(Λx. λ[(-x^2+x-1)⁻¹],0)","ℝ","1"),
	Case("NegativeCoordinateStationary","densityAtD(Λx. λ[(-x^2+x-1)⁻¹],1/2)","ℝ","0"),
	Case("NegativeCoordinateProduct","densityAtD(Λx. λ[(-exp(x)*cosh(x))⁻¹],0)","ℝ","1"),
	Case("NegativeCoordinatePower","densityAtD(Λx. λ[((-x^2+x-1)^3)⁻¹],0)","ℝ","3"),
	Case("NegativeCoordinateNested","densityAtD(Λx. λ[((-x^2+x-1)⁻¹)⁻¹],0)","ℝ","1"),
	Case("NegativeCoordinateRestricted","densityAtD(Λx. λ[(-x^2+x-1)⁻¹ | t. t≤-1],0)","ℝ","1"),
	Case("CoordinateReciprocalPole","Λx. λ[(-x^2+2*x-1)⁻¹]","Distribution(ℝ)"),
	Case("CoordinateNegativeLog","Λx. λ[log(-x^2+x-1)]","Distribution(ℝ)"),
	Case("CoordinateQueryMissing","densityAtD(Λx. λ[log(1+x²)],undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("CoordinateQueryMissingGuard","densityAtD(Λx. λ[sqrt(9+16*x²) | u. (1/(u-5))<0],1)","ℝ","undefined(ℝ)"),
	Case("CoordinateLogPole","Λx. λ[log(x²)]","Distribution(ℝ)"),
	Case("CoordinatePartialSqrt","Λy. λ[sqrt(y)]","Distribution(ℝ)","Λ(y:ℝ). λ[(sqrt(y))]"),
	Case("CoordinatePartialLog","Λy. λ[log(y)]","Distribution(ℝ)","Λ(y:ℝ). λ[(log(y))]"),
	Case("RestrictedSmoothMass","∫dy λ[2*y+1 | x. 0<x<1]","ℝ","1"),
	Case("RestrictedSmoothSquare","densityAtD(Λy. λ[y² | x. x≤1],-1)","ℝ","2"),
	Case("RestrictedCornerOff","densityAtD(Λy. λ[abs(y) | x. 0<x],0)","ℝ","0"),
	Case("RestrictedCornerOn","densityAtD(Λy. λ[abs(y) | x. 0≤x],0)","ℝ","undefined(ℝ)"),
	Case("RestrictedCornerMass","∫dy λ[abs(y) | x. 0<x<1]","ℝ","2"),
	Case("RestrictedCornerPredicate","λ(p:ℝ→𝔹). Λy. λ[abs(y-1) | x. p(x)]","(ℝ→𝔹)→Distribution(ℝ)"),
	Case("RestrictedCornerWithJump","densityAtD(Λy. λ[abs(y-1)+2*[2≤y] | x. 0<x<2],1)","ℝ","0"),
	Case("RestrictedCornerJumpAtom","densityAtD(Λy. λ[abs(y-1)+2*[2≤y] | x. 0<x<2],2)","ℝ","undefined(ℝ)"),
	Case("RestrictedJumpWindow","∫dy λ[2*[0≤y] | x. 0<x<1]","ℝ","1"),
	Case("RestrictedJumpDescending","∫dy λ[2*[y<0] | x. 1/2≤x≤3/2]","ℝ","1"),
	Case("RestrictedJumpDisjoint","∫dy λ[2*[0≤y] | x. 2<x]","ℝ","0"),
	Case("RestrictedJumpEndpoint","∫dy λ[2*[0≤y] | x. x=2]","ℝ","0"),
	Case("RestrictedJumpTwo","∫dy λ[2*[0≤y]+[1≤y] | x. 1<x<5/2]","ℝ","3/2"),
	Case("RestrictedJumpDensity","densityAtD(Λy. λ[2*[0≤y] | x. 0<x<1],0)","ℝ","undefined(ℝ)"),
	Case("RestrictedJumpPartialProbe","∫dy y⁻¹·λ[2*[0≤y] | x. 0<x<1]","ℝ","undefined(ℝ)"),
	Case("RestrictedJumpSlope","densityAtD(Λy. λ[y+2*[0≤y] | x. 1<x<3],1/2)","ℝ","1"),
	Case("JumpPartialRestriction","∫dy λ[2*[0≤y] | x. x⁻¹<1]","ℝ","undefined(ℝ)"),
	Case("JumpOutputWindow","∫dy [0<y<1]·λ[2*[0≤y]]","ℝ","0"),
	Case("SheetPartPairing","λ(p:ℝ→𝔹). λ(t:ℝ→ℝ). ∫dy t(y)·λ[-sqrt(y),sqrt(y) | x. p(x)]","(ℝ→𝔹)→(ℝ→ℝ)→ℝ"),
	Case("SheetPartCritical","∫dy y⁻¹·λ[-sqrt(y),sqrt(y) | x. 0<x]","ℝ","undefined(ℝ)"),
	Case("SheetPartDensityPositive","densityAtD(Λy. λ[-sqrt(y),sqrt(y) | x. 0<x],4)","ℝ","1/4"),
	Case("SheetPartDensityExcluded","densityAtD(Λy. λ[-sqrt(y),sqrt(y) | x. 0<x],0)","ℝ","0"),
	Case("SheetPartDensityCritical","densityAtD(Λy. λ[-sqrt(y),sqrt(y) | x. x≤0],0)","ℝ","undefined(ℝ)"),
	Case("SheetPartMass","∫dy λ[-sqrt(y),sqrt(y) | x. 0<x<1]","ℝ","1"),
	Case("CoverAffineSum","Λy. λ[3-2*y]+λ[y+1]","Distribution(ℝ)"),
	Case("CoverPartSum","Λy. λ[-sqrt(y),sqrt(y) | x. x≤0] + λ[-sqrt(y),sqrt(y) | x. 0<x]","Distribution(ℝ)"),
	Case("CoverPartCapture","λ(a:ℝ). Λy. λ[y+a,y-a | x. a<x]","ℝ→Distribution(ℝ)"),
	Case("CoverPartMissing","inversePartD(undefined(ℝ→𝔹),(λ(y:ℝ).y,))","Distribution(ℝ)"),
	Case("CoverShadow","λ(a:ℝ).Λy. λ[a-y,a+y,a]","ℝ→Distribution(ℝ)"),
	Case("ChartComposition","Λy. ∫dx λ[±1/2·sqrt(x)]·δ(x)[y]","Distribution(ℝ)"),
	Case("BandAtEdge","densityAtD(Λy. [y≤1]·λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)],1)","ℝ","1/2"),
	Case("BandAtCritical","densityAtD(Λy. [y≤1]·λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)],0)","ℝ","undefined(ℝ)"),
	Case("BandAbove","densityAtD(Λy. [y≤1]·λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)],2)","ℝ","0"),
	Case("BandOutsideImage","densityAtD(Λy. [y≤1]·λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)],-1)","ℝ","0"),
	Case("BandMissing","densityAtD(Λy. [y≤1]·λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)],undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("BandInside","densityAtD(Λy. ∫dx [0≤x≤1]·λ[x]·δ((1-2*x)^2)[y],1/4)","ℝ","1"),
	Case("BandTotalMass","∫dy [y≤1]·λ[1/2-1/2·sqrt(y), 1/2+1/2·sqrt(y)]","ℝ","1"),
	Case("ChartCaptured","λ(y:ℝ). Λz. λ[y ± 1/2·sqrt(z)]","ℝ→Distribution(ℝ)"),
	Case("PartialChart","radiusImageD(3,undefined(ℝ→ℝ))","Distribution(ℝ)"),
	Case("RadiusPositive","densityAtD(radiusImageD(1/2,λ(y:ℝ). 1/2·sqrt(y)),4)","ℝ","1/4"),
	Case("RadiusCritical","densityAtD(radiusImageD(3,λ(y:ℝ). sqrt(y)·3),0)","ℝ","undefined(ℝ)"),
	Case("RadiusEmpty","densityAtD(radiusImageD(0,λ(y:ℝ). sqrt(y)),-1)","ℝ","0"),
	Case("RadiusGuarded","densityAtD(radiusImageD(0,λ(y:{y:ℝ | 0≤y}). sqrt(y)),4)","ℝ","1/2"),
	Case("RadiusMissing","densityAtD(radiusImageD(0,λ(y:ℝ). sqrt(y)),undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("RadiusSublevel","massD(weightD(λ(y:ℝ).[y≤4],Λz. ∫dx λ[x]·δ((1-2*x)^2)[z]))","ℝ","2"),
	Case("RadiusSublevelGap","∫dy [y≤-1]·(radiusImageD(3,λ(y:ℝ).3*sqrt(y)))[y]","ℝ","0"),
	Case("RadiusSublevelCritical","∫dy [y≤0]·(radiusImageD(3,λ(y:ℝ).3*sqrt(y)))[y]","ℝ","0"),
	Case("RadiusSublevelShifted","∫dy [y≤4]·(radiusImageD(3,λ(y:ℝ).3*sqrt(y)))[y]","ℝ","12"),
	Case("RadiusSublevelMissing","∫dy [y≤undefined(ℝ)]·(radiusImageD(1/2,λ(y:ℝ).1/2*sqrt(y)))[y]","ℝ","undefined(ℝ)"),
	Case("RadiusSublevelSymbolic","λ(t:ℝ).∫dy [y≤t]·(radiusImageD(1/2,λ(y:ℝ).1/2*sqrt(y)))[y]","ℝ→ℝ","λ(t:ℝ). [0≤t]·sqrt(t)"),
	Case("BareCriticalPoint","densityAtD(Λy. ∫dx λ[x]·δ((1-2*x)^2)[y],0)","ℝ","undefined(ℝ)"),
	Case("BareCriticalNegative","densityAtD(Λy. ∫dx λ[x]·δ((1-2*x)^2)[y],-1)","ℝ","0"),
	Case("BareCriticalPositive","densityAtD(Λy. ∫dx λ[x]·δ((1-2*x)^2)[y],4)","ℝ","1/4"),
	Case("ClosedSquareDensity","λ(y:ℝ).densityAtD(Λz. ∫dx λ[x]·δ((1-2*x)^2)[z],y)","ℝ→ℝ","λ(y:{y:ℝ | y≠0}). [0≤y]·(sqrt(y)⁻¹·(1/2))"),
	Case("ClosedSquareMass","λ(y:ℝ).∫dx λ[x]·δ((1-2*x)^2)[y]//λ[y]","ℝ→ℝ","λ(y:{y:ℝ | y≠0}). [0≤y]·(sqrt(y)⁻¹·(1/2))"),
	Case("ClosedSquareMissing","densityAtD(pushforwardOnD(λ(x:ℝ).true,λ(x:ℝ).(x/3-1)*(x/3-1)),undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("ClosedSquareRational","densityAtD(pushforwardOnD(λ(x:ℝ).true,λ(x:ℝ).(x/3-1)*(x/3-1)),4)","ℝ","3/2"),
	Case("NativeTruePartial","pushforwardOnD(λ(x:ℝ).true,λ(x:ℝ).x⁻¹)","Distribution(ℝ)"),
	Case("WeightedAbsObservation","λ(z:ℝ). densityAtD(Λy. ∫dx λ[x]·δ(x²)[y]·abs(x),z)","ℝ→ℝ","λ(z:ℝ). [0<z]"),
	Case("WeightedSquareSource","bindD(weightD(λ(x:ℝ).abs(x),lebesgueD()),λ(x:ℝ).δ(x*x))","Distribution(ℝ)","Λ(y:ℝ). [0<y]·λ[y]"),
	Case("WeightedSquareAsymmetric","Λy. ∫dx λ[x]·δ(x²)[y]·(x*(x+1))^2","Distribution(ℝ)"),
	Case("WeightedSquareChanging","integralD(λ(x:ℝ).scaleD(x²*(x²-1)*(1+x)^2,δ(x²)))","Distribution(ℝ)"),
	Case("WeightedSquareMasked","Λy. ∫dx ([0<x]·(1+x²))·λ[x]·δ(x²)[y]","Distribution(ℝ)"),
	Case("WeightedSquareNegative","integralD(λ(x:ℝ).scaleD(-x²,δ(x*x)))","Distribution(ℝ)"),
	Case("WeightedSquareCancels","Λy. ∫dx λ[x]·δ(x²)[y]·x","Distribution(ℝ)"),
	Case("WeightedSquareCritical","integralD(λ(x:ℝ).scaleD(1+x²,δ(x²)))","Distribution(ℝ)"),
	Case("WeightedSquarePartial","integralD(λ(x:ℝ).scaleD(abs((x-1)⁻¹)*x²,δ(x²)))","Distribution(ℝ)"),
	Case("SquareChartShifted","Λy. ∫dx λ[x]·δ((2*x+1)^2)[y]·[0<x<1]","Distribution(ℝ)"),
	Case("SquareChartOverlap","Λy. ∫dx λ[x]·δ(x²)[y]·[x≠0∧-2<x]","Distribution(ℝ)"),
	Case("SquareChartBoth","Λy. ∫dx λ[x]·δ((1-2*x)^2)[y]·[2*x≠1]","Distribution(ℝ)","Λ(y:ℝ). ([0<y]·(sqrt(y)⁻¹·(1/2)))·λ[y]"),
	Case("SquareChartRational","pushforwardOnD(λ(x:ℝ).x<3,λ(x:ℝ).(x/3-1)*(x/3-1))","Distribution(ℝ)"),
	Case("SquareChartScaledPuncture","Λy. ∫dx λ[x]·δ((x/3-1)^2)[y]·[x≠3]","Distribution(ℝ)","Λ(y:ℝ). ([0<y]·(3·sqrt(y)⁻¹))·λ[y]"),
	Case("SquareChartWrongPuncture","pushforwardOnD(λ(x:ℝ).x≠0,λ(x:ℝ).(x/3-1)^2)","Distribution(ℝ)"),
	Case("SquareChartBare","Λy. ∫dx λ[x]·δ(x²)[y]·[x≠0]","Distribution(ℝ)","Λ(y:ℝ). ([0<y]·sqrt(y)⁻¹)·λ[y]"),
	Case("SquareChartActive","Λy. ∫dx λ[x]·δ((1-2*x)^2)[y]·[0<x]","Distribution(ℝ)"),
	Case("SquareChartPartial","pushforwardOnD(λ(x:ℝ).0<(x+2)⁻¹,λ(x:ℝ).(x/3-1)^2)","Distribution(ℝ)"),
	Case("AffineSquareSymbolic","λ[x]·δ((2*x+1)^2)[y]//λ[y]","Distribution(ℝ)"),
	Case("AffineSquareIncreasing","(λ(y:ℝ). λ[x]·δ((2*x+1)^2)[y]//λ[y])(9)","Distribution(ℝ)","Λ(x:ℝ). 1/12·δ(-2)[x]+1/12·δ(1)[x]"),
	Case("AffineSquareDecreasing","(λ(y:ℝ). λ[x]·δ((1-2*x)^2)[y]//λ[y])(9)","Distribution(ℝ)","Λ(x:ℝ). 1/12·δ(-1)[x]+1/12·δ(2)[x]"),
	Case("AffineSquareMasked","(λ(y:ℝ). [0<x]·λ[x]·δ((1-2*x)^2)[y]//λ[y])(9)","Distribution(ℝ)","Λ(x:ℝ). 0·δ(-1)[x]+1/12·δ(2)[x]"),
	Case("AffineSquareExcluded","(λ(y:ℝ). [2*x≠1]·λ[x]·δ((1-2*x)^2)[y]//λ[y])(0)","Distribution(ℝ)","Λ(x:ℝ). 0·δ(1/2)[x]"),
	Case("AffineSquareCritical","(λ(y:ℝ). λ[x]·δ((1-2*x)^2)[y]//λ[y])(0)","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("AffineSquareNegative","(λ(y:ℝ). λ[x]·δ((1-2*x)^2)[y]//λ[y])(-1)","Distribution(ℝ)","Λ(x:ℝ). 0"),
	Case("AffineSquareMass","(λ(y:ℝ). ∫dx λ[x]·δ((2*x+1)^2)[y]//λ[y])(9)","ℝ","1/6"),
	Case("AffineSquareInterior","densityAtD(Λy. ∫dx λ[x]·δ((2*x+1)^2)[y]·[0<x],9)","ℝ","1/12"),
	Case("AffineSquareActiveDensity","densityAtD(pushforwardOnD(λ(x:ℝ).x<0,λ(x:ℝ).(2*x+1)^2),0)","ℝ","undefined(ℝ)"),
	Case("AffineSquareExcludedDensity","densityAtD(pushforwardOnD(λ(x:ℝ).0<x,λ(x:ℝ).(2*x+1)^2),0)","ℝ","0"),
	Case("AffineSquareEmptyDensity","densityAtD(pushforwardOnD(λ(x:ℝ).0<x⁻¹,λ(x:ℝ).x^2),-1)","ℝ","0"),
	Case("AffineSquarePartialDensity","densityAtD(pushforwardOnD(λ(x:ℝ).0<(x+2)⁻¹,λ(x:ℝ).(2*x+1)^2),9)","ℝ","undefined(ℝ)"),
	Case("AffineSquareRationalProduct","λ[x]·δ((x/3-1)*(x/3-1))[y]//λ[y]","Distribution(ℝ)"),
	Case("AffineSquareRationalAt","(λ(y:ℝ). λ[x]·δ((x/3-1)*(x/3-1))[y]//λ[y])(4)","Distribution(ℝ)","Λ(x:ℝ). 3/4·δ(-3)[x]+3/4·δ(9)[x]"),
	Case("AffineSquareMissingQuery","densityAtD(pushforwardOnD(λ(x:ℝ).false,λ(x:ℝ).(2*x+1)^2),undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("AffineSquarePredicate","λ(p:ℝ→𝔹).densityAtD(pushforwardOnD(p,λ(x:ℝ).(2*x+1)^2),-1)","(ℝ→𝔹)→ℝ"),
	Case("AffineSquareZeroSlope","λ[x]·δ((0*x+2)^2)[y]//λ[y]","Distribution(ℝ)"),
	Case("AffineOddSymbolic","λ[x]·δ((2*x+1)^3)[y]//λ[y]","Distribution(ℝ)"),
	Case("AffineOddRational","λ[x]·δ((x/2-1)^3)[y]//λ[y]","Distribution(ℝ)","(2·(3·cbrt(y)^2)⁻¹)·δ(2·cbrt(y)+2)[x]"),
	Case("AffineOddRationalAt","(λ(y:ℝ). (λ[x]·δ((x/2-1)^3)[y])//λ[y])(8)","Distribution(ℝ)","Λ(x:ℝ). 1/6·δ(6)[x]"),
	Case("AffineOddIncreasing","(λ(y:ℝ). (λ[x]·δ((2*x+1)^3)[y])//λ[y])(8)","Distribution(ℝ)","Λ(x:ℝ). 1/24·δ(1/2)[x]"),
	Case("AffineOddDecreasing","(λ(y:ℝ). (λ[x]·δ((1-2*x)^3)[y])//λ[y])(-8)","Distribution(ℝ)","Λ(x:ℝ). 1/24·δ(3/2)[x]"),
	Case("AffineOddFifth","(λ(y:ℝ). (λ[x]·δ((3*x-2)^5)[y])//λ[y])(-32)","Distribution(ℝ)","Λ(x:ℝ). 1/240·δ(0)[x]"),
	Case("AffineOddMass","(λ(y:ℝ). ∫dx λ[x]·δ((1-2*x)^3)[y]//λ[y])(-8)","ℝ","1/24"),
	Case("AffineOddCritical","(λ(y:ℝ). (λ[x]·δ((2*x+1)^3)[y])//λ[y])(0)","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("AffineOddExcluded","(λ(y:ℝ). [2*x≠-1]·λ[x]·δ((2*x+1)^3)[y]//λ[y])(0)","Distribution(ℝ)","Λ(x:ℝ). 0·δ(-1/2)[x]"),
	Case("AffineOddCapture","(λ(t:ℝ).maskedGraphD(λ(x:ℝ).x<t,λ(x:ℝ).(2*x+1)^3)(t))(8)","Distribution(ℝ)","Λ(x:ℝ). 1/24·δ(1/2)[x]"),
	Case("AffineOddHole","densityAtD(pushforwardOnD(λ(x:ℝ).0<(2*x-1)⁻¹,λ(x:ℝ).(2*x+1)^3),8)","ℝ","undefined(ℝ)"),
	Case("AffineOddMissingDensity","densityAtD(pushforwardOnD(λ(x:ℝ).false,λ(x:ℝ).(2*x+1)^3),undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("AffineOddActiveDensity","densityAtD(pushforwardOnD(λ(x:ℝ).x<0,λ(x:ℝ).(2*x+1)^3),0)","ℝ","0⁻¹"),
	Case("AffineOddExcludedDensity","densityAtD(pushforwardOnD(λ(x:ℝ).0<x,λ(x:ℝ).(2*x+1)^3),0)","ℝ","0"),
	Case("AffineOddInterior","densityAtD(Λy. ∫dx λ[x]·δ((2*x+1)^3)[y]·[0<x<1],8)","ℝ","1/24"),
	Case("AffineOddChart","Λy. ∫dx λ[x]·δ((2*x+1)^3)[y]·[2*x≠-1]","Distribution(ℝ)"),
	Case("AffineOddCriticalSource","Λy. ∫dx λ[x]·δ((2*x+1)^3)[y]·[x≠0]","Distribution(ℝ)"),
	Case("OddNonAffineSource","λ[x]·δ((x²+1)^3)[y]//λ[y]","Distribution(ℝ)","λ[x]·δ((x^2+1)^3)[y]//λ[y]"),
	Case("QuarticGraph","λ[x]·δ(x^4)[y]//λ[y]","Distribution(ℝ)","λ[x]·δ(x^4)[y]//λ[y]"),
	Case("MaskedJointSymbolic","[0≤x<1]·λ[x]·δ(1-2*x)[y]//λ[y]","Distribution(ℝ)","([y≤1∧-1<y]·(1/2))·δ(-y·(1/2)+1/2)[x]"),
	Case("MaskedJointIncluded","(λ(y:ℝ). (δ(1-2*x)[y]·([0≤x<1]·λ[x]))//λ[y])(1)","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(0)[x]"),
	Case("MaskedJointExcluded","(λ(y:ℝ). (λ[x]·δ(1-2*x)[y]·[0≤x<1])//λ[y])(-1)","Distribution(ℝ)","Λ(x:ℝ). 0·δ(1)[x]"),
	Case("MaskedJointMass","∫dx [x≠0]·λ[x]·δ(2*x+1)[y]//λ[y]","ℝ","[y≠1]·(1/2)"),
	Case("MaskedJointMissingWeight","(λ(y:ℝ). ∫dx ([0<x⁻¹]·λ[x]·δ(2*x+1)[y])//λ[y])(1)","ℝ","undefined(ℝ)"),
	Case("MaskedJointPartialElsewhere","(λ(y:ℝ). ∫du ([0<u⁻¹]·λ[u]·δ(2*u+1)[y])//λ[y])(3)","ℝ","1/2"),
	Case("MaskedJointHoleDensity","(λ(y:ℝ).densityAtD(([0≤x<1]·λ[x]·δ(1-2*x)[y])//λ[y],1))(-1)","ℝ","0"),
	Case("MaskedJointActiveDensity","(λ(y:ℝ).densityAtD(([0≤x<1]·λ[x]·δ(1-2*x)[y])//λ[y],0))(1)","ℝ","undefined(ℝ)"),
	Case("MaskedJointPredicate","λ(p:ℝ→𝔹).maskedGraphD(p,λ(x:ℝ).2*x+1)(3)","(ℝ→𝔹)→Distribution(ℝ)"),
	Case("MaskedMissingTarget","(λ(y:ℝ). (λ[x]·δ(x+1)[y]·[0<x])//λ[y])(undefined(ℝ))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("MaskedCapture","λ(y:ℝ).maskedGraphD(λ(u:ℝ).u<y,λ(u:ℝ).u^3)(y)","ℝ→Distribution(ℝ)"),
	Case("MaskedSquareSymbolic","λ[x]·δ(x²)[y]·[0<x]//λ[y]","Distribution(ℝ)"),
	Case("MaskedSquareFour","(λ(y:ℝ). [0<x]·λ[x]·δ(x²)[y]//λ[y])(4)","Distribution(ℝ)","Λ(x:ℝ). 0·δ(-2)[x]+1/4·δ(2)[x]"),
	Case("MaskedSquareProduct","(λ(y:ℝ). ∫dx [0<x]·λ[x]·δ(x*x)[y]//λ[y])(4)","ℝ","1/4"),
	Case("MaskedSquareBoth","(λ(y:ℝ). ∫dx [0<x²]·λ[x]·δ(x²)[y]//λ[y])(4)","ℝ","1/2"),
	Case("MaskedSquareExcluded","(λ(y:ℝ). [0<x]·λ[x]·δ(x²)[y]//λ[y])(0)","Distribution(ℝ)","Λ(x:ℝ). 0·δ(0)[x]"),
	Case("MaskedSquareCritical","(λ(y:ℝ). [0≤x]·λ[x]·δ(x²)[y]//λ[y])(0)","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("MaskedSquareMissingAtZero","(λ(y:ℝ). [0<x⁻¹]·λ[x]·δ(x²)[y]//λ[y])(0)","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("MaskedSquareNegative","(λ(y:ℝ). [0<x⁻¹]·λ[x]·δ(x²)[y]//λ[y])(-1)","Distribution(ℝ)","Λ(x:ℝ). 0"),
	Case("MaskedSquareMissingNegativeRoot","(λ(y:ℝ). ∫dx [0<(x+2)⁻¹]·λ[x]·δ(x²)[y]//λ[y])(4)","ℝ","undefined(ℝ)"),
	Case("MaskedSquareMissingPositiveRoot","(λ(y:ℝ). ∫dx [0<(x-2)⁻¹]·λ[x]·δ(x²)[y]//λ[y])(4)","ℝ","undefined(ℝ)"),
	Case("MaskedSquarePredicate","λ(p:ℝ→𝔹).maskedGraphD(p,λ(x:ℝ).x*x)(-1)","(ℝ→𝔹)→Distribution(ℝ)"),
	Case("MaskedSquareMissingQuery","(λ(y:ℝ). [0<x]·λ[x]·δ(x²)[y]//λ[y])(undefined(ℝ))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("PartialBracketProduct","defined(([guard(true,false)]·2)·(0:ℝ)⁻¹)","𝔹","true"),
	Case("TypedBracketProduct","defined(([guard(true,false)]:ℝ)·(0:ℝ)⁻¹)","𝔹","true"),
	Case("StrictBracketProduct","defined(mulR([guard(true,false)],(0:ℝ)⁻¹))","𝔹","false"),
	Case("JointAffineSymbolic","λ[x]·δ(2*x+1)[y]//λ[y]","Distribution(ℝ)","1/2·δ(y·(1/2)-1/2)[x]"),
	Case("JointAffineDecreasing","(λ(y:ℝ). (λ[x]·δ(1-2*x)[y])//λ[y])(5)","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(-2)[x]"),
	Case("JointAffineFraction","(λ(v:ℝ). (δ((3/2)*u-1)[v]·λ[u])//λ[v])(2)","Distribution(ℝ)","Λ(x:ℝ). 2/3·δ(2)[x]"),
	Case("JointAffineMass","∫dx λ[x]·δ(1-2*x)[y]//λ[y]","ℝ","1/2"),
	Case("JointAffineMassDomain","λ(t:ℝ).massD(graphFibreD(λ(x:ℝ).1-2*x,t⁻¹))","ℝ→ℝ","λ(t:{t:ℝ | t≠0}). (1/2:ℝ)"),
	Case("JointAffineMissing","(λ(y:ℝ). (λ[x]·δ(1-2*x)[y])//λ[y])(undefined(ℝ))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("JointAffineMassMissing","(λ(y:ℝ). ∫dx λ[x]·δ(1-2*x)[y]//λ[y])(undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("JointAffineAtAtom","(λ(y:ℝ).densityAtD((λ[x]·δ(1-2*x)[y])//λ[y],-2))(5)","ℝ","undefined(ℝ)"),
	Case("JointAffineOffAtom","(λ(y:ℝ).densityAtD((λ[x]·δ(1-2*x)[y])//λ[y],2))(5)","ℝ","0"),
	Case("JointConstant","λ[x]·δ((3:ℝ))[y]//λ[y]","Distribution(ℝ)","λ[x]·δ((3:ℝ))[y]//λ[y]"),
	Case("SquareGraph","λ[x]·δ(x²)[y]//λ[y]","Distribution(ℝ)"),
	Case("SquareGraphMass","massD((λ[x]·δ(x²)[y])//λ[y])","ℝ","[0≤y]·sqrt(y)⁻¹"),
	Case("SquareGraphIntegral","∫dx λ[x]·δ(x²)[y]//λ[y]","ℝ","[0≤y]·sqrt(y)⁻¹"),
	Case("SquareGraphMassZero","(λ(y:ℝ).∫dx λ[x]·δ(x²)[y]//λ[y])(0)","ℝ","0⁻¹"),
	Case("SquareGraphMassMissing","(λ(y:ℝ).∫dx λ[x]·δ(x²)[y]//λ[y])(undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("IdentityGraphMask","densityAtD(Λy. ∫dx λ[x]·δ(x)[y]·[x≠0],0)","ℝ","0"),
	Case("IdentityGraphInside","densityAtD(Λy. ∫dx λ[x]·δ(x)[y]·[x≠0],2)","ℝ","1"),
	Case("RestrictedSquare","Λy. ∫dx λ[x]·δ(x²)[y]·[0<x<1]","Distribution(ℝ)","Λ(y:ℝ). ([0<y∧y<1]·(sqrt(y)⁻¹·(1/2)))·λ[y]"),
	Case("SquareProductChart","Λz. ∫du [0<u<1]·δ(u*u)[z]·λ[u]","Distribution(ℝ)","Λ(y:ℝ). ([0<y∧y<1]·(sqrt(y)⁻¹·(1/2)))·λ[y]"),
	Case("NestedPositiveChart","δ(Λy. ∫dx λ[x]·δ(x²)[y]·[0<x<1])","Distribution(Distribution(ℝ))"),
	Case("CriticalSquareSource","Λy. ∫dx λ[x]·δ(x²)[y]·[0≤x<1]","Distribution(ℝ)"),
	Case("LegacyPositiveChart","Λy. ([0<y∧y<1]·(sqrt(y)⁻¹·(1/2)))·λ₊[y]","Distribution(ℝ)","Λ(y:ℝ). ([0<y∧y<1]·(sqrt(y)⁻¹·(1/2)))·λ[y]"),
	Case("LegacyPositiveMass","massD(Λy. ([0<y∧y<1]·(sqrt(y)⁻¹·(1/2)))·λ₊[y])","ℝ","1"),
	Case("PositiveChartMass","massD(Λ(y:ℝ). ([0<y∧y<1]·(sqrt(y)⁻¹·(1/2)))·λ[y])","ℝ","1"),
	Case("PositiveChartInterior","densityAtD(Λ(y:ℝ). ([0<y∧y<1]·(sqrt(y)⁻¹·(1/2)))·λ[y],1/4)","ℝ","1"),
	Case("PositiveChartEndpoint","densityAtD(Λ(y:ℝ). ([0<y∧y<1]·(sqrt(y)⁻¹·(1/2)))·λ[y],0)","ℝ","0"),
	Case("PositiveLebesgue","λ₊[y]","Distribution(ℝ)","[0<y]·λ[y]"),
	Case("PositiveLebesgueDensity","densityAtD(positiveLebesgueD(),1)","ℝ","1"),
	Case("PositiveLebesgueZero","densityAtD(positiveLebesgueD(),0)","ℝ","0"),
	Case("RestrictedSquareDensity","λ(y:ℝ).densityAtD(Λy. ∫dx λ[x]·δ(x²)[y]·[0<x<1],y)","ℝ→ℝ"),
	Case("RestrictedSquareMass","massD(Λy. ∫dx λ[x]·δ(x²)[y]·[0<x<1])","ℝ","1"),
	Case("RestrictedSquareInterior","densityAtD(Λy. ∫dx λ[x]·δ(x²)[y]·[0<x<1],1/4)","ℝ","1"),
	Case("RestrictedSquareCritical","densityAtD(Λy. ∫dx λ[x]·δ(x²)[y]·[0<x<1],0)","ℝ","0"),
	Case("RestrictedSquareEndpoint","densityAtD(Λy. ∫dx λ[x]·δ(x²)[y]·[0<x<1],1)","ℝ","0"),
	Case("RestrictedSquareNegative","densityAtD(Λy. ∫dx λ[x]·δ(x²)[y]·[0<x<1],-1)","ℝ","0"),
	Case("RestrictedSquarePartial","densityAtD(Λy. ∫dx λ[x]·δ(x²)[y]·[0<x<1],undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("RestrictedSquareProduct","densityAtD(Λv. ∫du [0<u<1]·δ(u*u)[v]·λ[u],1/4)","ℝ","1"),
	Case("RestrictedRatio","(λ(v:ℝ).(∫du λ[u]·δ(u²)[v]·[0<u<1])//λ[v])(1/4)","ℝ","1"),
	Case("RestrictedHigherType","Λ(y:Distribution(ℝ)). ∫dx λ[x]·δ(δ(x))[y]·[x<1]","Distribution(Distribution(ℝ))"),
	Case("RestrictedCubic","densityAtD(Λy. ∫dx λ[x]·δ(x³)[y]·[0<x<1],1/4)","ℝ"),
	Case("ExplicitRestrictedBind","bindD(lebesgueD(),λ(x:ℝ).scaleD([0<x<1],δ(x²)))","Distribution(ℝ)"),
	Case("ExplicitBindQuarter","densityAtD(bindD(lebesgueD(),λ(x:ℝ).scaleD([0<x<1],δ(x²))),1/4)","ℝ","1"),
	Case("ExplicitWeightedBind","densityAtD(bindD(weightD(λ(x:ℝ).[0<x<1],lebesgueD()),λ(x:ℝ).δ(x*x)),1/4)","ℝ","1"),
	Case("ExplicitAtomIntegral","densityAtD(integralD(λ(x:ℝ).scaleD([0<x<1],δ(x²))),0)","ℝ","0"),
	Case("ExplicitIdentityRows","densityAtD(integralD(λ(x:ℝ).scaleD([0<x<1],δ(x))),1/2)","ℝ","1"),
	Case("ExplicitCubicRows","integralD(λ(x:ℝ).scaleD([0<x<1],δ(x³)))","Distribution(ℝ)"),
	Case("PartialDiracRows","bindD(lebesgueD(),λ(x:ℝ).scaleD([0<x<1],δ(x⁻¹)))","Distribution(ℝ)"),
	Case("TotalRowsPuncture","densityAtD(bindD(lebesgueD(),λ(x:ℝ).scaleD([x≠2],δ(x))),2)","ℝ","0"),
	Case("TotalRowsAffine","integralD(λ(x:ℝ).scaleD([-2≤x<3],δ(2*x+1)))","Distribution(ℝ)"),
	Case("TotalRowsMaskedInverse","bindD(weightD(λ(x:ℝ).[x≠2],lebesgueD()),λ(x:ℝ).δ([x≠0]·x⁻¹))","Distribution(ℝ)"),
	Case("TotalRowsPositiveDenominator","integralD(λ(x:ℝ).scaleD([x≠0],δ((1+x²)⁻¹)))","Distribution(ℝ)"),
	Case("TotalRowsFreeParameter","integralD(λ(x:ℝ).scaleD([x≠z],δ(x+z)))","Distribution(ℝ)"),
	Case("PartialRowPredicate","bindD(lebesgueD(),λ(x:ℝ).scaleD([0<x⁻¹],δ(x)))","Distribution(ℝ)"),
	Case("TotalRowsGuardedPredicate","densityAtD(integralD(λ(x:ℝ).scaleD([x=0∨0<x⁻¹],δ(x))),0)","ℝ","1"),
	Case("PartialRowGuardTooLate","integralD(λ(x:ℝ).scaleD([0<x⁻¹∧x≠0],δ(x)))","Distribution(ℝ)"),
	Case("PartialRowOffSupport","integralD(λ(x:ℝ).scaleD([x≠0],δ(x⁻¹)))","Distribution(ℝ)"),
	Case("AffineRowMass","massD(integralD(λ(x:ℝ).scaleD([-2≤x<3],δ(2*x+1))))","ℝ","5"),
	Case("AffineChartUnrestricted","Λy. ∫dx λ[x]·δ(2*x+1)[y]","Distribution(ℝ)","Λ(y:ℝ). 1/2·λ[y]"),
	Case("AffineChartBareIntegral","densityAtD(integralD(λ(x:ℝ).δ(1-2*x)),3)","ℝ","1/2"),
	Case("AffineChartIncreasing","Λy. ∫dx λ[x]·δ(2*x+1)[y]·[0<x<1]","Distribution(ℝ)","Λ(y:ℝ). ([1<y∧y<3]·(1/2))·λ[y]"),
	Case("AffineChartDecreasing","Λy. ∫dx λ[x]·δ(1-2*x)[y]·[0≤x<1]","Distribution(ℝ)","Λ(y:ℝ). ([y≤1∧-1<y]·(1/2))·λ[y]"),
	Case("AffineChartIncluded","densityAtD(Λy. ∫dx λ[x]·δ(1-2*x)[y]·[0≤x<1],1)","ℝ","1/2"),
	Case("AffineChartExcluded","densityAtD(Λy. ∫dx λ[x]·δ(1-2*x)[y]·[0≤x<1],-1)","ℝ","0"),
	Case("AffineChartHole","densityAtD(Λy. ∫dx λ[x]·δ(2*x+1)[y]·[x≠0],1)","ℝ","0"),
	Case("AffineChartRational","densityAtD(Λy. ∫dx λ[x]·δ((3/2)*x-1)[y]·[0≤x<1],-1)","ℝ","2/3"),
	Case("AffineChartParameter","Λy. ∫dx λ[x]·δ(1-2*x)[y]·[x≠z]","Distribution(ℝ)"),
	Case("ConstantGraph","Λy. ∫dx λ[x]·δ((3:ℝ))[y]·[0<x<1]","Distribution(ℝ)"),
	Case("PartialAffinePredicate","Λy. ∫dx λ[x]·δ(1-2*x)[y]·[0<x⁻¹]","Distribution(ℝ)"),
	Case("NativeTotalMapMass","massD(Λy. ∫dx λ[x]·δ((1+x²)⁻¹)[y]·[0<x<1])","ℝ","1"),
	Case("NativePartialMapMass","massD(Λy. ∫dx λ[x]·δ(x⁻¹)[y]·[0<x<1])","ℝ"),
	Case("CubicMarginal","∫du λ[u]·δ(u^3)[v]//λ[v]","ℝ"),
	Case("IndirectCubicMarginal","(λ(d:Distribution(ℝ)).massD(d))((λ[x]·δ(x^3)[y])//λ[y])","ℝ"),
	Case("CapturedGraphQuery","λ(y:ℝ).graphFibreD(λ(x:ℝ).x+y,y)","ℝ→Distribution(ℝ)"),
	Case("StrictConstantAtom","massD(Λ(x:ℝ).undefined(ℝ)·δ(1)[x])","ℝ"),
	Case("TypedZeroBranches","Λ(x:ℝ).if y<0 then 0 else undefined(Distribution(ℝ))","Distribution(ℝ)"),
	Case("SquareGraphNegative","(λ(y:ℝ).massD((λ[x]·δ(x²)[y])//λ[y]))(-1)","ℝ","0"),
	Case("SquareGraphCritical","(λ(y:ℝ).(λ[x]·δ(x²)[y])//λ[y])(0)","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("SquareGraphFour","(λ(v:ℝ).(λ[u]·δ(u²)[v])//λ[v])(4)","Distribution(ℝ)","Λ(x:ℝ). 1/4·δ(-2)[x]+1/4·δ(2)[x]"),
	Case("SquareGraphOneBranch","(λ(y:ℝ).densityAtD((λ[x]·δ(x²)[y])//λ[y],-2))(4)","ℝ","undefined(ℝ)"),
	Case("SquareGraphOffBranch","(λ(y:ℝ).densityAtD((λ[x]·δ(x²)[y])//λ[y],0))(4)","ℝ","0"),
	Case("SquareGraphMassFour","(λ(y:ℝ).massD((δ(x*x)[y]·λ[x])//λ[y]))(4)","ℝ","1/2"),
	Case("MixedUnitIntervalMass","∫dx δ(0)[x]+[0≤x≤1]*λ[x]","ℝ","2"),
	Case("MixedIntegral","∫dx δ(0)[x]+[-1≤x≤1]·λ[x]","ℝ","3"),
	Case("BoundRectangle","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).weightD(λ(y:ℝ).[0≤y≤2],lebesgueD())))","ℝ","2"),
	Case("SignedRectangle","massD(bindD(weightD(λ(x:ℝ).(-3)*[0≤x≤1],lebesgueD()),λ(x:ℝ).weightD(λ(y:ℝ).[0≤y≤2],lebesgueD())))","ℝ","-6"),
	Case("IntegralRectangle","massD(integralD(λ(x:ℝ).scaleD([0≤x≤1],weightD(λ(y:ℝ).[0≤y≤2],lebesgueD()))))","ℝ","2"),
	Case("ParametricWeight","λ(a:ℝ).massD(weightD(λ(y:ℝ).a,weightD(λ(y:ℝ).[0≤y≤2],lebesgueD())))","ℝ→ℝ"),
	Case("ParametricPartialWeight","λ(a:ℝ).massD(weightD(λ(y:ℝ).1/a,weightD(λ(y:ℝ).[0≤y≤2],lebesgueD())))","ℝ→ℝ"),
	Case("ParametricNestedWeights","λ(a:ℝ).λ(b:ℝ).massD(weightD(λ(y:ℝ).a,weightD(λ(y:ℝ).[0≤y≤2],weightD(λ(y:ℝ).b,lebesgueD()))))","ℝ→ℝ→ℝ"),
	Case("WeightedRows","massD(integralD(λ(x:ℝ).weightD(λ(y:ℝ).[0≤x≤1],weightD(λ(y:ℝ).[0≤y≤2],lebesgueD()))))","ℝ","2"),
	Case("TripleBind","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).bindD(weightD(λ(y:ℝ).[0≤y≤2],lebesgueD()),λ(y:ℝ).weightD(λ(z:ℝ).[0≤z≤3],lebesgueD()))))","ℝ","6"),
	Case("BoundFunction","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).δ(λ(n:ℕ).n)))","ℝ","1"),
	Case("BoundDistribution","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).δ(δ(x))))","ℝ","1"),
	Case("BoundType","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).δ(Distribution(ℝ))))","ℝ","1"),
	Case("UnboundedParameter","λ(a:ℝ).massD(weightD(λ(y:ℝ).a,lebesgueD()))","ℝ→ℝ"),
	Case("ZeroInfiniteRow","massD(bindD(weightD(λ(x:ℝ).0,lebesgueD()),λ(x:ℝ).lebesgueD()))","ℝ"),
	Case("NestedMaskedRectangle","∫dx ∫dy [0≤x≤1]*[0≤y≤2]*λ[y]*λ[x]","ℝ","2"),
	Case("ReversedMaskedRectangle","∫dx ∫dy [0≤y≤2]*[0≤x≤1]*λ[y]*λ[x]","ℝ","2"),
	Case("SignedMaskedRectangle","∫dx ∫dy (-3)*[0≤x≤1]*[0≤y≤2]*λ[y]*λ[x]","ℝ","-6"),
	Case("PuncturedMaskedRectangle","∫dx ∫dy [x≠0]*[-1≤x≤1]*[0≤y≤2]*λ[y]*λ[x]","ℝ","4"),
	Case("MaskedParameter","λ(a:ℝ).∫dx [0≤x≤2]*a*λ[x]","ℝ→ℝ"),
	Case("MaskedPartialParameter","λ(a:ℝ).∫dx [0≤x≤2]*(1/a)*λ[x]","ℝ→ℝ"),
	Case("OuterParameterMask","λ(p:𝔹).∫dx [p]*[0≤x≤2]*λ[x]","𝔹→ℝ"),
	Case("InnerParameterMask","λ(p:𝔹).∫dx [0≤x≤2]*[p]*λ[x]","𝔹→ℝ"),
	Case("MaskedPartialBranch","λ(p:𝔹).λ(a:ℝ).∫dx [p]*[0≤x≤2]*(1/a)*λ[x]","𝔹→ℝ→ℝ"),
	Case("MixedParameterMasks","λ(p:𝔹).λ(q:𝔹).∫dx [p]*[0≤x≤2]*[q]*λ[x]","𝔹→𝔹→ℝ"),
	Case("NullPointParameter","λ(a:ℝ).∫dx [x=0]*(1/a)*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("ClosedSingletonParameter","λ(a:ℝ).∫dx [0≤x≤0]*(1/a)*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("OpenEmptyParameter","λ(a:ℝ).∫dx [0<x<0]*(1/a)*λ[x]","ℝ→ℝ","λ(a:ℝ). (0:ℝ)"),
	Case("EmptyMaskedParameter","λ(a:ℝ).∫dx [x<0]*[1<x]*(1/a)*λ[x]","ℝ→ℝ","λ(a:ℝ). (0:ℝ)"),
	Case("DisjointPartialWeights","λ(a:ℝ).massD(weightD(λ(x:ℝ).[x=0]*(1/a),weightD(λ(x:ℝ).[x=1],lebesgueD())))","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("DisjointOpenSupports","λ(a:ℝ).massD(weightD(λ(x:ℝ).[0<x<1]*(1/a),weightD(λ(x:ℝ).[2<x<3],lebesgueD())))","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("DisjointTwoParameters","λ(a:ℝ).λ(b:ℝ).massD(weightD(λ(x:ℝ).[x=0]*(1/a),weightD(λ(x:ℝ).[x=1]*(1/b),lebesgueD())))","ℝ→ℝ→ℝ"),
	Case("MaskedNullPoint","λ(p:𝔹).λ(a:ℝ).∫dx [p]*[x=0]*(1/a)*λ[x]","𝔹→ℝ→ℝ"),
	Case("ShiftedNullPoint","λ(a:ℝ).∫dx [2*x=1]*(1/a)*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("NullPointDensity","λ(a:ℝ).densityAtD(weightD(λ(x:ℝ).[x=0]*a,lebesgueD()),0)","ℝ→ℝ"),
	Case("StepSum","∫dx ([0≤x≤1]+2*[1≤x≤3])*λ[x]","ℝ","5"),
	Case("StepUnion","∫dx [(0<x<1)∨(2<x<3)]*λ[x]","ℝ","2"),
	Case("StepOverlap","∫dx ([0≤x≤2]+[1≤x≤3])*λ[x]","ℝ","4"),
	Case("StepSigned","∫dx ((-3)*[0<x<1]+2*[1<x<2])*λ[x]","ℝ","-1"),
	Case("StepPartialParameter","λ(a:ℝ).∫dx ([0≤x≤1]*a+[2≤x≤3]*(1/a))*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). a+a⁻¹"),
	Case("StepTwoParameters","λ(a:ℝ).λ(b:ℝ).∫dx ([0<x<1]*a+[1<x<2]*b)*λ[x]","ℝ→ℝ→ℝ"),
	Case("StepBoundaryParameter","λ(a:ℝ).∫dx ([0<x<1]+[1<x<2]+[x=1]*(1/a))*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (2:ℝ)"),
	Case("StepProduct","∫dx ([0<x<1]+[1<x<3])*λ[x]*[0≤x≤2]","ℝ","2"),
	Case("StepUnbounded","∫dx [x<0∨1<x]*λ[x]","ℝ"),
	Case("StepNonconstant","∫dx x*[0≤x≤1]*λ[x]","ℝ","1/2"),
	Case("PolynomialMoment","∫dx [0≤x≤1]*x^2*λ[x]","ℝ","1/3"),
	Case("PolynomialQuadratic","∫dx [0≤x≤2]*(x^2+3*x+1)*λ[x]","ℝ","32/3"),
	Case("PolynomialVariance","∫dx ([0≤x≤1]*λ[x])*(x-1/2)^2","ℝ","1/12"),
	Case("PolynomialTriangle","∫dx [0≤x≤2]*([x≤1]*x+[1<x]*(2-x))*λ[x]","ℝ","1"),
	Case("PolynomialBeta","∫dx [0≤x≤1]*x^2*(1-x)^3*λ[x]","ℝ","1/60"),
	Case("PolynomialOdd","∫dx [-1≤x≤1]*x^3*λ[x]","ℝ","0"),
	Case("PolynomialRationalCuts","∫dx [1/3≤x≤1/2]*x*λ[x]","ℝ","5/72"),
	Case("PolynomialOpenCell","∫dx [0<x<1]*[x≠1/2]*x*λ[x]","ℝ","1/2"),
	Case("PolynomialTwoIntervals","∫dx ([0≤x≤1]+[2≤x≤3])*x*λ[x]","ℝ","3"),
	Case("PolynomialMixedMean","∫dx (1/2*δ(0)[x]+1/2*[0≤x≤1]*λ[x])*x","ℝ","1/4"),
	Case("PolynomialMixedMoment","∫dx (1/3*δ(1)[x]+2/3*[0≤x≤3]*(1/3)*λ[x])*x^2","ℝ","7/3"),
	Case("PolynomialAbsolute","∫dx [-1≤x≤1]*abs(x)*λ[x]","ℝ","1"),
	Case("PolynomialAbsoluteShifted","∫dx [-1≤x≤2]*abs(x-1)*x*λ[x]","ℝ","1/6"),
	Case("PolynomialAbsoluteTurning","∫dx [-2≤x≤2]·λ[x³-3*x]","ℝ","12"),
	Case("PolynomialAbsoluteRoots","∫dx [-1≤x≤1]*abs(6*x^2+x-1)*λ[x]","ℝ","341/108"),
	Case("RepeatedAbsoluteRoot","∫dx [-2≤x≤2]*abs((x-1)^2*(x+1))*λ[x]","ℝ","35/6"),
	Case("UnsplitAbsolute","∫dx [-2≤x≤2]*abs(x^2-2)*λ[x]","ℝ"),
	Case("PolynomialAbsoluteScaled","∫dx [0≤x≤1]*abs(2*x-1)*λ[x]","ℝ","1/2"),
	Case("PolynomialAbsoluteCube","∫dx [-1≤x≤1]*abs(x)^3*λ[x]","ℝ","1/2"),
	Case("PolynomialAbsoluteCoordinate","∫dx [-1≤x≤1]·x²·λ[x²]","ℝ","1"),
	Case("PolynomialAbsoluteMixture","∫dx (1/2*δ(0)[x]+1/2*[-1≤x≤1]*(1/2)*λ[x])*abs(x)","ℝ","1/4"),
	Case("PolynomialAbsoluteNested","∫dx [-2≤x≤2]*abs(abs(x)-1)*λ[x]","ℝ"),
	Case("PolynomialUnbounded","∫dx [0≤x]*x*λ[x]","ℝ"),
	Case("PolynomialEverywhere","∫dx x^2*λ[x]","ℝ"),
	Case("SymbolicIntervalLength","∫dx [a≤x]*[x≤b]*λ[x]","ℝ","[a≤b]·(-a+b)"),
	Case("SymbolicIntervalSwapped","∫dx [x≤b]*[a≤x]*λ[x]","ℝ","[a≤b]·(b-a)"),
	Case("SymbolicIntervalHalf","∫dx [0≤x]*[x≤a]*λ[x]","ℝ","[0≤a]·a"),
	Case("SymbolicIntervalStrict","∫dx c*[a<x]*[x<b]*x*λ[x]","ℝ","[a<b]·(c·(-1/2·a^2+1/2·b^2))"),
	Case("SymbolicIntervalMoment","∫dx [a≤x]*[x≤b]*x^2*λ[x]","ℝ","[a≤b]·(-1/3·a^3+1/3·b^3)"),
	Case("SymbolicIntervalMean","∫dx ([a≤x]*[x≤b]*λ[x])*x","ℝ","[a≤b]·(-1/2·a^2+1/2·b^2)"),
	Case("SymbolicIntervalScaledMoment","∫dx ([a≤x]*[x≤b]*c*λ[x])*x^2","ℝ","[a≤b]·(c·(-1/3·a^3+1/3·b^3))"),
	Case("SymbolicIntervalCoefficients","∫dx [a≤x≤b]*(x^2+c*x+d)*λ[x]","ℝ","[a≤b]·(-1/3·a^3+1/3·b^3+c·(-1/2·a^2+1/2·b^2)+d·(-a+b))"),
	Case("SymbolicIntervalParameter","∫dx [0≤x≤1]*(x+y)*λ[x]","ℝ","y+1/2"),
	Case("SymbolicIntervalPartialScale","∫dx [a≤x≤b]*(1/c)*λ[x]","ℝ","[a≤b]·((-a+b)·c⁻¹)"),
	Case("SymbolicIntervalBoundCoefficient","λ(a:ℝ).∫dx [0≤x≤1]*(x+a)*λ[x]","ℝ→ℝ","λ(a:ℝ). a+1/2"),
	Case("SymbolicIntervalBoundVariable","λ(a:ℝ).∫dx [0≤x]*[x≤a]*x*λ[x]","ℝ→ℝ","λ(a:ℝ). [0≤a]·(1/2·a^2)"),
	Case("SymbolicIntervalTwoBinders","λ(a:ℝ).λ(b:ℝ).∫dx [a<x]*[x≤b]*λ[x]","ℝ→ℝ→ℝ","λ(a:ℝ). λ(b:ℝ). [a<b]·(-a+b)"),
	Case("SymbolicIntervalNested","∫dx [0≤x≤1]*λ[x]*∫dy [0≤y]*[y≤x]*λ[y]","ℝ","1/2"),
	Case("SymbolicIntervalNestedMoment","∫dx [0≤x≤1]*λ[x]*∫dy [0≤y]*[y≤x]*y*λ[y]","ℝ","1/6"),
	Case("SymbolicIntervalNestedSum","∫dx [0≤x≤2]*λ[x]*∫dy [x≤y]*[y≤2]*(x+y)*λ[y]","ℝ","4"),
	Case("SymbolicIntervalSimplex","∫dx [0≤x≤1]*λ[x]*∫dy [0≤y]*[y≤1-x]*λ[y]","ℝ","1/2"),
	Case("SymbolicIntervalDensity","Λ(x:ℝ). (∫dy [0≤y]*[y≤x]*λ[y])*[0≤x≤1]*λ[x]","Distribution(ℝ)","Λ(x:ℝ). ([0≤x∧x≤1]·x)·λ[x]"),
	Case("GuardedIntervalParameter","∫dx [c≤d]*[a≤x]*[x≤b]*x*λ[x]","ℝ","[c≤d∧a≤b]·(-1/2·a^2+1/2·b^2)"),
	Case("GuardedIntervalBracket","∫dx [c≤d]*[a≤x]*[x≤b]*λ[x]","ℝ","[c≤d∧a≤b]·(-a+b)"),
	Case("GuardedPolynomial","∫dx [c≤d]*[0≤x≤1]*x*λ[x]","ℝ","[c≤d]·(1/2)"),
	Case("GuardedBoundVariable","λ(c:ℝ). ∫dx [0≤c]*[0≤x]*[x≤c]*x*λ[x]","ℝ→ℝ","λ(c:ℝ). [0≤c]·(1/2·c^2)"),
	Case("GuardedJointTriangle","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤x]*λ[x]*λ[y]","ℝ","1/2"),
	Case("GuardedJointMoment","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤x]*x*y*λ[x]*λ[y]","ℝ","1/8"),
	Case("GuardedSine","∫dx [c≤d]*sin(x)*[0≤x≤1]*λ[x]","ℝ","[c≤d]·(-cos(1)+1)"),
	Case("GuardedUnobserved","∫dx [c≤d]*sin(x²)*[0≤x≤1]*λ[x]","ℝ"),
	Case("ExponentialGuarded","∫dx [c≤d]*e^x*[0≤x≤1]*λ[x]","ℝ","[c≤d]·(e-1)"),
	Case("ExponentialInterval","∫dx [0≤x≤1]*exp(2*x)*λ[x]","ℝ","1/2·exp(2)-1/2"),
	Case("ExponentialSymbolicBounds","∫dx [a≤x≤b]*exp(-x)*λ[x]","ℝ","[a≤b]·(exp(-a)-exp(-b))"),
	Case("ExponentialMoment","∫dx [0≤x≤1]*x^3*exp(-2*x)*λ[x]","ℝ","-19/8·exp(-2)+3/8"),
	Case("ExponentialScaled","∫dx [a≤x≤b]*c*exp(3*x)*x*λ[x]","ℝ","[a≤b]·(c·(-(a·(1/3)-1/9)·exp(3·a)+(b·(1/3)-1/9)·exp(3·b)))"),
	Case("ExponentialWeight","∫dx ([a≤x≤b]*c*λ[x])*x*exp(x)","ℝ","[a≤b]·(c·(-(a-1)·exp(a)+(b-1)·exp(b)))"),
	Case("ExponentialSum","∫dx [0≤x≤1]*(c*exp(x)+d*x)*λ[x]","ℝ","c·(e-1)+d·(1/2)"),
	Case("ExponentialTwoScales","∫dx [a≤x≤b]*c*x*d*λ[x]","ℝ","[a≤b]·(c·d·(-1/2·a^2+1/2·b^2))"),
	Case("ExponentialCdf","λ(a:ℝ).∫dx [0≤x]*[x≤a]*2*exp(-2*x)*λ[x]","ℝ→ℝ","λ(a:ℝ). [0≤a]·(-exp(-2·a)+1)"),
	Case("ExponentialNested","∫dx [0≤x≤2]*λ[x]*∫dy [0≤y]*[y≤x]*exp(-y)*λ[y]","ℝ","exp(-2)+1"),
	Case("HalfLineExponential","∫dx [0≤x]*exp(-x)*λ[x]","ℝ","1"),
	Case("HalfLineGamma","∫dx [0≤x]*x^3*exp(-2*x)*λ[x]","ℝ","3/8"),
	Case("HalfLineSymbolicBound","∫dx [a≤x]*exp(-x)*λ[x]","ℝ","exp(-a)"),
	Case("HalfLineStrictScaled","∫dx [a<x]*c*exp(-3*x)*x*λ[x]","ℝ","-c·(-a·(1/3)-1/9)·exp(-3·a)"),
	Case("HalfLineLawMean","∫dx ([0≤x]*2*exp(-2*x)*λ[x])*x","ℝ","1/2"),
	Case("HalfLineLawMoment","∫dx ([0≤x]*2*exp(-2*x)*λ[x])*x^2","ℝ","1/2"),
	Case("HalfLineBracketWeight","∫dx ([0≤x]*λ[x])*exp(-x)","ℝ","1"),
	Case("HalfLineSum","∫dx [0≤x]*(exp(-x)+exp(-2*x))*λ[x]","ℝ","3/2"),
	Case("HalfLineBoundVariable","λ(a:ℝ).∫dx [a≤x]*exp(-x)*λ[x]","ℝ→ℝ","λ(a:ℝ). exp(-a)"),
	Case("HalfLineGuarded","∫dx [c≤d]*[0≤x]*exp(-x)*λ[x]","ℝ","[c≤d]"),
	Case("HalfLineNested","∫dx [0≤x]*λ[x]*exp(-x)*∫dy [0≤y]*[y≤x]*λ[y]","ℝ","1"),
	Case("HalfLineGrowing","∫dx [0≤x]*exp(x)*λ[x]","ℝ"),
	Case("UpperExponential","∫dx [x≤0]*exp(x)*λ[x]","ℝ","1"),
	Case("UpperSymbolicBound","∫dx [x≤a]*exp(x)*λ[x]","ℝ","exp(a)"),
	Case("UpperStrictScaled","∫dx [x<a]*c*exp(3*x)*x*λ[x]","ℝ","c·(a·(1/3)-1/9)·exp(3·a)"),
	Case("UpperSum","∫dx [x≤0]*(exp(x)+exp(2*x))*λ[x]","ℝ","3/2"),
	Case("UpperOffset","∫dx [x≤0]*exp(a+x)*λ[x]","ℝ","exp(a)"),
	Case("UpperDomain","∫dx [x≤0]*exp(x)/a*λ[x]","ℝ","guard(a≠0,a⁻¹)"),
	Case("UpperGuarded","∫dx [c≤d]*[x≤0]*exp(x)*λ[x]","ℝ","[c≤d]"),
	Case("UpperBoundVariable","λ(a:ℝ).∫dx [x≤a]*exp(x)*λ[x]","ℝ→ℝ","λ(a:ℝ). exp(a)"),
	Case("UpperLawMean","∫dx ([x≤0]*exp(x)*λ[x])*x","ℝ","-1"),
	Case("UpperCurve","∫dx [x≤0]*x*exp(-x^2)*λ[x]","ℝ","-1/2"),
	Case("UpperCurveBound","∫dx [x≤a]*x*exp(-x^2)*λ[x]","ℝ","-1/2·exp(-a^2)"),
	Case("UpperCurveCubic","∫dx [x≤0]*x^2*exp(x^3)*λ[x]","ℝ","1/3"),
	Case("UpperCurveScaled","∫dx [x≤0]*x*exp(b-x^2)*c*λ[x]","ℝ","-c·(1/2)·exp(b)"),
	Case("UpperGrowing","∫dx [x≤0]*exp(-x)*λ[x]","ℝ"),
	Case("UpperCurveGrowing","∫dx [x≤0]*x*exp(x^2)*λ[x]","ℝ"),
	Case("UpperBracket","∫dx [x≤0]*λ[x]","ℝ"),
	Case("ScalarAsymptoteLogisticLower","lim[x→-∞] (1+exp(-x))⁻¹","ℝ","0"),
	Case("ScalarAsymptoteLogisticUpper","lim[x→∞] (exp(x)+1)⁻¹","ℝ","0"),
	Case("ScalarAsymptoteLogisticRegular","lim[x→∞] (1+exp(-x))⁻¹","ℝ","1"),
	Case("ScalarAsymptoteAtanPlus","lim[x→∞] atan(x)","ℝ","1/2·π"),
	Case("ScalarAsymptoteAtanMinus","lim[x→-∞] atan(x)","ℝ","-1/2·π"),
	Case("ScalarAsymptoteAtanCubic","lim[x→-∞] atan(3*x-x^3)","ℝ","1/2·π"),
	Case("ScalarAsymptoteAtanQuartic","lim[x→-∞] atan(7-x^4)","ℝ","-1/2·π"),
	Case("ScalarAsymptoteAtanExp","lim[x→∞] atan(exp(x))","ℝ","1/2·π"),
	Case("ScalarAsymptoteAtanExpSigned","lim[x→∞] atan(-2*exp(x)+7)","ℝ","-1/2·π"),
	Case("ScalarAsymptoteTwoGrowing","lim[x→∞] atan(x²+exp(x))","ℝ","1/2·π"),
	Case("ScalarAsymptoteTanhPositive","lim[x→∞] tanh(x)","ℝ","1"),
	Case("ScalarAsymptoteTanhNegative","lim[x→-∞] tanh(x)","ℝ","-1"),
	Case("ScalarAsymptoteTanhNested","lim[x→∞] tanh(-2*exp(x))","ℝ","-1"),
	Case("ScalarAsymptoteTanhWeighted","lim[x→-∞] 7*tanh(x)^2","ℝ","7"),
	Case("ScalarAsymptotePoleAway","lim[x→∞] (exp(x)-2)⁻¹","ℝ","0"),
	Case("ScalarAsymptoteGaussianEdge","lim[x→-∞] (exp(x^2)+3)⁻¹","ℝ","0"),
	Case("ScalarAsymptoteOuter","lim[x→-∞] exp(atan(x))","ℝ","exp(-1/2·π)"),
	Case("ScalarAsymptoteOpposite","lim[x→∞] atan(exp(x)-x^2)","ℝ","lim[x→∞] atan(-x^2+exp(x))"),
	Case("ScalarAsymptoteOscillation","lim[x→∞] tanh(sin(x))","ℝ","lim[x→∞] tanh(sin(x))"),
	Case("ScalarAsymptoteOpaque","λ(h:ℝ→ℝ).lim[x→∞] atan(h(x))","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). lim[x→∞] atan(h(x))"),
	Case("ScalarAsymptoteMissing","defined(lim[x→∞] atan(undefined(ℝ)))","𝔹","false"),
	Case("LimitDecay","lim[x→∞] exp(-x)*x^2","ℝ","0"),
	Case("LimitBottom","lim[x→-∞] x^3*exp(x/2)","ℝ","0"),
	Case("LimitConstant","lim[x→∞] 1/a","ℝ","a⁻¹"),
	Case("LimitParameter","lim[t→∞] a*exp(-t)+b","ℝ","b"),
	Case("LimitScale","lim[x→∞] a*x*exp(-x)*b","ℝ","0"),
	Case("LimitPartialScale","λ(a:ℝ). lim[x→∞] exp(-x)/a","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("LimitProduct","lim[x→∞] (a+exp(-x))*(b+x*exp(-2*x))","ℝ","a·b"),
	Case("LimitPower","lim[x→-∞] (exp(x)+c)^2+1","ℝ","c^2+1"),
	Case("LimitBinder","λ(y:ℝ). lim[x→∞] y*exp(-x)","ℝ→ℝ","λ(y:ℝ). (0:ℝ)"),
	Case("LimitNested","lim[x→∞] lim[y→-∞] exp(-x)*exp(y)+x*exp(-x)","ℝ","0"),
	Case("LimitBracket","lim[x→∞] [3≤x]*5","ℝ","5"),
	Case("LimitBracketBottom","lim[x→-∞] [x≤3]","ℝ","1"),
	Case("LimitBracketAffine","lim[x→∞] [2*x+1≤x+5]+[x≠7]","ℝ","1"),
	Case("LimitBracketBounds","lim[x→∞] [a≤x]*[x≤b]","ℝ","0"),
	Case("LimitBracketPartialBound","λ(a:ℝ). lim[x→∞] [1/a≤x]","ℝ→ℝ"),
	Case("LimitConditional","lim[x→∞] (if x≤3 then 1 else 2)","ℝ","2"),
	Case("LimitMask","lim[t→∞] [0≤t]*(1-exp(-t))","ℝ","1"),
	Case("LimitIntegral","lim[t→∞] ∫dx [0≤x≤t]*exp(-x)*λ[x]","ℝ","1"),
	Case("LimitIntegralBound","lim[t→∞] ∫dx [a≤x≤t]*exp(-x)*λ[x]","ℝ","exp(-a)"),
	Case("LimitIntegralBottom","lim[t→-∞] ∫dx [t≤x≤0]*exp(x)*λ[x]","ℝ","1"),
	Case("LimitIntegralMoment","lim[t→∞] ∫dx [0≤x≤t]*x*exp(-x)*λ[x]","ℝ","1"),
	Case("LimitGuardOscillating","lim[x→∞] [sin(x)≤2]","ℝ"),
	Case("LimitHiddenGrowth","lim[x→∞] [x≤0]*exp(x)","ℝ","0"),
	Case("LimitHiddenGrowthBottom","lim[x→-∞] [0≤x≤1]*exp(-x)","ℝ","0"),
	Case("LimitHiddenGrowthBound","lim[x→∞] [x≤a]*exp(x)/b","ℝ","0"),
	Case("LimitHiddenOscillation","lim[x→∞] [x≤0]*sin(x)","ℝ","0"),
	Case("LimitTwoSided","lim[x→∞] [x≤0]*exp(x)/2+[0≤x]*exp(-x)/2","ℝ","0"),
	Case("LimitTwoSidedBottom","lim[x→-∞] [x≤0]*exp(x)/2+[0≤x]*exp(-x)/2","ℝ","0"),
	Case("LimitConditionalDecay","lim[x→∞] (if x<0 then exp(x) else exp(-x))","ℝ","0"),
	Case("LimitAbsolute","lim[x→∞] |x|*exp(-x)","ℝ","0"),
	Case("LimitAbsoluteBottom","lim[x→-∞] a*|x-1|*exp(x)","ℝ","0"),
	Case("LimitPiecewiseFactor","lim[x→∞] ([x≤0]+[1≤x])*x*exp(-x)*c","ℝ","0"),
	Case("LimitPiecewiseZero","lim[x→∞] ([x≤0]+[x≤1])*exp(x)","ℝ","0"),
	Case("LimitPiecewiseGrowing","lim[x→∞] ([x≤0]+[1≤x])*exp(x)","ℝ"),
	Case("LimitVisibleGrowth","lim[x→∞] [0≤x]*x^2","ℝ"),
	Case("LimitLogistic","lim[x→∞] 1/(1+exp(-x))","ℝ","1"),
	Case("LimitReciprocal","lim[x→∞] 3/(2+exp(-x))","ℝ","3/2"),
	Case("LimitReciprocalStep","lim[x→∞] 1/(2-[0≤x])","ℝ","1"),
	Case("LimitReciprocalZero","lim[x→∞] 1/(1-[0≤x])","ℝ","0⁻¹"),
	Case("LimitReciprocalParameter","lim[x→∞] 1/(a+exp(-x))","ℝ"),
	Case("LimitContinuous","lim[x→∞] cos(exp(-x))+sin(x*exp(-x))","ℝ","1"),
	Case("LimitContinuousNested","lim[x→∞] exp(exp(-x))","ℝ","1"),
	Case("LimitContinuousAbsolute","lim[x→∞] |exp(-x)-2|","ℝ","2"),
	Case("LimitContinuousComplex","lim[x→∞] exp(ⅈ*exp(-x))","ℂ","1"),
	Case("LimitInterior","lim[x→∞] log(1+exp(-x))","ℝ","0"),
	Case("LimitInteriorRoot","lim[x→∞] sqrt(4+exp(-x))","ℝ","2"),
	Case("LimitInteriorArc","lim[x→∞] asin(exp(-x))","ℝ","0"),
	Case("LimitInteriorBoundary","lim[x→∞] acos(1+exp(-x))","ℝ"),
	Case("LimitStrictGuard","lim[x→∞] log(2*x)-log(x)","ℝ","log(2)"),
	Case("LimitStrictGuardUndefined","lim[x→-∞] log(2*x)-log(x)","ℝ","undefined(ℝ)"),
	Case("LimitStrictGuardDecay","lim[x→∞] exp(-x)+log(x)-log(x)","ℝ","0"),
	Case("LimitQuotientReciprocal","lim[x→∞] 1/x","ℝ","0"),
	Case("LimitQuotientDegrees","lim[x→∞] (2*x+1)/(x+3)","ℝ","2"),
	Case("LimitQuotientBottom","lim[x→-∞] (x^3-x)/(1-2*x^3)","ℝ","-1/2"),
	Case("LimitQuotientSmaller","lim[x→∞] x/(x^2+1)","ℝ","0"),
	Case("LimitQuotientSum","lim[x→∞] 1/x+1/x^2+y","ℝ","y"),
	Case("LimitQuotientScale","lim[x→∞] a/x","ℝ","0"),
	Case("LimitQuotientPower","lim[x→-∞] 3*x/(1+x^2)^2","ℝ","0"),
	Case("LimitQuotientInside","lim[x→∞] exp(1/x)+cos(1/x)","ℝ","2"),
	Case("LimitQuotientDecay","lim[x→∞] exp(-x)/(1+x^2)","ℝ","0"),
	Case("LimitQuotientLarger","lim[x→∞] x^3/(x^2+1)","ℝ"),
	Case("LimitQuotientParameter","lim[x→∞] (a*x+1)/x","ℝ"),
	Case("LimitGaussian","lim[x→∞] exp(-x^2/2)/sqrt(2*π)","ℝ","0"),
	Case("LimitGaussianMoment","lim[x→-∞] x^3*exp(-x^2/2)","ℝ","0"),
	Case("LimitGaussianShifted","lim[x→∞] a*exp(-(x-1)^2)","ℝ","0"),
	Case("LimitGaussianTilted","lim[x→∞] exp(-x^2)*exp(3*x)","ℝ","0"),
	Case("LimitGaussianPiecewise","lim[x→∞] |x|*exp(-x^2)","ℝ","0"),
	Case("LimitExponentShifted","lim[x→∞] exp(1-x)","ℝ","0"),
	Case("LimitExponentShiftedBottom","lim[x→-∞] exp(x+5)*x","ℝ","0"),
	Case("LimitExponentCubic","lim[x→-∞] exp(x^3)","ℝ","0"),
	Case("LimitExponentCubicGrowing","lim[x→∞] exp(x^3)","ℝ"),
	Case("LimitGaussianSymbolic","lim[x→∞] exp(-(x-m)^2)","ℝ","0"),
	Case("LimitGaussianSymbolicMoment","lim[x→-∞] x*exp(-(x-m)^2+a)","ℝ","0"),
	Case("LimitGaussianSymbolicScaled","lim[x→∞] c*x^3*exp(-x^2+b*x)","ℝ","0"),
	Case("LimitGaussianSymbolicSum","lim[x→∞] (1+exp(-(x-m)^2))*b","ℝ","b"),
	Case("LimitGaussianSymbolicPartial","λ(a:ℝ). lim[x→∞] exp(-(x-1/a)^2)","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("LimitGaussianSymbolicCurvature","lim[x→∞] exp(-a*x^2)","ℝ"),
	Case("LimitGaussianSymbolicGrowing","lim[x→∞] exp((x-m)^2)","ℝ"),
	Case("LimitGrowing","lim[x→∞] exp(x)","ℝ"),
	Case("LimitPolynomial","lim[x→∞] x^2","ℝ"),
	Case("LimitWrongEnd","lim[x→-∞] exp(-x)","ℝ"),
	Case("LimitOscillating","lim[x→∞] sin(x)","ℝ"),
	Case("LimitComplex","lim[x→∞] ⅈ*exp(-x)","ℂ","0"),
	Case("GaussianMass","∫dx exp(-x^2)*λ[x]","ℝ","sqrt(π)"),
	Case("GaussianNormal","∫dx exp(-x^2/2)/sqrt(2*π)*λ[x]","ℝ","1"),
	Case("GaussianVariance","∫dx x^2*exp(-x^2/2)/sqrt(2*π)*λ[x]","ℝ","1"),
	Case("GaussianOdd","∫dx x*exp(-x^2/2)*λ[x]","ℝ","0"),
	Case("GaussianMean","∫dx x*exp(-(x-3)^2/8)/sqrt(8*π)*λ[x]","ℝ","3"),
	Case("GaussianFourth","∫dx x^4*exp(-x^2)*λ[x]","ℝ","3/4·sqrt(π)"),
	Case("GaussianTilted","∫dx exp(-x^2)*exp(2*x)*λ[x]","ℝ","sqrt(π)·e"),
	Case("GaussianCentral","∫dx (x-1)^2*exp(-(x-1)^2/2)/sqrt(2*π)*λ[x]","ℝ","1"),
	Case("GaussianScaled","∫dx a*exp(-x^2)*λ[x]","ℝ","a·sqrt(π)"),
	Case("GaussianGuarded","∫dx [c≤d]*exp(-x^2)*λ[x]","ℝ","[c≤d]·sqrt(π)"),
	Case("GaussianPartialScale","λ(a:ℝ). ∫dx exp(-x^2)/a*λ[x]","ℝ→ℝ"),
	Case("GaussianTwoWeights","∫dx exp(-x^2)*λ[x]*x^2","ℝ","1/2·sqrt(π)"),
	Case("GaussianGrowing","∫dx exp(x^2)*λ[x]","ℝ"),
	Case("GaussianQuartic","∫dx exp(-x^4)*λ[x]","ℝ"),
	Case("VertexHalfLine","∫dx [0≤x]*exp(-x^2)*λ[x]","ℝ","1/2·sqrt(π)"),
	Case("VertexEven","∫dx [0≤x]*x^2*exp(-x^2)*λ[x]","ℝ","1/4·sqrt(π)"),
	Case("VertexFourth","∫dx [0≤x]*x^4*exp(-x^2/2)*λ[x]","ℝ","3/2·sqrt(2·π)"),
	Case("VertexShifted","∫dx [1≤x]*exp(-(x-1)^2)*λ[x]","ℝ","1/2·sqrt(π)"),
	Case("VertexTilted","∫dx [1/2≤x]*exp(x-x^2)*λ[x]","ℝ","1/2·sqrt(π)·exp(1/4)"),
	Case("VertexMixed","∫dx [0≤x]*(1+x)*exp(-(x^2))*λ[x]","ℝ","1/2·sqrt(π)+1/2"),
	Case("VertexUpper","∫dx [x≤0]*exp(-x^2)*λ[x]","ℝ","1/2·sqrt(π)"),
	Case("VertexUpperPolynomial","∫dx [x≤0]*(x+1)^2*exp(-x^2)*λ[x]","ℝ","3/4·sqrt(π)-1"),
	Case("VertexScaled","∫dx [0≤x]*c*exp(-x^2/2)*λ[x]","ℝ","c·(1/2)·sqrt(2·π)"),
	Case("VertexOffset","∫dx [0≤x]*exp(a-x^2)*λ[x]","ℝ","1/2·sqrt(π)·exp(a)"),
	Case("VertexSum","∫dx [0≤x]*(exp(-x^2)+exp(-x))*λ[x]","ℝ","1/2·sqrt(π)+1"),
	Case("VertexDomain","∫dx [0≤x]*exp(-x^2)/a*λ[x]","ℝ","guard(a≠0,a⁻¹·(1/2)·sqrt(π))"),
	Case("VertexNormal","∫dx [0≤x]*exp(-x^2)/sqrt(π)*2*λ[x]","ℝ","1"),
	Case("ErfInterval","∫dx [0≤x≤1]*exp(-x^2)*λ[x]","ℝ","1/2·sqrt(π)·erf(1)"),
	Case("ErfAbove","∫dx [1≤x]*exp(-x^2)*λ[x]","ℝ","1/2·sqrt(π)·erfc(1)"),
	Case("ErfBelow","∫dx [x≤1]*exp(-x^2)*λ[x]","ℝ","1/2·sqrt(π)·erfc(-1)"),
	Case("ErfSymbolicBounds","∫dx [a≤x≤b]*exp(-x^2/2)*λ[x]","ℝ","[a≤b]·(-1/2·sqrt(2·π)·erf(a·(1/2)·sqrt(2))+1/2·sqrt(2·π)·erf(b·(1/2)·sqrt(2)))"),
	Case("ErfPolynomial","∫dx [0≤x≤1]*x^2*exp(-x^2)*λ[x]","ℝ","1/4·sqrt(π)·erf(1)-1/2·exp(-1)"),
	Case("ErfCubic","∫dx [0≤x≤2]*(x^3+1)*exp(-(x-1)^2)*λ[x]","ℝ","-7/4·sqrt(π)·erf(-1)+7/4·sqrt(π)·erf(1)-3·exp(-1)"),
	Case("ErfNormalTail","∫dx [0≤x]*exp(-(x-1)^2/2)/sqrt(2*π)*λ[x]","ℝ","1/2·erfc(-1/2·sqrt(2))"),
	Case("ErfNormalCdf","λ(t:ℝ).∫dx [x≤t]*exp(-x^2/2)/sqrt(2*π)*λ[x]","ℝ→ℝ","λ(t:ℝ). 1/2·erfc(-t·(1/2)·sqrt(2))"),
	Case("ErfNormalInterval","∫dx [-1≤x≤1]*exp(-x^2/2)/sqrt(2*π)*λ[x]","ℝ","(-1/2·sqrt(2·π)·erf(-1/2·sqrt(2))+1/2·sqrt(2·π)·erf(1/2·sqrt(2)))·sqrt(2·π)⁻¹"),
	Case("ErfScaled","∫dx [0≤x≤1]*c*exp(-x^2)*λ[x]","ℝ","c·(1/2)·sqrt(π)·erf(1)"),
	Case("ErfAboveScaled","∫dx [1≤x]*c*exp(-x^2)*λ[x]","ℝ","c·(1/2)·sqrt(π)·erfc(1)"),
	Case("ErfBelowScaled","∫dx [x≤1]*c*exp(-x^2)*λ[x]","ℝ","c·(1/2)·sqrt(π)·erfc(-1)"),
	Case("ErfOffset","∫dx [0≤x≤1]*exp(a-x^2)*λ[x]","ℝ","1/2·sqrt(π)·exp(a)·erf(1)"),
	Case("ErfBelowPolynomial","∫dx [x≤a]*x*exp(-(x-1)^2)*λ[x]","ℝ","1/2·sqrt(π)·erfc(-a+1)-1/2·exp(a·(-a+2)-1)"),
	Case("ErfDomain","∫dx [0≤x≤1]*exp(-x^2)/a*λ[x]","ℝ","guard(a≠0,a⁻¹·(1/2)·sqrt(π)·erf(1))"),
	Case("ErfSum","∫dx [0≤x≤1]*(exp(-x^2)+exp(-x))*λ[x]","ℝ","1/2·sqrt(π)·erf(1)-exp(-1)+1"),
	Case("ErfVertexSum","∫dx [0≤x]*(exp(-x^2)+exp(-(x-1)^2))*λ[x]","ℝ","1/2·sqrt(π)·erfc(-1)+1/2·sqrt(π)"),
	Case("ErfStrict","∫dx [0<x]*[x<1]*exp(-x^2)*λ[x]","ℝ","1/2·sqrt(π)·erf(1)"),
	Case("ErfNested","λ(t:ℝ).∫dx [0≤x]*[x≤t]*exp(-x^2)*λ[x]","ℝ→ℝ","λ(t:ℝ). [0≤t]·(1/2·sqrt(π)·erf(t))"),
	Case("ErfGuarded","∫dx [c≤d]*[1≤x]*exp(-x^2)*λ[x]","ℝ","[c≤d]·(1/2·sqrt(π)·erfc(1))"),
	Case("ErfGrowing","∫dx [0≤x≤1]*exp(x^2)*λ[x]","ℝ"),
	Case("ErfQuartic","∫dx [0≤x≤1]*exp(-x^4)*λ[x]","ℝ"),
	Case("ErfSymbolicMean","∫dx [0≤x≤1]*exp(-(x-m)^2)*λ[x]","ℝ","1/2·sqrt(π)·erf(-m+1)-1/2·sqrt(π)·erf(-m)"),
	Case("ErfSymbolicCdf","∫dx [x≤t]*exp(-(x-m)^2/2)/sqrt(2*π)*λ[x]","ℝ","1/2·erfc((-t+m)·(1/2)·sqrt(2))"),
	Case("ErfSymbolicTail","∫dx [a≤x]*exp(-(x-m)^2/2)/sqrt(2*π)*λ[x]","ℝ","1/2·erfc((a-m)·(1/2)·sqrt(2))"),
	Case("ErfSymbolicScaled","∫dx [a≤x≤b]*c*exp(m*x-x^2)*λ[x]","ℝ","[a≤b]·(c·(-1/2·sqrt(π)·exp(1/4·m^2)·erf(a-m·(1/2))+1/2·sqrt(π)·exp(1/4·m^2)·erf(b-m·(1/2))))"),
	Case("ErfSymbolicSum","∫dx [0≤x]*(exp(-(x-m)^2)+exp(-x))*λ[x]","ℝ","1/2·sqrt(π)·erfc(-m)+1"),
	Case("ErfSymbolicUndefined","∫dx [x≤t]*exp(-(x-1/m)^2)/c*λ[x]","ℝ","guard(m≠0∧c≠0,c⁻¹·(1/2)·sqrt(π)·erfc(-t+m⁻¹))"),
	Case("ErfSymbolicFunction","λ(t:ℝ).∫dx [x<t]*exp(-(x-m)^2/2)/sqrt(2*π)*λ[x]","ℝ→ℝ","λ(t:ℝ). 1/2·erfc((m-t)·(1/2)·sqrt(2))"),
	Case("ErfSymbolicPolynomial","∫dx [0≤x≤1]*x*exp(-(x-m)^2)*λ[x]","ℝ","m·(1/2·sqrt(π)·erf(-m+1)-1/2·sqrt(π)·erf(-m))-1/2·exp(-m^2+2·m-1)+1/2·exp(-m^2)"),
	Case("ErfSymbolicPositive","∫dx [0≤x]*x*exp(-(x-m)^2/2)/sqrt(2*π)*λ[x]","ℝ","(m·(1/2)·sqrt(2·π)·erfc(-m·(1/2)·sqrt(2))+exp(-1/2·m^2))·sqrt(2·π)⁻¹"),
	Case("ErfSymbolicSecond","∫dx [x≤t]*x^2*exp(-(x-m)^2/2)*λ[x]","ℝ","(m^2+1)·(1/2)·sqrt(2·π)·erfc((-t+m)·(1/2)·sqrt(2))+(-t-m)·exp(-1/2·t^2+t·m-1/2·m^2)"),
	Case("ErfSymbolicQuadratic","∫dx [a≤x≤b]*(x^2+1)*exp(c+m*x-x^2)*λ[x]","ℝ",
		"[a≤b]·(-(-a·(1/2)-m·(1/4))·exp(-a^2+a·m+c)+(-b·(1/2)-m·(1/4))·exp(-b^2+b·m+c)+(1/4·m^2+3/2)·(-1/2·sqrt(π)·exp(1/4·m^2+c)·erf(a-m·(1/2))+1/2·sqrt(π)·exp(1/4·m^2+c)·erf(b-m·(1/2))))"),
	Case("ErfSymbolicDegree","∫dx [0≤x≤1]*x^17*exp(-(x-m)^2)*λ[x]","ℝ"),
	Case("ErfSymbolicCurvature","∫dx [0≤x≤1]*exp(-a*x^2)*λ[x]","ℝ"),
	Case("PiecesLaplace","∫dx ([x≤0]*exp(x)+[0≤x]*exp(-x))*λ[x]","ℝ","2"),
	Case("PiecesShifted","∫dx ([0≤x]*exp(-x)+[1≤x]*exp(-2*x))*λ[x]","ℝ","1/2·exp(-2)+1"),
	Case("PiecesStrict","∫dx ([x≤0]*exp(x)+[0<x]*exp(-x))*λ[x]/2","ℝ","1"),
	Case("PiecesSymbolicBounds","∫dx ([x≤a]*exp(x)+[b≤x]*exp(-x))*λ[x]","ℝ","exp(a)+exp(-b)"),
	Case("PiecesInterval","∫dx ([0≤x≤1]*exp(x)+[1≤x]*exp(-x))*λ[x]","ℝ","2·cosh(1)-1"),
	Case("PiecesPolynomial","∫dx ([0≤x≤1]*x+[2≤x]*exp(-x))*λ[x]","ℝ","exp(-2)+1/2"),
	Case("PiecesVertex","∫dx ([x≤0]*exp(x)+[0≤x]*exp(-x^2))*λ[x]","ℝ","1/2·sqrt(π)+1"),
	Case("PiecesThree","∫dx ([x≤-1]*exp(x)+[-1≤x≤1]+[1≤x]*exp(-x))*λ[x]","ℝ","2·exp(-1)+2"),
	Case("PiecesFour","∫dx (([x≤0]*exp(x)+[0≤x]*exp(-x))+([x≤-1]*exp(2*x)+[1≤x]*exp(-2*x)))*λ[x]","ℝ","exp(-2)+2"),
	Case("PiecesScaled","∫dx ([x≤0]*c*exp(x)+[0≤x]*d*exp(-x))*λ[x]","ℝ","c+d"),
	Case("PiecesMoment","∫dx ([x≤0]*exp(x)*x^2+[0≤x]*exp(-x)*x^2)*λ[x]","ℝ","4"),
	Case("PiecesGuarded","∫dx [c≤d]*([x≤0]*exp(x)+[0≤x]*exp(-x))*λ[x]","ℝ","[c≤d]·2"),
	Case("PiecesNested","λ(t:ℝ).∫dx ([x≤0]*exp(x)+[0≤x]*[x≤t]*exp(-x))*λ[x]","ℝ→ℝ","λ(t:ℝ). [0≤t]·(-exp(-t)+1)+1"),
	Case("PiecesGrowing","∫dx ([x≤0]*exp(x)+[0≤x]*exp(x))*λ[x]","ℝ"),
	Case("PiecesWhole","∫dx ([x≤0]*exp(x)+exp(-x^2))*λ[x]","ℝ"),
	Case("SpreadMoment","∫dx ([x≤0]*exp(x)+[0≤x]*exp(-x))*x^2*λ[x]","ℝ","4"),
	Case("SpreadMean","∫dx ([x≤0]*exp(x)+[0≤x]*exp(-x))*λ[x]*x","ℝ","0"),
	Case("SpreadScaled","∫dx c*([x≤0]*exp(x)+[0≤x]*exp(-x))*λ[x]","ℝ","2·c"),
	Case("SpreadDomain","∫dx ([x≤0]*exp(x)+[0≤x]*exp(-x))/a*λ[x]","ℝ","guard(a≠0,2·a⁻¹)"),
	Case("SpreadRoot","∫dx sqrt(b)*([x≤0]*exp(x)+[0≤x]*exp(-x))*x^2*λ[x]","ℝ","guard(0≤b,4·sqrt(b))"),
	Case("SpreadNested","∫dx x*([x≤0]*exp(x)+[0≤x]*exp(-x))*(x+1)/2*λ[x]","ℝ","2"),
	Case("SpreadSummand","∫dx (([x≤0]*exp(x)+[0≤x]*exp(-x))*x+[1≤x]*exp(-x))*λ[x]","ℝ","exp(-1)"),
	Case("SpreadThree","∫dx ([x≤-1]*exp(x)+[-1≤x≤1]+[1≤x]*exp(-x))*x^2*λ[x]","ℝ","10·exp(-1)+2/3"),
	Case("SpreadGuarded","∫dx [c≤d]*([x≤0]*exp(x)+[0≤x]*exp(-x))*x^2*λ[x]","ℝ","[c≤d]·4"),
	Case("SpreadMask","∫dx [x≤1]*([x≤0]*exp(x)+[0≤x]*exp(-x))*λ[x]","ℝ","-exp(-1)+2"),
	Case("SpreadMaskInterval","∫dx [-1≤x≤1]*([x≤0]*exp(x)+[0≤x]*exp(-x))*λ[x]","ℝ","-2·exp(-1)+2"),
	Case("SpreadMaskPolynomial","∫dx [0≤x]*([x≤1]*x+[1≤x]*exp(1-x))*x*λ[x]","ℝ","7/3"),
	Case("SpreadGrowing","∫dx ([x≤0]*exp(x)+[0≤x]*exp(x))*x^2*λ[x]","ℝ"),
	Case("SpreadGaussian","∫dx ([x≤0]*exp(x)+[0≤x]*exp(-x))*exp(-x^2)*λ[x]","ℝ","sqrt(π)·exp(1/4)·erfc(1/2)"),
	Case("SpreadSymbolicBound","∫dx [x≤t]*([x≤0]*exp(x)+[0≤x]*exp(-x))*λ[x]","ℝ","[0≤t]·(-exp(-t)+1)+[t≤0]·exp(t)+[0<t]"),
	Case("SpreadPower","∫dx ([x≤0]*exp(x)+[0≤x]*exp(-x))^2*λ[x]","ℝ"),
	Case("SpreadAxisDomain","∫dx (([x≤0]*exp(x)+[0≤x]*exp(-x))/a+[1≤x]*exp(-x)*sqrt(b))*λ[x]","ℝ"),
	Case("AbsoluteLaplace","∫dx exp(-abs(x))*λ[x]","ℝ","2"),
	Case("AbsoluteDensity","∫dx exp(-abs(x-1)/2)/4*λ[x]","ℝ","1"),
	Case("AbsoluteSlope","∫dx exp(-abs(2*x-1))*λ[x]","ℝ","1"),
	Case("AbsoluteTwo","∫dx exp(-abs(x-1)-abs(x+1))*λ[x]","ℝ","3·exp(-2)"),
	Case("AbsoluteThree","∫dx exp(-abs(x)-2*abs(x-1)-abs(x-3))*λ[x]","ℝ","-1/4·exp(-7)-1/4·exp(-5)+exp(-3)"),
	Case("AbsoluteMoment","∫dx x^2*exp(-abs(x))/2*λ[x]","ℝ","2"),
	Case("AbsoluteFactor","∫dx abs(x)*exp(-abs(x))*λ[x]","ℝ","2"),
	Case("AbsoluteGaussian","∫dx abs(x)*exp(-x^2)*λ[x]","ℝ","1"),
	Case("AbsoluteNormal","∫dx abs(x)*exp(-x^2/2)/sqrt(2*π)*λ[x]","ℝ","2·sqrt(2·π)⁻¹"),
	Case("AbsoluteErf","∫dx abs(x-1)*exp(-x^2)*λ[x]","ℝ","1/2·sqrt(π)·erfc(-1)-1/2·sqrt(π)·erfc(1)+exp(-1)"),
	Case("AbsoluteProduct","∫dx abs(x)*abs(x-1)*abs(x-2)*exp(-x^2)*λ[x]","ℝ","-3/2·sqrt(π)·erf(1)+3/4·sqrt(π)·erf(2)-3/4·sqrt(π)·erfc(2)+3/4·sqrt(π)+exp(-4)-exp(-1)+3"),
	Case("AbsoluteInterval","∫dx [0≤x≤3]*abs(x-1)*exp(-x)*λ[x]","ℝ","-3·exp(-3)+2·exp(-1)"),
	Case("AbsoluteScaled","∫dx c*exp(-abs(x))*λ[x]","ℝ","2·c"),
	Case("AbsoluteDomain","∫dx exp(-abs(x))/a*λ[x]","ℝ","guard(a≠0,2·a⁻¹)"),
	Case("AbsoluteRoot","∫dx sqrt(b)*abs(x)*exp(-x^2)*λ[x]","ℝ","guard(0≤b,sqrt(b))"),
	Case("AbsoluteGuarded","∫dx [c≤d]*exp(-abs(x))*λ[x]","ℝ","[c≤d]·2"),
	Case("AbsolutePieces","∫dx ([x≤0]*exp(x)+[0≤x]*exp(-x))*abs(x)*λ[x]","ℝ","2"),
	Case("AbsoluteSymbolic","∫dx exp(-abs(x-m))*λ[x]","ℝ","2"),
	Case("AbsoluteSquare","∫dx exp(-abs(x^2-1))*λ[x]","ℝ"),
	Case("AbsoluteGrowing","∫dx abs(x)*λ[x]","ℝ"),
	Case("AbsoluteMany","∫dx exp(-abs(x)-abs(x-1)-abs(x-2)-abs(x-3))*λ[x]","ℝ"),
	Case("AbsoluteTermInterval","∫dx [0≤x]*[x≤1]*abs(x-a)*λ[x]","ℝ","[0≤a∧a≤1]·(-1/2·a^2-a·(-a+1)+1/2)+[0<a]·([1<a]·(a-1/2)+[a≤1]·(1/2·a^2))+[a<0]·(-a+1/2)"),
	Case("AbsoluteTermSlope","∫dx exp(-abs(2*x-a)/3)*λ[x]","ℝ","3"),
	Case("AbsoluteTermSum","∫dx exp(-abs(x-a-b))*λ[x]","ℝ","2"),
	Case("AbsoluteTermFactor","∫dx exp(-abs(x-a))*abs(x-a)*λ[x]","ℝ","2"),
	Case("AbsoluteTermMoment","∫dx exp(-abs(x-a))*x^2*λ[x]","ℝ","a·(a-2)-a·(-a-2)+4"),
	Case("AbsoluteTermProduct","∫dx [0≤x]*[x≤1]*abs(2*x-a)*x*λ[x]","ℝ","[0≤a∧a≤2]·(-1/12·a^3+a·(1/8·a^2-1/2)+2/3)+[0<a]·([2<a]·(a·(1/2)-2/3)+[a≤2]·(1/24·a^3))+[a<0]·(-a·(1/2)+2/3)"),
	Case("AbsoluteTermRate","∫dx [0≤x]*exp(-x)*abs(x-a)*λ[x]","ℝ","[0<a]·(a·(-exp(-a)+1)+(a+1)·exp(-a)-1)+[a<0]·(-a+1)+[0≤a]·(-a·exp(-a)-(-a-1)·exp(-a))"),
	Case("AbsoluteTermGaussian","∫dx exp(-x^2)*abs(x-a)*λ[x]","ℝ","-a·(1/2)·sqrt(π)·erfc(a)+a·(1/2)·sqrt(π)·erfc(-a)+exp(-a^2)"),
	Case("AbsoluteTermCurve","∫dx exp(-abs(x-a)-x^2)*λ[x]","ℝ","1/2·sqrt(π)·exp(a+1/4)·erfc(a+1/2)+1/2·sqrt(π)·exp(-a+1/4)·erfc(-a+1/2)"),
	Case("AbsoluteTermTwo","∫dx exp(-abs(x-a))*exp(-abs(x-b))*λ[x]","ℝ","[a<b]·((-a+b)·exp(a-b)+1/2·exp(a-b))+[b<a]·((a-b)·exp(-a+b)+1/2·exp(-a+b))+[a≤b]·(1/2·exp(a-b))+[b≤a]·(1/2·exp(-a+b))"),
	Case("AbsoluteTermMixed","∫dx exp(-abs(x-a)-abs(x-1))*λ[x]","ℝ","[1<a]·((a-1)·exp(-a+1)+1/2·exp(-a+1))+[a<1]·((-a+1)·exp(a-1)+1/2·exp(a-1))+[1≤a]·(1/2·exp(-a+1))+[a≤1]·(1/2·exp(a-1))"),
	Case("AbsoluteTermScaled","∫dx c*exp(-abs(x-a))*λ[x]","ℝ","2·c"),
	Case("AbsoluteTermDomain","∫dx exp(-abs(x-a))/c*λ[x]","ℝ","guard(c≠0,2·c⁻¹)"),
	Case("AbsoluteTermGuarded","∫dx [c≤d]*exp(-abs(x-a))*λ[x]","ℝ","[c≤d]·2"),
	Case("AbsoluteTermFunction","λ(t:ℝ).∫dx exp(-abs(x-t))*abs(x)*λ[x]","ℝ→ℝ","λ(t:ℝ). [0<t]·(((t-1)·exp(t)+1)·exp(-t)+exp(-t))+[t<0]·((-(t+1)·exp(-t)+1)·exp(t)+exp(t))+[0≤t]·(t+1)+[t≤0]·(-t+1)"),
	Case("AbsoluteTermNested","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*abs(x-y)*λ[x]*λ[y]","ℝ","1/3"),
	Case("AbsoluteTermPartial","∫dx [0≤x]*[x≤1]*abs(x-log(a))*λ[x]","ℝ"),
	Case("AbsoluteTermThree","∫dx exp(-abs(x-a)-abs(x-b)-abs(x-c))*λ[x]","ℝ"),
	Case("AbsoluteTermInner","∫dx [0≤x]*[x≤1]*abs(abs(x-a)-b)*λ[x]","ℝ"),
	Case("AbsoluteTermRateTerm","∫dx exp(-abs(a-x)/b)*λ[x]","ℝ"),
	Case("GaussianSymbolic","∫dx exp(-(x-m)^2)*λ[x]","ℝ","sqrt(π)"),
	Case("GaussianSymbolicOffset","∫dx exp(-x^2+a)*λ[x]","ℝ","sqrt(π)·exp(a)"),
	Case("GaussianSymbolicMean","∫dx x*exp(-(x-m)^2/2)/sqrt(2*π)*λ[x]","ℝ","m"),
	Case("GaussianSymbolicSecond","∫dx x^2*exp(-(x-m)^2/2)*λ[x]","ℝ","(m^2+1)·sqrt(2·π)"),
	Case("GaussianSymbolicCubic","∫dx (x^3+2*x)*exp(-(x-m)^2)*λ[x]","ℝ","(m^3+m·(7/2))·sqrt(π)"),
	Case("GaussianSymbolicTilt","∫dx exp(-x^2+b*x)*λ[x]","ℝ","sqrt(π)·exp(1/4·b^2)"),
	Case("GaussianSymbolicMixed","∫dx exp(a+2*x-x^2)*λ[x]","ℝ","sqrt(π)·exp(a+1)"),
	Case("GaussianSymbolicSlope","∫dx exp(-(2*x-m)^2)*λ[x]","ℝ","sqrt(1/4·π)"),
	Case("GaussianSymbolicProduct","∫dx exp(-(x-a)*(x-b))*λ[x]","ℝ","sqrt(π)·exp(-a·b+1/4·(a+b)^2)"),
	Case("GaussianSymbolicConvolution","∫dx exp(-x^2)*exp(-(y-x)^2)*λ[x]","ℝ","sqrt(1/2·π)·exp(-1/2·y^2)"),
	Case("GaussianSymbolicPosterior","∫dx x*exp(-(x-m)^2/2)*exp(-(y-x)^2/2)/(2*π)*λ[x]","ℝ"),
	Case("GaussianSymbolicNested","∫dy (∫dx exp(-x^2-y^2)*λ[x])*λ[y]","ℝ","π"),
	Case("GaussianSymbolicFunction","λ(m:ℝ). ∫dx exp(-(x-m)^2)*λ[x]","ℝ→ℝ","λ(m:ℝ). sqrt(π)"),
	Case("GaussianSymbolicScaled","∫dx b*x*exp(-(x-m)^2)*a*λ[x]","ℝ","b·m·a·sqrt(π)"),
	Case("GaussianSymbolicGuarded","∫dx [c≤d]*exp(-(x-m)^2)*λ[x]","ℝ","[c≤d]·sqrt(π)"),
	Case("GaussianSymbolicTwoWeights","∫dx exp(-x^2)*λ[x]*exp(a*x)","ℝ","sqrt(π)·exp(1/4·a^2)"),
	Case("GaussianSymbolicPartial","∫dx exp(-x^2+1/a)*λ[x]","ℝ","sqrt(π)·exp(a⁻¹)"),
	Case("Curvature","∫dx exp(a*x^2)*λ[x]","ℝ","sqrt(-a⁻¹·π)"),
	Case("CurvatureVariance","∫dx exp(-(x-m)^2/(2*v))*λ[x]","ℝ","guard(0<v,sqrt(2·v·π))"),
	Case("CurvatureNormal","∫dx exp(-(x-m)^2/(2*v))/sqrt(2*π*v)*λ[x]","ℝ","guard(0<v,(1:ℝ))"),
	Case("CurvatureDeviation","∫dx exp(-(x-m)^2/(2*s^2))/(s*sqrt(2*π))*λ[x]","ℝ","guard(s≠0,s⁻¹·abs(s))"),
	Case("CurvatureFactor","∫dx 2*exp(-a*x^2+b*x)*λ[x]","ℝ","2·sqrt(a⁻¹·π)·exp(a⁻¹·(1/4)·b^2)"),
	Case("CurvatureInverse","∫dx exp(c-a*x^2)/b*λ[x]","ℝ","b⁻¹·sqrt(a⁻¹·π)·exp(c)"),
	Case("CurvatureInverses","∫dx exp(-a*x^2)/(b*c)*λ[x]","ℝ","guard(b≠0∧(c≠0∧0<a),b⁻¹·c⁻¹·sqrt(a⁻¹·π))"),
	Case("CurvatureCircle","∫dx 2*π*exp(-a*x^2)*λ[x]","ℝ","2·sqrt(a⁻¹·π)·π"),
	Case("CurvatureSquare","∫dx exp(-a^2*x^2)*λ[x]","ℝ","sqrt((a^2)⁻¹·π)"),
	Case("CurvatureFunction","λ(v:ℝ).∫dx exp(-x^2/(2*v))*λ[x]","ℝ→ℝ","λ(v:{v:ℝ | 0<v}). sqrt(2·v·π)"),
	Case("CurvatureBound","λ(b:ℝ).∫dx exp(-a*x^2)*π/b*λ[x]","ℝ→ℝ","λ(b:{b:ℝ | b≠0∧0<a}). b⁻¹·sqrt(a⁻¹·π)·π"),
	Case("CurvatureGuarded","∫dx [c≤d]*exp(-a*x^2)*λ[x]","ℝ","[c≤d]·sqrt(a⁻¹·π)"),
	Case("CurvatureScale","∫dx c*exp(-a*x^2)*λ[x]","ℝ","[c≠0]·(c·sqrt(a⁻¹·π))"),
	Case("CurvatureRoot","∫dx sqrt(c)*exp(-a*x^2)*λ[x]","ℝ","guard(c=0∨0<c∧0<a,[c≠0]·sqrt(c·a⁻¹·π))"),
	Case("CurvatureScaleFunction","λ(a:ℝ).∫dx c*exp(-a*x^2)*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | c=0∨0<a}). [c≠0]·(c·sqrt(a⁻¹·π))"),
	Case("CurvatureScaleNormal","∫dx c*exp(-x^2/(2*v))/sqrt(2*π*v)*λ[x]","ℝ","guard(0<v,[c≠0]·c)"),
	Case("CurvaturePolynomial","∫dx x^2*exp(-a*x^2)*λ[x]","ℝ","a⁻¹·(1/2)·sqrt(a⁻¹·π)"),
	Case("CurvatureMean","∫dx x*exp(-(x-m)^2/(2*v))/sqrt(2*π*v)*λ[x]","ℝ","guard(0<v,m)"),
	Case("CurvatureSecond","∫dx x^2*exp(-(x-m)^2/(2*v))/sqrt(2*π*v)*λ[x]","ℝ","guard(0<v,m^2+v)"),
	Case("CurvatureFourth","∫dx x^4*exp(-x^2/(2*v))/sqrt(2*π*v)*λ[x]","ℝ","guard(0<v,3·v^2)"),
	Case("CurvatureOdd","∫dx (x^3+x)*exp(-a*x^2)*λ[x]","ℝ","0"),
	Case("CurvatureMixed","∫dx (1+x^2)*exp(-a*x^2)*λ[x]","ℝ","(1+a⁻¹·(1/2))·sqrt(a⁻¹·π)"),
	Case("CurvatureLinear","∫dx x^2*exp(-a*x^2-b*x)*λ[x]","ℝ","((a^2)⁻¹·(1/4)·b^2+a⁻¹·(1/2))·sqrt(a⁻¹·π)·exp(a⁻¹·(1/4)·b^2)"),
	Case("CurvatureOddFunction","λ(a:ℝ).∫dx (x^3+x)*exp(-a*x^2)*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | 0<a}). (0:ℝ)"),
	Case("CurvatureDegree","∫dx x^17*exp(-a*x^2)*λ[x]","ℝ"),
	Case("CurvatureCentral","∫dx (x-m)^2*exp(-(x-m)^2/(2*v))/sqrt(2*π*v)*λ[x]","ℝ","guard(0<v,v)"),
	Case("CurvatureShifted","∫dx (x-m)^2*exp(-a*x^2)*λ[x]","ℝ","(m^2+a⁻¹·(1/2))·sqrt(a⁻¹·π)"),
	Case("CurvatureClosed","∫dx (a*x+1)^2*exp(-b*x^2)*λ[x]","ℝ","(b⁻¹·(1/2)·a^2+1)·sqrt(b⁻¹·π)"),
	Case("CurvatureForm","∫dx (x/b+π*c)*x*exp(-a*x^2+x)*λ[x]","ℝ","guard(b≠0∧0<a,(c·a⁻¹·(1/2)·π+b⁻¹·a⁻¹·(1/2)+b⁻¹·(a^2)⁻¹·(1/4))·sqrt(a⁻¹·π)·exp(a⁻¹·(1/4)))"),
	Case("CurvatureAbsent","∫dx (x^2+m)*exp(-a*x^2)*λ[x]","ℝ","(m+a⁻¹·(1/2))·sqrt(a⁻¹·π)"),
	Case("CurvatureVanishing","∫dx (c*x)^2*exp(-a*x^2)*λ[x]","ℝ","[c≠0]·(a⁻¹·(1/2)·c^2·sqrt(a⁻¹·π))"),
	Case("CurvatureEither","∫dx (c*x+d)*exp(-a*x^2)*λ[x]","ℝ","[d≠0∨c≠0]·(d·sqrt(a⁻¹·π))"),
	Case("CurvatureSteady","∫dx (c*x+d)*exp(-a*x^2)/b*λ[x]","ℝ","guard(b≠0∧(d=0∧c=0)∨b≠0∧0<a,[d≠0∨c≠0]·(d·b⁻¹·sqrt(a⁻¹·π)))"),
	Case("CurvatureBoth","∫dx b*(c*x+d)*exp(-a*x^2)*λ[x]","ℝ","[b≠0∧d≠0∨b≠0∧c≠0]·(b·d·sqrt(a⁻¹·π))"),
	Case("CurvatureScaleMonic","∫dx b*(x+d)*exp(-a*x^2)*λ[x]","ℝ","[b≠0]·(b·d·sqrt(a⁻¹·π))"),
	Case("CurvatureSkipped","∫dx (1-x/2)*exp(-a*x^2)*λ[x]","ℝ","sqrt(a⁻¹·π)"),
	Case("CurvatureSkippedOdd","∫dx (-x)*exp(-a*x^2)*λ[x]","ℝ","0"),
	Case("CurvatureSkippedTerms","∫dx (b+x)*(1-x/3)*exp(-a*x^2)*λ[x]","ℝ","(b-a⁻¹·(1/6))·sqrt(a⁻¹·π)"),
	Case("GaussianSymbolicLinear","∫dx exp(a*x)*λ[x]","ℝ"),
	Case("GaussianSymbolicPrefactor","∫dx (x-m)^2*exp(-(x-m)^2/2)*λ[x]","ℝ","sqrt(2·π)"),
	Case("GaussianSymbolicPrefactorShift","∫dx (x+a)*exp(-x^2)*λ[x]","ℝ","a·sqrt(π)"),
	Case("GaussianSymbolicPrefactorSquare","∫dx (a*x+b)^2*exp(-x^2)*λ[x]","ℝ","(1/2·a^2+b^2)·sqrt(π)"),
	Case("GaussianSymbolicPrefactorRoots","∫dx (x-m)*(x-n)*exp(-x^2)*λ[x]","ℝ","(m·n+1/2)·sqrt(π)"),
	Case("GaussianSymbolicPrefactorKurtosis","∫dx (x-m)^4*exp(-(x-m)^2/2)/sqrt(2*π)*λ[x]","ℝ","3"),
	Case("GaussianSymbolicPrefactorSkewness","∫dx (x-m)^3*exp(-(x-m)^2/2)*λ[x]","ℝ","0"),
	Case("GaussianSymbolicPrefactorMixed","∫dx x*(x-m)*exp(-(x-m)^2)*λ[x]","ℝ","1/2·sqrt(π)"),
	Case("GaussianSymbolicPrefactorPartial","∫dx (x+1/a)*exp(-x^2)*λ[x]","ℝ","a⁻¹·sqrt(π)"),
	Case("GaussianSymbolicPrefactorTilted","∫dx (c*x^2+d)*exp(-x^2+b*x)*λ[x]","ℝ","(c·(1/4)·b^2+c·(1/2)+d)·sqrt(π)·exp(1/4·b^2)"),
	Case("GaussianSymbolicPrefactorScaled","∫dx (x-m)^2*exp(-(x-n)^2)*a*λ[x]","ℝ","a·(m^2-2·m·n+n^2+1/2)·sqrt(π)"),
	Case("GaussianSymbolicPrefactorProduct","∫dx (x*(x-a)+b)*exp(-x^2)*λ[x]","ℝ","(b+1/2)·sqrt(π)"),
	Case("GaussianSymbolicPrefactorDegree","∫dx (x-m)^17*exp(-x^2)*λ[x]","ℝ"),
	Case("StrictGuardGaussian","∫dx exp(-(x-1/a)^2)*λ[x]*x","ℝ","guard(a≠0,a⁻¹·sqrt(π))"),
	Case("StrictGuardTwo","∫dx x*λ[x]*exp(-(x-1/a)^2)*exp(-x^2+1/b)","ℝ","guard(b≠0∧a≠0,a⁻¹·(1/2)·sqrt(1/2·π)·exp(b⁻¹-(a^2)⁻¹·(1/2)))"),
	Case("StrictGuardSquare","∫dx (x*exp(-x^2+1/b))^2*λ[x]","ℝ","guard(b≠0,1/4·sqrt(1/2·π)·exp(2·b⁻¹))"),
	Case("StrictGuardMasked","∫dx exp(-(x-1/a)^2)*λ[x]*x^2*[c≤d]","ℝ","guard(a≠0,[c≤d]·((1/2+(a^2)⁻¹)·sqrt(π)))"),
	Case("StrictGuardLeft","∫dx λ[x]*exp(-(x-1/b)^2)*x","ℝ","guard(b≠0,b⁻¹·sqrt(π))"),
	Case("StrictGuardPower","∫dx λ[x]*(exp(-(x-1/b)^2)*x)^2","ℝ","guard(b≠0,(1/4+(b^2)⁻¹)·sqrt(1/2·π))"),
	Case("StrictGuardRetained","∫dx exp(-(x-1/a)^4)*λ[x]*x","ℝ","guard(a≠0,∫dx (x·exp(-(x-a⁻¹)^4))·λ[x])"),
	Case("StrictGuardAxis","∫dx (x+1/a)*λ[x]*[0≤x]*[x≤1]","ℝ","guard(a≠0,1/2+a⁻¹)"),
	Case("ExponentialShifted","∫dx [0≤x≤1]*exp(x+1)*λ[x]","ℝ","(e-1)·e"),
	Case("ExponentialOffsetSum","∫dx [0≤x≤1]*exp(2*x+a+b)*λ[x]","ℝ","(1/2·exp(2)-1/2)·exp(a+b)"),
	Case("ExponentialOffsetTerms","∫dx [0≤x≤1]*(x+exp(a+x))*λ[x]","ℝ","(e-1)·exp(a)+1/2"),
	Case("ExponentialOffsetScaled","∫dx [0≤x≤1]*c*exp(x+1)*x*λ[x]","ℝ","c·e"),
	Case("ExponentialOffsetWeight","∫dx [0≤x≤1]*exp(x+1)*λ[x]*exp(x)","ℝ","(1/2·exp(2)-1/2)·e"),
	Case("HalfLineOffset","∫dx [0≤x]*exp(a-x)*λ[x]","ℝ","exp(a)"),
	Case("HalfLineOffsetMoment","∫dx [0≤x]*x*exp(1-2*x)*λ[x]","ℝ","1/4·e"),
	Case("HalfLineOffsetBound","∫dx [a≤x]*exp(b-x)*λ[x]","ℝ","exp(-a+b)"),
	Case("HalfLineOffsetGrowing","∫dx [0≤x]*exp(a+x)*λ[x]","ℝ"),
	Case("CdfNormal","∫dx [x≤t]*exp(-(x-m)^2/(2*v))/sqrt(2*π*v)*λ[x]","ℝ","guard(0<v,1/2·erfc((-t+m)·sqrt(v⁻¹·(1/2))))"),
	Case("CdfTail","∫dx [a≤x]*exp(-x^2/(2*v))*λ[x]","ℝ","guard(0<v,1/2·sqrt(2·v·π)·erfc(a·sqrt(v⁻¹·(1/2))))"),
	Case("CdfDeviation","∫dx [x≤t]*exp(-(x-m)^2/(2*s^2))/(s*sqrt(2*π))*λ[x]","ℝ","guard(s≠0,s⁻¹·(1/2)·abs(s)·erfc((-t+m)·sqrt((s^2)⁻¹·(1/2))))"),
	Case("CdfScale","∫dx [0≤x]*c*exp(-x^2/v)*λ[x]","ℝ","guard(v≠0∧c=0∨0<v,[c≠0]·(c·(1/2)·sqrt(v·π)))"),
	Case("CdfFunction","λ(t:ℝ).∫dx [x≤t]*exp(-(x-m)^2/(2*v))/sqrt(2*π*v)*λ[x]","ℝ→ℝ","λ(t:{t:ℝ | 0<v}). 1/2·erfc((m-t)·sqrt(v⁻¹·(1/2)))"),
	Case("CdfBelowScale","∫dx [x<b]*c*exp(m*x-x^2/v)*λ[x]","ℝ","guard(v≠0∧c=0∨0<v,[c≠0]·(c·(1/2)·sqrt(v·π)·exp(v·(1/4)·m^2)·erfc((m·v·(1/2)-b)·sqrt(v⁻¹))))"),
	Case("CdfVanishing","∫dx [0≤x]*exp(-a*x^2)*λ[x]","ℝ"),
	Case("CdfPolynomial","∫dx [0≤x]*x^2*exp(-x^2/v)*λ[x]","ℝ"),
	Case("RateAbove","∫dx [0≤x]*exp(-r*x)*λ[x]","ℝ","guard(0<r,r⁻¹)"),
	Case("RateDensity","∫dx [0≤x]*r*exp(-r*x)*λ[x]","ℝ","guard(r=0∨0<r,[r≠0])"),
	Case("RateBound","∫dx [a≤x]*exp(-r*x)*λ[x]","ℝ","guard(0<r,r⁻¹·exp(-a·r))"),
	Case("RateBelow","∫dx [x≤b]*exp(r*x+c)*λ[x]","ℝ","guard(0<r,r⁻¹·exp(b·r+c))"),
	Case("RateScale","∫dx [0≤x]*exp(-x/s)/s*λ[x]","ℝ","guard(0<s,(1:ℝ))"),
	Case("RateCircle","∫dx [x≤0]*2*exp(r*x)/π*λ[x]","ℝ","guard(0<r,2·r⁻¹·π⁻¹)"),
	Case("RateSurvival","λ(t:ℝ).∫dx [t<x]*r*exp(-r*x)*λ[x]","ℝ→ℝ","λ(t:{t:ℝ | r=0∨0<r}). [r≠0]·exp(-r·t)"),
	Case("RateBelowMasked","∫dx [x<b]*c*exp(r*x)*λ[x]","ℝ","guard(c=0∨0<r,[c≠0]·(c·r⁻¹·exp(b·r)))"),
	Case("RateSquare","∫dx [0≤x]*exp(-r^2*x)*λ[x]","ℝ","guard(r≠0,(r^2)⁻¹)"),
	Case("RateGuarded","∫dx [c≤d]*[0≤x]*exp(-r*x)*λ[x]","ℝ","[c≤d]·(guard(0<r,r⁻¹))"),
	Case("RatePolynomial","∫dx [0≤x]*x*exp(-r*x)*λ[x]","ℝ","guard(0<r,(r^2)⁻¹)"),
	Case("RateMean","∫dx [0≤x]*x*r*exp(-r*x)*λ[x]","ℝ","guard(r=0∨0<r,[r≠0]·r⁻¹)"),
	Case("RateSecond","∫dx [0≤x]*x^2*r*exp(-r*x)*λ[x]","ℝ","guard(r=0∨0<r,[r≠0]·(2·(r^2)⁻¹))"),
	Case("RateShifted","∫dx [a≤x]*x^2*exp(-r*x)*λ[x]","ℝ","guard(0<r,(r⁻¹·a^2+2·a·(r^2)⁻¹+2·(r^3)⁻¹)·exp(-a·r))"),
	Case("RateClosed","∫dx [1/2<x]*(2*x-1)^2*exp(-r*x)*λ[x]","ℝ","guard(0<r,8·(r^3)⁻¹·exp(-r·(1/2)))"),
	Case("RateFraction","∫dx [0≤x]*(x/2-1/3)*exp(-r*x)*λ[x]","ℝ","guard(0<r,-r⁻¹·(1/3)+(r^2)⁻¹·(1/2))"),
	Case("RateGamma","∫dx [0<x]*x^3*exp(-x/s)*λ[x]","ℝ","guard(0<s,6·s^4)"),
	Case("RateFactorial","∫dx [0≤x]*x^16*exp(-r*x)*λ[x]","ℝ","guard(0<r,20922789888000·(r^17)⁻¹)"),
	Case("RateInverse","∫dx [0≤x]*x^2*exp(-r*x-c)/b*λ[x]","ℝ","guard(b≠0∧0<r,2·b⁻¹·(r^3)⁻¹·exp(-c))"),
	Case("RateBelowPolynomial","∫dx [x≤b]*(x+1)*exp(r*x)*λ[x]","ℝ","guard(0<r,(b·r⁻¹+r⁻¹-(r^2)⁻¹)·exp(b·r))"),
	Case("RateBelowZero","∫dx [x<0]*x*exp(r*x)*λ[x]","ℝ","guard(0<r,-(r^2)⁻¹)"),
	Case("RateBelowMean","∫dx [x≤b]*x*c*exp(r*x)*λ[x]","ℝ","guard(c=0∨0<r,[c≠0]·(c·(b·r⁻¹-(r^2)⁻¹)·exp(b·r)))"),
	Case("RateMeanFunction","λ(t:ℝ).∫dx [t≤x]*x*r*exp(-r*x)*λ[x]","ℝ→ℝ","λ(t:{t:ℝ | r=0∨0<r}). [r≠0]·(r·(t·r⁻¹+(r^2)⁻¹)·exp(-r·t))"),
	Case("RatePolynomialGuarded","∫dx [c≤d]*[1≤x]*x*exp(-r*x)*λ[x]","ℝ","[c≤d]·(guard(0<r,(r⁻¹+(r^2)⁻¹)·exp(-r)))"),
	Case("RateDegree","∫dx [0≤x]*x^17*exp(-r*x)*λ[x]","ℝ"),
	Case("RateTerms","∫dx [0≤x]*(x+m)*exp(-r*x)*λ[x]","ℝ"),
	Case("RateBetween","∫dx [0≤x≤1]*exp(-r*x)*λ[x]","ℝ","[r≠0]·(-r⁻¹·exp(-r)+r⁻¹)+[r=0]"),
	Case("RateBetweenPolynomial","∫dx [0≤x≤1]*x*exp(-r*x)*λ[x]","ℝ","[r≠0]·((-r⁻¹-(r^2)⁻¹)·exp(-r)+(r^2)⁻¹)+[r=0]·(1/2)"),
	Case("RateBetweenBounds","∫dx [a≤x≤b]*exp(r*x)*λ[x]","ℝ","[a≤b]·([r≠0]·(-r⁻¹·exp(a·r)+r⁻¹·exp(b·r))+[r=0]·(-a+b))"),
	Case("RateBetweenScaled","∫dx [a≤x≤b]*x*c*exp(r*x+d)*λ[x]","ℝ",
		"[a≤b]·(c·([r≠0]·(-(a·r⁻¹-(r^2)⁻¹)·exp(a·r+d)+(b·r⁻¹-(r^2)⁻¹)·exp(b·r+d))+[r=0]·((-1/2·a^2+1/2·b^2)·exp(d))))"),
	Case("RateBetweenStrict","∫dx [0<x<t]*r*exp(-r*x)*λ[x]","ℝ","[0<t]·(r·([r≠0]·(-r⁻¹·exp(-t·r)+r⁻¹)+[r=0]·t))"),
	Case("RateBetweenSum","∫dx [0≤x≤1]*(exp(-r*x)+exp(-x))*λ[x]","ℝ","[r≠0]·(-r⁻¹·exp(-r)+r⁻¹)+[r=0]-exp(-1)+1"),
	Case("RateBetweenInverse","∫dx [0≤x≤1]*exp(-x/s)*λ[x]","ℝ","guard(s≠0,-s·exp(-s⁻¹)+s)"),
	Case("RateBetweenCircle","∫dx [0≤x≤1]*x^2*exp(π*x)*λ[x]","ℝ","(π⁻¹-2·(π^2)⁻¹+2·(π^3)⁻¹)·exp(π)-2·(π^3)⁻¹"),
	Case("RateBetweenFunction","λ(t:ℝ).∫dx [0≤x≤t]*r*exp(-r*x)*λ[x]","ℝ→ℝ","λ(t:ℝ). [0≤t]·(r·([r≠0]·(-r⁻¹·exp(-r·t)+r⁻¹)+[r=0]·t))"),
	Case("RateBetweenGuarded","∫dx [c≤d]*[0≤x≤1]*exp(-r*x)*λ[x]","ℝ","[c≤d]·([r≠0]·(-r⁻¹·exp(-r)+r⁻¹)+[r=0])"),
	Case("RateBetweenDegree","∫dx [0≤x≤1]*x^17*exp(-r*x)*λ[x]","ℝ"),
	Case("RateBetweenTerms","∫dx [0≤x≤1]*(x+m)*exp(-r*x)*λ[x]","ℝ","[r≠0]·((-m·r⁻¹-r⁻¹-(r^2)⁻¹)·exp(-r)+m·r⁻¹+(r^2)⁻¹)+[r=0]·(m+1/2)"),
	Case("RateBetweenTermsBounds","∫dx [a≤x≤b]*(c*x^2+d)*exp(r*x)*λ[x]","ℝ",
		"[a≤b]·([r≠0]·(-(c·r⁻¹·a^2-2·a·c·(r^2)⁻¹+d·r⁻¹+2·c·(r^3)⁻¹)·exp(a·r)+(c·r⁻¹·b^2-2·b·c·(r^2)⁻¹+d·r⁻¹+2·c·(r^3)⁻¹)·exp(b·r))+[r=0]·(-c·(1/3)·a^3+c·(1/3)·b^3-a·d+b·d))"),
	Case("RateBetweenTermsScaled","∫dx [0≤x≤1]*(x-m)^2*r*exp(-r*x)*λ[x]","ℝ",
		"r·([r≠0]·((-r⁻¹·m^2+2·m·r⁻¹+2·m·(r^2)⁻¹-r⁻¹-2·(r^2)⁻¹-2·(r^3)⁻¹)·exp(-r)+r⁻¹·m^2-2·m·(r^2)⁻¹+2·(r^3)⁻¹)+[r=0]·(m^2-m+1/3))"),
	Case("RateBetweenTermsProduct","∫dx [0≤x≤t]*(m*x+1)*(x-1)*exp(-x/s)*λ[x]","ℝ",
		"[0≤t]·(guard(s≠0,2·m·s^3-m·s^2+s^2+(-m·s·t^2-2·t·m·s^2-2·m·s^3+t·m·s+m·s^2-t·s-s^2+s)·exp(-t·s⁻¹)-s))"),
	Case("RateBetweenTermsDegree","∫dx [0≤x≤1]*(x^17+m)*exp(-r*x)*λ[x]","ℝ"),
	Case("RateBetweenTermsFactor","∫dx [0≤x≤1]*(x+m)*(exp(-r*x)+1)*λ[x]","ℝ",
		"m·([r≠0]·(-r⁻¹·exp(-r)+r⁻¹)+[r=0])+m+[r≠0]·((-r⁻¹-(r^2)⁻¹)·exp(-r)+(r^2)⁻¹)+[r=0]·(1/2)+1/2"),
	Case("RateSum","∫dx [0≤x]*(exp(-r*x)+exp(-x))*λ[x]","ℝ"),
	Case("LimitOffset","lim[x→∞] exp(a-x)","ℝ","0"),
	Case("LimitOffsetBottom","lim[x→-∞] x*exp(a+b+3*x)","ℝ","0"),
	Case("LimitOffsetGrowing","lim[x→∞] exp(a+x)","ℝ"),
	Case("ExponentialSymbolicRate","∫dx [0≤x≤1]*r*exp(-r*x)*λ[x]","ℝ","r·([r≠0]·(-r⁻¹·exp(-r)+r⁻¹)+[r=0])"),
	Case("CurveHalfLine","∫dx [0≤x]*x*exp(-x^2)*λ[x]","ℝ","1/2"),
	Case("CurveInterval","∫dx [0≤x≤1]*x*exp(-x^2)*λ[x]","ℝ","-1/2·exp(-1)+1/2"),
	Case("CurveSymbolicBound","∫dx [a≤x]*x*exp(-x^2)*λ[x]","ℝ","1/2·exp(-a^2)"),
	Case("CurveSymbolicBounds","∫dx [a≤x≤b]*x*exp(-x^2/2)*λ[x]","ℝ","[a≤b]·(exp(-1/2·a^2)-exp(-1/2·b^2))"),
	Case("CurveGrowing","∫dx [0≤x≤1]*(2*x+1)*exp(x^2+x)*λ[x]","ℝ","exp(2)-1"),
	Case("CurveMoment","∫dx [0≤x]*x^3*exp(-x^2)*λ[x]","ℝ","1/2"),
	Case("CurveCubic","∫dx [0≤x]*x^2*exp(-x^3)*λ[x]","ℝ","1/3"),
	Case("CurveScaled","∫dx [0≤x]*c*x*exp(-x^2)*λ[x]","ℝ","c·(1/2)"),
	Case("CurveTwoScales","∫dx [0<x]*[x<1]*c*x*exp(x^2)*d*λ[x]","ℝ","c·d·(1/2·e-1/2)"),
	Case("CurveSum","∫dx [0≤x]*(x*exp(-x^2)+exp(-x))*λ[x]","ℝ","3/2"),
	Case("CurveConstant","∫dx [0≤x]*x*exp(-x^2+1)*λ[x]","ℝ","1/2·e"),
	Case("CurveCdf","λ(a:ℝ).∫dx [0≤x]*[x≤a]*2*x*exp(-x^2)*λ[x]","ℝ→ℝ","λ(a:ℝ). [0≤a]·(-exp(-a^2)+1)"),
	Case("CurveGuarded","∫dx [c≤d]*[0≤x]*x*exp(-x^2)*λ[x]","ℝ","[c≤d]·(1/2)"),
	Case("CurveLaw","∫dx ([0≤x]*2*x*exp(-x^2)*λ[x])*x^2","ℝ","1"),
	Case("CurveHalfLineGrowing","∫dx [0≤x]*x*exp(x^2)*λ[x]","ℝ"),
	Case("CurveOffset","∫dx [0≤x]*x*exp(-x^2+a)*λ[x]","ℝ","1/2·exp(a)"),
	Case("CurveOffsetInterval","∫dx [0≤x≤1]*x*exp(b-x^2)*c*λ[x]","ℝ","c·(-1/2·exp(-1)+1/2)·exp(b)"),
	Case("CurveOffsetShift","∫dx [1≤x]*(x-1)*exp(a-(x-1)^2)*λ[x]","ℝ","1/2·exp(a)"),
	Case("CurveOffsetLinear","∫dx [0≤x]*x*exp(a-x)*exp(-x^2+x)*λ[x]","ℝ","1/2·exp(a)"),
	Case("CurveOffsetSum","∫dx [0≤x]*(x*exp(-x^2+a)+exp(b-x))*λ[x]","ℝ","1/2·exp(a)+exp(b)"),
	Case("CurveOffsetBounds","∫dx [u≤x≤v]*(2*x+1)*exp(x^2+x+w)*λ[x]","ℝ","[u≤v]·((-exp(u·(u+1))+exp(v·(v+1)))·exp(w))"),
	Case("CurveMean","∫dx [m≤x]*(x-m)*exp(-(x-m)^2)*λ[x]","ℝ","1/2"),
	Case("CurveCurvature","∫dx [0≤x]*x*exp(-a*x^2)*λ[x]","ℝ"),
	Case("DomainHalfLine","∫dx [0≤x]*exp(-x)/a*λ[x]","ℝ","guard(a≠0,a⁻¹)"),
	Case("DomainInterval","∫dx [0≤x]*[x≤1]*exp(x)/a*λ[x]","ℝ","guard(a≠0,(e-1)·a⁻¹)"),
	Case("DomainSwapped","∫dx [x≤1]*[0≤x]*exp(x)/a*λ[x]","ℝ","guard(a≠0,(e-1)·a⁻¹)"),
	Case("DomainStrict","∫dx [0<x]*[x<1]*(x+1/a)*λ[x]","ℝ","guard(a≠0,1/2+a⁻¹)"),
	Case("DomainRoot","∫dx [0≤x]*exp(-x)*sqrt(a)*λ[x]","ℝ","guard(0≤a,sqrt(a))"),
	Case("DomainLogarithm","∫dx [0≤x]*exp(-x)*log(a)*λ[x]","ℝ","guard(0<a,log(a))"),
	Case("DomainSum","∫dx [0≤x]*(x*exp(-x^2)/a+exp(-x)/b)*λ[x]","ℝ","guard(a≠0∧b≠0,b⁻¹+a⁻¹·(1/2))"),
	Case("DomainOffset","∫dx [0≤x≤1]*x*exp(-x^2+1/a)*λ[x]","ℝ","guard(a≠0,(-1/2·exp(-1)+1/2)·exp(a⁻¹))"),
	Case("DomainSymbolicBounds","∫dx [u≤x≤v]*exp(x)/a*λ[x]","ℝ","[u≤v]·(guard(a≠0,(-exp(u)+exp(v))·a⁻¹))"),
	Case("DomainGuarded","∫dx [c≤d]*[0≤x]*exp(-x)/a*λ[x]","ℝ","[c≤d]·(guard(a≠0,a⁻¹))"),
	Case("DomainGuardedStrict","∫dx [c<d]*[0≤x≤1]*sqrt(a)*x*λ[x]","ℝ","[c<d]·(guard(0≤a,1/2·sqrt(a)))"),
	Case("DomainTwoGuards","∫dx [c≤d]*[e<f]*[0≤x]*exp(-x)/a*λ[x]","ℝ","[c≤d]·([e<f]·(guard(a≠0,a⁻¹)))"),
	Case("DomainNested","λ(t:ℝ).∫dx [0≤x]*[x≤t]*exp(-x)/a*λ[x]","ℝ→ℝ","λ(t:ℝ). [0≤t]·(guard(a≠0,(-exp(-t)+1)·a⁻¹))"),
	Case("DomainAxis","∫dx [1≤x≤2]*(1/x)*λ[x]","ℝ","log(2)"),
	Case("DomainAxisRoot","∫dx [1≤x≤2]*sqrt(x)*λ[x]","ℝ"),
	Case("Quotient","∫dx [1≤x≤2]*x^(-2)*λ[x]","ℝ","1/2"),
	Case("QuotientSum","∫dx [1≤x≤2]*(1/x+x)*λ[x]","ℝ","log(2)+3/2"),
	Case("QuotientProduct","∫dx [1≤x≤2]*(x+1)^2/x^3*λ[x]","ℝ","log(2)+11/8"),
	Case("QuotientScaled","∫dx [1/2≤x≤3]*(x^2+1)/(2*x^4)*λ[x]","ℝ","175/81"),
	Case("QuotientDifference","∫dx [1<x<2]*(2/x^2-1/x)*λ[x]","ℝ","-log(2)+1"),
	Case("QuotientMinus","∫dx [1≤x≤2]*(1/x-x^2)*λ[x]","ℝ","log(2)-7/3"),
	Case("QuotientFactors","∫dx [1≤x≤2]*(1/x+1)*(1/x+2)*λ[x]","ℝ","3·log(2)+5/2"),
	Case("QuotientNegative","∫dx [-2≤x≤-1]*(1/x)*λ[x]","ℝ","-log(2)"),
	Case("QuotientAcross","∫dx [-1≤x≤1]*(1/x)*λ[x]","ℝ","undefined(ℝ)"),
	Case("QuotientEdge","∫dx [0<x≤1]*(1/x^2)*λ[x]","ℝ","undefined(ℝ)"),
	Case("QuotientUpper","∫dx [1≤x≤t]*(1/x)*λ[x]","ℝ","[1≤t]·log(t)"),
	Case("QuotientLower","∫dx [a≤x≤1]*(1/x)*λ[x]","ℝ","[a≤1]·(guard(0<a,-log(abs(a))))"),
	Case("QuotientBounds","∫dx [a≤x≤b]*(1/x^2)*λ[x]","ℝ","[a≤b]·(guard(0<a∧b≠0∨b<0∧a≠0,-b⁻¹+a⁻¹))"),
	Case("QuotientFunction","λ(t:ℝ).∫dx [1≤x≤t]*(1/x^2)*λ[x]","ℝ→ℝ","λ(t:ℝ). [1≤t]·(1-t⁻¹)"),
	Case("QuotientGuarded","∫dx [c≤d]*[1≤x≤2]*(1/x)*λ[x]","ℝ","[c≤d]·log(2)"),
	Case("QuotientAbove","∫dx [1≤x]*(1/x^2)*λ[x]","ℝ","1"),
	Case("QuotientAboveTerm","∫dx [a≤x]*(1/x^2)*λ[x]","ℝ","guard(0<a,a⁻¹)"),
	Case("QuotientAboveSum","∫dx [2≤x]*(1/x^3+3/x^2)*λ[x]","ℝ","13/8"),
	Case("QuotientAboveZero","∫dx [0≤x]*(1/x^2)*λ[x]","ℝ","undefined(ℝ)"),
	Case("QuotientAboveEdge","∫dx [0<x]*(1/x^2)*λ[x]","ℝ","undefined(ℝ)"),
	Case("QuotientAboveFunction","λ(t:ℝ).∫dx [t≤x]*(1/x^3)*λ[x]","ℝ→ℝ","λ(t:{t:ℝ | 0<t}). (t^2)⁻¹·(1/2)"),
	Case("QuotientAboveGuarded","∫dx [c≤d]*[1≤x]*(1/x^2)*λ[x]","ℝ","[c≤d]"),
	Case("QuotientAbovePolynomial","∫dx [1≤x]*(1/x^2+1)*λ[x]","ℝ"),
	Case("QuotientBelow","∫dx [x≤-1]*(1/x^2)*λ[x]","ℝ","1"),
	Case("QuotientBelowLowest","∫dx [x<b]*(2/x^3-1/x^4)*λ[x]","ℝ","guard(b<0,(-b+1/3)·(b^3)⁻¹)"),
	Case("QuotientDiverges","∫dx [1≤x]*(1/x)*λ[x]","ℝ"),
	Case("QuotientDomain","∫dx [a≤x≤b]*(1/x+x)*λ[x]","ℝ","[a≤b]·(guard(0<a∧b≠0∨b<0∧a≠0,-1/2·a^2+1/2·b^2-log(abs(a))+log(abs(b))))"),
	Case("QuotientDomainStrict","∫dx [a<x≤b]*(x+1)/x^4*λ[x]","ℝ","[a<b]·(guard(0<a∧b≠0∨b<0∧a≠0,(-b·(1/2)-1/3)·(b^3)⁻¹-(-a·(1/2)-1/3)·(a^3)⁻¹))"),
	Case("QuotientDomainAbove","∫dx [a<x]*(x+1)/x^4*λ[x]","ℝ","guard(0<a,-(-a·(1/2)-1/3)·(a^3)⁻¹)"),
	Case("QuotientDomainBelow","∫dx [x≤b]*(x+1)/x^4*λ[x]","ℝ","guard(b<0,(-b·(1/2)-1/3)·(b^3)⁻¹)"),
	Case("QuotientDomainCancelled","∫dx [a≤x]*x^2/x^5*λ[x]","ℝ","guard(0<a,(a^2)⁻¹·(1/2))"),
	Case("QuotientRemovable","∫dx [a≤x≤b]*x^3/x*λ[x]","ℝ"),
	Case("QuotientPole","∫dx [1≤x≤2]*1/(x+1)*λ[x]","ℝ","-log(2)+log(3)"),
	Case("QuotientPoleBounds","∫dx [a≤x≤b]*1/(x+1)*λ[x]","ℝ","[a≤b]·(guard(-1<a∧b≠-1∨b<-1∧a≠-1,-log(abs(a+1))+log(abs(b+1))))"),
	Case("QuotientPoleSquare","∫dx [1≤x≤2]*(1/(2*x+1)^2)*λ[x]","ℝ","1/15"),
	Case("QuotientPoleProduct","∫dx [1≤x≤2]*x/(x+1)*λ[x]","ℝ","log(2)-log(3)+1"),
	Case("QuotientPoleDivision","∫dx [0≤x≤1]*(x^2+1)/(x+1)*λ[x]","ℝ","2·log(2)-1/2"),
	Case("QuotientPoleReversed","∫dx [a≤x≤b]*1/(1-x)*λ[x]","ℝ","[a≤b]·(guard(1<a∧b≠1∨b<1∧a≠1,log(abs(a-1))-log(abs(b-1))))"),
	Case("QuotientPoleFunction","λ(t:ℝ).∫dx [0≤x]*[x≤t]*1/(x+1)^2*λ[x]","ℝ→ℝ","λ(t:ℝ). [0≤t]·(1-(t+1)⁻¹)"),
	Case("QuotientPoleAbove","∫dx [0≤x]*1/(x+1)^2*λ[x]","ℝ","1"),
	Case("QuotientPoleAboveTerm","∫dx [a≤x]*1/(x-2)^3*λ[x]","ℝ","guard(2<a,((a-2)^2)⁻¹·(1/2))"),
	Case("QuotientPoleBelow","∫dx [x<b]*1/(2-x)^2*λ[x]","ℝ","guard(b<2,-(b-2)⁻¹)"),
	Case("QuotientPoleScale","∫dx [1≤x≤2]*c/(x+1)*λ[x]","ℝ","c·(-log(2)+log(3))"),
	Case("QuotientPoleScaleStrict","∫dx [a<x≤b]*c/(x+1)*λ[x]","ℝ","[a<b]·(guard(c=0∧-1≤a∨(-1<a∧b≠-1∨b<-1∧a≠-1),[c≠0]·(c·(-log(abs(a+1))+log(abs(b+1))))))"),
	Case("QuotientPoleScaleClosed","∫dx [0<x<1]*c/(x+1)*λ[x]","ℝ","c·log(2)"),
	Case("QuotientPoleScaleBelow","∫dx [x≤b]*c/(x-2)^2*λ[x]","ℝ","guard(b<2,-c·(b-2)⁻¹)"),
	Case("QuotientPoleUniform","∫dx [a≤x≤b]*(1/(x+1))/log(b/a)*λ[x]","ℝ","[a≤b]·(guard(a≠0∧(0<b·a⁻¹∧(b≠a∧(-1<a∧b≠-1)))∨a<0∧(b≠a∧(b<-1∧a≠-1)),(-log(abs(a+1))+log(abs(b+1)))·log(b·a⁻¹)⁻¹))"),
	Case("QuotientPoleInside","∫dx [-2≤x≤0]*1/(x+1)*λ[x]","ℝ"),
	Case("Logarithm","∫dx [1≤x≤2]*log(x)*λ[x]","ℝ","2·log(2)-1"),
	Case("LogarithmProduct","∫dx [1≤x≤2]*x*log(x)*λ[x]","ℝ","2·log(2)-3/4"),
	Case("LogarithmPolynomial","∫dx [1≤x≤2]*(x^2-1)*log(x)*λ[x]","ℝ","2/3·log(2)+2/9"),
	Case("LogarithmSum","∫dx [1≤x≤2]*(log(x)+x*log(x))*λ[x]","ℝ","4·log(2)-7/4"),
	Case("LogarithmMinus","∫dx [1≤x≤2]*(x*log(x)-x)*λ[x]","ℝ","2·log(2)-9/4"),
	Case("LogarithmMixed","∫dx [1≤x≤2]*(log(x)*x^2+log(x)+1)*λ[x]","ℝ","14/3·log(2)-7/9"),
	Case("LogarithmZero","∫dx [0<x≤1]*log(x)*λ[x]","ℝ","-1"),
	Case("LogarithmEntropy","∫dx [0<x≤1]*x*log(x)*λ[x]","ℝ","-1/4"),
	Case("LogarithmClosed","∫dx [0≤x≤1]*log(x)*λ[x]","ℝ","undefined(ℝ)"),
	Case("LogarithmAcross","∫dx [-1≤x≤1]*log(x)*λ[x]","ℝ","undefined(ℝ)"),
	Case("LogarithmBounds","∫dx [a≤x≤b]*log(x)*λ[x]","ℝ","[a≤b]·(guard(0<a∧0<b,-a·log(a)+b·log(b)+a-b))"),
	Case("LogarithmStrict","∫dx [a<x≤b]*log(x)*λ[x]","ℝ","[a<b]·(guard(0≤a∧0<b,b·log(b)+a-b+[a≠0]·(-a·log(a))))"),
	Case("LogarithmDomain","∫dx [a≤x≤b]*(log(x)+x)*λ[x]","ℝ","[a≤b]·(guard(0<a∧0<b,-a·(a·(1/2)-1)-a·log(a)+b·(b·(1/2)-1)+b·log(b)))"),
	Case("LogarithmDomainProduct","∫dx [a≤x≤b]*(x+1)*log(x)*λ[x]","ℝ","[a≤b]·(guard(0<a∧0<b,-a·(a·(1/2)+1)·log(a)+b·(b·(1/2)+1)·log(b)-a·(-a·(1/4)-1)+b·(-b·(1/4)-1)))"),
	Case("LogarithmFunction","λ(t:ℝ).∫dx [1≤x]*[x≤t]*log(x)*λ[x]","ℝ→ℝ","λ(t:ℝ). [1≤t]·(t·log(t)-t+1)"),
	Case("LogarithmPole","∫dx [1≤x≤2]*log(x+1)*λ[x]","ℝ","-2·log(2)+3·log(3)-1"),
	Case("LogarithmPoleBounds","∫dx [a≤x≤b]*log(x+1)*λ[x]","ℝ","[a≤b]·(guard(-1<a∧-1<b,-(a+1)·log(a+1)+(b+1)·log(b+1)+a-b))"),
	Case("LogarithmPoleProduct","∫dx [0≤x≤1]*x*log(x+1)*λ[x]","ℝ","1/4"),
	Case("LogarithmPoleStrict","∫dx [2<x≤3]*log(x-2)*λ[x]","ℝ","-1"),
	Case("LogarithmSquare","∫dx [1≤x≤2]*log(x)^2*λ[x]","ℝ"),
	Case("LogarithmQuotient","∫dx [1≤x≤2]*log(x)/x*λ[x]","ℝ"),
	Case("LogarithmScale","∫dx [1≤x≤2]*c*log(x)*λ[x]","ℝ","c·(2·log(2)-1)"),
	Case("LogarithmScaleFactors","∫dx [1≤x≤2]*x*c*log(x)*d*λ[x]","ℝ","c·d·(2·log(2)-3/4)"),
	Case("LogarithmScaleSum","∫dx [1≤x≤2]*c*(log(x)+x)*λ[x]","ℝ","c·(2·log(2)+1/2)"),
	Case("LogarithmScaleStrict","∫dx [a<x≤b]*c*log(x)*λ[x]","ℝ","[a<b]·(guard(0≤a∧0<b,c·(b·log(b)+a-b+[a≠0]·(-a·log(a)))))"),
	Case("LogarithmScaleEntropy","∫dx [0<x≤1]*c*x*log(x)*λ[x]","ℝ","-c·(1/4)"),
	Case("LogarithmScaleDomain","∫dx [1≤x≤2]*log(x)/c*λ[x]","ℝ","guard(c≠0,(2·log(2)-1)·c⁻¹)"),
	Case("LogarithmScaleGuarded","∫dx [a≤x≤b]*c*(x+1)*log(x)*λ[x]","ℝ","[a≤b]·(guard(0<a∧0<b,c·(-a·(a·(1/2)+1)·log(a)+b·(b·(1/2)+1)·log(b)-a·(-a·(1/4)-1)+b·(-b·(1/4)-1))))"),
	Case("LogarithmScaleJoined","∫dx [a≤x≤b]*(x+1)*log(x)/sqrt(c)*λ[x]","ℝ","[a≤b]·(guard(0<c∧(0<a∧0<b),(-a·(a·(1/2)+1)·log(a)+b·(b·(1/2)+1)·log(b)-a·(-a·(1/4)-1)+b·(-b·(1/4)-1))·sqrt(c)⁻¹))"),
	Case("LogarithmScaleJoinedFirst","∫dx [a≤x≤b]*(1/sqrt(c))*(log(x)+x)*λ[x]","ℝ","[a≤b]·(guard(0<c∧(0<a∧0<b),(-a·(a·(1/2)-1)-a·log(a)+b·(b·(1/2)-1)+b·log(b))·sqrt(c)⁻¹))"),
	Case("LogarithmScalePole","∫dx [1≤x≤2]*c*log(x+1)*λ[x]","ℝ","c·(-2·log(2)+3·log(3)-1)"),
	Case("LogarithmScalePoleBounds","∫dx [a≤x≤b]*log(x+1)*exp(m)*λ[x]","ℝ","[a≤b]·(guard(-1<a∧-1<b,(-(a+1)·log(a+1)+(b+1)·log(b+1)+a-b)·exp(m)))"),
	Case("LogarithmScaleFunction","λ(t:ℝ).∫dx [1≤x]*[x≤t]*c*log(x)*λ[x]","ℝ→ℝ","λ(t:ℝ). [1≤t]·(c·(t·log(t)-t+1))"),
	Case("LogarithmScaleConstant","∫dx [1≤x≤2]*(c*log(x)+d)*λ[x]","ℝ","c·(2·log(2)-1)+d"),
	Case("LogarithmAbove","∫dx [1≤x]*log(x)*λ[x]","ℝ"),
	Case("LogarithmTwo","∫dx [1≤x≤2]*(log(x)-log(x+1))*λ[x]","ℝ"),
	Case("LogarithmMultiple","∫dx [1≤x≤2]*log(2*x)*λ[x]","ℝ","3·log(2)-1"),
	Case("Summand","∫dx [1≤x≤2]*(log(x)+c)*λ[x]","ℝ","c+2·log(2)-1"),
	Case("SummandQuotient","∫dx [1≤x≤2]*(1/x+c)*λ[x]","ℝ","c+log(2)"),
	Case("SummandBounds","∫dx [a≤x≤b]*(log(x)+c)*λ[x]","ℝ","[a≤b]·(c·(-a+b)+(guard(0<a∧0<b,-a·log(a)+b·log(b)+a-b)))"),
	Case("SummandQuotientBounds","∫dx [a≤x≤b]*(1/x+c)*λ[x]","ℝ","[a≤b]·(c·(-a+b)+(guard(0<a∧b≠0∨b<0∧a≠0,-log(abs(a))+log(abs(b)))))"),
	Case("SummandScale","∫dx [a≤x≤b]*(c/x+d)*λ[x]","ℝ","[a≤b]·(d·(-a+b)+(guard(0<a∧b≠0∨b<0∧a≠0,c·(-log(abs(a))+log(abs(b))))))"),
	Case("SummandPole","∫dx [1≤x≤2]*(1/(x+1)+c)*λ[x]","ℝ","c-log(2)+log(3)"),
	Case("SummandPoleStrict","∫dx [a<x≤b]*(log(x+1)+c)*λ[x]","ℝ","[a<b]·(c·(-a+b)+(guard(-1<b∧a=-1∨-1<b∧-1<a,(b+1)·log(b+1)+a-b+[a≠-1]·(-(a+1)·log(a+1)))))"),
	Case("SummandDomain","∫dx [1≤x≤2]*(log(x)+sqrt(c))*λ[x]","ℝ","guard(0≤c,sqrt(c)+2·log(2)-1)"),
	Case("SummandFunction","λ(t:ℝ).∫dx [1≤x]*[x≤t]*(log(x)+c)*λ[x]","ℝ→ℝ","λ(t:ℝ). [1≤t]·(c·(t-1)+t·log(t)-t+1)"),
	Case("SummandAbove","∫dx [1≤x]*(1/x^2+c)*λ[x]","ℝ"),
	Case("SummandNested","∫dx [1≤x≤2]*(log(2*x)+x)*λ[x]","ℝ"),
	Case("Competing","∫dx [0≤x]*[x≤1]*[x≤a]*λ[x]","ℝ","[a<1∧0≤a]·a+[1≤a]"),
	Case("CompetingLower","∫dx [0≤x]*[x≤1]*[a≤x]*λ[x]","ℝ","[0<a∧a≤1]·(-a+1)+[a≤0]"),
	Case("CompetingStrict","∫dx [0<x]*[x<1]*[x<a]*λ[x]","ℝ","[a<1∧0<a]·a+[1≤a]"),
	Case("CompetingStrictLower","∫dx [0≤x]*[x≤1]*[a<x]*x*λ[x]","ℝ","[0≤a∧a<1]·(-1/2·a^2+1/2)+[a<0]·(1/2)"),
	Case("CompetingValue","∫dx [0≤x]*[x≤1]*[x≤a]*x*λ[x]","ℝ","[a<1∧0≤a]·(1/2·a^2)+[1≤a]·(1/2)"),
	Case("CompetingUpperFirst","∫dx [x<a]*[b<x]*[x≤c]*x*λ[x]","ℝ","[b<a]·([c<a∧b<c]·(-1/2·b^2+1/2·c^2)+[a≤c]·(1/2·a^2-1/2·b^2))"),
	Case("CompetingUpperFirstLower","∫dx [x<a]*[b<x]*[c≤x]*x*λ[x]","ℝ","[b<a]·([b<c∧c<a]·(1/2·a^2-1/2·c^2)+[c≤b]·(1/2·a^2-1/2·b^2))"),
	Case("CompetingFour","∫dx [0≤x]*[x≤1]*[a≤x]*[x≤b]*λ[x]","ℝ","[0<a∧a≤1]·([b<1∧a≤b]·(-a+b)+[1≤b]·(-a+1))+[a≤0]·([b<1∧0≤b]·b+[1≤b])"),
	Case("CompetingFourValue","∫dx [0≤x]*[x≤1]*[a≤x]*[x≤b]*x*λ[x]","ℝ","[0<a∧a≤1]·([b<1∧a≤b]·(-1/2·a^2+1/2·b^2)+[1≤b]·(-1/2·a^2+1/2))+[a≤0]·([b<1∧0≤b]·(1/2·b^2)+[1≤b]·(1/2))"),
	Case("CompetingHalfLine","∫dx [0≤x]*[a≤x]*exp(-x)*λ[x]","ℝ","[0<a]·exp(-a)+[a≤0]"),
	Case("CompetingBelow","∫dx [x≤1]*[x≤a]*exp(x)*λ[x]","ℝ","[a<1]·exp(a)+[1≤a]·e"),
	Case("CompetingSameSide","∫dx [x≤a]*[x≤b]*[0≤x]*x*λ[x]","ℝ","[b<a∧0≤b]·(1/2·b^2)+[a≤b∧0≤a]·(1/2·a^2)"),
	Case("CompetingSameSideUnit","∫dx [x≤a]*[x≤b]*[0≤x]*λ[x]","ℝ","[b<a∧0≤b]·b+[a≤b∧0≤a]·a"),
	Case("CompetingSameSideLower","∫dx [a≤x]*[b≤x]*[x≤1]*x*λ[x]","ℝ","[a<b∧b≤1]·(-1/2·b^2+1/2)+[b≤a∧a≤1]·(-1/2·a^2+1/2)"),
	Case("CompetingDomain","∫dx [0≤x]*[x≤1]*[x≤a]*(1/c)*λ[x]","ℝ","[a<1]·([0≤a]·(guard(c≠0,a·c⁻¹)))+[1≤a]·(guard(c≠0,c⁻¹))"),
	Case("CompetingDomainSameSide","∫dx [x≤a]*[x≤b]*[0≤x]*(1/c)*x*λ[x]","ℝ","[b<a]·([0≤b]·(guard(c≠0,c⁻¹·(1/2)·b^2)))+[a≤b]·([0≤a]·(guard(c≠0,c⁻¹·(1/2)·a^2)))"),
	Case("CompetingDomainFour","∫dx [0≤x]*[x≤1]*[a≤x]*[x≤b]*log(c)*x*λ[x]","ℝ"),
	Case("CompetingDomainHalfLine","∫dx [a≤x]*[b≤x]*log(c)*exp(-x)*λ[x]","ℝ","[a<b]·(guard(0<c,exp(-b)·log(c)))+[b≤a]·(guard(0<c,exp(-a)·log(c)))"),
	Case("CompetingGaussian","∫dx [0≤x]*[x≤1]*[x≤a]*exp(-x^2)*λ[x]","ℝ","[a<1∧0≤a]·(1/2·sqrt(π)·erf(a))+[1≤a]·(1/2·sqrt(π)·erf(1))"),
	Case("CompetingQuotient","∫dx [1≤x]*[x≤a]*[x≤b]*(c/x)*λ[x]","ℝ","[1≤a]·([b<a∧1≤b]·(c·log(b))+[a≤b]·(c·log(a)))"),
	Case("CompetingLogarithm","∫dx [1≤x]*[x≤a]*[x≤b]*log(x)*λ[x]","ℝ","[1≤a]·([b<a∧1≤b]·(b·log(b)-b+1)+[a≤b]·(a·log(a)-a+1))"),
	Case("CompetingRate","∫dx [0≤x]*[x≤1]*[x≤a]*exp(c*x)*λ[x]","ℝ","[a<1∧0≤a]·([c≠0]·(c⁻¹·exp(a·c)-c⁻¹)+[c=0]·a)+[1≤a]·([c≠0]·(c⁻¹·exp(c)-c⁻¹)+[c=0])"),
	Case("CompetingRateHalfLine","∫dx [0≤x]*[a≤x]*exp(-c*x)*λ[x]","ℝ","[0<a]·(guard(0<c,c⁻¹·exp(-a·c)))+[a≤0]·(guard(0<c,c⁻¹))"),
	Case("CompetingGuard","∫dx [1≤c]*[0≤x]*[x≤1]*[x≤a]*x*λ[x]","ℝ","[1≤c]·([a<1∧0≤a]·(1/2·a^2)+[1≤a]·(1/2))"),
	Case("CompetingFactor","∫dx c*[0≤x]*[x≤1]*[x≤a]*λ[x]","ℝ","[a<1∧0≤a]·(c·a)+[1≤a]·c"),
	Case("CompetingFunction","λ(t:ℝ).∫dx [0≤x]*[x≤1]*[x≤t]*λ[x]","ℝ→ℝ","λ(t:ℝ). [t<1∧0≤t]·t+[1≤t]"),
	Case("CompetingFunctionValue","λ(t:ℝ).∫dx [0≤x]*[x≤1]*[x≤t]*x*λ[x]","ℝ→ℝ","λ(t:ℝ). [t<1∧0≤t]·(1/2·t^2)+[1≤t]·(1/2)"),
	Case("CompetingFunctionHalfLine","λ(t:ℝ).∫dx [0≤x]*[t≤x]*exp(-x)*λ[x]","ℝ→ℝ","λ(t:ℝ). [0<t]·exp(-t)+[t≤0]"),
	Case("CompetingNested","∫dy [0≤y]*[y≤2]*λ[y]*∫dx [0≤x]*[x≤1]*[x≤y]*λ[x]","ℝ","3/2"),
	Case("CompetingNestedValue","∫dy [0≤y]*[y≤1]*(∫dx [0≤x]*[x≤1]*[x≤y]*x*λ[x])*λ[y]","ℝ","1/6"),
	Case("CompetingCurvature","∫dx [0≤x]*[x≤1]*[x≤a]*exp(-c*x^2)*λ[x]","ℝ"),
	Case("CompetingPole","∫dx [0≤x]*[x≤1]*[x≤a]*(1/x)*λ[x]","ℝ"),
	Case("CompetingUnbounded","∫dx [0≤x]*[a≤x]*λ[x]","ℝ"),
	Case("BracketNatural","∫dx [0≤x]*[x≤a]*2*λ[x]","ℝ","[0≤a]·(2·a)"),
	Case("BracketInteger","∫dx [0≤x]*[x≤a]*(-3)*λ[x]","ℝ","[0≤a]·(-3·a)"),
	Case("BracketRational","∫dx [0≤x]*[x≤a]*(1/2)*λ[x]","ℝ","[0≤a]·(a·(1/2))"),
	Case("BracketStrict","∫dx [a<x]*[x<b]*(3/4)*λ[x]","ℝ","[a<b]·(-a·(3/4)+b·(3/4))"),
	Case("BracketGuard","∫dx [1≤c]*[0≤x]*[x≤a]*2*λ[x]","ℝ","[1≤c∧0≤a]·(2·a)"),
	Case("BracketGuardInteger","∫dx [1≤c]*[0≤x]*[x≤a]*(-3)*λ[x]","ℝ","[1≤c∧0≤a]·(-3·a)"),
	Case("BracketGuardRational","∫dx [1≤c]*[0≤x]*[x≤a]*(1/2)*λ[x]","ℝ","[1≤c∧0≤a]·(a·(1/2))"),
	Case("BracketCompeting","∫dx [0≤x]*[x≤2]*(1/2)*[x≤t]*λ[x]","ℝ","[t<2∧0≤t]·(t·(1/2))+[2≤t]"),
	Case("BracketCompetingNatural","∫dx [0≤x]*[x≤a]*[x≤b]*2*λ[x]","ℝ"),
	Case("BracketCompetingInteger","∫dx [0≤x]*[x≤a]*[x≤b]*(-3)*λ[x]","ℝ"),
	Case("BracketSolved","∫dx [0≤x]*[2*x≤a]*3*λ[x]","ℝ","[0≤a]·(a·(3/2))"),
	Case("BracketFunction","λ(t:ℝ).∫dx [0≤x]*[x≤t]*2*λ[x]","ℝ→ℝ","λ(t:ℝ). [0≤t]·(2·t)"),
	Case("BracketUnbounded","∫dx [a≤x]*2*λ[x]","ℝ"),
	Case("PieceCases","∫dx [0≤x]*[x≤1]*([x≤a]*x+[a<x]*a)*λ[x]","ℝ","[a<1∧0≤a]·(1/2·a^2)+[0≤a∧a<1]·(a·(-a+1))+[a<0]·a+[1≤a]·(1/2)"),
	Case("PieceCasesSpread","∫dx [0≤x]*[x≤1]*[x≤a]*(x+[x≤1/2])*λ[x]","ℝ","[a<1∧0≤a]·(1/2·a^2)+[0≤a]·([a≤1/2]·a+[1/2<a]·(1/2))+[1≤a]·(1/2)"),
	Case("PieceCasesHalfLine","∫dx [0≤x]*([x≤a]*exp(-x)+[a<x]*exp(-2*x))*λ[x]","ℝ","[0≤a]·(1/2·exp(-2·a)-exp(-a)+1)+[a<0]·(1/2)"),
	Case("PieceCasesSameSide","∫dx ([a≤x]*[b≤x]*exp(-x)+[0≤x]*[x≤1]*x)*λ[x]","ℝ","[a<b]·exp(-b)+[b≤a]·exp(-a)+1/2"),
	Case("PieceCasesUpperFirst","∫dx ([x<a]*[b<x]*[c≤x]*x+[0≤x]*[x≤1]*x^2)*λ[x]","ℝ","[b<a]·([b<c∧c<a]·(1/2·a^2-1/2·c^2)+[c≤b]·(1/2·a^2-1/2·b^2))+1/3"),
	Case("PieceCasesUpperFirstUpper","∫dx ([x<a]*[b<x]*[x≤c]*x+[0≤x]*[x≤1]*x^2)*λ[x]","ℝ","[b<a]·([c<a∧b<c]·(-1/2·b^2+1/2·c^2)+[a≤c]·(1/2·a^2-1/2·b^2))+1/3"),
	Case("PieceCasesNested","∫dy [0≤y]*[y≤a]*λ[y]*∫dx [0≤x]*[x≤1]*[x≤y]*λ[x]","ℝ","[0≤a]·([a<1]·(1/2·a^2)+[1≤a]·(1/2))+[1≤a]·(a-1)"),
	Case("PieceCasesHat","∫dx [0≤x]*[x≤a]*([x≤1]*x+[1<x]*(2-x)*[x≤2])*λ[x]","ℝ","[1<a]·([a≤2]·(a·(-a·(1/2)+2)-3/2)+[2<a]·(1/2))+[0≤a]·([a≤1]·(1/2·a^2)+[1<a]·(1/2))"),
	Case("PieceCasesAbsolute","∫dx [0≤x]*[x≤1]*[x≤a]*abs(x-1/2)*λ[x]","ℝ","[a<1∧1/2≤a]·(a·(a·(1/2)-1/2)+1/8)+[a<1/2∧0≤a]·(a·(-a·(1/2)+1/2))+[1≤a]·(1/8)+[1/2≤a]·(1/8)"),
	Case("PieceCasesSolved","∫dx [0≤x]*[x≤1]*([2*x≤a]*x+[a<2*x]*x^2)*λ[x]","ℝ","[a<2∧0≤a]·(1/8·a^2)+[0≤a∧a<2]·(-1/24·a^3+1/3)+[a<0]·(1/3)+[2≤a]·(1/2)"),
	Case("CastSum","∫dx ([0≤x]*[x≤a]+[0≤x]*[x≤b]*2)*λ[x]","ℝ","[0≤a]·a+[0≤b]·(2·b)"),
	Case("CastSumThree","∫dx ([0≤x]*[x≤a]+[1≤x]*[x≤b]*2+[2≤x]*[x≤c]*3)*λ[x]","ℝ","[0≤a]·a+[1≤b]·(2·b-2)+[2≤c]·(3·c-6)"),
	Case("CastSumInteger","∫dx ([0≤x]*[x≤a]-[0≤x]*[x≤b]*2)*λ[x]","ℝ","[0≤a]·a+[0≤b]·(-2·b)"),
	Case("CastSumRational","∫dx [0≤x]*[x≤1]*([x≤a]/2+[a<x]/3)*λ[x]","ℝ","[a<1∧0≤a]·(a·(1/2))+[0≤a∧a<1]·(-a·(1/3)+1/3)+[a<0]·(1/3)+[1≤a]·(1/2)"),
	Case("CastSumCompeting","∫dx [0≤x]*[x≤1]*([x≤a]+[a<x]*2)*λ[x]","ℝ","[a<1∧0≤a]·a+[0≤a∧a<1]·(-2·a+2)+[a<0]·2+[1≤a]"),
	Case("CastSumCompetingInteger","∫dx [0≤x]*[x≤1]*([x≤a]-[a<x]*2)*λ[x]","ℝ","[a<1∧0≤a]·a+[0≤a∧a<1]·(2·a-2)+[a<0]·-2+[1≤a]"),
	Case("CastSumClosed","∫dx ([0≤x]*[x≤1]+[1/2≤x]*[x≤a])*λ[x]","ℝ","[1/2≤a]·(a-1/2)+1"),
	Case("CastSumMany","∫dx [0≤x]*[x≤1]*([x≤a]+[x≤b]+[x≤c])*λ[x]","ℝ","[a<1∧0≤a]·a+[b<1∧0≤b]·b+[c<1∧0≤c]·c+[1≤a]+[1≤b]+[1≤c]"),
	Case("CastSumOne","∫dx [0≤x]*[x≤1]*([x≤a]+1)*λ[x]","ℝ","[a<1∧0≤a]·a+[1≤a]+1"),
	Case("CastSumMixed","∫dx [0≤x]*[x≤1]*(([x≤a]+[a<x]*2)+([x≤b]-[b<x]*3)/2)*λ[x]","ℝ","[a<1∧0≤a]·a+[b<1∧0≤b]·(b·(1/2))+[0≤a∧a<1]·(-2·a+2)+[0≤b∧b<1]·(b·(3/2)-3/2)+[b<0]·(-3/2)+[1≤b]·(1/2)+[a<0]·2+[1≤a]"),
	Case("CastSumBound","∫dx [0≤x]*[x≤1]*[x≤c]*([x≤a]+[a<x]*2)*λ[x]","ℝ","[c<1∧0≤c]·([a<c∧0≤a]·a+[0≤a∧a<c]·(2·c-2·a)+[a<0]·(2·c)+[c≤a]·c)+[1≤c]·([a<1∧0≤a]·a+[0≤a∧a<1]·(-2·a+2)+[a<0]·2+[1≤a])"),
	Case("CastSumWeight","∫dx [0≤x]*[x≤1]*x*([x≤a]+[a<x]*2)*λ[x]","ℝ","[a<1∧0≤a]·(1/2·a^2)+[0≤a∧a<1]·(-a^2+1)+[1≤a]·(1/2)+[a<0]"),
	Case("CastSumExponential","∫dx [0≤x]*[x≤2]*e^(-x)*([x≤1]+[1<x]*2)*λ[x]","ℝ","-2·exp(-2)+exp(-1)+1"),
	Case("CastSumHalfLine","∫dx [0≤x]*e^(-x)*([x≤a]+[a<x]*2)*λ[x]","ℝ","[0≤a]·(exp(-a)+1)+[a<0]·2"),
	Case("CastSumUnbounded","∫dx ([0≤x]*[x≤a]+[0≤x]*2)*λ[x]","ℝ"),
	Case("SumFactorsProduct","∫dx [0≤x]*[x≤1]*([x≤a]+[a<x]*2)*([x≤b]+[b<x]*3)*λ[x]","ℝ",
		"[a<1∧0≤a]·([b<a∧0≤b]·b+[a≤b]·a)+[0≤a∧a<1]·([a<b∧b<1]·(-6·b+6)+[b<1∧a<b]·(-2·a+2·b)+[1≤b]·(-2·a+2)+[b≤a]·(-6·a+6))+[0≤b∧b<1]·([a<1∧b<a]·(3·a-3·b)+[1≤a]·(-3·b+3))+[a<0]·([b<1∧0≤b]·(2·b)+[0≤b∧b<1]·(-6·b+6)+[b<0]·6+[1≤b]·2)+[b<0]·([a<1∧0≤a]·(3·a)+[1≤a]·3)+[1≤a]·([b<1∧0≤b]·b+[1≤b])"),
	Case("SumFactorsProductSame","∫dx [0≤x]*[x≤1]*([x≤a]+[a<x]*2)*([x≤a]+[a<x]*3)*λ[x]","ℝ","[a<1∧0≤a]·a+[0≤a∧a<1]·(-6·a+6)+[a<0]·6+[1≤a]"),
	Case("SumFactorsOnes","∫dx [0≤x]*[x≤1]*(1+[x≤a])*(1+[x≤b])*λ[x]","ℝ","[a<1∧0≤a]·(a+[b<a∧0≤b]·b+[a≤b]·a)+[b<1∧0≤b]·b+[1≤a]·([b<1∧0≤b]·b+[1≤b]+1)+[1≤b]+1"),
	Case("SumFactorsInteger","∫dx [0≤x]*[x≤1]*(1-[x≤a])*(1-[x≤b])*λ[x]","ℝ","[a<1∧0≤a]·(-a+[b<a∧0≤b]·b+[a≤b]·a)+[b<1∧0≤b]·-b+[1≤a]·([b<1∧0≤b]·b+[1≤b]-1)+[1≤b]·-1+1"),
	Case("SumFactorsRational","∫dx [0≤x]*[x≤1]*([x≤a]/2+[a<x]/3)*([x≤a]/5+[a<x]/7)*λ[x]","ℝ","[a<1∧0≤a]·(a·(1/10))+[0≤a∧a<1]·(-a·(1/21)+1/21)+[a<0]·(1/21)+[1≤a]·(1/10)"),
	Case("SumFactorsSquare","∫dx [0≤x]*[x≤1]*([x≤a]+[a<x]*2)^2*λ[x]","ℝ","[a<1∧0≤a]·a+[0≤a∧a<1]·(-4·a+4)+[a<0]·4+[1≤a]"),
	Case("SumFactorsSquareInteger","∫dx [0≤x]*[x≤1]*([x≤a]-[a<x]*2)^2*λ[x]","ℝ","[a<1∧0≤a]·a+[0≤a∧a<1]·(-4·a+4)+[a<0]·4+[1≤a]"),
	Case("SumFactorsSquareRational","∫dx [0≤x]*[x≤1]*([x≤a]/2+[a<x]/3)^2*λ[x]","ℝ","[a<1∧0≤a]·(a·(1/4))+[0≤a∧a<1]·(-a·(1/9)+1/9)+[a<0]·(1/9)+[1≤a]·(1/4)"),
	Case("SumFactorsSquareWeight","∫dx [0≤x]*[x≤1]*x*([x≤a]+[a<x]*2)^2*λ[x]","ℝ","[a<1∧0≤a]·(1/2·a^2)+[0≤a∧a<1]·(-2·a^2+2)+[1≤a]·(1/2)+[a<0]·2"),
	Case("SumFactorsSquareBounds","∫dx ([0≤x]*[x≤a]+[1≤x]*[x≤b]*2)^2*λ[x]","ℝ","[0≤a]·a+[1≤a]·([b<a∧1≤b]·(4·b-4)+[a≤b]·(4·a-4))+[1≤b]·(4·b-4)"),
	Case("SumFactorsCube","∫dx [0≤x]*[x≤1]*([x≤a]+[a<x]*2)^3*λ[x]","ℝ","[a<1∧0≤a]·a+[0≤a∧a<1]·(-8·a+8)+[a<0]·8+[1≤a]"),
	Case("SumFactorsMixed","∫dx [0≤x]*[x≤1]*([x≤a]+[a<x]*2)^2*([x≤a]+3)*λ[x]","ℝ","[a<1∧0≤a]·(4·a)+[0≤a∧a<1]·(-12·a+12)+[a<0]·12+[1≤a]·4"),
	Case("SumFactorsFourth","∫dx [0≤x]*[x≤1]*([x≤a]+[a<x]*2)^4*λ[x]","ℝ"),
	Case("SumFactorsReal","∫dx [0≤x]*[x≤1]*([x≤a]*x+[a<x]*2)*([x≤a]*x+[a<x]*3)*λ[x]","ℝ","[a<1∧0≤a]·(1/3·a^3)+[0≤a∧a<1]·(-6·a+6)+[1≤a]·(1/3)+[a<0]·6"),
	Case("SumFactorsRealSquare","∫dx [0≤x]*[x≤1]*([x≤a]*x+[a<x]*2)^2*λ[x]","ℝ","[a<1∧0≤a]·(1/3·a^3)+[0≤a∧a<1]·(-4·a+4)+[1≤a]·(1/3)+[a<0]·4"),
	Case("SumFactorsRealCube","∫dx [0≤x]*[x≤1]*([x≤a]*x+[a<x]*2)^3*λ[x]","ℝ","[a<1∧0≤a]·(1/4·a^4)+[0≤a∧a<1]·(-8·a+8)+[1≤a]·(1/4)+[a<0]·8"),
	Case("SumFactorsMasked","∫dx [0≤x]*[x≤1]*([x≤a]*x)^2*λ[x]","ℝ","[a<1∧0≤a]·(1/3·a^3)+[1≤a]·(1/3)"),
	Case("BehindBetween","∫dx [0≤x]*[x≤a]*[0<a]*λ[x]","ℝ","[0<a]·a"),
	Case("BehindBetweenUniform","∫dx [0≤x]*[x≤a]*[0<a]*(1/a)*λ[x]","ℝ","[0<a]"),
	Case("BehindBetweenUniformTerms","∫dx [a≤x]*[x≤b]*[a<b]*(1/(b-a))*λ[x]","ℝ","[a<b]"),
	Case("BehindBetweenOther","∫dx [0≤x]*[x≤a]*[b≠0]*λ[x]","ℝ","[0≤a∧b≠0]·a"),
	Case("BehindBetweenTerms","∫dx [a≤x]*[x≤b]*[0<c]*λ[x]","ℝ","[a≤b∧0<c]·(-a+b)"),
	Case("BehindBetweenStrict","∫dx [a≤x]*[x<b]*[0<c]*x*λ[x]","ℝ","[a<b∧0<c]·(-1/2·a^2+1/2·b^2)"),
	Case("BehindBetweenTwo","∫dy [0≤y]*[y≤1]*[0≤x]*[x≤1]*λ[y]","ℝ","[0≤x∧x≤1]"),
	Case("BehindBoundThenBetween","∫dy [0≤y]*[0≤x]*[y≤1]*[x≤1]*λ[y]","ℝ","[0≤x∧x≤1]"),
	Case("BehindBoundStrict","∫dx [x<1]*[0<a]*[0<x]*[b<a]*λ[x]","ℝ","[0<a∧b<a]"),
	Case("BehindBoundHalfLine","∫dx [0≤x]*e^(-x)*[0<a]*λ[x]","ℝ","[0<a]"),
	Case("BehindBoundUpper","∫dx [x≤0]*e^x*[0<a]*[b<1]*λ[x]","ℝ","[0<a∧b<1]"),
	Case("BehindNested","∫dx ∫dy [0≤y]*[y≤1]*[0≤x]*[x≤1]*[x+y≤1]*λ[x]*λ[y]","ℝ","1/2"),
	Case("BehindPieces","∫dx ([0≤x]*[x≤1]*[0<a]+[1≤x]*[x≤2]*[b<1]*3)*λ[x]","ℝ","[0<a]+[b<1]·3"),
	Case("BehindPiecesHalfLine","∫dx ([0≤x]*e^(-x)*[0<a]+[x≤0]*e^x*[b<1])*λ[x]","ℝ","[b<1]+[0<a]"),
	Case("BehindPiecesSpread","∫dx [0≤x]*[x≤1]*[0<a]*([x≤a]+[a<x]*2)*λ[x]","ℝ","[a≠0]·([a<1∧0<a]·a+[1≤a])+[0<a∧a<1]·(-2·a+2)"),
	Case("BehindBetweenDomain","∫dx [0≤x]*[x≤1]*[c<1]*(1/b)*λ[x]","ℝ","[c<1]·(guard(b≠0,b⁻¹))"),
	Case("BehindBoundDomain","∫dx [0≤x]*[c<1]*[x≤1]*(1/b)*λ[x]","ℝ","[c<1]·(guard(b≠0,b⁻¹))"),
	Case("BehindBetweenDomainTwo","∫dx [0≤x]*[x≤1]*[c<1]*[0<d]*(1/b)*λ[x]","ℝ","guard(1≤c∨(d≤0∨b≠0),[c<1∧0<d]·(guard(b≠0,b⁻¹)))"),
	Case("OriginUniform","∫dx [0≤x]*[x≤a]*(1/a)*λ[x]","ℝ","guard(a≠0,[0≤a])"),
	Case("OriginLogarithm","∫dx [0≤x]*[x≤a]*log(a)*λ[x]","ℝ","guard(a≠0,[0≤a]·(a·log(a)))"),
	Case("OriginBelow","∫dx [a≤x]*[x≤0]*(1/a)*λ[x]","ℝ","guard(a≠0,[a≤0]·-1)"),
	Case("OriginMoment","∫dx [0≤x]*[x≤a]*x*(1/a)*λ[x]","ℝ","guard(a≠0,[0≤a]·(a·(1/2)))"),
	Case("OriginCompeting","∫dx [0≤x]*[x≤a]*[x≤1]*(1/a)*λ[x]","ℝ","guard(a≠0,[0≤a]·([1<a]·(guard(a≠0,a⁻¹))+[a≤1]·([0≤a]·(a·a⁻¹))))"),
	Case("OriginOther","∫dx [1≤x]*[x≤a]*(1/(a-1))*λ[x]","ℝ","[1≤a]·(guard(a≠1,(1:ℝ)))"),
	Case("TermDomainLogarithm","∫dx [0≤x]*[x≤log(a)]*λ[x]","ℝ","guard(0<a,[1≤a]·log(a))"),
	Case("TermDomainRoot","∫dx [0≤x]*[x≤sqrt(a)]*x*λ[x]","ℝ","guard(0≤a,a·(1/2))"),
	Case("TermDomainLower","∫dx [x≤0]*[log(a)≤x]*λ[x]","ℝ","guard(0<a,[a≤1]·-log(a))"),
	Case("TermDomainExponential","∫dx [0≤x]*[x≤log(a)]*e^(-x)*λ[x]","ℝ","guard(0<a,[1≤a]·(1-a⁻¹))"),
	Case("TermDomainCondition","∫dx [0≤x]*[x≤1/a]*[0<a]*λ[x]","ℝ","guard(a≠0,[0<a]·a⁻¹)"),
	Case("TermDomainBetween","∫dx [0≤x]*[x≤1]*[x≤1/a]*x*λ[x]","ℝ","guard(a≠0,[a⁻¹<1∧0≤a]·((a^2)⁻¹·(1/2))+[1≤a⁻¹]·(1/2))"),
	Case("TermDomainBetweenLower","∫dx [0≤x]*[x≤1]*[log(a)≤x]*λ[x]","ℝ","guard(0<a,[1<a∧log(a)≤1]·(-log(a)+1)+[a≤1])"),
	Case("TermDomainBetweenStrict","∫dx [0<x]*[x<1]*[x<1/a]*λ[x]","ℝ","guard(a≠0,[a⁻¹<1∧0<a]·a⁻¹+[1≤a⁻¹])"),
	Case("TermDomainSum","∫dx ([0≤x]*[x≤log(a)]+[0≤x]*[x≤1]*2)*λ[x]","ℝ","guard(0<a,(guard(0<a,[1≤a]·log(a)))+2)"),
	Case("TermDomainSumBetween","∫dx [0≤x]*[x≤1]*x*([x≤1/a]+2)*λ[x]","ℝ","guard(a≠0,(guard(a≠0,[a⁻¹<1∧0≤a]·((a^2)⁻¹·(1/2))+[1≤a⁻¹]·(1/2)))+1)"),
	Case("TermDomainSumValue","∫dx [0≤x]*[x≤1]*([x≤c]+2)*(1/b)*λ[x]","ℝ","guard(b≠0,(guard(b≠0,2·b⁻¹))+(guard(b≠0,[c<1∧0≤c]·(c·b⁻¹)+[1≤c]·b⁻¹)))"),
	Case("TermDomainSumApart","∫dx ([0≤x]*[x≤1]*[x≤1/a]+[1≤x]*[x≤2]*3)*λ[x]","ℝ"),
	Case("TermDomainTwo","∫dx [0≤x]*[x≤log(a)]*[x≤log(b)]*λ[x]","ℝ"),
	Case("TermDomainValue","∫dx [0≤x]*[x≤log(a)]*(1/b)*λ[x]","ℝ"),
	Case("ExcludedEnd","∫dx [0≤x]*[x≤a]*[x≠a]*λ[x]","ℝ","[0<a]·a"),
	Case("ExcludedEndSwapped","∫dx [0≤x]*[x≤a]*[a≠x]*λ[x]","ℝ","[0<a]·a"),
	Case("ExcludedEndStrict","∫dx [0≤x]*[x<a]*[x≠a]*λ[x]","ℝ","[0<a]·a"),
	Case("ExcludedEnds","∫dx [a≤x]*[x≠a]*[x≤b]*[b≠x]*λ[x]","ℝ","[a<b]·(-a+b)"),
	Case("ExcludedEndsOrigin","∫dx [0≤x]*[0≠x]*[x≤a]*[a≠x]*λ[x]","ℝ","[0<a]·a"),
	Case("ExcludedEndMoment","∫dx [0≤x]*[x≤a]*[a≠x]*x*λ[x]","ℝ","[0<a]·(1/2·a^2)"),
	Case("ExcludedEndOffset","∫dx [0≤x]*[x≤a+1]*[x-a≠1]*λ[x]","ℝ","[-1<a]·(a+1)"),
	Case("ExcludedEndScaled","∫dx [0≤x]*[2*x≤a]*[a≠2*x]*λ[x]","ℝ","[0<a]·(a·(1/2))"),
	Case("ExcludedEndExponential","∫dx [0≤x]*[x≤a]*[x≠a]*[x≠0]*e^(-x)*λ[x]","ℝ","[0<a]·(-exp(-a)+1)"),
	Case("TermPointExcluded","∫dx [0≤x]*[x≤1]*[x≠a]*λ[x]","ℝ","1"),
	Case("TermPointExcludedFirst","∫dx [x≠a]*[0≤x]*[x≤1]*λ[x]","ℝ","1"),
	Case("TermPointExcludedBetween","∫dx [0≤x]*[x≠a]*[x≤1]*λ[x]","ℝ","1"),
	Case("TermPointExcludedSwapped","∫dx [0≤x]*[x≤1]*[a≠x]*λ[x]","ℝ","1"),
	Case("TermPointExcludedScaled","∫dx [0≤x]*[x≤1]*[2*x≠a]*x*λ[x]","ℝ","1/2"),
	Case("TermPointExcludedTerms","∫dx [0≤x]*[x≤1]*[x+a≠b]*λ[x]","ℝ","1"),
	Case("TermPointExcludedTwo","∫dx [0≤x]*[x≤1]*[x≠a]*[x≠b]*λ[x]","ℝ","1"),
	Case("TermPointExcludedRational","∫dx [0≤x]*[x≤1]*[x≠1/2]*[x≠a]*λ[x]","ℝ","1"),
	Case("TermPointExcludedLine","∫dx [x≠a]*e^(-x^2)*λ[x]","ℝ","sqrt(π)"),
	Case("TermPointExcludedHalfLine","∫dx [0≤x]*[x≠a]*e^(-x)*λ[x]","ℝ","1"),
	Case("TermPointExcludedBound","∫dx [0≤x]*[x≤b]*[x≠a]*λ[x]","ℝ","[0≤b]·b"),
	Case("TermPointExcludedCompeting","∫dx [0≤x]*[x≤1]*[x≠a]*[x≤b]*λ[x]","ℝ","[b<1∧0≤b]·b+[1≤b]"),
	Case("TermPointExcludedCondition","∫dx [0≤x]*[x≤1]*[x≠a]*[0<b]*λ[x]","ℝ","[0<b]"),
	Case("TermPointExcludedSum","∫dx ([0≤x]*[x≤1]*[x≠a]+[1≤x]*[x≤2]*[x≠b]*3)*λ[x]","ℝ","4"),
	Case("TermPointExcludedQuotient","∫dx [0≤x]*[x≤1]*[x≠a]*(1/(1+x^2))*λ[x]","ℝ","1/4·π"),
	Case("TermPointOnly","∫dx [0≤x]*[x≤1]*[x=a]*λ[x]","ℝ","0"),
	Case("TermPointOnlyValue","∫dx [0≤x]*[x≤1]*[x=a]*x*λ[x]","ℝ","0"),
	Case("TermPointOnlySummand","∫dx [0≤x]*[x≤1]*([x=a]+2)*λ[x]","ℝ","2"),
	Case("TermPointCases","∫dx [0≤x]*[x≤1]*([x=a]*3+[x≠a]*x)*λ[x]","ℝ","1/2"),
	Case("TermPointExcludedDomain","∫dx [0≤x]*[x≤1]*[x≠a]*(1/b)*λ[x]","ℝ"),
	Case("TermPointExcludedPartial","∫dx [0≤x]*[x≤1]*[x≠log(a)]*λ[x]","ℝ","guard(0<a,(1:ℝ))"),
	Case("TermPointExcludedTermDomain","∫dx [0≤x]*[x≤log(b)]*[x≠a]*λ[x]","ℝ","guard(0<b,[1≤b]·log(b))"),
	Case("TermPointExcludedNested","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[x≠y]*λ[x]*λ[y]","ℝ","1"),
	Case("TermPointMissingLine","∫dx [x≠log(a)]*e^(-x^2)*λ[x]","ℝ","guard(0<a,sqrt(π))"),
	Case("TermPointMissingHalfLine","∫dx [0≤x]*[x≠log(a)]*e^(-x)*λ[x]","ℝ","guard(0<a,(1:ℝ))"),
	Case("TermPointMissingFront","∫dx [x≠log(a)]*[0≤x]*[x≤1]*λ[x]","ℝ","guard(0<a,(1:ℝ))"),
	Case("TermPointMissingScaled","∫dx [0≤x]*[x≤1]*[2*x≠log(a)]*x*λ[x]","ℝ","guard(0<a,(1/2:ℝ))"),
	Case("TermPointMissingBound","∫dx [0≤x]*[x≤b]*[x≠log(a)]*λ[x]","ℝ","[0≤b]·(guard(0<a,[0≤b]·b))"),
	Case("TermPointMissingRoot","∫dx [0≤x]*[x≤1]*[x≠sqrt(a)]*λ[x]","ℝ","guard(0≤a,(1:ℝ))"),
	Case("TermPointMissingValue","∫dx [0≤x]*[x≤1]*[x≠log(a)]*x*λ[x]","ℝ","guard(0<a,(1/2:ℝ))"),
	Case("TermPointMissingTwo","∫dx [0≤x]*[x≤1]*[x≠log(a)]*[x≠b]*λ[x]","ℝ","guard(0<a,(1:ℝ))"),
	Case("TermPointMissingOrder","∫dx [0≤x]*[x≤1]*[x≠b]*[x≠log(a)]*λ[x]","ℝ"),
	Case("TermPointMissingSum","∫dx ([0≤x]*[x≤1]*[x≠log(a)]+[1≤x]*[x≤2]*3)*λ[x]","ℝ"),
	Case("TermPointMissingOnly","∫dx [0≤x]*[x≤1]*[x=log(a)]*λ[x]","ℝ","guard(0<a,(0:ℝ))"),
	Case("TermPointMissingOnlyLine","∫dx [x=log(a)]*e^(-x^2)*λ[x]","ℝ","guard(0<a,(0:ℝ))"),
	Case("TermPointMissingOnlyHalfLine","∫dx [0≤x]*[x=log(a)]*e^(-x)*λ[x]","ℝ","guard(0<a,(0:ℝ))"),
	Case("TermPointMissingOnlyBound","∫dx [0≤x]*[x≤b]*[x=log(a)]*λ[x]","ℝ","[0≤b]·(guard(0<a,(0:ℝ)))"),
	Case("TermPointNestedFront","∫dx ∫dy [0≤x]*[x≤1]*[x≠y]*[0≤y]*[y≤1]*λ[x]*λ[y]","ℝ","1"),
	Case("TermPointNestedScaled","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[2*y≠x]*λ[x]*λ[y]","ℝ","1"),
	Case("TermPointNestedFactor","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[x≠y]*2*λ[x]*λ[y]","ℝ","2"),
	Case("TermPointNestedTwo","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[x≠y]*[y≠a]*λ[x]*λ[y]","ℝ","1"),
	Case("TermPointNestedThree","∫dx ∫dy ∫dz [0≤x]*[x≤1]*[0≤y]*[y≤1]*[0≤z]*[z≤1]*[x≠y]*[y≠z]*λ[x]*λ[y]*λ[z]","ℝ","1"),
	Case("TermPointNestedOnly","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[x=y]*λ[x]*λ[y]","ℝ","0"),
	Case("TermPointNestedValue","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[x≠y]*x*y*λ[x]*λ[y]","ℝ","1/4"),
	Case("TermPointNestedCases","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*([x=y]*3+[x≠y]*2)*λ[x]*λ[y]","ℝ","2"),
	Case("TermPointExcludedSquare","∫dx [0≤x]*[x≤1]*[x^2≠a]*λ[x]","ℝ"),
	Case("MultipliedSquare","∫dx [0≤x]*[x≤1]*(a+x)^2*λ[x]","ℝ","a^2+a+1/3"),
	Case("MultipliedCube","∫dx [0≤x]*[x≤1]*(a+x)^3*λ[x]","ℝ","a^3+3/2·a^2+a+1/4"),
	Case("MultipliedProduct","∫dx [0≤x]*[x≤1]*(a+x)*(b+x)*λ[x]","ℝ","a·b+a·(1/2)+b·(1/2)+1/3"),
	Case("MultipliedFactor","∫dx [0≤x]*[x≤1]*a*(b+x)*λ[x]","ℝ","a·(b+1/2)"),
	Case("MultipliedSlope","∫dx [0≤x]*[x≤1]*(a*x+b)^2*λ[x]","ℝ","1/3·a^2+a·b+b^2"),
	Case("MultipliedBound","∫dx [0≤x]*[x≤a]*(x-a)^2*λ[x]","ℝ","[0≤a]·(1/3·a^3)"),
	Case("MultipliedCompeting","∫dx [0≤x]*[x≤1]*[x≤b]*(a+x)^2*λ[x]","ℝ","[b<1∧0≤b]·(1/3·b^3+a·b^2+b·a^2)+[1≤b]·(a^2+a+1/3)"),
	Case("MultipliedCondition","∫dx [0≤x]*[x≤1]*[0<c]*(a+x)^2*λ[x]","ℝ","[0<c]·(a^2+a+1/3)"),
	Case("MultipliedExcluded","∫dx [0≤x]*[x≤1]*[x≠b]*(a+x)^2*λ[x]","ℝ","a^2+a+1/3"),
	Case("MultipliedDomain","∫dx [0≤x]*[x≤1]*(a+x)^2*(1/a)*λ[x]","ℝ","guard(a≠0,a+1+a⁻¹·(1/3))"),
	Case("MultipliedTermDomain","∫dx [0≤x]*[x≤1]*(x+a)*(x+log(b))*λ[x]","ℝ","guard(0<b,a·log(b)+a·(1/2)+1/2·log(b)+1/3)"),
	Case("MultipliedSum","∫dx ([0≤x]*[x≤1]*(a+x)^2+[1≤x]*[x≤2]*3)*λ[x]","ℝ","a^2+a+10/3"),
	Case("MultipliedHalfLine","∫dx [0≤x]*e^(-x)*(a+x)^2*λ[x]","ℝ","a^2+2·a+2"),
	Case("MultipliedExponentials","∫dx [0≤x]*(1-e^(-2*x))*e^(-x)*λ[x]","ℝ","2/3"),
	Case("MultipliedNested","∫dx ∫dy [0≤x]*e^(-x)*[0≤y]*e^(-y)*[x+y≤a]*λ[x]*λ[y]","ℝ","[0≤a]·(-a·exp(-a)-exp(-a)+1)"),
	Case("MultipliedNestedRates","∫dx ∫dy [0≤x]*e^(-x)*[0≤y]*e^(-2*y)*[y≤x]*λ[x]*λ[y]","ℝ","1/3"),
	Case("MultipliedKept","∫dx [0≤x]*[x≤1]*(a+x)^2*sin(x)*λ[x]","ℝ","∫dx ([0≤x∧x≤1]·((a+x)^2·sin(x)))·λ[x]"),
	Case("MultipliedOuter","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*(x+y)^2*λ[x]*λ[y]","ℝ","7/6"),
	Case("OpenedMaximum","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*([x≤y]*y+[y<x]*x)*λ[x]*λ[y]","ℝ","2/3"),
	Case("OpenedDistance","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*([x≤y]*(y-x)+[y<x]*(x-y))*λ[x]*λ[y]","ℝ","1/3"),
	Case("OpenedGaussian","∫dx ∫dy e^(-x^2/2)*e^(-(y-x)^2/2)*λ[x]*λ[y]","ℝ","2·π"),
	Case("OpenedGaussianMoment","∫dx ∫dy e^(-x^2/2)*e^(-(y-x)^2/2)*y^2*λ[x]*λ[y]","ℝ","4·π"),
	Case("OpenedExponential","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*e^(x+y)*λ[x]*λ[y]","ℝ","(e-1)^2"),
	Case("OpenedRates","∫dx ∫dy [0≤x]*e^(-x)*[0≤y]*e^(-y)*(x-y)^2*λ[x]*λ[y]","ℝ","2"),
	Case("OpenedCube","∫dx ∫dy ∫dz [0≤x]*[x≤1]*[0≤y]*[y≤1]*[0≤z]*[z≤1]*(x+y+z)^2*λ[x]*λ[y]*λ[z]","ℝ","5/2"),
	Case("OpenedSimplex","∫dx ∫dy ∫dz [0≤x]*[0≤y]*[0≤z]*[x+y+z≤1]*λ[x]*λ[y]*λ[z]","ℝ","1/6"),
	Case("OpenedFunction","λ(t:ℝ).∫dx [0≤x]*[x≤1]*(x+t)^2*λ[x]","ℝ→ℝ","λ(t:ℝ). t^2+t+1/3"),
	Case("OpenedInner","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*e^(-x*y)*λ[x]*λ[y]","ℝ","∫dx ([0≤x∧x≤1]·([x≠0]·(-x⁻¹·exp(-x)+x⁻¹)+[x=0]))·λ[x]"),
	Case("OpenedKept","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[x*y≤1/2]*λ[x]*λ[y]","ℝ","∫dx (∫dy [0≤x∧(x≤1∧(0≤y∧(y≤1∧x·y≤1/2)))]·λ[y])·λ[x]"),
	Case("OpenedDirect","∫dx ∫dy [0≤x]*[x≤1]*[x≤y]*[y≤2*x]*λ[x]*λ[y]","ℝ","1/2"),
	Case("PieceCasesDomain","∫dx [0≤x]*[x≤1]*([x≤a]*x*(1/c)+[a<x]*x^2)*λ[x]","ℝ"),
	Case("Solved","∫dx [0≤x]*[2*x≤a]*λ[x]","ℝ","[0≤a]·(a·(1/2))"),
	Case("SolvedStrict","∫dx [0<x]*[2*x<a]*λ[x]","ℝ","[0<a]·(a·(1/2))"),
	Case("SolvedOffset","∫dx [0≤x]*[x+1≤a]*λ[x]","ℝ","[1≤a]·(a-1)"),
	Case("SolvedNegative","∫dy [0≤y]*[0≤x-y]*λ[y]","ℝ","[0≤x]·x"),
	Case("SolvedNegativeLeft","∫dx [1-x≤a]*[x≤1]*λ[x]","ℝ","[0≤a]·a"),
	Case("SolvedRight","∫dx [a≤2*x+1]*[x≤1]*x*λ[x]","ℝ","[a≤3]·(-(a·(1/4)-1/4)·(a·(1/2)-1/2)+1/2)"),
	Case("SolvedRightNegative","∫dx [0≤x]*[a≤3-2*x]*x*λ[x]","ℝ","[a≤3]·((-a·(1/2)+3/2)·(-a·(1/4)+3/4))"),
	Case("SolvedTerms","∫dx [0≤x]*[3*x-a≤b+1]*x*λ[x]","ℝ","[-1/3≤a·(1/3)+b·(1/3)]·((a·(1/6)+b·(1/6)+1/6)·(a·(1/3)+b·(1/3)+1/3))"),
	Case("SolvedHalf","∫dx [x/2+b≤a]*[0≤x]*exp(x)*λ[x]","ℝ","[0≤-2·b+2·a]·(exp(-2·b+2·a)-1)"),
	Case("SolvedDomain","∫dx [0≤x]*[2*x≤a]*(1/c)*λ[x]","ℝ","[0≤a]·(guard(c≠0,a·c⁻¹·(1/2)))"),
	Case("SolvedCompeting","∫dx [0≤x]*[x≤1]*[2*x≤a]*λ[x]","ℝ","[a<2∧0≤a]·(a·(1/2))+[2≤a]"),
	Case("SolvedConvolution","∫dy [0≤y]*[y≤1]*[0≤x-y]*[x-y≤1]*λ[y]","ℝ","[x<1∧0≤x]·x+[1≤x]·([1<x∧x≤2]·(-x+2)+[x≤1])"),
	Case("SolvedFunction","λ(t:ℝ).∫dx [0≤x]*[2*x≤t]*λ[x]","ℝ→ℝ","λ(t:ℝ). [0≤t]·(t·(1/2))"),
	Case("SolvedFunctionSum","λ(t:ℝ).∫dx [0≤x]*[2*x+t+3*x≤1]*λ[x]","ℝ→ℝ","λ(t:ℝ). [t≤1]·(-t·(1/5)+1/5)"),
	Case("SolvedNested","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[x+y≤1]*λ[x]*λ[y]","ℝ","1/2"),
	Case("SolvedNestedSum","∫dy [0≤y]*[y≤1]*λ[y]*∫dx [0≤x]*[x+y+x≤1]*λ[x]","ℝ","1/4"),
	Case("SolvedBothSides","∫dx [0≤x]*[x≤1]*[x+a≤2*x+b]*λ[x]","ℝ","[0<a-b∧a-b≤1]·(-a+b+1)+[a-b≤0]"),
	Case("SolvedBothUpper","∫dx [0≤x]*[x≤1]*[3*x+a≤2*x+b]*λ[x]","ℝ","[-a+b<1∧0≤-a+b]·(-a+b)+[1≤-a+b]"),
	Case("SolvedBothAxis","∫dx [0≤x]*[x≤1]*[x≤2*x+b]*λ[x]","ℝ","[b<0∧-1≤b]·(b+1)+[0≤b]"),
	Case("SolvedBothStrict","∫dx [0≤x]*[x≤1]*[2*x+a<x/2+b]*λ[x]","ℝ","[-a·(2/3)+b·(2/3)≤1∧0<-a·(2/3)+b·(2/3)]·(-a·(2/3)+b·(2/3))+[1<-a·(2/3)+b·(2/3)]"),
	Case("SolvedBothNegative","∫dx [0≤x]*[x≤1]*[a-x≤b-3*x]*λ[x]","ℝ","[-a·(1/2)+b·(1/2)<1∧0≤-a·(1/2)+b·(1/2)]·(-a·(1/2)+b·(1/2))+[1≤-a·(1/2)+b·(1/2)]"),
	Case("SolvedBothValue","∫dx [0≤x]*[x+a≤2*x]*e^(-x)*λ[x]","ℝ","[0<a]·exp(-a)+[a≤0]"),
	Case("SolvedBothMoment","∫dx [0≤x]*[x≤1]*[x+a≤2*x+b]*x*λ[x]","ℝ","[0<a-b∧a-b≤1]·(-(a-b)·(a·(1/2)-b·(1/2))+1/2)+[a-b≤0]·(1/2)"),
	Case("SolvedBothTwo","∫dx [x+a≤2*x]*[3*x≤x+b]*λ[x]","ℝ","[a≤b·(1/2)]·(-a+b·(1/2))"),
	Case("SolvedBothChain","∫dx [0≤x]*[x≤1]*[x+a<2*x+b]*[2*x+b≤3*x+c]*λ[x]","ℝ","[0≤a-b∧a-b<1]·([a-b<b-c∧b-c≤1]·(-b+c+1)+[b-c≤a-b]·(-a+b+1))+[a-b<0]·([0<b-c∧b-c≤1]·(-b+c+1)+[b-c≤0])"),
	Case("SolvedBothDomain","∫dx [0≤x]*[x≤1]*[x≤2*x+b]*(1/c)*λ[x]","ℝ","[b<0]·([-1≤b]·(guard(c≠0,(b+1)·c⁻¹)))+[0≤b]·(guard(c≠0,c⁻¹))"),
	Case("SolvedBothDomainUpper","∫dx [0≤x]*[x≤1]*[3*x+a≤2*x+b]*(1/c)*λ[x]","ℝ","[-a+b<1]·([0≤-a+b]·(guard(c≠0,(-a+b)·c⁻¹)))+[1≤-a+b]·(guard(c≠0,c⁻¹))"),
	Case("SolvedBothPartial","∫dx [0≤x]*[x≤1]*[x+log(a)≤2*x]*λ[x]","ℝ","guard(0<a,[1<a∧log(a)≤1]·(-log(a)+1)+[a≤1])"),
	Case("SolvedBothFunction","λ(t:ℝ).∫dx [0≤x]*[x≤1]*[x+t≤3*x]*λ[x]","ℝ→ℝ","λ(t:ℝ). [0<t∧t≤2]·(-t·(1/2)+1)+[t≤0]"),
	Case("SolvedBothNested","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[2*x+y≤x+2*y]*λ[x]*λ[y]","ℝ","1/2"),
	Case("SolvedBothNestedValue","∫dx ∫dy [0≤x]*[x≤1]*[0≤y]*[y≤1]*[2*x+y≤x+2*y]*x*y*λ[x]*λ[y]","ℝ","1/8"),
	Case("SolvedBothEqual","∫dx [0≤x]*[x≤1]*[x+a≤x+b]*λ[x]","ℝ","[a≤b]"),
	Case("SolvedSlope","∫dx [0≤x]*[x≤1]*[a*x≤1]*λ[x]","ℝ"),
	Case("SolvedSquare","∫dx [0≤x]*[x≤1]*[x^2≤a]*λ[x]","ℝ"),
	Case("QuotientPoleTwo","∫dx [1≤x≤2]*(1/(x+1)+1/x)*λ[x]","ℝ"),
	Case("QuotientPoleQuadratic","∫dx [1≤x≤2]*(1/(x^2+1))*λ[x]","ℝ","atan(2)-1/4·π"),
	Case("QuotientScale","∫dx [1≤x≤2]*c/x*λ[x]","ℝ","c·log(2)"),
	Case("QuotientScaleBounds","∫dx [a≤x≤b]*c/x*λ[x]","ℝ","[a≤b]·(guard(0<a∧b≠0∨b<0∧a≠0,c·(-log(abs(a))+log(abs(b)))))"),
	Case("QuotientScaleStrict","∫dx [a<x≤b]*c/x*λ[x]","ℝ","[a<b]·(guard(c=0∧0≤a∨(0<a∧b≠0∨b<0∧a≠0),[c≠0]·(c·(-log(abs(a))+log(abs(b))))))"),
	Case("QuotientScaleClosed","∫dx [1<x<2]*c/x*λ[x]","ℝ","c·log(2)"),
	Case("QuotientScaleFactors","∫dx [1≤x≤2]*c*(1/x+x)*d*λ[x]","ℝ","c·d·(log(2)+3/2)"),
	Case("QuotientScaleEdge","∫dx [0<x≤1]*c/x*λ[x]","ℝ","guard(c=0,[c≠0]·(-c·log(0)))"),
	Case("QuotientScaleAcross","∫dx [-1≤x≤1]*c/x*λ[x]","ℝ","undefined(ℝ)"),
	Case("QuotientScaleFunction","λ(t:ℝ).∫dx [1≤x]*[x≤t]*c/x*λ[x]","ℝ→ℝ","λ(t:ℝ). [1≤t]·(c·log(t))"),
	Case("QuotientScaleAbove","∫dx [1≤x]*c/x^2*λ[x]","ℝ","c"),
	Case("QuotientScaleAboveTerm","∫dx [a≤x]*c/x^2*λ[x]","ℝ","guard(0<a,c·a⁻¹)"),
	Case("QuotientScaleAboveStrict","∫dx [a<x]*c/x^2*λ[x]","ℝ","guard(0<a∨c=0∧0≤a,[c≠0]·(c·a⁻¹))"),
	Case("QuotientScaleAboveClosed","∫dx [1<x]*(c+1)/x^2*λ[x]","ℝ","c+1"),
	Case("QuotientScaleBelow","∫dx [x≤b]*c/x^2*λ[x]","ℝ","guard(b<0,-c·b⁻¹)"),
	Case("QuotientScaleBelowStrict","∫dx [x<b]*c/x^2*λ[x]","ℝ","guard(b<0∨c=0∧b=0,[c≠0]·(-c·b⁻¹))"),
	Case("QuotientScaleBelowClosed","∫dx [x<-1]*c/x^3*λ[x]","ℝ","-c·(1/2)"),
	Case("QuotientScaleDomain","∫dx [1≤x≤2]*(1/x)/(b-a)*λ[x]","ℝ","guard(b≠a,(b-a)⁻¹·log(2))"),
	Case("QuotientScaleUniform","∫dx [a≤x≤b]*(1/x)/log(b/a)*λ[x]","ℝ","[a≤b]·(guard(b≠a∧(0<a∧0<b)∨b≠a∧(b<0∧a<0),(-log(abs(a))+log(abs(b)))·log(b·a⁻¹)⁻¹))"),
	Case("QuotientScaleDomainFirst","∫dx [a≤x≤b]*(1/sqrt(c))*((x+1)/x^2)*λ[x]","ℝ","[a≤b]·(guard(0<c∧(0<a∧b≠0)∨0<c∧(b<0∧a≠0),(-log(abs(a))+log(abs(b))-b⁻¹+a⁻¹)·sqrt(c)⁻¹))"),
	Case("QuotientScaleDomainAbove","∫dx [a≤x]*(1/x^2)/sqrt(c)*λ[x]","ℝ","guard(0<c∧0<a,a⁻¹·sqrt(c)⁻¹)"),
	Case("QuotientScaleDomainBelow","∫dx [x<b]*(1/x^2)/(d-c)*λ[x]","ℝ","guard(d≠c∧b<0,-b⁻¹·(d-c)⁻¹)"),
	Case("QuotientScaleDomainNested","λ(t:ℝ).∫dx [1≤x]*[x≤t]*(1/x)/(b-a)*λ[x]","ℝ→ℝ","λ(t:ℝ). [1≤t]·(guard(b≠a∧t≠0,(b-a)⁻¹·log(abs(t))))"),
	Case("QuotientScaleSum","∫dx [1≤x≤2]*(c/x+x)*λ[x]","ℝ"),
	Case("QuotientScaleDiverges","∫dx [1≤x]*c/x*λ[x]","ℝ"),
	Case("QuotientExponential","∫dx [1≤x≤2]*(1/x)*exp(x)*λ[x]","ℝ"),
	Case("SymbolicIntervalThreeBounds","∫dx [a≤x]*[x≤b]*[x≤c]*λ[x]","ℝ","[a≤b]·([c<b∧a≤c]·(-a+c)+[b≤c]·(-a+b))"),
	Case("SymbolicIntervalUnbounded","∫dx [a≤x]*λ[x]","ℝ"),
	Case("SymbolicIntervalSine","∫dx [a≤x≤b]*sin(x)*λ[x]","ℝ","[a≤b]·(cos(a)-cos(b))"),
	Case("WeightedAffineChart","Λx. ∫dy [0≤y≤1]*y*λ[y]*δ(2*y+1)[x]","Distribution(ℝ)","Λ(y:ℝ). ([1≤y∧y≤3]·(y·(1/4)-1/4))·λ[y]"),
	Case("WeightedAffineReflection","Λx. ∫dy [0≤y≤1]*2*y*λ[y]*δ(1-y)[x]","Distribution(ℝ)","Λ(y:ℝ). ([y≤1∧0≤y]·(-2·y+2))·λ[y]"),
	Case("WeightedAffineMixture","Λx. ∫dy (1/2*δ(0)[y]+1/2*[0≤y≤1]*λ[y])*δ(y+1)[x]","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(1)[x]+([1≤x∧x≤2]·(1/2))·λ[x]"),
	Case("WeightedAffineGaussian","Λx. ∫dy exp(-y^2/2)/sqrt(2*π)*λ[y]*δ(3*y+1)[x]","Distribution(ℝ)","Λ(y:ℝ). (sqrt(2·π)⁻¹·(1/3)·exp(-1/2·(y·(1/3)-1/3)^2))·λ[y]"),
	Case("WeightedAffineExponential","Λx. ∫dy exp(-y)*[0≤y]*λ[y]*δ(y/2)[x]","Distribution(ℝ)","Λ(y:ℝ). ([0≤y]·(2·exp(-2·y)))·λ[y]"),
	Case("WeightedAffineRows","integralD(λ(y:ℝ). scaleD(y^2+1, δ(1-y)))","Distribution(ℝ)","Λ(y:ℝ). ((-y+1)^2+1)·λ[y]"),
	Case("WeightedAffineBindRows","bindD(Λ(y:ℝ). λ[y], λ(y:ℝ). scaleD(y^2+1, δ(1-y)))","Distribution(ℝ)","Λ(y:ℝ). ((-y+1)^2+1)·λ[y]"),
	Case("WeightedAffineMean","∫dx (∫dy [0≤y≤1]*λ[y]*δ(2*y+1)[x])*x","ℝ","2"),
	Case("WeightedAffineMoment","∫dx (∫dy [0≤y≤1]*2*y*λ[y]*δ(3-y)[x])*x^2","ℝ","11/2"),
	Case("WeightedAffinePartialWeight","Λx. ∫dy (1/y)*λ[y]*δ(2*y)[x]","Distribution(ℝ)"),
	Case("Puncture","Λ(x:ℝ).[x≠0]*λ[x]","Distribution(ℝ)"),
	Case("WeightedDirac","Λ(x:ℝ).x*δ(2)[x]","Distribution(ℝ)","Λ(x:ℝ). 2·δ(2)[x]"),
	Case("MixtureExpectation","∫dx (1/2*δ(0)[x]+1/2*δ(1)[x])*x","ℝ","1/2"),
	Case("MixtureEvent","∫dx (1/2*δ(0)[x]+1/2*δ(1)[x])*[x=1]","ℝ","1/2"),
	Case("MixtureSymbolicMean","λ(p:ℝ). ∫dx (p*δ(1)[x]+(1-p)*δ(0)[x])*x","ℝ→ℝ","λ(p:ℝ). p"),
	Case("MixtureWeightedAtoms","Λx. (1/3*δ(1)[x]+2/3*δ(2)[x])*x","Distribution(ℝ)"),
	Case("MixtureAtomBind","Λx. ∫dy δ(0)[y]*δ(y+1)[x]","Distribution(ℝ)","δ((1:ℝ))"),
	Case("MixtureBind","Λx. ∫dy (1/2*δ(0)[y]+1/2*δ(1)[y])*δ(y+1)[x]","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(1)[x]+1/2·δ(2)[x]"),
	Case("MixtureBranch","Λr. ∫dx (1/2*δ(0)[x]+1/2*δ(1)[x])*(if x=1 then δ(10)[r] else δ(20)[r])","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(20)[x]+1/2·δ(10)[x]"),
	Case("MixtureBindDensityOff","densityAtD(Λx. ∫dy (1/2*δ(0)[y]+1/2*δ(1)[y])*δ(y+1)[x],3)","ℝ","0"),
	Case("MixtureBindDensityAtom","densityAtD(Λx. ∫dy (1/2*δ(0)[y]+1/2*δ(1)[y])*δ(y+1)[x],2)","ℝ","undefined(ℝ)"),
	Case("MixtureTwoSources","∫dx x*(∫dy ∫dz (1/2*δ(0)[y]+1/2*δ(1)[y])*(1/2*δ(0)[z]+1/2*δ(1)[z])*δ(y+z)[x])","ℝ","1"),
	Case("MixtureProductExpectation","∫dx ∫dy (1/2*δ(0)[x]+1/2*δ(1)[x])*(1/3*δ(1)[y]+2/3*δ(2)[y])*x*y","ℝ","5/6"),
	Case("MixtureDependentKernel","∫dx ∫dy (1/2*δ(0)[x]+1/2*δ(1)[x])*δ(x+1)[y]*y","ℝ","3/2"),
	Case("MixtureNestedKernel","∫dx (1/2*δ(0)[x]+1/2*δ(1)[x])*∫dy (1/2*δ(x)[y]+1/2*δ(x+1)[y])*y","ℝ","1"),
	Case("MixtureHigherAtoms","bindD(addD(δ(λ(n:ℕ).n),δ(λ(n:ℕ).n+1)),λ(f:ℕ→ℕ).δ(f(1)))","Distribution(ℕ)","Λ(x:ℕ). δ(1)[x]+δ(2)[x]"),
	Case("MixtureZeroSource","massD(bindD(zeroD(ℝ),λ(y:ℝ). δ(y+1)))","ℝ","0"),
	Case("MixturePartialAtom","∫dx (1/2*δ(0)[x]+1/2*δ(1/0)[x])*x","ℝ","undefined(ℝ)"),
	Case("MixturePartialWeight","∫dx (δ(0)[x]+δ(1)[x])*(1/x)","ℝ","undefined(ℝ)"),
	Case("MixtureMissingKernel","bindD(δ((1:ℝ)),undefined(ℝ→Distribution(ℝ)))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("MixtureMissingSummand","densityAtD(addD(undefined(Distribution(ℝ)),lebesgueD()),1)","ℝ","undefined(ℝ)"),
	Case("MixtureChartSummand","λ(d:Distribution(ℝ)). bindD(addD(d,δ((0:ℝ))),λ(y:ℝ). δ(y+1))","Distribution(ℝ)→Distribution(ℝ)"),
	Case("MixtureScaledChart","bindD(scaleD(2,lebesgueD()),λ(y:ℝ). δ(y+1))","Distribution(ℝ)"),
	Case("MixtureMaskedChart","Λx. ∫dy (1/2*δ(0)[y]+[0≤y]*[y≤1]*λ[y])*δ(y+1)[x]","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(1)[x]+[1≤x∧x≤2]·λ[x]"),
	Case("MixtureMaskedChartMass","∫dx ∫dy (1/2*δ(0)[y]+1/2*[0≤y]*[y≤1]*λ[y])*δ(y+1)[x]","ℝ","1"),
	Case("MixtureStrictSummand","addD(lebesgueD(),undefined(Distribution(ℝ)))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("MixtureStrictScale","scaleD(2,undefined(Distribution(ℝ)))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("MixtureStrictWeight","weightD(λ(x:ℝ). x,undefined(Distribution(ℝ)))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("MixtureStrictSource","bindD(undefined(Distribution(ℝ)),λ(y:ℝ). δ(y+1))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("MixtureStrictHigherSource","bindD(undefined(Distribution(ℕ)),λ(n:ℕ). δ(λ(m:ℕ).n))","Distribution(ℕ→ℕ)","undefined(Distribution(ℕ→ℕ))"),
	Case("MixtureStrictQuery","λ(d:Distribution(ℝ)). densityAtD(d,undefined(ℝ))","Distribution(ℝ)→ℝ","λ(d:Distribution(ℝ)). undefined(ℝ)"),
	Case("MixtureHigherZero","bindD(zeroD(ℕ),λ(n:ℕ). δ(λ(m:ℕ).n))","Distribution(ℕ→ℕ)","Λ(x:ℕ→ℕ). 0"),
	Case("MixtureHigherScale","bindD(scaleD(2,δ(3)),λ(n:ℕ). δ(λ(m:ℕ).n+1))","Distribution(ℕ→ℕ)","Λ(x:ℕ→ℕ). 2·δ(λ(m:ℕ). 4)[x]"),
	Case("MixtureNaturalWeight","weightD(λ(n:ℕ). (n:ℝ),addD(δ(1),δ(2)))","Distribution(ℕ)","Λ(x:ℕ). 1·δ(1)[x]+2·δ(2)[x]"),
	Case("MixtureScaledSum","bindD(scaleD(2,addD(δ((1:ℝ)),zeroD(ℝ))),λ(y:ℝ). δ(y+1))","Distribution(ℝ)"),
	Case("CountingMeasure","Λx. ∑_i δ(i)[x]","Distribution(ℝ)","Λ(x:ℝ). (∑(i:ℤ). δ((i:ℝ))[x])"),
	Case("CountingExplicit","sumD(λ(i:ℤ). δ((i:ℝ)))","Distribution(ℝ)","Λ(x:ℝ). (∑(i:ℤ). δ((i:ℝ))[x])"),
	Case("CountingMass","∫dx ∑_i δ(i)[x]","ℝ","undefined(ℝ)"),
	Case("SumUniform","Λx. ∑_i [0≤i]·[i≤3]·(1/4)·δ(i)[x]","Distribution(ℝ)"),
	Case("SumMean","∫dx (∑_i [0≤i]·[i≤3]·(1/4)·δ(i)[x])·x","ℝ","3/2"),
	Case("SumGeometricMass","∫dx (∑_i [0≤i]·(1/2)^(i+1)·δ(i)[x])","ℝ","1"),
	Case("SumGeometricMean","∫dx (∑_i [0≤i]·(1/2)^(i+1)·δ(i)[x])·x","ℝ","1"),
	Case("SumDieVariance","∫dx (∑_i [1≤i≤6]·(1/6)·δ(i)[x])·(x-7/2)^2","ℝ","35/12"),
	Case("SumIntegerAtoms","∫(x:ℤ). ∑_i δ(i)[x]·(1/2)^i·[0≤x]","ℝ","2"),
	Case("SumBind","Λx. ∫dy (∑_i [0≤i]·[i≤1]·(1/2)·δ(i)[y])·δ(y+1)[x]","Distribution(ℝ)"),
	Case("SumMissingWeight","weightD(undefined(ℝ→ℝ),sumD(λ(i:ℤ). δ((i:ℝ))))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("NaturalCounting","Λx. ∑(n:ℕ). δ(n)[x]","Distribution(ℝ)","Λ(x:ℝ). (∑(n:ℕ). δ((n:ℝ))[x])"),
	Case("NaturalAtoms","sumD(λ(n:ℕ). δ(n))","Distribution(ℕ)","Λ(x:ℕ). (∑(n:ℕ). δ(n)[x])"),
	Case("NaturalCountingMass","∫dx ∑(n:ℕ). δ(n)[x]","ℝ","undefined(ℝ)"),
	Case("NaturalGeometricMass","∫dx (∑(n:ℕ). (1/2)^(n+1)·δ(n)[x])","ℝ","1"),
	Case("NaturalGeometricMean","∫dx (∑(n:ℕ). (1/3)·(2/3)^n·δ(n)[x])·x","ℝ","2"),
	Case("NaturalDieMean","∫dx (∑(n:ℕ). [n<6]·(1/6)·δ(n+1)[x])·x","ℝ","7/2"),
	Case("NaturalDieVariance","∫dx (∑(n:ℕ). [n<6]·(1/6)·δ(n+1)[x])·(x-7/2)^2","ℝ","35/12"),
	Case("NaturalBind","Λx. ∫dy (∑(n:ℕ). [n≤1]·(1/2)·δ(n)[y])·δ(y+1)[x]","Distribution(ℝ)"),
	Case("TwoMaskGraph","Λx. ∫dy [0≤y]*[y≤1]*λ[y]*δ(2*y+1)[x]","Distribution(ℝ)","Λ(y:ℝ). ([1≤y∧y≤3]·(1/2))·λ[y]"),
	Case("TwoMaskJoint","(λ[y]*[0≤y]*[y≤1]*δ(2*y)[x])//λ[x]","Distribution(ℝ)","([0≤x∧x≤2]·(1/2))·δ(x·(1/2))[y]"),
	Case("TwoSourceGraph","Λx. ∫dy ∫dz [0≤y]*[y≤1]*λ[y]*[0≤z]*[z≤1]*λ[z]*δ(y+z)[x]","Distribution(ℝ)"),
	Case("Mixture","Λ(x:ℝ).δ(0)[x]+[x≠0]*λ[x]","Distribution(ℝ)"),
	Case("Signed","Λ(x:ℝ).-δ(0)[x]","Distribution(ℝ)"),
	Case("Integral","∫(x:ℝ).x*δ(2)[x]","ℝ"),
	Case("DensityRecovery","([x≠0]*λ[x])//λ[x]","ℝ"),
	Case("DensityOne","λ[x]//λ[x]","ℝ","1"),
	Case("Capture","(λ(a:ℝ).Λ(x:ℝ).(a+x)*λ[x])(2)","Distribution(ℝ)"),
	Case("Shadow","λ(x:ℝ).Λ(x:ℝ).x*λ[x]","ℝ→Distribution(ℝ)"),
	Case("FormalIntegral","integralD(λ(x:ℝ).δ(x))","Distribution(ℝ)"),
	Case("RetryObservationSigned","massD(weightD(λ(x:ℝ).x-3,"~retry~"))","ℝ","-2"),
	Case("RetryObservationPartialOutside","massD(weightD(λ(x:ℝ).1/(x-1),"~retry~"))","ℝ","0"),
	Case("RetryObservationZeroVisit","massD(weightD(λ(x:ℝ).1/x,μ(d:Distribution(ℝ)).addD(addD(scaleD(0,δ(0)),scaleD(1/4,δ(2))),scaleD(1/2,d))))","ℝ","undefined(ℝ)"),
	Case("RetryObservationPartialInside","massD(weightD(λ(x:ℝ).1/x,"~retry~"))","ℝ","undefined(ℝ)"),
	Case("RetryObservationBind","massD(bindD("~retry~",λ(x:ℝ).scaleD(x+1,δ((1:ℕ)))))","ℝ","2"),
	Case("RetryObservationRealBind","massD(bindD("~retry~",λ(x:ℝ).scaleD(x-4,δ(x))))","ℝ","-3"),
	Case("RetryObservationMappedMoment","massD(weightD(λ(y:ℝ).y²,bindD("~retry~",λ(x:ℝ).δ(x+1))))","ℝ","5"),
	Case("RetryObservationMappedNatural","massD(weightD(λ(y:ℕ).(y:ℝ),bindD("~retry~",λ(x:ℝ).δ((3:ℕ)))))","ℝ","3"),
	Case("RetryObservationFreeProbe","λ(f:ℝ→ℝ).massD(weightD(f,"~retry~"))","(ℝ→ℝ)→ℝ","λ(f:ℝ→ℝ). 2·(f(0)·(1/4)+f(2)·(1/4))"),
	Case("RetryObservationMissingProbe","massD(weightD(undefined(ℝ→ℝ),"~retry~"))","ℝ","undefined(ℝ)"),
	Case("RetryObservationMissingKernel","massD(bindD("~retry~",undefined(ℝ→Distribution(ℝ))))","ℝ","undefined(ℝ)"),
	Case("RetryObservationContinuousOutput","massD(bindD("~retry~",λ(x:ℝ).Λy. [0≤y≤1]·λ[y]))","ℝ","1"),
	Case("InfiniteSeriesVarying","λ(x:ℝ).densityAtD(sumD(λ(i:ℤ).δ((i:ℝ))),x)","ℝ→ℝ","λ(x:{x:ℝ | x≠floor(x)}). (0:ℝ)"),
	Case("SeriesFibreNaturalCounting","λ(x:ℝ).densityAtD(sumD(λ(i:ℕ).δ((i:ℝ))),x)","ℝ→ℝ","λ(x:{x:ℝ | x≠floorN(x)}). (0:ℝ)"),
	Case("SeriesFibreIntegerHit","densityAtD(sumD(λ(i:ℤ).δ((i:ℝ))),2)","ℝ","undefined(ℝ)"),
	Case("SeriesFibreIntegerGap","densityAtD(sumD(λ(i:ℤ).δ((i:ℝ))),1/2)","ℝ","0"),
	Case("SeriesFibreNaturalHit","densityAtD(sumD(λ(i:ℕ).δ((i:ℝ))),2)","ℝ","undefined(ℝ)"),
	Case("SeriesFibreNaturalGap","densityAtD(sumD(λ(i:ℕ).δ((i:ℝ))),-1)","ℝ","0"),
	Case("SeriesFibreNaturalRepeat","densityAtD(sumD(λ(i:ℕ).δ((0:ℝ))),0)","ℝ","undefined(ℝ)"),
	Case("SeriesFibreSigned","densityAtD(sumD(λ(i:ℤ).addD(δ((i:ℝ)),scaleD(-1,δ((i:ℝ))))),1)","ℝ","0"),
	Case("SeriesFibreLebesgue","densityAtD(sumD(λ(n:ℕ).scaleD((1/2)^(n+1),lebesgueD())),0)","ℝ","1"),
	Case("SeriesFibreParameter","λ(a:ℝ).λ(x:ℝ).densityAtD(sumD(λ(i:ℤ).δ(a+(i:ℝ))),x)","ℝ→ℝ→ℝ"),
	Case("SeriesFibreMissing","densityAtD(sumD(λ(i:ℤ).δ((i:ℝ))),undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("SeriesFibreMissingPoint","densityAtD(sumD(λ(i:ℕ).δ(undefined(ℝ))),2)","ℝ","undefined(ℝ)"),
	Case("SeriesFibreMissingRow","densityAtD(sumD(λ(i:ℕ).undefined(Distribution(ℝ))),2)","ℝ","undefined(ℝ)"),
	Case("RetryUnboundedMass","massD("~mixedLoop~")","ℝ","undefined(ℝ)"),
	Case("RetryUnboundedCancel","massD(weightD(λ(x:ℝ).x-1,"~mixedLoop~"))","ℝ","0"),
	Case("RetryUnboundedNegative","massD(weightD(λ(x:ℝ).x-3,"~mixedLoop~"))","ℝ","undefined(ℝ)"),
	Case("RetryUnboundedPartial","massD(weightD(λ(x:ℝ).x⁻¹,"~mixedLoop~"))","ℝ","undefined(ℝ)"),
	Case("RetryUnboundedPartialAway","massD(weightD(λ(x:ℝ).(x-1)⁻¹,"~mixedLoop~"))","ℝ","0"),
	Case("RetryUnboundedSupercritical","massD(weightD(λ(x:ℝ).x-1,μ(d:Distribution(ℝ)).addD(addD(δ(0),δ(2)),scaleD(3,d))))","ℝ","0"),
	Case("RetryUnboundedZeroWeightMissing","massD(weightD(λ(x:ℝ).x⁻¹,μ(d:Distribution(ℝ)).addD(addD(scaleD(0,δ(0)),scaleD(0,δ(2))),d)))","ℝ","undefined(ℝ)"),
	Case("RetryUnboundedZeroWeights","massD(μ(d:Distribution(ℝ)).addD(addD(scaleD(0,δ(0)),scaleD(0,δ(2))),d))","ℝ","0"),
	Case("RetryUnboundedBind","massD(bindD("~mixedLoop~",λ(x:ℝ).scaleD(x-1,δ((2:ℕ)))))","ℝ","0"),
	Case("RetryUnboundedRealBind","massD(weightD(λ(y:ℝ).y,bindD("~mixedLoop~",λ(x:ℝ).δ(x-1))))","ℝ","0"),
	Case("RetryUnboundedFreeProbe","λ(f:ℝ→ℝ).massD(weightD(f,"~mixedLoop~"))","(ℝ→ℝ)→ℝ","λ(f:{f:ℝ→ℝ | f(0)+f(2)=0}). (0:ℝ)"),
	Case("RetryUnboundedMissingProbe","massD(weightD(undefined(ℝ→ℝ),"~mixedLoop~"))","ℝ","undefined(ℝ)"),
	Case("LoopDensityCritical","λ(x:ℝ).densityAtD(μ(d:Distribution(ℝ)).addD(addD(δ(0),δ(2)),d),x)","ℝ→ℝ","λ(x:{x:ℝ | x≠0∧x≠2}). (0:ℝ)"),
	Case("LoopDensityZeroRatio","densityAtD(μ(d:Distribution(ℝ)).addD(addD(δ(0),δ(2)),scaleD(0,d)),2)","ℝ","undefined(ℝ)"),
	Case("LoopDensitySupercritical","densityAtD(μ(d:Distribution(ℝ)).addD(addD(δ(0),δ(2)),scaleD(3,d)),1)","ℝ","0"),
	Case("LoopDensitySupercriticalAt","densityAtD(μ(d:Distribution(ℝ)).addD(addD(δ(0),δ(2)),scaleD(3,d)),0)","ℝ","undefined(ℝ)"),
	Case("LoopDensityZeroWeight","densityAtD(μ(d:Distribution(ℝ)).addD(addD(scaleD(0,δ(0)),δ(2)),d),0)","ℝ","0"),
	Case("LoopDensityZeroWeightAt","densityAtD(μ(d:Distribution(ℝ)).addD(addD(scaleD(0,δ(0)),δ(2)),d),2)","ℝ","undefined(ℝ)"),
	Case("LoopDensityMissingSeed","densityAtD(μ(d:Distribution(ℝ)).addD(addD(δ(undefined(ℝ)),δ(2)),d),1)","ℝ","undefined(ℝ)"),
	Case("LoopDensityMissingQuery","densityAtD(μ(d:Distribution(ℝ)).addD(addD(δ(0),δ(2)),d),undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("LoopExistsCritical","defined(μ(d:Distribution(ℝ)).addD(addD(δ(0),δ(2)),d))","𝔹","true"),
	Case("LoopExistsSupercritical","defined(μ(d:Distribution(ℝ)).addD(addD(scaleD(0,δ(0)),δ(2)),scaleD(3,d)))","𝔹","true"),
	Case("LoopExistsContracting","defined("~retry~")","𝔹","true"),
	Case("LoopExistsHigher","defined(μ(d:Distribution(ℕ→ℕ)).addD(addD(δ(λ(n:ℕ).n),δ(λ(n:ℕ).n+1)),d))","𝔹","true"),
	Case("LoopExistsDistribution","defined(μ(d:Distribution(Distribution(ℝ))).addD(addD(δ(δ((0:ℝ))),δ(δ((2:ℝ)))),d))","𝔹","true"),
	Case("LoopExistsPartial","λ(x:ℝ).defined(μ(d:Distribution(ℝ)).addD(addD(δ(x⁻¹),δ(2)),d))","ℝ→𝔹","λ(x:ℝ). x≠0"),
	Case("LoopExistsMissing","defined(μ(d:Distribution(ℝ)).addD(addD(δ(undefined(ℝ)),δ(2)),d))","𝔹","false"),
	Case("InfiniteRetryFunction","μ(d:Distribution(ℕ→ℕ)).addD(δ(λ(n:ℕ).n),d)","Distribution(ℕ→ℕ)","Λ(x:ℕ→ℕ). (∑(i:ℤ). δ(λ(n:ℕ). n)[x])"),
	Case("InfiniteRetrySupercritical","μ(d:Distribution(ℝ)).addD(scaleD(3/4,δ(2)),scaleD(4,d))","Distribution(ℝ)","Λ(x:ℝ). (∑(i:ℤ). δ(2)[x])"),
	Case("InfiniteRetryMass","massD("~endless~")","ℝ","undefined(ℝ)"),
	Case("InfiniteRetryAt","densityAtD("~endless~",0)","ℝ","undefined(ℝ)"),
	Case("InfiniteRetryAway","densityAtD("~endless~",2)","ℝ","0"),
	Case("InfiniteRetryDensity","λ(x:ℝ).densityAtD("~endless~",x)","ℝ→ℝ","λ(x:{x:ℝ | x≠0}). (0:ℝ)"),
	Case("InfiniteRetryZeroProbe","massD(weightD(λ(x:ℝ).x,"~endless~"))","ℝ","0"),
	Case("InfiniteRetryNegativeProbe","massD(weightD(λ(x:ℝ).x-1,"~endless~"))","ℝ","undefined(ℝ)"),
	Case("InfiniteRetryMissing","μ(d:Distribution(ℝ)).addD(δ(undefined(ℝ)),d)","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("InfiniteRetryCaptured","λ(x:ℝ).μ(d:Distribution(ℝ)).addD(δ(x),d)","ℝ→Distribution(ℝ)","λ(x:ℝ). Λ(x1:ℝ). (∑(i:ℤ). δ(x)[x1])"),
	Case("InfiniteRetryDirectSeries","densityAtD(sumD(λ(i:ℤ).δ((0:ℝ))),1)","ℝ","0"),
	Case("WeightEmptyPartialBody","massD(weightD(λ(x:ℝ).undefined(ℝ),zeroD(ℝ)))","ℝ","0"),
	Case("WeightEmptyReciprocal","massD(weightD(λ(x:ℝ).1/x,zeroD(ℝ)))","ℝ","0"),
	Case("WeightEmptyMissing","massD(weightD(undefined(ℝ→ℝ),zeroD(ℝ)))","ℝ","undefined(ℝ)"),
	Case("WeightEmptyFunction","weightD(λ(k:ℕ→ℕ).undefined(ℝ),zeroD(ℕ→ℕ))","Distribution(ℕ→ℕ)","Λ(x:ℕ→ℕ). 0"),
	Case("WeightEmptyLoop","massD(weightD(λ(x:ℝ).undefined(ℝ),μ(d:Distribution(ℝ)).addD(d,d)))","ℝ","0"),
	Case("AffineBodyFair","μ(d:Distribution(ℝ)).scaleD(1/2,addD(δ(3),d))","Distribution(ℝ)","δ((3:ℝ))"),
	Case("AffineBodyWeight","μ(d:Distribution(ℝ)).Λx. 1/2·(δ(3)[x]+d[x])","Distribution(ℝ)","δ((3:ℝ))"),
	Case("AffineBodyConstant","μ(d:Distribution(ℝ)).δ(5)","Distribution(ℝ)","δ((5:ℝ))"),
	Case("AffineBodyConstantPair","μ(d:Distribution(ℝ)).addD(δ(0),δ(1))","Distribution(ℝ)","μ(d:Distribution(ℝ)). Λ(x:ℝ). δ(0)[x]+δ(1)[x]"),
	Case("AffineBodyPartial","μ(d:Distribution(ℝ)).scaleD(1/2,addD(undefined(Distribution(ℝ)),d))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("AffineBodyCapture","λ(x:ℝ).μ(d:Distribution(ℝ)).scaleD(1/2,addD(δ(x),d))","ℝ→Distribution(ℝ)","λ(x:ℝ). δ(x)"),
	Case("AffineBodyType","μ(d:Distribution(Type)).scaleD(1/2,addD(δ(Distribution(ℝ)),d))","Distribution(Type)","δ(Distribution(ℝ))"),
	Case("AffineBodySet","μ(d:Distribution(Set(ℝ))).scaleD(1/2,addD(δ({x:ℝ|x≠0}),d))","Distribution(Set(ℝ))","δ({x:ℝ | x≠0})"),
	Case("AffineBodyHigher","μ(d:Distribution(ℕ→ℕ)).scaleD(1/2,addD(δ(λ(n:ℕ).n),d))","Distribution(ℕ→ℕ)","δ(λ(n:ℕ). n)"),
	Case("AffineBodyMixed",twoArms,"Distribution(ℝ)","μ(d:Distribution(ℝ)). addD(Λ(x:ℝ). 1/4·δ(0)[x]+1/4·δ(2)[x],scaleD(1/2,d))"),
	Case("AffineBodyMass","massD("~twoArms~")","ℝ","1"),
	Case("AffineBodyFirstMoment","massD(weightD(λ(x:ℝ).x,"~twoArms~"))","ℝ","1"),
	Case("AffineBodyDuplicate","μ(d:Distribution(ℝ)).addD(scaleD(1/4,addD(δ(3),d)),scaleD(1/4,addD(δ(3),d)))","Distribution(ℝ)","δ((3:ℝ))"),
	Case("AffineBodyNested","μ(d:Distribution(ℝ)).scaleD(1/2,addD(addD(δ(2),d),scaleD(1/2,d)))","Distribution(ℝ)","Λ(x:ℝ). 2·δ(2)[x]"),
	Case("AffineBodyZeroVisit","massD(weightD(λ(x:ℝ).1/(x-1),μ(d:Distribution(ℝ)).addD(scaleD(1/2,addD(δ(0),d)),scaleD(0,δ(1)))))","ℝ","undefined(ℝ)"),
	Case("AffineBodyNoMass","μ(d:Distribution(ℝ)).scaleD(0,addD(δ(4),d))","Distribution(ℝ)","Λ(x:ℝ). 0·δ(4)[x]"),
	Case("RetryVisitsCoincident","μ(d:Distribution(ℝ)).addD(addD(scaleD(1/4,δ(2)),scaleD(1/4,δ(2))),scaleD(1/2,d))","Distribution(ℝ)","δ((2:ℝ))"),
	Case("RetryVisitsLeftEmpty","μ(d:Distribution(ℝ)).addD(addD(zeroD(ℝ),scaleD(1/2,δ(2))),scaleD(1/2,d))","Distribution(ℝ)","δ((2:ℝ))"),
	Case("RetryVisitsRightEmpty","μ(d:Distribution(ℝ)).addD(addD(scaleD(1/2,δ(2)),scaleD(8,zeroD(ℝ))),scaleD(1/2,d))","Distribution(ℝ)","δ((2:ℝ))"),
	Case("RetryVisitsEmpty","μ(d:Distribution(ℝ)).addD(addD(zeroD(ℝ),scaleD(2,zeroD(ℝ))),scaleD(3,d))","Distribution(ℝ)","Λ(x:ℝ). 0"),
	Case("RetryVisitsCritical","μ(d:Distribution(ℝ)).addD(scaleD(0,δ(2)),scaleD(1,d))","Distribution(ℝ)","Λ(x:ℝ). 0·δ(2)[x]"),
	Case("RetryVisitsSupercritical","massD(weightD(λ(x:ℝ).1/(2-x),μ(d:Distribution(ℝ)).addD(scaleD(0,δ(2)),scaleD(3,d))))","ℝ","undefined(ℝ)"),
	Case("RetryVisitsZeroDensity","λ(x:ℝ).densityAtD(μ(d:Distribution(ℝ)).addD(scaleD(0,δ(2)),scaleD(3,d)),x)","ℝ→ℝ","λ(x:ℝ). (0:ℝ)"),
	Case("RetryVisitsCapture","λ(x:ℝ).μ(d:Distribution(ℝ)).addD(addD(scaleD(1/4,δ(x)),scaleD(1/4,δ(x))),scaleD(1/2,d))","ℝ→Distribution(ℝ)","λ(x:ℝ). δ(x)"),
	Case("RetryVisitsDistinct","μ(d:Distribution(ℝ)).addD(addD(scaleD(0,δ(2)),scaleD(0,δ(3))),scaleD(2,d))","Distribution(ℝ)","μ(d:Distribution(ℝ)). addD(Λ(x:ℝ). 0·δ(2)[x]+0·δ(3)[x],scaleD(2,d))"),
	Case("LinearTailSelf","μ(d:Distribution(ℝ)).d","Distribution(ℝ)","Λ(x:ℝ). 0"),
	Case("LinearTailScaled","μ(d:Distribution(ℝ)).scaleD(2,d)","Distribution(ℝ)","Λ(x:ℝ). 0"),
	Case("LinearTailCopied","μ(d:Distribution(ℝ)).addD(d,d)","Distribution(ℝ)","Λ(x:ℝ). 0"),
	Case("LinearTailFunction","μ(d:Distribution(ℕ→ℕ)).addD(scaleD(9,d),scaleD(2,addD(d,d)))","Distribution(ℕ→ℕ)","Λ(x:ℕ→ℕ). 0"),
	Case("LinearTailEmissions","μ(d:Distribution(ℝ)).addD(scaleD(1/4,δ(7)),addD(scaleD(1/4,d),scaleD(1/2,d)))","Distribution(ℝ)","δ((7:ℝ))"),
	Case("LinearTailWeights","μ(d:Distribution(ℝ)).Λx. 1/4·δ(7)[x]+1/2·(1/2·d[x]+d[x])","Distribution(ℝ)","δ((7:ℝ))"),
	Case("LinearTailSwapped","μ(d:Distribution(ℝ)).addD(addD(scaleD(1/4,d),scaleD(1/4,d)),scaleD(1/2,δ(2)))","Distribution(ℝ)","δ((2:ℝ))"),
	Case("LinearTailUnitGain","μ(d:Distribution(ℝ)).addD(δ(0),d)","Distribution(ℝ)","Λ(x:ℝ). (∑(i:ℤ). δ(0)[x])"),
	Case("LinearTailNestedScale","μ(d:Distribution(ℝ)).addD(δ(3),scaleD(1/2,scaleD(1/2,d)))","Distribution(ℝ)","Λ(x:ℝ). 4/3·δ(3)[x]"),
	Case("LinearTailZeroVisit","μ(d:Distribution(ℝ)).addD(addD(scaleD(0,d),scaleD(0,d)),scaleD(0,δ(0)))","Distribution(ℝ)","Λ(x:ℝ). 0·δ(0)[x]"),
	Case("AtomicRetryFair","μ(d:Distribution(ℝ)).Λx. 1/2·δ(0)[x]+1/2·d[x]","Distribution(ℝ)","δ((0:ℝ))"),
	Case("AtomicRetrySwapped","μ(d:Distribution(ℝ)).Λx. 1/2·d[x]+1/2·δ(0)[x]","Distribution(ℝ)","δ((0:ℝ))"),
	Case("AtomicRetryFiniteWeight","μ(d:Distribution(ℝ)).addD(scaleD(1/4,δ(3)),scaleD(1/2,d))","Distribution(ℝ)","Λ(x:ℝ). 1/2·δ(3)[x]"),
	Case("AtomicRetryCapture","λ(x:ℝ).μ(d:Distribution(ℝ)).addD(scaleD(1/2,δ(x)),scaleD(1/2,d))","ℝ→Distribution(ℝ)","λ(x:ℝ). δ(x)"),
	Case("AtomicRetryFunction","μ(d:Distribution(ℕ→ℕ)).addD(scaleD(1/2,δ(λ(x:ℕ).x)),scaleD(1/2,d))","Distribution(ℕ→ℕ)","δ(λ(x:ℕ). x)"),
	Case("AtomicRetryHigher","μ(d:Distribution(Distribution(ℕ))).addD(scaleD(1/2,δ(δ(3))),scaleD(1/2,d))","Distribution(Distribution(ℕ))","δ(δ(3))"),
	Case("AtomicRetryZeroRatio","μ(d:Distribution(ℝ)).addD(δ(0),scaleD(0,d))","Distribution(ℝ)","δ((0:ℝ))"),
	Case("AtomicRetryZeroSeed","μ(d:Distribution(ℝ)).addD(zeroD(ℝ),scaleD(1,d))","Distribution(ℝ)","Λ(x:ℝ). 0"),
	Case("AtomicRetryMissing","μ(d:Distribution(ℝ)).addD(undefined(Distribution(ℝ)),scaleD(1/2,d))","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("AtomicRetryZeroVisit","massD(weightD(λ(x:ℝ).undefined(ℝ),μ(d:Distribution(ℝ)).addD(scaleD(0,δ(0)),scaleD(1/2,d))))","ℝ","undefined(ℝ)"),
	Case("AtomicRetryAtomDensity","densityAtD(μ(d:Distribution(ℝ)).Λx. 1/2·δ(0)[x]+1/2·d[x],0)","ℝ","undefined(ℝ)"),
	Case("AtomicRetryTwo","μ(d:Distribution(ℝ)).addD(addD(scaleD(1/4,δ(0)),scaleD(1/4,δ(1))),scaleD(1/2,d))","Distribution(ℝ)","μ(d:Distribution(ℝ)). addD(Λ(x:ℝ). 1/4·δ(0)[x]+1/4·δ(1)[x],scaleD(1/2,d))"),
	Case("AtomicRetryMass","massD(μ(d:Distribution(ℝ)).addD(addD(scaleD(1/4,δ(0)),scaleD(1/4,δ(1))),scaleD(1/2,d)))","ℝ","1"),
	Case("AtomicRetryDensity","λ(x:ℝ).densityAtD(μ(d:Distribution(ℝ)).addD(addD(scaleD(1/4,δ(0)),scaleD(1/4,δ(1))),scaleD(1/2,d)),x)","ℝ→ℝ","λ(x:{x:ℝ | x≠0∧x≠1}). (0:ℝ)"),
	Case("AtomicRetryUnitRatio","μ(d:Distribution(ℝ)).addD(δ(0),scaleD(1,d))","Distribution(ℝ)","Λ(x:ℝ). (∑(i:ℤ). δ(0)[x])"),
	Case("CountdownGeometric","λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(1/2,f(n sub 1)))(k))","ℕ→ℝ","λ(k:ℕ). ((1/2)^k:ℝ)"),
	Case("ObservedGuardSeed","λ(t:ℝ).massD(weightD(λ(x:ℝ).x,"~reflectAcross("5-x","δ(t)")~"))","ℝ→ℝ","λ(t:ℝ). t·(2/3)+10/3"),
	Case("ObservedGuardWeight","λ(p:𝔹).massD(weightD(λ(x:ℝ).x,guard(p,δ((3:ℝ)))))","𝔹→ℝ","λ(p:{p:𝔹 | p}). (3:ℝ)"),
	Case("ObservedGuardMass","λ(p:𝔹).massD(guard(p,δ((3:ℝ))))","𝔹→ℝ","λ(p:{p:𝔹 | p}). (1:ℝ)"),
	Case("ObservedGuardBind","λ(p:𝔹).massD(bindD(guard(p,δ((3:ℝ))),λ(x:ℝ).scaleD(x,δ(x))))","𝔹→ℝ","λ(p:{p:𝔹 | p}). (3:ℝ)"),
	Case("ObservedGuardDensity","λ(p:𝔹).densityAtD(guard(p,Λx.[x≠0]·λ[x]),0)","𝔹→ℝ","λ(p:{p:𝔹 | p}). (0:ℝ)"),
	Case("ObservedGuardPoint","λ(p:𝔹).densityAtD(Λx.[x≠0]·λ[x],guard(p,(1:ℝ)))","𝔹→ℝ","λ(p:{p:𝔹 | p}). (1:ℝ)"),
	Case("ObservedGuardCritical","defined(densityAtD(guard(true,δ((0:ℝ))),0))","𝔹","false"),
	Case("ObservedGuardAbsent","defined(massD(weightD(λ(x:ℝ).x,guard(undefined(𝔹),δ((3:ℝ))))))","𝔹","false"),
	Case("ObservedGuardEmpty","defined(massD(weightD(undefined(ℝ→ℝ),guard(true,zeroD(ℝ)))))","𝔹","false"),
	Case("ObservedGuardMasked","λ(p:𝔹).∫dx [p]·λ[x]","𝔹→ℝ","λ(p:𝔹). ∫dx [p]·λ[x]"),
	Case("ObservedGuardUnknown","λ(h:ℝ→ℝ).λ(t:ℝ).massD(weightD(h,guard(t≠0,δ(t))))","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(t:{t:ℝ | t≠0}). h(t)"),
	Case("ObservedGuardPartialPoint","defined(densityAtD(guard(false,Λx. λ[x]),(1:ℝ)))","𝔹","false"),
	Case("AffineCycleMass","massD("~reflectAcross()~")","ℝ","2"),
	Case("AffineCycleFirst","massD(weightD(λ(x:ℝ).x,"~reflectAcross()~"))","ℝ","4"),
	Case("AffineCycleSecond","massD(weightD(λ(x:ℝ).x^2,"~reflectAcross()~"))","ℝ","12"),
	Case("AffineCycleNested","massD(weightD(λ(x:ℝ).x,"~reflectAcross("2*(3-x/2)")~"))","ℝ","14/3"),
	Case("AffineCycleCenter","massD(weightD(λ(x:ℝ).x,"~reflectAcross("5-x","scaleD(1/2,δ((5/2:ℝ)))")~"))","ℝ","5/2"),
	Case("AffineCyclePartial","λ(h:ℝ→ℝ).massD(weightD(h,"~reflectAcross()~"))","(ℝ→ℝ)→ℝ"),
	Case("AffineCycleUnusedWeight","defined(massD(weightD(λ(x:ℝ).(x-4)⁻¹,"~reflectAcross("5-x","δ((1:ℝ))","0")~")))","𝔹","false"),
	Case("AffineCycleDiverges","defined(massD(weightD(λ(x:ℝ).x-2,"~reflectAcross("4-x","δ((1:ℝ))","1")~")))","𝔹","false"),
	Case("AffineCycleZero","massD(weightD(λ(x:ℝ).x-1,"~reflectAcross("2-x","δ((1:ℝ))","1")~"))","ℝ","0"),
	Case("AffineCycleFraction","massD(weightD(λ(x:ℝ).x,"~reflectAcross("1/2-x")~"))","ℝ","1"),
	Case("CycleBoolMass","massD("~flip()~")","ℝ","2"),
	Case("CycleBoolFalse","massD(weightD(λ(b:𝔹).[¬b],"~flip("scaleD(1/2,δ(false))")~"))","ℝ","2/3"),
	Case("CycleBoolTrue","massD(weightD(λ(b:𝔹).[b],"~flip("scaleD(1/2,δ(false))")~"))","ℝ","1/3"),
	Case("CycleBoolZero","massD(weightD(λ(b:𝔹).if b then undefined(ℝ) else 1,"~flip("δ(false)","0")~"))","ℝ","undefined(ℝ)"),
	Case("CycleBoolMissing","massD("~flip("δ(undefined(𝔹))")~")","ℝ","undefined(ℝ)"),
	Case("CycleDivergentMass","massD("~flip("δ(false)","1")~")","ℝ","undefined(ℝ)"),
	Case("CycleDivergentAlternation","massD(weightD(λ(x:ℝ).x,"~reflect("δ((2:ℝ))","2")~"))","ℝ","undefined(ℝ)"),
	Case("CycleDivergentBalanced","massD(weightD(λ(x:ℝ).x,"~reflect("addD(δ((2:ℝ)),δ((-2:ℝ)))","2")~"))","ℝ","0"),
	Case("CycleDivergentMissing","massD(weightD(λ(b:𝔹).if b then undefined(ℝ) else 0,"~flip("scaleD(0,δ(false))","2")~"))","ℝ","undefined(ℝ)"),
	Case("CycleDivergentZeroCharge","massD("~flip("scaleD(0,δ(false))","3")~")","ℝ","0"),
	Case("CycleDivergentBareAlternation","massD(weightD(λ(x:ℝ).x,μ(d:Distribution(ℝ)).addD(δ((2:ℝ)),bindD(d,λ(x:ℝ).δ(-x)))))","ℝ","undefined(ℝ)"),
	Case("CycleDivergentBareBalanced","massD(weightD(λ(x:ℝ).x,μ(d:Distribution(ℝ)).addD(addD(δ((2:ℝ)),δ((-2:ℝ))),bindD(d,λ(x:ℝ).δ(-x)))))","ℝ","0"),
	Case("InvolutionBare","μ(d:Distribution(ℝ)).addD(δ((1:ℝ)),bindD(d,λ(x:ℝ).δ(-x)))","Distribution(ℝ)"),
	Case("CycleRealMean","massD(weightD(λ(x:ℝ).x,"~reflect()~"))","ℝ","4/3"),
	Case("CycleRealConstant","massD(weightD(λ(x:ℝ).x^2,"~reflect()~"))","ℝ","8"),
	Case("CycleRealFixedPoint","massD(weightD(λ(x:ℝ).x+1,"~reflect("δ((0:ℝ))")~"))","ℝ","2"),
	Case("CycleRealMixture","massD(weightD(λ(x:ℝ).x,"~reflect("addD(δ((2:ℝ)),scaleD(1/2,δ((-2:ℝ))))")~"))","ℝ","2/3"),
	Case("CycleRealBind","massD(bindD("~reflect()~",λ(x:ℝ).scaleD(x,δ((0:ℕ)))))","ℝ","4/3"),
	Case("ReemitNat","massD("~shift("3","n")~")","ℝ","1"),
	Case("ReemitNatZeroRight","massD(weightD(λ(n:ℕ).(n:ℝ),"~shift("3","n+0")~"))","ℝ","3"),
	Case("ReemitNatZeroLeft","massD(weightD(λ(n:ℕ).(n:ℝ),"~shift("3","0+n")~"))","ℝ","3"),
	Case("ReemitMissing","massD("~shift("0 sub 1","n")~")","ℝ","undefined(ℝ)"),
	Case("ReemitReal","densityAtD(μ(d:Distribution(ℝ)).addD(δ((2:ℝ)),scaleD(1/2,bindD(d,λ(x:ℝ).δ(x)))),2)","ℝ","undefined(ℝ)"),
	Case("ReemitOutside","densityAtD(μ(d:Distribution(ℝ)).addD(δ((2:ℝ)),scaleD(1/2,bindD(d,λ(x:ℝ).δ(x)))),3)","ℝ","0"),
	Case("ReemitFunction","massD(μ(d:Distribution(ℕ→ℕ)).addD(δ(λ(n:ℕ).n),scaleD(1/2,bindD(d,λ(f:ℕ→ℕ).δ(f)))))","ℝ","2"),
	Case("ReemitNested","massD(μ(d:Distribution(Distribution(ℕ))).addD(δ(δ((2:ℕ))),scaleD(1/2,bindD(d,λ(u:Distribution(ℕ)).δ(u)))))","ℝ","2"),
	Case("ReemitAffine","massD(μ(d:Distribution(ℕ)).bindD(addD(δ((2:ℕ)),scaleD(1/4,d)),λ(n:ℕ).δ(n)))","ℝ","4/3"),
	Case("ShiftOrbitBare",counter,"Distribution(ℕ)"),
	Case("ShiftOrbitMass","massD("~counter~")","ℝ","1"),
	Case("ShiftOrbitMean","massD(weightD(λ(n:ℕ).(n:ℝ),"~counter~"))","ℝ","1"),
	Case("ShiftOrbitAlternating","massD(weightD(λ(n:ℕ).(-1:ℝ)^n,"~counter~"))","ℝ","1/3"),
	Case("ShiftOrbitAmplified","massD(weightD(λ(n:ℕ).(2:ℝ)^n,"~counter~"))","ℝ","undefined(ℝ)"),
	Case("ShiftOrbitSecond","massD(weightD(λ(n:ℕ).(n:ℝ)^2,"~counter~"))","ℝ","3"),
	Case("ShiftOrbitCubic","massD(weightD(λ(n:ℕ).(n:ℝ)^3,"~counter~"))","ℝ","13"),
	Case("ShiftOrbitSixth","massD(weightD(λ(n:ℕ).(n:ℝ)^6,"~counter~"))","ℝ","4683"),
	Case("ShiftOrbitPolynomial","massD(weightD(λ(n:ℕ).2*(n:ℝ)^3-3*(n:ℝ)+4,"~counter~"))","ℝ","27"),
	Case("ShiftOrbitPowerOfSum","massD(weightD(λ(n:ℕ).(1+(n:ℝ))^12,"~counter~"))","ℝ","56183135190"),
	Case("ShiftOrbitFractional","massD(weightD(λ(n:ℕ).(1/3*(n:ℝ)-1/2)^2,"~shift("0","n+1","1/3","2/3")~"))","ℝ","25/36"),
	Case("ShiftOrbitOffsetSquare","massD(weightD(λ(n:ℕ).(n:ℝ)^2,"~shift("3","2+n")~"))","ℝ","33"),
	Case("ShiftOrbitUnnormalizedSecond","massD(weightD(λ(n:ℕ).(n:ℝ)^2,"~shift("0","n+1","2")~"))","ℝ","12"),
	Case("ShiftOrbitStride","massD(weightD(λ(n:ℕ).(n:ℝ),"~shift("3","2+n")~"))","ℝ","5"),
	Case("ShiftOrbitEven","massD(weightD(λ(n:ℕ).(n:ℝ),"~shift("0","n+2")~"))","ℝ","2"),
	Case("ShiftOrbitOffset","massD(weightD(λ(n:ℕ).(n:ℝ),"~shift("3")~"))","ℝ","4"),
	Case("ShiftOrbitUnnormalized","massD("~shift("0","n+1","2")~")","ℝ","4"),
	Case("ShiftOrbitUnitEmission","massD("~shift("0","n+1","")~")","ℝ","2"),
	Case("ShiftOrbitNoRetry","massD("~shift("0","n+1","1/2","0")~")","ℝ","1/2"),
	Case("ShiftOrbitDiverges","massD("~shift("0","n+1","1","1")~")","ℝ","undefined(ℝ)"),
	Case("ShiftOrbitMissing","massD("~shift("undefined(ℕ)")~")","ℝ","undefined(ℝ)"),
	Case("ShiftOrbitProbe","λ(f:ℕ→ℝ).massD(weightD(f,"~counter~"))","(ℕ→ℝ)→ℝ"),
	Case("ShiftOrbitPole","massD(weightD(λ(n:ℕ).1/((n:ℝ)-2),"~counter~"))","ℝ","undefined(ℝ)"),
	Case("ShiftOrbitPoleAfterZero","massD(weightD(λ(n:ℕ).1/((n:ℝ)-2),"~shift("0","n+1","1/2","0")~"))","ℝ","undefined(ℝ)"),
	Case("ShiftOrbitBind","massD(bindD("~counter~",λ(n:ℕ).scaleD(2,δ(n))))","ℝ"),
	Case("ShiftOrbitStart","λ(a:ℕ).massD("~shift("a")~")","ℕ→ℝ","λ(a:ℕ). (1:ℝ)"),
	Case("ShiftOrbitZeroCharge","massD("~shift("0","n+1","0","2")~")","ℝ","0"),
	Case("ShiftOrbitMissingProbe","massD(weightD(λ(n:ℕ).undefined(ℝ),"~shift("0","n+1","0","0")~"))","ℝ","undefined(ℝ)"),
	Case("PrintedOperandBinder","λ(qsymOperand0:ℝ).λ(h:ℝ→ℝ).h(qsymOperand0)^2+qsymOperand0","ℝ→(ℝ→ℝ)→ℝ","λ(qsymOperand0:ℝ). λ(h:ℝ→ℝ). h(qsymOperand0)^2+qsymOperand0"),
	Case("PrintedOperandFraction","λ(h:ℝ→ℝ).h(1/2)","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). h(1/2)"),
	Case("PrintedOperandDisjunction","λ(p:𝔹).λ(q:𝔹).λ(x:ℝ).maskR(p,[q∨x<0])","𝔹→𝔹→ℝ→ℝ","λ(p:𝔹). λ(q:𝔹). λ(x:ℝ). [p∧(q∨x<0)]"),
	Case("PrintedOperandSignedIndicator","λ(p:𝔹).λ(q:𝔹).λ(x:ℝ).maskR(p,-([q∨x<0]:ℝ))","𝔹→𝔹→ℝ→ℝ","λ(p:𝔹). λ(q:𝔹). λ(x:ℝ). [p]·mulR(-1,[q∨x<0])"),

	Case("PrintedOperandParity","λ(l:ℝ).λ(u:ℝ).mulR(powRZ(-1,floor(l)),sin(u))","ℝ→ℝ→ℝ","λ(l:ℝ). λ(u:ℝ). (-1:ℝ)^floor(l)·sin(u)"),
	Case("PrintedOperandComplexPower","λ(h:ℕ→ℕ).λ(k:ℕ).mulC(powCN(toℂ(h(2)),k),ⅈ)","(ℕ→ℕ)→ℕ→ℂ","λ(h:ℕ→ℕ). λ(k:ℕ). ⅈ·(h(2):ℂ)^k"),
	Case("PrintedOperandIntegerPower","λ(h:ℕ→ℕ).λ(k:ℤ).mulR(powRZ(toℝ(h(1)),k),sin(1))","(ℕ→ℕ)→ℤ→ℝ","λ(h:ℕ→ℕ). λ(k:ℤ). (h(1):ℝ)^k·sin(1)"),
	Case("PrintedOperandKnownBase","λ(h:ℕ→ℝ).λ(k:ℤ).powRZ(h(0),k)","(ℕ→ℝ)→ℤ→ℝ","λ(h:ℕ→ℝ). λ(k:ℤ). h(0)^k"),
	Case("PrintedOperandOverload","λ(h:ℕ→ℕ).λ(k:ℕ).powRN(toℝ(h(1)),k)","(ℕ→ℕ)→ℕ→ℝ","λ(h:ℕ→ℕ). λ(k:ℕ). (h(1):ℝ)^k"),
	Case("MaskContextHigher","λ(h:ℝ→ℝ).λ(x:ℝ).[h(x)≠0]·abs(h(x))","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). abs(h(x))"),
	Case("MaskContextWeight","λ(h:ℝ→ℝ).Λx. [h(x)≠0]·(2·abs(h(x)))·λ[x]","(ℝ→ℝ)→Distribution(ℝ)","λ(h:ℝ→ℝ). Λ(x:ℝ). (2·abs(h(x)))·λ[x]"),
	Case("MaskContextRepeated","λ(h:ℝ→ℝ).λ(x:ℝ).[h(x)≠0]·(h(x)·(h(x)-1))","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). h(x)·(h(x)-1)"),
	Case("MaskContextSine","λ(x:ℝ).[sin(x)≠0]·abs(sin(x))","ℝ→ℝ","λ(x:ℝ). abs(sin(x))"),
	Case("MaskContextCosine","λ(h:ℝ→ℝ).λ(x:ℝ).[h(x)≠0]·(cos(h(x))-1)","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). cos(h(x))-1"),
	Case("MaskContextReciprocal","λ(h:ℝ→ℝ).λ(x:ℝ).[h(x)≠0]·h(x)⁻¹","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). [h(x)≠0]·h(x)⁻¹"),
	Case("MaskContextNonstrict","λ(h:ℝ→ℝ).λ(x:ℝ).[h(x)≠0]·([false]·h(x))","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). [h(x)≠0]·0"),
	Case("MaskContextOtherPoint","λ(h:ℝ→ℝ).λ(x:ℝ).[h(x)≠0]·abs(h(x+1))","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). [h(x)≠0]·abs(h(x+1))"),
	Case("MaskContextMissing","defined((λ(h:ℝ→ℝ).λ(x:ℝ).[h(x)≠0]·abs(h(x)))(λ(x:ℝ).x⁻¹)(0))","𝔹","false"),
	Case("MaskContextMissingGuard","defined((λ(h:ℝ→ℝ).λ(x:ℝ).[h(x)≠0]·([false]·h(x)))(λ(x:ℝ).x⁻¹)(0))","𝔹","false"),
	Case("OpaquePunctureWeight","λ(h:ℝ→ℝ).λ(x:ℝ).[x≠3∧cos(x-3)<0]·h(x)","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). [cos(x-3)<0]·h(x)"),
	Case("OpaquePunctureKept","λ(h:ℝ→ℝ).λ(x:ℝ).[x≠3∧cos(x-3)>0]·h(x)","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). [x≠3∧0<cos(x-3)]·h(x)"),
	Case("OpaquePuncturePrefix","λ(k:ℝ→𝔹).λ(h:ℝ→ℝ).λ(x:ℝ).[x≠3∧(cos(x-3)<0∧k(x))]·h(x)","(ℝ→𝔹)→(ℝ→ℝ)→ℝ→ℝ","λ(k:ℝ→𝔹). λ(h:ℝ→ℝ). λ(x:ℝ). [cos(x-3)<0∧k(x)]·h(x)"),
	Case("OpaquePunctureOrder","λ(k:ℝ→𝔹).λ(h:ℝ→ℝ).λ(x:ℝ).[x≠3∧(k(x)∧cos(x-3)<0)]·h(x)","(ℝ→𝔹)→(ℝ→ℝ)→ℝ→ℝ","λ(k:ℝ→𝔹). λ(h:ℝ→ℝ). λ(x:ℝ). [x≠3∧(k(x)∧cos(x-3)<0)]·h(x)"),
	Case("OpaquePunctureSquare","λ(h:ℝ→ℝ).λ(x:ℝ).[x≠2∧x^2<3]·h(x)","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). [-sqrt(3)<x∧x<sqrt(3)]·h(x)"),
	Case("OpaquePunctureDensity","λ(h:ℝ→ℝ).Λx. [x≠3∧cos(x-3)<0]·h(x)·λ[x]","(ℝ→ℝ)→Distribution(ℝ)","λ(h:ℝ→ℝ). Λ(x:ℝ). ([cos(x-3)<0]·h(x))·λ[x]"),
	Case("OpaquePunctureAt","(λ(h:ℝ→ℝ).λ(x:ℝ).[x≠3∧cos(x-3)<0]·h(x))(λ(x:ℝ).(x-3)⁻¹)(3)","ℝ","0"),
	Case("OrderedPunctureCoordinate","Λx. [x≠3∧x<4]·λ[(x-3)^2]","Distribution(ℝ)","Λ(x:ℝ). ([x<4]·abs(2·x-6))·λ[x]"),
	Case("OrderedPunctureLeft","λ(x:ℝ).[x≠3∧cos(x-3)>0∧x≠4]·abs(x-3)","ℝ→ℝ","λ(x:ℝ). [0<cos(x-3)∧x≠4]·abs(x-3)"),
	Case("OrderedPunctureRight","λ(x:ℝ).[x≠3∧(x≠4∧cos(x-3)>0)]·abs(x-3)","ℝ→ℝ","λ(x:ℝ). [x≠4∧0<cos(x-3)]·abs(x-3)"),
	Case("OrderedPunctureHiddenPole","λ(x:ℝ).[x≠3∧cos(x-3)<0]·(x-3)⁻¹","ℝ→ℝ","λ(x:ℝ). [cos(x-3)<0]·(x-3)⁻¹"),
	Case("OrderedPunctureExposedPole","λ(x:ℝ).[x≠3∧cos(x-3)>0]·(x-3)⁻¹","ℝ→ℝ","λ(x:ℝ). [x≠3∧0<cos(x-3)]·(x-3)⁻¹"),
	Case("OrderedPunctureAfterPartial","λ(h:ℝ→𝔹).λ(x:ℝ).[h(x)∧(x≠3∧cos(x-3)>0)]·abs(x-3)","(ℝ→𝔹)→ℝ→ℝ","λ(h:ℝ→𝔹). λ(x:ℝ). [h(x)∧0<cos(x-3)]·abs(x-3)"),
	Case("OrderedPunctureAt","densityAtD(Λx. [x≠3∧x<4]·λ[(x-3)^2],3)","ℝ","0"),
	Case("OrderedPunctureCut","densityAtD(Λx. [x≠3∧x<4]·λ[(x-3)^2],4)","ℝ","0"),
	Case("OrderedPunctureMass","∫dx [2≤x≤4]·[x≠3∧x<4]·λ[(x-3)^2]","ℝ","2"),
	Case("MaskRootCoordinate","Λx. [x≠3]·λ[(x-3)^2]","Distribution(ℝ)","Λ(x:ℝ). (abs(2·x-6))·λ[x]"),
	Case("MaskRootFraction","Λx. [x≠1/2]·abs(2*x-1)·λ[x]","Distribution(ℝ)","Λ(x:ℝ). (abs(2·x-1))·λ[x]"),
	Case("MaskRootPolynomial","λ(x:ℝ).[x^2≠1]·abs(x^2-1)","ℝ→ℝ","λ(x:ℝ). abs(x^2-1)"),
	Case("MaskRootThree","λ(x:ℝ).[x≠1∧x≠2∧x≠3]·((x-1)*(x-2)*(x-3))","ℝ→ℝ","λ(x:ℝ). (x-3)·(x-2)·(x-1)"),
	Case("MaskRootOneKept","λ(x:ℝ).[x≠2∧x≠3]·abs(x-3)","ℝ→ℝ","λ(x:ℝ). [x≠2]·abs(x-3)"),
	Case("MaskRootAfterPartial","λ(h:ℝ→𝔹).λ(x:ℝ).[h(x)∧x≠3]·abs(x-3)","(ℝ→𝔹)→ℝ→ℝ","λ(h:ℝ→𝔹). λ(x:ℝ). [h(x)]·abs(x-3)"),
	Case("MaskRootBeforePartial","λ(h:ℝ→𝔹).λ(x:ℝ).[x≠3∧h(x)]·abs(x-3)","(ℝ→𝔹)→ℝ→ℝ","λ(h:ℝ→𝔹). λ(x:ℝ). [x≠3∧h(x)]·abs(x-3)"),
	Case("MaskRootPole","λ(x:ℝ).[x≠2]·(x-2)⁻¹","ℝ→ℝ","λ(x:ℝ). [x≠2]·(x-2)⁻¹"),
	Case("MaskRootAt","densityAtD(Λx. [x≠3]·λ[(x-3)^2],3)","ℝ","0"),
	Case("MaskRootOff","densityAtD(Λx. [x≠3]·λ[(x-3)^2],4)","ℝ","2"),
	Case("MaskRootMass","∫dx [2≤x≤4]·[x≠3]·λ[(x-3)^2]","ℝ","2"),
	Case("EraseMaskNatural","λ(k:ℕ).[k≠0]·k","ℕ→ℕ","λ(k:ℕ). k"),
	Case("EraseMaskInteger","λ(i:ℤ).[i≠0]·(-2*i)","ℤ→ℤ","λ(i:ℤ). -2·i"),
	Case("EraseMaskRational","λ(q:ℚ).[q≠0]·q^2","ℚ→ℚ","λ(q:ℚ). q^2"),
	Case("EraseMaskComplex","λ(z:ℂ).[z≠0]·z","ℂ→ℂ","λ(z:ℂ). z"),
	Case("EraseMaskJacobian","Λx. [x≠0]·(2·abs(x))·λ[x]","Distribution(ℝ)","Λ(x:ℝ). (2·abs(x))·λ[x]"),
	Case("EraseMaskExponential","λ(x:ℝ).[x≠0]·(exp(x)-1)","ℝ→ℝ","λ(x:ℝ). exp(x)-1"),
	Case("KeepMaskReciprocal","λ(x:ℝ).[x≠0]·x⁻¹","ℝ→ℝ","λ(x:ℝ). [x≠0]·x⁻¹"),
	Case("KeepMaskHigher","λ(h:ℝ→ℝ).λ(x:ℝ).[x≠0]·(h(x)·x)","(ℝ→ℝ)→ℝ→ℝ","λ(h:ℝ→ℝ). λ(x:ℝ). [x≠0]·(x·h(x))"),
	Case("KeepMaskLebesgue","Λx. [x≠0]·λ[x]","Distribution(ℝ)","Λ(x:ℝ). [x≠0]·λ[x]"),
	Case("IndexedVisitCount","λ(k:ℕ).massD("~indexedAtoms~"(k))","ℕ→ℝ","λ(k:ℕ). (k:ℝ)"),
	Case("IndexedVisitFirstMoment","λ(k:ℕ).massD(weightD(λ(x:ℝ).x,"~indexedAtoms~"(k)))","ℕ→ℝ","λ(k:ℕ). (k·(1/2·k+1/2):ℝ)"),
	Case("IndexedVisitSecondMoment","λ(k:ℕ).massD(weightD(λ(x:ℝ).x^2,"~indexedAtoms~"(k)))","ℕ→ℝ","λ(k:ℕ). (k·(k·(1/3·k+1/2)+1/6):ℝ)"),
	Case("IndexedVisitThousand","massD(weightD(λ(x:ℝ).x,"~indexedAtoms~"(1000)))","ℝ","500500"),
	Case("IndexedVisitHigher","λ(h:ℝ→ℝ).λ(k:ℕ).massD(weightD(h,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else addD(δ((n:ℝ)),f(n sub 1)))(k)))","(ℝ→ℝ)→ℕ→ℝ","λ(h:ℝ→ℝ). λ(k:ℕ). h(0)+(∑(i:ℕ). [i<k]·(h((i+1:ℝ))))"),
	Case("IndexedVisitOffset","λ(t:ℝ).λ(k:ℕ).massD(weightD(λ(x:ℝ).x,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ(t) else addD(scaleD(1,f(n sub 1)),δ((n:ℝ)+t)))(k)))","ℝ→ℕ→ℝ","λ(t:ℝ). λ(k:ℕ). t+[k≠0]·(t·k)+k·(1/2·k+1/2)"),
	Case("IndexedVisitEmpty","massD(weightD(λ(x:ℝ).(x-2)⁻¹,"~indexedAtoms~"(0)))","ℝ","0"),
	Case("IndexedVisitBeforeHole","massD(weightD(λ(x:ℝ).(x-2)⁻¹,"~indexedAtoms~"(1)))","ℝ","-1"),
	Case("IndexedVisitIncludesHole","defined(massD(weightD(λ(x:ℝ).(x-2)⁻¹,"~indexedAtoms~"(3))))","𝔹","false"),
	Case("IndexedVisitMissingIndex","defined(massD("~indexedAtoms~"(0 sub 1)))","𝔹","false"),
	Case("UnitEmissionMass","λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else addD(δ((1:ℝ)),f(n sub 1)))(k))","ℕ→ℝ","λ(k:ℕ). (k+1:ℝ)"),
	Case("UnitEmissionWeighted","λ(k:ℕ).massD(weightD(λ(x:ℝ).x,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((5:ℝ)) else addD(f(n sub 1),δ((-2:ℝ))))(k)))","ℕ→ℝ","λ(k:ℕ). (-2·k+5:ℝ)"),
	Case("UnitEmissionMillion","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then zeroD(ℝ) else addD(f(n sub 1),δ((3:ℝ))))(1000000))","ℝ","1000000"),
	Case("UnitEmissionUnused","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((3:ℝ)) else addD(f(n sub 1),undefined(Distribution(ℝ))))(0))","ℝ","1"),
	Case("UnitEmissionMissing","defined(massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((3:ℝ)) else addD(f(n sub 1),undefined(Distribution(ℝ))))(1)))","𝔹","false"),
	Case("UnitEmissionHigher","λ(h:ℝ→ℝ).λ(k:ℕ).massD(weightD(h,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((5:ℝ)) else addD(δ((2:ℝ)),f(n sub 1)))(k)))","(ℝ→ℝ)→ℕ→ℝ","λ(h:ℝ→ℝ). λ(k:ℕ). h(5)+[k≠0]·(h(2)·k)"),
	Case("EmittingSeries","λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then zeroD(ℝ) else addD(δ((3:ℝ)),scaleD(1/2,f(n sub 1))))(k))","ℕ→ℝ","λ(k:ℕ). (-2·(1/2)^k+2:ℝ)"),
	Case("EmittingWeighted","λ(k:ℕ).massD(weightD(λ(x:ℝ).x,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((5:ℝ)) else addD(scaleD(1/2,f(n sub 1)),δ((2:ℝ))))(k)))","ℕ→ℝ","λ(k:ℕ). [k=0]·5+[k≠0]·((1/2)^k+4)"),
	Case("EmittingThousand","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else addD(δ((2:ℝ)),scaleD(1,f(n sub 1))))(1000))","ℝ","1001"),
	Case("EmittingSigned","λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then zeroD(ℝ) else addD(δ((3:ℝ)),scaleD(-1,f(n sub 1))))(k))","ℕ→ℝ","λ(k:ℕ). (-1/2·(-1)^k+1/2:ℝ)"),
	Case("EmittingUnused","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else addD(undefined(Distribution(ℝ)),scaleD(undefined(ℝ),f(n sub 1))))(0))","ℝ","1"),
	Case("EmittingMissing","defined(massD(weightD(λ(x:ℝ).x⁻¹,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((2:ℝ)) else addD(δ((0:ℝ)),scaleD(0,f(n sub 1))))(2))))","𝔹","false"),
	Case("EmittingParameter","λ(r:ℝ).λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then zeroD(ℝ) else addD(δ((1:ℝ)),scaleD(r,f(n sub 1))))(k))","ℝ→ℕ→ℝ"),
	Case("VaryingEmission","λ(k:ℕ).massD("~discountedAtoms("k")~")","ℕ→ℝ","λ(k:ℕ). ((1/2)^k·(2·2^k-2):ℝ)"),
	Case("ConvolutionSymbolic","λ(r:ℝ).λ(k:ℕ).massD(weightD(λ(x:ℝ).x,"~discountedAtoms("k","r","δ((3:ℝ))")~"))","ℝ→ℕ→ℝ"),
	Case("ConvolutionTwo","λ(r:ℝ).massD(weightD(λ(x:ℝ).x,"~discountedAtoms("2","r","δ((3:ℝ))")~"))","ℝ→ℝ","λ(r:ℝ). 3·r^2+r+2"),
	Case("StableApplicationSum","λ(h:ℝ→ℝ).h(3)+h(1)+h(2)+h(0)","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). h(0)+h(1)+h(2)+h(3)"),
	Case("StableApplicationRows","λ(h:ℝ→ℝ).∑(i:ℕ).[i<4]·(h((i:ℝ)))","(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). h(0)+h(1)+h(2)+h(3)"),
	Case("StableApplicationNested","λ(h:ℝ→ℝ).λ(g:ℝ→ℝ).h(g(2))+g(h(1))+h(g(0))","(ℝ→ℝ)→(ℝ→ℝ)→ℝ","λ(h:ℝ→ℝ). λ(g:ℝ→ℝ). g(h(1))+h(g(0))+h(g(2))"),
	Case("StableApplicationShadow","λ(qsymOperand0:ℝ).λ(h:ℝ→ℝ).h(qsymOperand0)+h(2)","ℝ→(ℝ→ℝ)→ℝ","λ(qsymOperand0:ℝ). λ(h:ℝ→ℝ). h(2)+h(qsymOperand0)"),
	Case("OpaqueUnitPairLeft","λ(h:ℝ→ℝ).λ(n:ℕ).(n+1:ℝ)*(h((n:ℝ))*(n+1:ℝ)⁻¹)","(ℝ→ℝ)→ℕ→ℝ","λ(h:ℝ→ℝ). λ(n:ℕ). h((n:ℝ))"),
	Case("OpaqueUnitPairInner","λ(h:ℝ→ℝ).λ(n:ℕ).(n+1:ℝ)*((n+1:ℝ)⁻¹*h((n:ℝ)))","(ℝ→ℝ)→ℕ→ℝ","λ(h:ℝ→ℝ). λ(n:ℕ). h((n:ℝ))"),
	Case("OpaqueUnitPairRight","λ(h:ℝ→ℝ).λ(n:ℕ).((n+1:ℝ)⁻¹*h((n:ℝ)))*(n+1:ℝ)","(ℝ→ℝ)→ℕ→ℝ","λ(h:ℝ→ℝ). λ(n:ℕ). h((n:ℝ))"),
	Case("OpaqueUnitPairRational","λ(h:ℝ→ℝ).λ(n:ℕ).(n+1)⁻¹*(h((n:ℝ))*(n+1))","(ℝ→ℝ)→ℕ→ℝ","λ(h:ℝ→ℝ). λ(n:ℕ). h((n:ℝ))"),
	Case("OpaqueUnitPairZero","λ(h:ℝ→ℝ).λ(n:ℕ).(n:ℝ)*(h((n:ℝ))*0)","(ℝ→ℝ)→ℕ→ℝ"),
	Case("OpaqueUnitPairPole","λ(h:ℝ→ℝ).λ(n:ℕ).(n:ℝ)*(h((n:ℝ))*(n:ℝ)⁻¹)","(ℝ→ℝ)→ℕ→ℝ","λ(h:ℝ→ℝ). λ(n:{n:ℕ | n≠0}). h((n:ℝ))"),
	Case("OpaqueUnitPairAtPole","defined((λ(h:ℝ→ℝ).λ(n:ℕ).(n:ℝ)*(h((n:ℝ))*(n:ℝ)⁻¹))(λ(x:ℝ).1)(0))","𝔹","false"),
	Case("OpaqueUnitPairMissing","defined((λ(h:ℝ→ℝ).λ(n:ℕ).(n+1:ℝ)*(h((n:ℝ))*(n+1:ℝ)⁻¹))(λ(x:ℝ).(x-2)⁻¹)(2))","𝔹","false"),
	Case("IntegratingFactorMass","λ(k:ℕ).massD("~discountedAtoms("k","n/(n+1)")~")","ℕ→ℝ","λ(k:ℕ). (k·(k+1)⁻¹·(1/2·k+3/2):ℝ)"),
	Case("IntegratingFactorMean","λ(k:ℕ).massD(weightD(λ(x:ℝ).x,"~discountedAtoms("k","n/(n+1)","zeroD(ℝ)",true)~"))","ℕ→ℝ"),
	Case("IntegratingFactorMillion","massD(weightD(λ(x:ℝ).x,"~discountedAtoms("1000000","n/(n+1)")~"))","ℝ","333334000000"),
	Case("IntegratingFactorHigher","λ(h:ℝ→ℝ).λ(k:ℕ).massD(weightD(h,"~discountedAtoms("k","n/(n+1)","δ((7:ℝ))")~"))","(ℝ→ℝ)→ℕ→ℝ"),
	Case("IntegratingFactorHarmonic","λ(k:ℕ).massD("~discountedAtoms("k","(n+1)/n")~")","ℕ→ℝ"),
	Case("IntegratingFactorGap","λ(k:ℕ).massD("~discountedAtoms("k","n/(n+2)")~")","ℕ→ℝ"),
	Case("IntegratingFactorBeforeHole","massD(weightD(λ(x:ℝ).(x-2)⁻¹,"~discountedAtoms("1","n/(n+1)")~"))","ℝ","-1"),
	Case("IntegratingFactorAtHole","defined(massD(weightD(λ(x:ℝ).(x-2)⁻¹,"~discountedAtoms("3","n/(n+1)")~")))","𝔹","false"),
	Case("IntegratingFactorSeed","defined(massD("~discountedAtoms("3","n/(n+1)","undefined(Distribution(ℝ))")~"))","𝔹","false"),
	Case("IntegratingFactorMissingIndex","defined(massD("~discountedAtoms("0 sub 1","n/(n+1)")~"))","𝔹","false"),
	Case("IntegratingFactorEmpty","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((3:ℝ)) else addD(undefined(Distribution(ℝ)),scaleD(n/(n+1),f(n sub 1))))(0))","ℝ","1"),
	Case("IntegratingFactorMissingEmission","defined(massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((3:ℝ)) else addD(undefined(Distribution(ℝ)),scaleD(n/(n+1),f(n sub 1))))(1)))","𝔹","false"),
	Case("IntegratingFactorPole","λ(k:ℕ).massD("~discountedAtoms("k","(n+1)/(n-1)")~")","ℕ→ℝ"),
	Case("UniformCountdownFive","massD("~uniformCountdown~"(5))","ℝ","1"),
	Case("UniformCountdownFiveMean","massD(weightD(λ(x:ℝ).x,"~uniformCountdown~"(5)))","ℝ","5/2"),
	Case("UniformCountdownFiveSecond","massD(weightD(λ(x:ℝ).x^2,"~uniformCountdown~"(5)))","ℝ","55/6"),
	Case("SmallRangePolynomial","∑(i:ℕ).[i<8]·((i:ℝ)^2+i+1)","ℝ","176"),
	Case("SmallRangePartial","defined(∑(i:ℕ).[i<4]·(i-2:ℝ)⁻¹)","𝔹","false"),
	Case("UniformCountdownMass","λ(k:ℕ).massD("~uniformCountdown~"(k))","ℕ→ℝ","λ(k:ℕ). (1:ℝ)"),
	Case("UniformCountdownMean","massD(weightD(λ(x:ℝ).x,"~uniformCountdown~"(1000000)))","ℝ","500000"),
	Case("UniformCountdownSecond","massD(weightD(λ(x:ℝ).x^2,"~uniformCountdown~"(1000000)))","ℝ","333333500000"),
	Case("UniformCountdownProbe","λ(h:ℝ→ℝ).λ(k:ℕ).massD(weightD(h,"~uniformCountdown~"(k)))","(ℝ→ℝ)→ℕ→ℝ"),
	Case("ExactProductLifted","λ(k:ℕ). 2*(k:ℝ)*(k+1)⁻¹*(k+3/2)","ℕ→ℝ","λ(k:ℕ). (2·k·(k+1)⁻¹·(k+3/2):ℝ)"),
	Case("ExactProductGrouped","λ(k:ℕ). ((2*k)*((k+1)⁻¹*(k+3/2)):ℝ)","ℕ→ℝ","λ(k:ℕ). (2·k·(k+1)⁻¹·(k+3/2):ℝ)"),
	Case("ExactProductSign","λ(k:ℕ). (-(2*k)*((k+1)⁻¹*(k+3/2)):ℝ)","ℕ→ℝ","λ(k:ℕ). (-2·k·(k+1)⁻¹·(k+3/2):ℝ)"),
	Case("ExactProductInteger","λ(z:ℤ). (2*z*((z+1)⁻¹*(z+3/2)):ℝ)","ℤ→ℝ","λ(z:{z:ℤ | z≠-1}). (2·z·(z+1)⁻¹·(z+3/2):ℝ)"),
	Case("ExactProductStrict","defined((λ(k:ℕ). (mulQ([k≠0],(2*k)*k⁻¹):ℝ))(0))","𝔹","false"),
	Case("GapProductPair","λ(k:ℕ).massD("~scaledSteps("(n+2)/n")~")","ℕ→ℝ","λ(k:ℕ). (k·(1/2·k+3/2)+1:ℝ)"),
	Case("GapProductReverse","λ(k:ℕ).massD("~scaledSteps("n/(n+3)")~")","ℕ→ℝ","λ(k:ℕ). (6·(k·(k·(k+6)+11)+6)⁻¹:ℝ)"),
	Case("GapProductShift","λ(k:ℕ).massD("~scaledSteps("(n+5)/(n+2)")~")","ℕ→ℝ","λ(k:ℕ). (k·(k·(1/60·k+1/5)+47/60)+1:ℝ)"),
	Case("GapProductMillion","massD("~scaledSteps("(n+2)/n","1000000")~")","ℝ","500001500001"),
	Case("GapProductReciprocalAt","massD("~scaledSteps("n/(n+3)","4")~")","ℝ","1/35"),
	Case("GapProductNonunitSlope","massD("~scaledSteps("(3*n+7)/(3*n+1)","1")~")","ℝ","5/2"),
	Case("GapProductWide","λ(k:ℕ).massD("~scaledSteps("(n+8)/n")~")","ℕ→ℝ"),
	Case("GapProductWideInverse","λ(k:ℕ).massD("~scaledSteps("n/(n+8)")~")","ℕ→ℝ"),
	Case("GapProductSeed","defined(massD("~scaledSteps("(n+2)/n","3","undefined(Distribution(ℝ))")~"))","𝔹","false"),
	Case("GapProductPole","λ(k:ℕ).massD("~scaledSteps("(n+1)/(n-1)")~")","ℕ→ℝ"),
	Case("GapProductHitsPole","defined(massD("~scaledSteps("(n+1)/(n-1)","2")~"))","𝔹","false"),
	Case("GapProductHalfStep","λ(k:ℕ).massD("~scaledSteps("(2*n+4)/(2*n+1)")~")","ℕ→ℝ"),
	Case("ProductCrossForward","λ(k:ℕ).massD("~scaledSteps("(2*n+5)/(2*n+3)")~")","ℕ→ℝ","λ(k:ℕ). (1/5·(2·k+5):ℝ)"),
	Case("ProductCrossReverse","λ(k:ℕ).massD("~scaledSteps("(2*n+3)/(2*n+5)")~")","ℕ→ℝ","λ(k:ℕ). (5·(2·k+5)⁻¹:ℝ)"),
	Case("ProductCrossSquared","λ(k:ℕ).massD("~scaledSteps("(2*n+5)^2/(2*n+3)^2")~")","ℕ→ℝ","λ(k:ℕ). (1/25·(2·k+5)^2:ℝ)"),
	Case("ProductCrossReversedQ","λ(k:ℕ).massD("~scaledSteps("invQ(n)*(n+1)")~")","ℕ→ℝ","λ(k:ℕ). (k+1:ℝ)"),
	Case("ProductCrossReversedR","λ(k:ℕ).massD("~scaledSteps("(n:ℝ)⁻¹*(n+1:ℝ)")~")","ℕ→ℝ","λ(k:ℕ). (k+1:ℝ)"),
	Case("ProductCrossDepth","massD("~scaledSteps("(2*n+3)/(2*n+5)","3")~")","ℝ","5/11"),
	Case("VisitQuotientNatural","λ(k:ℕ).massD("~scaledSteps("(n+1)/n")~")","ℕ→ℝ","λ(k:ℕ). (k+1:ℝ)"),
	Case("VisitQuotientReciprocal","λ(k:ℕ).massD("~scaledSteps("n/(n+1)")~")","ℕ→ℝ","λ(k:ℕ). ((k+1)⁻¹:ℝ)"),
	Case("VisitQuotientSquare","λ(k:ℕ).massD("~scaledSteps("(n+1)^2/n^2")~")","ℕ→ℝ","λ(k:ℕ). ((k+1)^2:ℝ)"),
	Case("VisitQuotientOffset","λ(k:ℕ).massD("~scaledSteps("(n+3)/(n+2)")~")","ℕ→ℝ","λ(k:ℕ). (1/3·(k+3):ℝ)"),
	Case("VisitQuotientMillion","massD("~scaledSteps("n/(n+1)","1000000")~")","ℝ","1/1000001"),
	Case("VisitQuotientCrossesZero","defined(massD("~scaledSteps("(n-1)/(n-2)","3")~"))","𝔹","false"),
	Case("ProductScaleGrowing","λ(k:ℕ).massD("~scaledSteps(growing)~")","ℕ→ℝ","λ(k:ℕ). (k+1:ℝ)"),
	Case("ProductScaleShrinking","λ(k:ℕ).massD("~scaledSteps(shrinking)~")","ℕ→ℝ","λ(k:ℕ). ((k+1)⁻¹:ℝ)"),
	Case("ProductScaleShifted","λ(k:ℕ).massD("~scaledSteps("(2*(n:ℝ)+5)/(2*(n:ℝ)+3)")~")","ℕ→ℝ","λ(k:ℕ). (2/5·k+1:ℝ)"),
	Case("ProductScaleSquared","λ(k:ℕ).massD("~scaledSteps("(n+1:ℝ)^2/(n:ℝ)^2")~")","ℕ→ℝ","λ(k:ℕ). ((k+1)^2:ℝ)"),
	Case("ProductScaleMillion","massD("~scaledSteps(growing,"1000000")~")","ℝ","1000001"),
	Case("ProductScaleMoment","λ(k:ℕ).massD(weightD(λ(x:ℝ).x,"~scaledSteps(growing)~"))","ℕ→ℝ","λ(k:ℕ). (3·(k+1):ℝ)"),
	Case("ProductScalePartialProbe","λ(h:ℝ→ℝ).λ(k:ℕ).massD(weightD(h,"~scaledSteps(shrinking)~"))","(ℝ→ℝ)→ℕ→ℝ","λ(h:ℝ→ℝ). λ(k:ℕ). h(3)·(k+1)⁻¹"),
	Case("ProductScaleZeroDepth","massD("~scaledSteps(growing,"0")~")","ℝ","1"),
	Case("ProductScaleMissing","defined(massD("~scaledSteps(growing,"0 sub 1")~"))","𝔹","false"),
	Case("ProductScalePartialSeed","defined(massD("~scaledSteps(growing,"4","undefined(Distribution(ℝ))")~"))","𝔹","false"),
	Case("ProductScalePole","λ(k:ℕ).massD("~scaledSteps("(n-1:ℝ)/(n-2:ℝ)")~")","ℕ→ℝ"),
	Case("ProductScaleHitsPole","defined(massD("~scaledSteps("(n-1:ℝ)/(n-2:ℝ)","3")~"))","𝔹","false"),
	Case("ConvolutionZeroRate","massD(weightD(λ(x:ℝ).x,"~discountedAtoms("4","0","δ((3:ℝ))")~"))","ℝ","4"),
	Case("ConvolutionZeroHole","defined(massD(weightD(λ(x:ℝ).(x-2)⁻¹,"~discountedAtoms("4","0","δ((3:ℝ))")~")))","𝔹","false"),
	Case("ConvolutionSeedHole","defined(massD(weightD(λ(x:ℝ).(x-2)⁻¹,"~discountedAtoms("1","0","δ((2:ℝ))")~")))","𝔹","false"),
	Case("ConvolutionUnusedRate","massD(weightD(λ(x:ℝ).x,"~discountedAtoms("0","undefined(ℝ)","δ((3:ℝ))")~"))","ℝ","3"),
	Case("ConvolutionMissingRate","defined(massD(weightD(λ(x:ℝ).x,"~discountedAtoms("1","undefined(ℝ)","δ((3:ℝ))")~")))","𝔹","false"),
	Case("ConvolutionMissingIndex","defined(massD(weightD(λ(x:ℝ).x,"~discountedAtoms("0 sub 1","undefined(ℝ)","δ((3:ℝ))")~")))","𝔹","false"),
	Case("ConvolutionHigher","λ(h:ℝ→ℝ).λ(k:ℕ).massD("~discountedAtoms("k","h((1:ℝ))","δ((3:ℝ))",true)~")","(ℝ→ℝ)→ℕ→ℝ"),
	Case("ConvolutionReciprocal","λ(r:ℝ).massD(weightD(λ(x:ℝ).x,"~discountedAtoms("2","r⁻¹","δ((3:ℝ))")~"))","ℝ→ℝ","λ(r:{r:ℝ | r≠0}). 2+r⁻¹+3·(r^2)⁻¹"),
	Case("DiscountVisitFirst","λ(k:ℕ).massD(weightD(λ(x:ℝ).x,"~discountedAtoms("k")~"))","ℕ→ℝ","λ(k:ℕ). ((1/2)^k·((2·k-2)·2^k+2):ℝ)"),
	Case("DiscountVisitFour","massD(weightD(λ(x:ℝ).x,"~discountedAtoms("4")~"))","ℝ","49/8"),
	Case("DiscountVisitSquares","massD(weightD(λ(x:ℝ).x^2,"~discountedAtoms("4")~"))","ℝ","173/8"),
	Case("DiscountVisitSigned","massD(weightD(λ(x:ℝ).x,"~discountedAtoms("4","-2/3","δ((3:ℝ))",true)~"))","ℝ","86/27"),
	Case("DiscountVisitEmpty","massD(weightD(λ(x:ℝ).(x-2)⁻¹,"~discountedAtoms("0")~"))","ℝ","0"),
	Case("DiscountVisitHole","defined(massD(weightD(λ(x:ℝ).(x-2)⁻¹,"~discountedAtoms("4")~")))","𝔹","false"),
	Case("DiscountVisitHigher","λ(h:ℝ→ℝ).λ(k:ℕ).massD(weightD(h,"~discountedAtoms("k","1/2","δ((0:ℝ))")~"))","(ℝ→ℝ)→ℕ→ℝ"),
	Case("DiscountVisitMissingIndex","defined(massD("~discountedAtoms("0 sub 1","-1")~"))","𝔹","false"),
	Case("CapturedScale","λ(r:ℝ).λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((3:ℝ)) else scaleD(r,f(n sub 1)))(k))","ℝ→ℕ→ℝ","λ(r:ℝ). λ(k:ℕ). [k≠0]·r^k+[k=0]"),
	Case("CapturedScaleMoment","λ(r:ℝ).λ(k:ℕ).massD(weightD(λ(x:ℝ).x^2,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((3:ℝ)) else scaleD(r⁻¹,f(n sub 1)))(k)))","ℝ→ℕ→ℝ","λ(r:ℝ). λ(k:ℕ). [k≠0]·(9·(r⁻¹)^k)+[k=0]·9"),
	Case("CapturedScaleHundred","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((3:ℝ)) else scaleD(undefined(ℝ),f(n sub 1)))(100))","ℝ","undefined(ℝ)"),
	Case("CapturedScaleMissingIndex","λ(r:ℝ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((3:ℝ)) else scaleD(r,f(n sub 1)))(0 sub 1))","ℝ→ℝ","λ(r:ℝ). undefined(ℝ)"),
	Case("VariableScaleByIndex","λ(r:ℝ).λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((3:ℝ)) else scaleD((n:ℝ),f(n sub 1)))(k))","ℝ→ℕ→ℝ"),
	Case("ProductFibreUniformMillionHit","densityAtD("~uniformCountdown~"(1000000),1000000)","ℝ","undefined(ℝ)"),
	Case("ProductFibreUniformMillionMiss","densityAtD("~uniformCountdown~"(1000000),1000001)","ℝ","0"),
	Case("ProductFibreUniformSymbolic","λ(k:ℕ).λ(x:ℝ).densityAtD("~uniformCountdown~"(k),x)","ℕ→ℝ→ℝ"),
	Case("ProductFibreUnweighted","λ(k:ℕ).λ(x:ℝ).densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","n/(n+1)","k")~",x)","ℕ→ℝ→ℝ"),
	Case("RootMissingDomain","defined(floorN(sqrt(-1)))","𝔹","false"),
	Case("SquareSelectorNatural","λ(x:ℝ). ∑(i:ℕ). [x=(i:ℝ)^2]·(i+1:ℝ)","ℝ→ℝ"),
	Case("SquareSelectorShifted","λ(k:ℕ).λ(x:ℝ).∑(i:ℕ).[i<k]·[x=(i+1:ℝ)^2]·(i+1:ℝ)","ℕ→ℝ→ℝ"),
	Case("SquareSelectorColumn","λ(k:ℕ).λ(o:ℕ).λ(x:ℝ).∑(i:ℕ).[i<k]·[((o+i)^2:ℝ)=x]·(i+1:ℝ)","ℕ→ℕ→ℝ→ℝ"),
	Case("SquareSelectorHit","∑(i:ℕ). [i<1000000]·[81=(i:ℝ)^2]·(i+1:ℝ)","ℝ","10"),
	Case("SquareSelectorReverse","∑(i:ℕ). [(i^2:ℝ)=81]·(i+1:ℝ)","ℝ","10"),
	Case("SquareSelectorGap","∑(i:ℕ). [i<1000000]·[82=(i:ℝ)^2]·undefined(ℝ)","ℝ","0"),
	Case("SquareSelectorNegative","∑(i:ℕ). [i<1000000]·[-1=(i:ℝ)^2]·undefined(ℝ)","ℝ","0"),
	Case("SquareSelectorExcluded","∑(i:ℕ). [i<9]·[81=(i:ℝ)^2]·undefined(ℝ)","ℝ","0"),
	Case("SquareSelectorMissingWeight","∑(i:ℕ). [i<10]·[81=(i:ℝ)^2]·undefined(ℝ)","ℝ","undefined(ℝ)"),
	Case("SquareSelectorEmpty","∑(i:ℕ).[i<0]·[undefined(ℝ)=(i:ℝ)^2]·undefined(ℝ)","ℝ","0"),
	Case("SquareSelectorMissingQuery","defined(∑(i:ℕ).[i<1000000]·[undefined(ℝ)=(i:ℝ)^2]·(1:ℝ))","𝔹","false"),
	Case("SquareSelectorCaptured","λ(k:ℕ).λ(o:ℕ).λ(f:ℕ→ℝ).λ(x:ℝ).∑(i:ℕ).[i<k]·[x=(i+o:ℝ)^2]·f(i)","ℕ→ℕ→(ℕ→ℝ)→ℝ→ℝ"),
	Case("SquareSelectorInteger","λ(x:ℝ). ∑(i:ℤ). [(i:ℝ)^2=x]·(1:ℝ)","ℝ→ℝ"),
	Case("SquareSelectorRecursive","λ(k:ℕ).λ(x:ℝ).densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ)^2)","","k")~",x)","ℕ→ℝ→ℝ"),
	Case("SquareSelectorRecursiveHit","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ)^2)","","1000000")~",81)","ℝ","undefined(ℝ)"),
	Case("SquareSelectorRecursiveOutside","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ)^2)","","8")~",81)","ℝ","1"),
	Case("SquareSelectorRecursiveGap","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ)^2)","","1000000")~",82)","ℝ","1"),
	Case("SquareSelectorRecursiveMissing","defined(densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ)^2)","","undefined(ℕ)")~",81))","𝔹","false"),
	Case("SquareSelectorRecursiveZero","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ)^2)","","0")~",81)","ℝ","1"),
	Case("SquareSelectorStrictBranch","λ(x:ℝ). ∑(i:ℕ). [x=(i:ℝ)^2]·(1/((i:ℝ)-9))","ℝ→ℝ"),
	Case("SelectedRowReciprocal","∑(i:ℕ). [i<1000000]·mulR((i+1:ℝ)⁻¹,[999999=(i:ℝ)]·(3:ℝ))","ℝ","3/1000000"),
	Case("SelectedRowRight","∑(i:ℕ). [i<1000000]·mulR([999999=(i:ℝ)]·(3:ℝ),(i+1:ℝ))","ℝ","3000000"),
	Case("SelectedRowNested","∑(i:ℕ). [i<1000000]·mulR((i+1:ℝ),mulR([999999=(i:ℝ)]·(3:ℝ),((i+1:ℝ)^2+1)⁻¹))","ℝ","3000000/1000000000001"),
	Case("SelectedRowMissingWeight","∑(i:ℕ). [i<1000000]·mulR((i+1:ℝ),[999999=(i:ℝ)]·undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("SelectedRowUnusedWeight","∑(i:ℕ). [i<1000000]·mulR((i+1:ℝ),[1000000=(i:ℝ)]·undefined(ℝ))","ℝ","0"),
	Case("SelectedRowPole","defined(∑(i:ℕ). [i<1000000]·mulR((i:ℝ)⁻¹,[999999=(i:ℝ)]·1))","𝔹","false"),
	Case("SelectedRowEmptyPole","∑(i:ℕ). [i<0]·mulR((i:ℝ)⁻¹,[999999=(i:ℝ)]·undefined(ℝ))","ℝ","0"),
	Case("SelectedRowOpaque","λ(h:ℕ→ℝ).∑(i:ℕ). [i<1000000]·mulR(mulR((i+1:ℝ),[999999=(i:ℝ)]·h(i)),(i+1:ℝ)⁻¹)","(ℕ→ℝ)→ℝ","λ(h:ℕ→ℝ). h(999999)"),
	Case("SelectedRowTranslated","λ(k:ℕ).λ(x:ℝ).∑(i:ℕ). [i<k]·mulR([x=(i+3:ℝ)]·(1:ℝ),(i+1:ℝ)⁻¹)","ℕ→ℝ→ℝ"),
	Case("SelectedRowFreePole","λ(r:ℝ).defined(∑(i:ℕ). [i<2]·mulR((r-(i:ℝ))⁻¹,[5=(i:ℝ)]·1))","ℝ→𝔹","λ(r:ℝ). r≠0∧r≠1"),
	Case("ProductFibreUniformSeed","densityAtD("~uniformCountdown~"(0),0)","ℝ","undefined(ℝ)"),
	Case("ProductFibreUniformEmpty","densityAtD("~uniformCountdown~"(0),1)","ℝ","0"),
	Case("ProductFibreUniformFirst","densityAtD("~uniformCountdown~"(5),0)","ℝ","undefined(ℝ)"),
	Case("ProductFibreUniformLast","densityAtD("~uniformCountdown~"(5),5)","ℝ","undefined(ℝ)"),
	Case("ProductFibreUniformFraction","densityAtD("~uniformCountdown~"(5),9/2)","ℝ","0"),
	Case("ProductFibreUniformBeyond","densityAtD("~uniformCountdown~"(5),6)","ℝ","0"),
	Case("ProductFibreRegular","densityAtD("~emittedSteps("lebesgueD()","(Λx. ((n:ℝ)+x)·λ[x])","n/(n+1)","3",true)~",1)","ℝ","15/2"),
	Case("ProductFibreCancel","densityAtD("~emittedSteps("addD(δ((2:ℝ)),lebesgueD())","scaleD(-1/(n+1),δ((n:ℝ)))","n/(n+1)","2",true)~",2)","ℝ","1/3"),
	Case("ProductFibreBefore","densityAtD("~emittedSteps("addD(δ((2:ℝ)),lebesgueD())","scaleD(-1/(n+1),δ((n:ℝ)))","n/(n+1)","1",true)~",2)","ℝ","undefined(ℝ)"),
	Case("ProductFibreAfter","densityAtD("~emittedSteps("addD(δ((2:ℝ)),lebesgueD())","scaleD(-1/(n+1),δ((n:ℝ)))","n/(n+1)","3",true)~",2)","ℝ","1/4"),
	Case("ProductFibreMissingUnused","densityAtD("~emittedSteps("lebesgueD()","undefined(Distribution(ℝ))","n/(n+1)","0")~",0)","ℝ","1"),
	Case("ProductFibreMissingVisit","defined(densityAtD("~emittedSteps("lebesgueD()","undefined(Distribution(ℝ))","n/(n+1)","1")~",0))","𝔹","false"),
	Case("ProductFibreRegularHole","defined(densityAtD("~emittedSteps("(Λx. x⁻¹·λ[x])","δ((n:ℝ))","n/(n+1)","2")~",0))","𝔹","false"),
	Case("ProductFibreMissingBound","defined(densityAtD("~emittedSteps("δ((0:ℝ))","scaleD(1/(n+1),δ((n:ℝ)))","n/(n+1)","0 sub 1")~",0))","𝔹","false"),
	Case("ProductFibreMissingQuery","defined(densityAtD("~emittedSteps("δ((0:ℝ))","scaleD(1/(n+1),δ((n:ℝ)))","n/(n+1)","3")~",undefined(ℝ)))","𝔹","false"),
	Case("ProductFibreGrowth","densityAtD("~emittedSteps("lebesgueD()","lebesgueD()","(n+1)/n","3")~",0)","ℝ","25/3"),
	Case("ProductFibreGap","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","n/(n+2)","3")~",4)","ℝ","1/10"),
	Case("ProductFibrePole","λ(k:ℕ).densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","(n+1)/(n-1)","k")~",1)","ℕ→ℝ"),
	Case("ProductFibreOpaque","λ(b:Distribution(ℝ)).λ(k:ℕ).densityAtD("~emittedSteps("b","δ((n:ℝ))","n/(n+1)","k")~",1)","Distribution(ℝ)→ℕ→ℝ"),
	Case("PowerSelectIndex","λ(r:ℝ). λ(n:ℕ). λ(x:ℝ). ∑(i:ℕ). [i<n]·mulR(r^i,[x=(i:ℝ)]·1)","ℝ→ℕ→ℝ→ℝ"),
	Case("PowerSelectSucc","λ(r:ℝ). λ(x:ℝ). ∑(i:ℕ). [i<1000000]·mulR([x=(i+2:ℝ)]·1,r^(i+1))","ℝ→ℝ→ℝ"),
	Case("PowerSelectRemaining","λ(r:ℝ). λ(n:ℕ). λ(x:ℝ). ∑(i:ℕ). [i<n]·mulR(r^(n sub (i+1)),[x=(i+1:ℝ)]·1)","ℝ→ℕ→ℝ→ℝ"),
	Case("PowerSelectZero","λ(r:ℝ). λ(n:ℕ). ∑(i:ℕ). [i<n]·mulR(r^(n sub (i+1)),(0:ℝ))","ℝ→ℕ→ℝ"),
	Case("PowerSelectMissingEmpty","∑(i:ℕ). [i<0]·mulR((undefined(ℝ))^i,[9=(i:ℝ)]·(1:ℝ))","ℝ","0"),
	Case("PowerSelectMissingMiss","∑(i:ℕ). [i<5]·mulR((undefined(ℝ))^i,[9=(i:ℝ)]·(1:ℝ))","ℝ","undefined(ℝ)"),
	Case("PowerSelectMissingZero","∑(i:ℕ). [i<5]·mulR((0:ℝ),(undefined(ℝ))^(5 sub (i+1)))","ℝ","undefined(ℝ)"),
	Case("PowerSelectMiss","∑(i:ℕ). [i<1000000]·mulR((-1:ℝ)^i,[1000000=(i:ℝ)]·undefined(ℝ))","ℝ","0"),
	Case("PowerSelectHit","∑(i:ℕ). [i<1000000]·mulR((-1:ℝ)^i,[999999=(i:ℝ)]·(2:ℝ))","ℝ","-2"),
	Case("PowerSelectOpaqueWeight","λ(f:ℕ→ℝ). ∑(i:ℕ). [i<1000000]·mulR([999999=(i:ℝ)]·f(i),(-1:ℝ)^(i+1))","(ℕ→ℝ)→ℝ"),
	Case("PowerSelectUnsafeExponent","defined(∑(i:ℕ). [i<2]·mulR((2:ℝ)^(i sub 1),[5=(i:ℝ)]·1))","𝔹","false"),
	Case("DiscountProbeAlternatingLast","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","-1","1000000")~",1000000)","ℝ","undefined(ℝ)"),
	Case("DiscountProbeAlternatingBeyond","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","-1","1000000")~",1000001)","ℝ","1"),
	Case("DiscountProbeZeroPast","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","0","1000000")~",999999)","ℝ","0"),
	Case("DiscountProbeZeroLatest","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","0","1000000")~",1000000)","ℝ","undefined(ℝ)"),
	Case("DiscountProbeZeroAfter","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","0","1000000")~",1000001)","ℝ","0"),
	Case("DiscountFibreCancel","densityAtD("~emittedSteps("addD(δ((2:ℝ)),lebesgueD())","scaleD(-1/4,δ((n:ℝ)))","1/2","2")~",2)","ℝ","1/4"),
	Case("DiscountFibreAfter","densityAtD("~emittedSteps("addD(δ((2:ℝ)),lebesgueD())","scaleD(-1/4,δ((n:ℝ)))","1/2","3",true)~",2)","ℝ","1/8"),
	Case("DiscountFibreBefore","densityAtD("~emittedSteps("addD(δ((2:ℝ)),lebesgueD())","scaleD(-1/4,δ((n:ℝ)))","1/2","1")~",2)","ℝ","undefined(ℝ)"),
	Case("DiscountFibreAlternating","densityAtD("~emittedSteps("addD(δ((1:ℝ)),lebesgueD())","δ((n:ℝ))","-1","1",true)~",1)","ℝ","-1"),
	Case("DiscountFibreZeroClears","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","0","2")~",1)","ℝ","0"),
	Case("DiscountFibreZeroLatest","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","0","2",true)~",2)","ℝ","undefined(ℝ)"),
	Case("DiscountFibreZeroHole","defined(densityAtD("~emittedSteps("(Λx. x⁻¹·λ[x])","δ((n:ℝ))","0","2")~",0))","𝔹","false"),
	Case("DiscountFibreZeroVisits","densityAtD("~emittedSteps("lebesgueD()","δ(((n:ℝ)-1)⁻¹)","undefined(ℝ)","0")~",1)","ℝ","1"),
	Case("DiscountFibreMissingRate","defined(densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","undefined(ℝ)","1")~",1))","𝔹","false"),
	Case("DiscountFibreMissingRow","defined(densityAtD("~emittedSteps("lebesgueD()","δ(((n:ℝ)-1)⁻¹)","0","2")~",3))","𝔹","false"),
	Case("DiscountFibreMissingBound","defined(densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","1/2","0 sub 1")~",1))","𝔹","false"),
	Case("DiscountFibreMissingQuery","defined(densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","-1","2")~",undefined(ℝ)))","𝔹","false"),
	Case("DiscountFibreSmooth","densityAtD("~emittedSteps("lebesgueD()","(Λx. ((n:ℝ)+x)·λ[x])","1/2","3")~",1)","ℝ","49/8"),
	Case("DiscountFibreCaptured","λ(r:ℝ).λ(k:ℕ).λ(x:ℝ).densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","r","k")~",x)","ℝ→ℕ→ℝ→ℝ"),
	Case("DiscountFibreMixed","densityAtD("~emittedSteps("lebesgueD()","addD(δ((n:ℝ)),scaleD((n:ℝ),lebesgueD()))","-1","3")~",4)","ℝ","1"),
	Case("DiscountFibreOpaqueSeed","λ(b:Distribution(ℝ)).densityAtD("~emittedSteps("b","δ((n:ℝ))","1/2","2")~",0)","Distribution(ℝ)→ℝ"),
	Case("VisitFibreMillion","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","","1000000")~",1000001)","ℝ","1"),
	Case("VisitFibreLast","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","","1000000")~",1000000)","ℝ","undefined(ℝ)"),
	Case("VisitFibreSymbolic","λ(k:ℕ).densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","","k")~",2)","ℕ→ℝ","λ(k:{k:ℕ | k≤1}). (1:ℝ)"),
	Case("IndexAddendLast","∑(i:ℕ). [i<1000000]·([((i+3):ℝ)=1000002]·(i:ℝ))","ℝ","999999"),
	Case("IndexAddendOutside","∑(i:ℕ). [i<1000000]·([((i+3):ℝ)=1000003]·undefined(ℝ))","ℝ","0"),
	Case("IndexAddendFraction","∑(i:ℕ). [i<1000000]·([((i+3):ℝ)=7/2]·undefined(ℝ))","ℝ","0"),
	Case("IndexAddendZero","∑(i:ℕ). [i<1000000]·([((i+3):ℝ)=3]·(-7:ℝ))","ℝ","-7"),
	Case("IndexAddendPositive","∑(i:ℕ). [i<1000000]·([((i:ℝ)+1)=0]·undefined(ℝ))","ℝ","0"),
	Case("IndexAddendDependent","λ(y:ℝ). ∑(i:ℕ). [i<1000000]·([((i+3):ℝ)+y=0]·(i:ℝ))","ℝ→ℝ","λ(y:ℝ). ([floorN(-y-3)≤999999∧y+(floorN(-y-3)+3)=0]·floorN(-y-3):ℝ)"),
	Case("IndexAddendFirst","λ(y:ℝ). ∑(i:ℕ). [i<1000000]·([y+((3+i):ℝ)=0]·(i:ℝ))","ℝ→ℝ","λ(y:ℝ). ([floorN(-y-3)≤999999∧y+(floorN(-y-3)+3)=0]·floorN(-y-3):ℝ)"),
	Case("IndexAddendMissing","∑(i:ℕ). [i<0]·([((i:ℝ)+undefined(ℝ))=0]·undefined(ℝ))","ℝ","0"),
	Case("IndexAddendRowHole","∑(i:ℕ). [i<1000000]·([((i+3):ℝ)=1000002]·undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("IndexAddendUnbounded","∑(i:ℤ). [(i:ℝ)=-7]·(i:ℝ)","ℝ","-7"),
	Case("IndexAddendUnboundedNat","∑(i:ℕ). [(i:ℝ)=17]·(i:ℝ)","ℝ","17"),
	Case("IndexAddendFunction","λ(f:ℕ→ℝ). ∑(i:ℕ). [i<1000000]·([((i+3):ℝ)=1000002]·f(i))","(ℕ→ℝ)→ℝ","λ(f:ℕ→ℝ). f(999999)"),
	Case("RangeProbeBare","λ(n:ℕ). λ(x:ℝ). ∑(i:ℕ). [i<n]·([x=(i:ℝ)]·1)","ℕ→ℝ→ℝ","λ(n:ℕ). λ(x:ℝ). [n≠0∧(floorN(x)<n∧x=floorN(x))]"),
	Case("RangeProbeShift","λ(n:ℕ). λ(x:ℝ). ∑(i:ℕ). [i<n]·([x=(i+3:ℝ)]·1)","ℕ→ℝ→ℝ","λ(n:ℕ). λ(x:ℝ). [n≠0∧(floorN(x-3)<n∧x=(floorN(x-3)+3))]"),
	Case("RangeProbeFlipped","λ(n:ℕ). λ(x:ℝ). ∑(i:ℕ). [i<n]·([(3+i:ℝ)=x]·1)","ℕ→ℝ→ℝ","λ(n:ℕ). λ(x:ℝ). [n≠0∧(floorN(x-3)<n∧x=(floorN(x-3)+3))]"),
	Case("RangeProbeCaptured","λ(o:ℕ). λ(x:ℝ). ∑(i:ℕ). [i<1000000]·([x=(o+i:ℝ)]·(i:ℝ))","ℕ→ℝ→ℝ","λ(o:ℕ). λ(x:ℝ). [floorN(x-o)<1000000]·([x=(o+floorN(x-o))]·(guard(defined(floorN(x-o)),(floorN(x-o):ℝ))))"),
	Case("RangeProbeLazy","∑(i:ℕ). [i<1000000]·([1/2=(i+3:ℝ)]·undefined(ℝ))","ℝ","0"),
	Case("RangeProbeRight","∑(i:ℕ). [i<1000000]·([1000003=(i+3:ℝ)]·undefined(ℝ))","ℝ","0"),
	Case("RangeProbeInside","∑(i:ℕ). [i<1000000]·([1000002=(i+3:ℝ)]·(i:ℝ))","ℝ","999999"),
	Case("RangeProbeMissingEmpty","∑(i:ℕ). [i<0]·([undefined(ℝ)=(i:ℝ)]·undefined(ℝ))","ℝ","0"),
	Case("RangeProbeMissingVisit","∑(i:ℕ). [i<2]·([undefined(ℝ)=(i:ℝ)]·1)","ℝ","undefined(ℝ)"),
	Case("RangeProbePartialOffset","λ(o:ℕ). ∑(i:ℕ). [i<5]·([2=(i+(o sub 1):ℝ)]·1)","ℕ→ℝ","λ(o:ℕ). [(guard(o≠0,floorN(-(o-1)+2)≤4))]·([(guard(o≠0,(floorN(-(o-1)+2)+(o sub 1))=2))]·(guard(o≠0,(1:ℝ))))"),
	Case("RangeProbeOpaque","λ(f:ℕ→ℝ). λ(x:ℝ). ∑(i:ℕ). [i<1000000]·([x=(i+1:ℝ)]·f(i))","(ℕ→ℝ)→ℝ→ℝ","λ(f:ℕ→ℝ). λ(x:ℝ). [floorN(x-1)≤999999]·([x=(floorN(x-1)+1)]·f(floorN(x-1)))"),
	Case("VisitFibreStart","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","","0")~",1)","ℝ","1"),
	Case("VisitFibreEnd","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","1","5",true)~",5)","ℝ","undefined(ℝ)"),
	Case("VisitFibreBetween","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","","5")~",3/2)","ℝ","1"),
	Case("VisitFibreBeyond","densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","","5")~",6)","ℝ","1"),
	Case("VisitFibreQuery","λ(k:ℕ).λ(x:ℝ).densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","","k")~",x)","ℕ→ℝ→ℝ","λ(k:ℕ). λ(x:{x:ℝ | [k≠0∧(floorN(x-1)<k∧x=(floorN(x-1)+1))]=0}). (guard(defined(k),(0:ℝ)))+1"),
	Case("VisitFibreSigned","densityAtD("~emittedSteps("addD(δ((2:ℝ)),lebesgueD())","scaleD(-1,δ((n:ℝ)))","","5")~",2)","ℝ","1"),
	Case("VisitFibreBefore","densityAtD("~emittedSteps("addD(δ((2:ℝ)),lebesgueD())","scaleD(-1,δ((n:ℝ)))","","1")~",2)","ℝ","undefined(ℝ)"),
	Case("VisitFibreRegular","densityAtD("~emittedSteps("lebesgueD()","(Λx. ((n:ℝ)+x)·λ[x])","","4")~",2)","ℝ","19"),
	Case("VisitFibreMixed","densityAtD("~emittedSteps("lebesgueD()","addD(δ((n:ℝ)),scaleD((n:ℝ),lebesgueD()))","","4",true)~",5)","ℝ","11"),
	Case("VisitFibreMixedAtom","densityAtD("~emittedSteps("lebesgueD()","addD(δ((n:ℝ)),scaleD((n:ℝ),lebesgueD()))","","4")~",3)","ℝ","undefined(ℝ)"),
	Case("VisitFibreEmptyPole","densityAtD("~emittedSteps("lebesgueD()","δ(((n:ℝ)-1)⁻¹)","","0")~",3)","ℝ","1"),
	Case("VisitFibreRowPole","defined(densityAtD("~emittedSteps("lebesgueD()","δ(((n:ℝ)-1)⁻¹)","","1")~",3))","𝔹","false"),
	Case("VisitFibreAwayHole","densityAtD("~emittedSteps("lebesgueD()","(Λx. (x-(n:ℝ))⁻¹·λ[x])","","2")~",3)","ℝ","5/2"),
	Case("VisitFibreHitHole","defined(densityAtD("~emittedSteps("lebesgueD()","(Λx. (x-(n:ℝ))⁻¹·λ[x])","","2")~",1))","𝔹","false"),
	Case("VisitFibreMissingQuery","defined(densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","","2")~",undefined(ℝ)))","𝔹","false"),
	Case("VisitFibreMissingBound","defined(densityAtD("~emittedSteps("lebesgueD()","δ((n:ℝ))","","0 sub 1")~",1))","𝔹","false"),
	Case("VisitFibreHigherOrder","λ(h:ℕ→ℝ).λ(k:ℕ).λ(x:ℝ).densityAtD("~emittedSteps("lebesgueD()","δ(h(n))","","k")~",x)","(ℕ→ℝ)→ℕ→ℝ→ℝ"),
	Case("VisitFibreOpaqueSeed","λ(b:Distribution(ℝ)).densityAtD("~emittedSteps("b","δ((n:ℝ))","","2")~",2)","Distribution(ℝ)→ℝ","λ(b:Distribution(ℝ)). (λ(x:ℝ). (δ(2)[x]+(δ(1)[x]+(b)[x]))//λ[x])((2:ℝ))"),
	Case("FibreWeightsCancellation","densityAtD("~emittedSteps("addD(scaleD(3,δ((0:ℝ))),lebesgueD())","scaleD(-(n:ℝ),δ((0:ℝ)))","","2")~",0)","ℝ","1"),
	Case("FibreWeightsBefore","densityAtD("~emittedSteps("addD(scaleD(3,δ((0:ℝ))),lebesgueD())","scaleD(-(n:ℝ),δ((0:ℝ)))","1","1",true)~",0)","ℝ","undefined(ℝ)"),
	Case("FibreWeightsAfter","densityAtD("~emittedSteps("addD(scaleD(3,δ((0:ℝ))),lebesgueD())","scaleD(-(n:ℝ),δ((0:ℝ)))","","3")~",0)","ℝ","undefined(ℝ)"),
	Case("FibreWeightsSymbolic","λ(k:ℕ).densityAtD("~emittedSteps("addD(scaleD(3,δ((0:ℝ))),lebesgueD())","scaleD(-(n:ℝ),δ((0:ℝ)))","","k")~",0)","ℕ→ℝ","λ(k:ℕ). [k=0]·(undefined(ℝ))+[k≠0]·(guard(k·(-1/2·k-1/2)=-3,(1:ℝ)))"),
	Case("FibreWeightsMillion","densityAtD("~emittedSteps("lebesgueD()","scaleD((n:ℝ),lebesgueD())","","1000000",true)~",2)","ℝ","500000500001"),
	Case("FibreWeightsPolynomial","λ(k:ℕ).densityAtD("~emittedSteps("lebesgueD()","scaleD((n:ℝ)^2,lebesgueD())","","k")~",0)","ℕ→ℝ","λ(k:ℕ). ([k=0]+[k≠0]·(k·(k·(1/3·k+1/2)+1/6)+1):ℝ)"),
	Case("FibreWeightsZero","densityAtD("~emittedSteps("lebesgueD()","scaleD((n:ℝ),undefined(Distribution(ℝ)))","","0")~",0)","ℝ","1"),
	Case("FibreWeightsMissing","defined(densityAtD("~emittedSteps("lebesgueD()","scaleD((n:ℝ),undefined(Distribution(ℝ)))","","1")~",0))","𝔹","false"),
	Case("FibreWeightsDefinedPrefix","densityAtD("~emittedSteps("lebesgueD()","scaleD(((n:ℝ)-3)⁻¹,lebesgueD())","","2")~",0)","ℝ","-1/2"),
	Case("FibreWeightsPole","defined(densityAtD("~emittedSteps("lebesgueD()","scaleD(((n:ℝ)-3)⁻¹,lebesgueD())","","3")~",0))","𝔹","false"),
	Case("FibreWeightsPartialCore","defined(densityAtD("~emittedSteps("(Λx. x⁻¹·λ[x])","scaleD((n:ℝ),lebesgueD())","","2")~",0))","𝔹","false"),
	Case("FibreWeightsMissingIndex","defined(densityAtD("~emittedSteps("lebesgueD()","scaleD((n:ℝ),lebesgueD())","","0 sub 1")~",0))","𝔹","false"),
	Case("FibreWeightsMissingQuery","defined(densityAtD("~emittedSteps("lebesgueD()","scaleD((n:ℝ),lebesgueD())","","2")~",undefined(ℝ)))","𝔹","false"),
	Case("FibreWeightsFunction","λ(w:ℕ→ℝ).λ(k:ℕ).densityAtD("~emittedSteps("lebesgueD()","scaleD(w(n),lebesgueD())","","k")~",0)","(ℕ→ℝ)→ℕ→ℝ","λ(w:ℕ→ℝ). λ(k:ℕ). [k≠0]·(guard(0·(∑(i:ℕ). [i<k]·(w(i+1)))=0,(∑(i:ℕ). [i<k]·(w(i+1)))+1))+[k=0]"),
	Case("FibreWeightsDistribution","λ(b:Distribution(ℝ)).λ(v:Distribution(ℝ)).λ(w:ℕ→ℝ).λ(k:ℕ).densityAtD("~emittedSteps("b","scaleD(w(n),v)","1","k",true)~",0)","Distribution(ℝ)→Distribution(ℝ)→(ℕ→ℝ)→ℕ→ℝ"),
	Case("FibreWeightsMoving","densityAtD("~emittedSteps("lebesgueD()","scaleD((n:ℝ),δ((n:ℝ)))","","2")~",1)","ℝ","undefined(ℝ)"),
	Case("FibreEmissionAtCancellation","densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","scaleD(-1,δ((0:ℝ)))","","1")~",0)","ℝ","1"),
	Case("FibreEmissionBeforeCancellation","densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","scaleD(-1,δ((0:ℝ)))","","0")~",0)","ℝ","undefined(ℝ)"),
	Case("FibreEmissionAfterCancellation","densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","scaleD(-1,δ((0:ℝ)))","","2")~",0)","ℝ","undefined(ℝ)"),
	Case("FibreEmissionSymbolic","λ(k:ℕ).densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","scaleD(-1,δ((0:ℝ)))","","k")~",0)","ℕ→ℝ"),
	Case("FibreEmissionSwapped","densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","scaleD(-1,δ((0:ℝ)))","1","1",true)~",0)","ℝ","1"),
	Case("FibreEmissionRegular","λ(k:ℕ).densityAtD("~emittedSteps("lebesgueD()","scaleD(2,lebesgueD())","","k")~",7)","ℕ→ℝ"),
	Case("FibreEmissionSeparate","densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","δ((1:ℝ))","","1000000",true)~",2)","ℝ","1"),
	Case("FibreEmissionMissingEmpty","densityAtD("~emittedSteps("lebesgueD()","undefined(Distribution(ℝ))","","0")~",0)","ℝ","1"),
	Case("FibreEmissionMissingVisit","defined(densityAtD("~emittedSteps("lebesgueD()","undefined(Distribution(ℝ))","","1")~",0))","𝔹","false"),
	Case("FibreEmissionPole","defined(densityAtD("~emittedSteps("(Λx. (1/x)·λ[x])","scaleD(-1,δ((0:ℝ)))","","1")~",0))","𝔹","false"),
	Case("FibreEmissionMissingIndex","defined(densityAtD("~emittedSteps("lebesgueD()","lebesgueD()","","0 sub 1",true)~",1))","𝔹","false"),
	Case("FibreEmissionMissingQuery","defined(densityAtD("~emittedSteps("lebesgueD()","lebesgueD()","","3")~",undefined(ℝ)))","𝔹","false"),
	Case("FibreEmissionGeometric","λ(k:ℕ).densityAtD("~emittedSteps("lebesgueD()","scaleD(3,lebesgueD())","1/2","k")~",0)","ℕ→ℝ"),
	Case("FibreEmissionSignedCancel","densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","δ((0:ℝ))","-1","1",true)~",0)","ℝ","-1"),
	Case("FibreEmissionSignedReturn","densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","δ((0:ℝ))","-1","2")~",0)","ℝ","undefined(ℝ)"),
	Case("FibreEmissionZeroClears","densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","lebesgueD()","0","3")~",0)","ℝ","1"),
	Case("FibreEmissionZeroPole","defined(densityAtD("~emittedSteps("(Λx. (1/x)·λ[x])","lebesgueD()","0","3",true)~",0))","𝔹","false"),
	Case("FibreEmissionUnknownEmpty","densityAtD("~emittedSteps("addD(δ((0:ℝ)),lebesgueD())","undefined(Distribution(ℝ))","undefined(ℝ)","0")~",2)","ℝ","1"),
	Case("FibreEmissionUnknownUsed","defined(densityAtD("~emittedSteps("lebesgueD()","lebesgueD()","undefined(ℝ)","1")~",2))","𝔹","false"),
	Case("FibreEmissionSymbolicScale","λ(r:ℝ).λ(k:ℕ).densityAtD("~emittedSteps("lebesgueD()","lebesgueD()","r","k")~",2)","ℝ→ℕ→ℝ"),
	Case("FibreEmissionParameters","λ(b:Distribution(ℝ)).λ(v:Distribution(ℝ)).λ(k:ℕ).densityAtD("~emittedSteps("b","v","","k",true)~",0)","Distribution(ℝ)→Distribution(ℝ)→ℕ→ℝ"),
	Case("FibreProductGrowing","λ(k:ℕ).densityAtD("~scaledSteps("(n+1)/n","k","lebesgueD()")~",1)","ℕ→ℝ","λ(k:ℕ). (k+1:ℝ)"),
	Case("FibreProductShrinking","λ(k:ℕ).densityAtD("~scaledSteps("n/(n+1)","k","lebesgueD()")~",1)","ℕ→ℝ","λ(k:ℕ). ((k+1)⁻¹:ℝ)"),
	Case("FibreProductMixed","densityAtD("~scaledSteps("(n+2)/n","4","addD(lebesgueD(),δ((0:ℝ)))")~",2)","ℝ","15"),
	Case("FibreProductSupport","densityAtD("~scaledSteps("(n+2)/n","4","addD(lebesgueD(),δ((0:ℝ)))")~",0)","ℝ","undefined(ℝ)"),
	Case("FibreProductCancelled","densityAtD("~scaledSteps("n/(n+3)","4","addD(addD(lebesgueD(),δ((0:ℝ))),scaleD(-1,δ((0:ℝ))))")~",0)","ℝ","1/35"),
	Case("FibreProductPuncture","densityAtD("~scaledSteps("(n+2)/n","4","(Λx. [x≠0]·λ[x])")~",0)","ℝ","0"),
	Case("FibreProductPole","defined(densityAtD("~scaledSteps("(n+2)/n","4","(Λx. (1/x)·λ[x])")~",0))","𝔹","false"),
	Case("FibreProductOffset","densityAtD("~scaledSteps("(2*n+3)/(2*n+5)","3","lebesgueD()")~",0)","ℝ","5/11"),
	Case("FibreProductMissingIndex","defined(densityAtD("~scaledSteps("(n+1)^2/n^2","0 sub 1","lebesgueD()")~",1))","𝔹","false"),
	Case("FibreProductMissingPoint","defined(densityAtD("~scaledSteps("(n+3)/(n+2)","3","lebesgueD()")~",undefined(ℝ)))","𝔹","false"),
	Case("FibreProductMissingSeed","defined(densityAtD("~scaledSteps("(n+1)/n","0","undefined(Distribution(ℝ))")~",1))","𝔹","false"),
	Case("FibreProductParameter","λ(d:Distribution(ℝ)).λ(k:ℕ).λ(y:ℝ).densityAtD("~scaledSteps("(n+1)/n","k","d")~",y)","Distribution(ℝ)→ℕ→ℝ→ℝ"),
	Case("FibreProductMillion","densityAtD("~scaledSteps("n/(n+1)","1000000","lebesgueD()")~",4)","ℝ","1/1000001"),
	Case("FibreProductCrossesPole","defined(densityAtD("~scaledSteps("(n+1)/(n-1)","2","lebesgueD()")~",1))","𝔹","false"),
	Case("FibreCountdownRegular","λ(k:ℕ).λ(y:ℝ).densityAtD("~scaledSteps("1/2","k","(Λx. [x≠0]·λ[x])")~",y)","ℕ→ℝ→ℝ","λ(k:ℕ). λ(y:ℝ). mulR([y≠0],(1/2:ℝ)^k)"),
	Case("FibreCountdownHole","densityAtD("~scaledSteps("1/2","31","(Λx. [x≠0]·λ[x])")~",0)","ℝ","0"),
	Case("FibreCountdownSigned","densityAtD("~scaledSteps("-2","9","addD(lebesgueD(),δ((0:ℝ)))")~",1)","ℝ","-512"),
	Case("FibreCountdownSingular","densityAtD("~scaledSteps("-2","9","addD(lebesgueD(),δ((0:ℝ)))")~",0)","ℝ","undefined(ℝ)"),
	Case("FibreCountdownZeroAtom","densityAtD("~scaledSteps("0","37","δ((0:ℝ))")~",0)","ℝ","0"),
	Case("FibreCountdownZeroAtZero","densityAtD("~scaledSteps("0","0","δ((0:ℝ))")~",0)","ℝ","undefined(ℝ)"),
	Case("FibreCountdownPartialRegular","defined("~"densityAtD("~scaledSteps("0","9","(Λx. (1/x)·λ[x])")~",0)"~")","𝔹","false"),
	Case("FibreCountdownCancelled","densityAtD("~scaledSteps("-2","7","addD(addD(lebesgueD(),δ((0:ℝ))),scaleD(-1,δ((0:ℝ))))")~",0)","ℝ","-128"),
	Case("FibreCountdownParameter","λ(d:Distribution(ℝ)).λ(k:ℕ).λ(y:ℝ).densityAtD("~scaledSteps("1/2","k","d")~",y)","Distribution(ℝ)→ℕ→ℝ→ℝ"),
	Case("FibreCountdownCaptured","λ(h:ℝ→ℝ).λ(t:ℝ).λ(k:ℕ).densityAtD("~scaledSteps("h(t)","k","δ((0:ℝ))")~",0)","(ℝ→ℝ)→ℝ→ℕ→ℝ"),
	Case("FibreCountdownCapturedZero","densityAtD("~scaledSteps("undefined(ℝ)","0","lebesgueD()")~",2)","ℝ","1"),
	Case("FibreCountdownCapturedOne","densityAtD("~scaledSteps("undefined(ℝ)","1","lebesgueD()")~",2)","ℝ","undefined(ℝ)"),
	Case("FibreCountdownMissingIndex","defined("~"densityAtD("~scaledSteps("-2","0 sub 1","lebesgueD()")~",4)"~")","𝔹","false"),
	Case("FibreCountdownMissingPoint","densityAtD("~scaledSteps("-2","4","lebesgueD()")~",undefined(ℝ))","ℝ","undefined(ℝ)"),
	Case("FibreCountdownMillion","densityAtD("~scaledSteps("-1","1000000","lebesgueD()")~",1)","ℝ","1"),
	Case("CountdownTestMoment","λ(k:ℕ).massD(weightD(λ(x:ℝ). x^2,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ). if n=0 then δ((3:ℝ)) else scaleD(1/2,f(n sub 1)))(k)))","ℕ→ℝ","λ(k:ℕ). (9·(1/2)^k:ℝ)"),
	Case("CountdownTestFree","λ(h:ℝ→ℝ). λ(k:ℕ).massD(weightD(h,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ). if n=0 then δ((3:ℝ)) else scaleD(-2,f(n sub 1)))(k)))","(ℝ→ℝ)→ℕ→ℝ","λ(h:ℝ→ℝ). λ(k:ℕ). h(3)·(-2)^k"),
	Case("CountdownTestBind","λ(k:ℕ).massD(weightD(λ(y:ℝ).y^2,bindD((μ(f:ℕ→Distribution(ℕ)).λ(n:ℕ). if n=0 then δ((2:ℕ)) else scaleD(1/2,f(n sub 1)))(k),λ(x:ℕ).δ((x:ℝ)+1))))","ℕ→ℝ","λ(k:ℕ). (9·(1/2)^k:ℝ)"),
	Case("CountdownTestMissing","λ(k:ℕ). massD(bindD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ). if n=0 then δ((2:ℝ)) else scaleD(1/2,f(n sub 1)))(k),undefined(ℝ→Distribution(ℕ))))","ℕ→ℝ","λ(k:ℕ). undefined(ℝ)"),
	Case("CountdownTestPole","λ(k:ℕ).massD(weightD(λ(x:ℝ).1/x,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ). if n=0 then δ((0:ℝ)) else scaleD(0,f(n sub 1)))(k)))","ℕ→ℝ","λ(k:ℕ). undefined(ℝ)"),
	Case("CountdownTestSeedWeight","λ(k:ℕ).massD(weightD(λ(x:ℝ).x,(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then weightD(λ(x:ℝ).x+1,δ((2:ℝ))) else scaleD(1/2,f(n sub 1)))(k)))","ℕ→ℝ","λ(k:ℕ). (6·(1/2)^k:ℝ)"),
	Case("CountdownSigned","λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then scaleD(-3,δ((0:ℝ))) else scaleD(-2,f(n sub 1)))(k))","ℕ→ℝ","λ(k:ℕ). (-3·(-2)^k:ℝ)"),
	Case("CountdownCapturedSeed","λ(d:Distribution(ℕ→ℕ)).λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℕ→ℕ)).λ(n:ℕ).if n=0 then d else scaleD(1/2,f(n sub 1)))(k))",
		"Distribution(ℕ→ℕ)→ℕ→ℝ","λ(d:Distribution(ℕ→ℕ)). λ(k:ℕ). (∫(x:ℕ→ℕ). (d)[x])·(1/2)^k"),
	Case("CountdownHundred","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(1/2,f(n sub 1)))(100))","ℝ","1/1267650600228229401496703205376"),
	Case("CountdownZeroAtZero","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(0,f(n sub 1)))(0))","ℝ","1"),
	Case("CountdownPartialIndex","defined(massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(1/2,f(n sub 1)))(0 sub 1)))","𝔹","false"),
	Case("CountdownPartialRatioZero","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(undefined(ℝ),f(n sub 1)))(0))","ℝ","1"),
	Case("CountdownPartialRatioOne","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(undefined(ℝ),f(n sub 1)))(1))","ℝ","undefined(ℝ)"),
	Case("CountdownDifferentStride","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(1/2,f(n sub 2)))(4))","ℝ","1/4"),
	Case("RecursiveScaledMass","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(1/2,f(n sub 1)))(3))","ℝ","1/8"),
	Case("RecursiveScaledAtom","densityAtD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(1/2,f(n sub 1)))(3),0)","ℝ","undefined(ℝ)"),
	Case("RecursiveMixtureMass","massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else addD(δ((1:ℝ)),scaleD(1/2,f(n sub 1))))(2))","ℝ","7/4"),
	Case("RecursiveStatePair","massD((μ(f:ℕ×𝔹→Distribution(ℝ)).λ(t:ℕ×𝔹).if get(t,0)=0 then δ((0:ℝ)) else scaleD(1/2,f((get(t,0) sub 1,get(t,1)))) )((2,true)))","ℝ","1/4"),
	Case("RecursiveDistributionState","(μ(f:Distribution(ℝ)→ℝ).λ(d:Distribution(ℝ)).if massD(d)=1 then 4 else f(δ((0:ℝ))))(scaleD(2,δ((7:ℝ))))","ℝ","4"),
	Case("RecursiveDistributionOutcome","(μ(f:ℕ→Distribution(Distribution(ℝ))).λ(n:ℕ).if n=0 then δ(δ((0:ℝ))) else f(n sub 1))(1)","Distribution(Distribution(ℝ))","δ(δ((0:ℝ)))"),
	Case("RecursiveFunctionOutcome","(μ(f:ℕ→Distribution(ℕ→ℕ)).λ(n:ℕ).if n=0 then δ(λ(k:ℕ).k) else f(n sub 1))(1)","Distribution(ℕ→ℕ)","δ(λ(k:ℕ). k)"),
	Case("RecursiveDistributionBottom","(μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).f(n))(3)","Distribution(ℝ)","undefined(Distribution(ℝ))"),
	Case("RecursivePartialArgument","defined((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else f(n sub 1))(0 sub 1))","𝔹","false"),
	Case("RecursiveAtom","(μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 0 else massD(δ(f(n sub 1))))(2)","ℝ"),
	Case("RecursiveConstant","μ(f:ℕ→ℝ).λ(n:ℕ).massD(δ(1))","ℕ→ℝ")
]; }

private void run(string directory){
	foreach(c;cases()){
		scope(failure) writeln("Failed distribution case: ",c.name);
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
		enforce(s.inspectType(a,c.source)==c.type,c.name~" type: "~s.inspectType(a,c.source));
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true));
		enforce(!r.exhausted,c.name~" exhausted");
		auto text=s.format(a,r);
		if(c.expected.length) enforce(text==c.expected,c.name~": "~text);
		if(c.name=="DensityRecovery") enforce(text=="[x≠0]",c.name~": "~text);
		if(c.name=="Interval"||c.name=="PuncturedInterval") enforce(text=="2",c.name~": "~text);
		if(c.name=="UnboundedPuncture") enforce(text=="∫dx λ[x]",c.name~": "~text);
		if(c.name=="Integral") enforce(text=="2",c.name~": "~text);
		if(c.name=="RecursiveAtom") enforce(text=="1",c.name~": "~text);
		auto again=s.run(a,text,[],Options(DensityMode.preserve,true));
		auto roundTrip=s.format(a,again);
		enforce(roundTrip==text,c.name~" round trip: "~text~" -> "~roundTrip);
		auto certificate=s.exportCertificate(a,r);
		// These existing rules now cross a proved bridge to the reference-aware
		// model. Keep their proof dependencies from silently reverting to the
		// presentation-only lemmas while the remaining backend is migrated.
		import std.string:indexOf;
		if(c.name.indexOf("PrintedOperand")==0) enforce(s.inspectType(a,text)==c.type,c.name~" printed type");
		if(c.name=="InfiniteSeriesVarying"||c.name=="SeriesFibreNaturalCounting"||c.name=="SeriesFibreIntegerHit"||
			c.name=="SeriesFibreIntegerGap"||c.name=="SeriesFibreNaturalHit"||c.name=="SeriesFibreNaturalGap"||c.name=="SeriesFibreMissing")
			enforce(certificate.indexOf("Distribution.counting_")>=0,c.name);
		else if(c.name.indexOf("SeriesFibre")==0)
			enforce(certificate.indexOf("Distribution.FibreCertificate.extract_sum")>=0||
				certificate.indexOf("Distribution.FibreCertificate.extract_nat_sum")>=0,c.name);
		if(c.name=="ShiftOrbitMean"||c.name=="ShiftOrbitSecond"||c.name=="ShiftOrbitCubic"||c.name=="ShiftOrbitSixth"||
				c.name=="ShiftOrbitPolynomial"||c.name=="ShiftOrbitPowerOfSum"||c.name=="ShiftOrbitFractional"||
				c.name=="ShiftOrbitOffsetSquare"||c.name=="ShiftOrbitUnnormalizedSecond"){
			enforce(certificate.indexOf("Atomic.nat_shift_polynomial")>=0,c.name~" polynomial proof");
			enforce(certificate.indexOf("Summation.tail_solution")<0,c.name~" replayed a symbolic antidifference");
		}
		if(c.name=="ShiftOrbitAlternating"||c.name=="ShiftOrbitAmplified")
			enforce(certificate.indexOf("SummationElementary.PowerAt.product")>=0,c.name);
		if(c.name=="ShiftOrbitPole"||c.name=="ShiftOrbitPoleAfterZero")
			enforce(certificate.indexOf("SummationLinearity.missing_guard")>=0,c.name);
		if(c.name=="InvolutionBare")
			enforce(text.indexOf("μ")>=0&&certificate.indexOf("fixed_involution_q")<0,c.name~" noncontracting source");
		if(c.name.indexOf("CycleDivergent")==0)
			enforce(certificate.indexOf(c.name.indexOf("CycleDivergentBare")==0?"fixed_involution_unscaled":"fixed_involution_noncontracting")>=0,c.name~" separate parity tests");
		if(c.name.indexOf("CycleBool")==0||c.name.indexOf("CycleReal")==0)
			enforce(certificate.indexOf("CountableObservation.fixed_involution_q")>=0,c.name~" involution certificate");
		if(c.name.indexOf("Reemit")==0)
			enforce(certificate.indexOf("Affine.bind_self")>=0||certificate.indexOf("Affine.realBind_self")>=0,c.name~" identity kernel");
		if(c.name.indexOf("ShiftOrbit")==0&&c.name!="ShiftOrbitBare")
			enforce(certificate.indexOf("CountableObservation.nat_shift")>=0||certificate.indexOf("Atomic.nat_shift_mass")>=0||
				certificate.indexOf("Atomic.nat_shift_polynomial")>=0,c.name~" shift observation");
		if(c.name.indexOf("RetryUnbounded")==0&&c.name!="RetryUnboundedMissingProbe")
			enforce(certificate.indexOf("CountableObservation.retry_noncontracting")>=0,c.name);
		if(c.name.indexOf("LoopDensity")==0&&c.name!="LoopDensityMissingSeed"&&c.name!="LoopDensityMissingQuery")
			enforce(certificate.indexOf("Atomic.density_retry_seed")>=0,c.name);
		if(c.name.indexOf("LoopExists")==0&&c.name!="LoopExistsMissing")
			enforce(certificate.indexOf("Atomic.retry_isSome")>=0,c.name);
		if(c.name.indexOf("InfiniteRetry")==0){
			if(c.name!="InfiniteRetryDirectSeries") enforce(certificate.indexOf("Atomic.retry_infinite_point")>=0,c.name);
			if(c.name=="InfiniteRetryAt"||c.name=="InfiniteRetryAway"||c.name=="InfiniteRetryDensity"||c.name=="InfiniteRetryDirectSeries")
				enforce(certificate.indexOf("Atomic.density_constant_dirac_series")>=0,c.name);
		}
		if(c.name.indexOf("WeightEmpty")==0&&c.name!="WeightEmptyMissing") enforce(certificate.indexOf("Distribution.weight_zeroValue")>=0,c.name);
		if(c.name.indexOf("AffineBody")==0) enforce(certificate.indexOf("Distribution.Atomic.fixed_affine")>=0,c.name);
		if(c.name.indexOf("RetryVisits")==0){
			if(c.name=="RetryVisitsEmpty") enforce(certificate.indexOf("Atomic.retry_empty")>=0,c.name);
			else if(c.name=="RetryVisitsDistinct") enforce(certificate.indexOf("Atomic.retry_zero_point")<0&&text.indexOf("μ")>=0,c.name);
			else if(c.name=="RetryVisitsCritical"||c.name=="RetryVisitsSupercritical"||c.name=="RetryVisitsZeroDensity")
				enforce(certificate.indexOf("Atomic.retry_zero_point")>=0,c.name);
			else enforce(certificate.indexOf("Atomic.point_add")>=0,c.name);
		}
		if(c.name.indexOf("LinearTail")==0){
			bool empty=c.name=="LinearTailSelf"||c.name=="LinearTailScaled"||c.name=="LinearTailCopied"||c.name=="LinearTailFunction";
			enforce(certificate.indexOf(empty?"Distribution.Atomic.fixed_tail":"Distribution.Atomic.fixed_add_tail")>=0,c.name);
		}
		if(c.name.indexOf("RetryObservation")==0&&c.name!="RetryObservationMissingProbe"&&c.name!="RetryObservationMissingKernel"){
			enforce(certificate.indexOf("Distribution.Atomic.Observation.retry")>=0,c.name);
			if(c.name=="RetryObservationMappedMoment") enforce(certificate.indexOf("Observation.realBind (Distribution.Atomic.Observation.weight")>=0,c.name);
		}
		if(c.name.indexOf("AtomicRetry")==0) enforce(certificate.indexOf("Distribution.Atomic.fixed_retry")>=0,c.name);
		if(c.name=="AtomicRetryMass"||c.name=="AtomicRetryDensity")
			enforce(certificate.indexOf(c.name=="AtomicRetryMass"?"Atomic.mass_retry":"Atomic.density_retry")>=0,c.name);
		if(c.name.indexOf("DensityHole")==0){
			bool witness=c.name!="DensityHoleDirac"&&c.name!="DensityHoleAbstract"&&c.name!="DensityHoleUnknown"&&c.name!="DensityHoleMasked";
			enforce((certificate.indexOf("MissingPoint.InDensity.mass ")>=0)==witness,c.name);
		}
		if(c.name.indexOf("MissingQuadratic")==0){
			bool witness=c.name!="MissingQuadraticInactive"&&c.name!="MissingQuadraticOutside"&&
				c.name!="MissingQuadraticHoleHidden"&&c.name!="MissingQuadraticSafe";
			enforce((certificate.indexOf("MissingPoint.InDensity.mass ")>=0)==witness,c.name);
		}
		if(c.name.indexOf("DirectedRange")==0){
			bool changed=c.name!="DirectedRangePole"&&c.name!="DirectedRangeGap"&&c.name!="DirectedRangeTouch";
			bool integrated=certificate.indexOf("Grid.Directed.interval ")>=0||certificate.indexOf("Grid.VariationChange.interval ")>=0;
			enforce(integrated==changed,c.name);
		}
		if(c.name.indexOf("Variation")==0){
			bool changed=c.name!="VariationJump";
			enforce((certificate.indexOf("Grid.VariationChange.interval ")>=0)==changed,c.name);
		}
		if(c.name.indexOf("MissingOutput")==0){
			bool witnessed=c.expected=="undefined(ℝ)";
			enforce((certificate.indexOf("GraphFibre.MissingOutput.")>=0)==witnessed,c.name);
			if(c.name=="MissingOutputWeighted"||c.name=="MissingOutputInverseZero")
				enforce(certificate.indexOf("MissingOutput.weight ")>=0,c.name);
			if(c.name=="MissingOutputZeroGuard"||c.name=="MissingOutputOutside")
				enforce(certificate.indexOf("MissingPoint.quadratic ")>=0,c.name);
		}
		if(c.name.indexOf("IversonParameter")==0){
			bool reciprocal=c.name=="IversonParameterGuardedInverse"||c.name=="IversonParameterInverseMass";
			bool masked=c.name=="IversonParameterBoolean"||c.name=="IversonParameterCompare"||c.name=="IversonParameterWeak"||
				c.name=="IversonParameterAnd"||c.name=="IversonParameterOr"||c.name=="IversonParameterNegated"||
				c.name=="IversonParameterMasked"||c.name=="IversonParameterBooleanMass";
			enforce((certificate.indexOf("Value.defined_guarded_inv ")>=0)==reciprocal,c.name);
			enforce((certificate.indexOf("Value.defined_mask_total ")>=0)==masked,c.name);
			if(c.name=="IversonParameterAnd") enforce(certificate.indexOf("Value.defined_and_total ")>=0,c.name);
			if(c.name=="IversonParameterOr") enforce(certificate.indexOf("Value.defined_or_total ")>=0,c.name);
		}
		if(c.name.indexOf("ScalarBinder")==0){
			import std.string:count;
			bool nested=c.name=="ScalarBinderMixed"||c.name=="ScalarBinderSameType";
			bool direct=c.name=="ScalarBinderHigherOrder"||c.name=="ScalarBinderPartial"||c.name=="ScalarBinderSpecialized";
			enforce(certificate.count(".lamOpened ")==(nested?2:direct?0:1),c.name);
			enforce(s.inspectType(a,text)==c.type,c.name~" parameter type after printing");
		}
		if(c.name.indexOf("CoordinateParameter")==0){
			bool directed=c.name=="CoordinateParameterIntegral"||c.name=="CoordinateParameterIncreasing"||
				c.name=="CoordinateParameterDecreasing"||c.name=="CoordinateParameterConstantMass";
			bool partial=c.name=="CoordinateParameterSingular"||c.name=="CoordinateParameterMissing"||c.name=="CoordinateParameterLookup";
			enforce((certificate.indexOf("Grid.Slope.parameter ")>=0)==(!directed&&!partial),c.name);
			enforce((certificate.indexOf("Grid.Directed.parameter ")>=0)==directed,c.name);
			if(c.name=="CoordinateParameterBound") enforce(certificate.indexOf(".lamOpened ")>=0,c.name);
		}
		if(c.name.indexOf("IntervalFactor")==0){
			bool factored=c.name=="IntervalFactorSigned"||c.name=="IntervalFactorPositive"||c.name=="IntervalFactorSymbolic"||
				c.name=="IntervalFactorConstantRight"||c.name=="IntervalFactorSignedSine"||c.name=="IntervalFactorHigherOrder"||
				c.name=="IntervalFactorSum"||c.name=="IntervalFactorTwoCoefficients"||c.name=="IntervalFactorInsideSum"||
				c.name=="IntervalFactorCauchySine"||c.name=="IntervalFactorBounds"||c.name=="IntervalFactorZeroAreaPartial";
			bool left=certificate.indexOf("StepSource.IntervalTerms.factor ")>=0,right=certificate.indexOf("StepSource.IntervalTerms.factorRight ")>=0;
			enforce((left||right)==factored,c.name);
			if(c.name=="IntervalFactorTwoCoefficients") enforce(left&&right,c.name);
			if(c.name=="IntervalFactorOpaque"||c.name=="IntervalFactorImproper"||c.name=="IntervalFactorSingular") enforce(text.indexOf("∫")>=0,c.name);
		}
		if(c.name.indexOf("TrigIntegral")==0){
			bool residual=c.name=="TrigIntegralMissing"||c.name=="TrigIntegralNonlinear"||c.name=="TrigIntegralHalfLine";
			bool parameters=c.name=="TrigIntegralUnknownFrequency";
			enforce((certificate.indexOf("StepSource.HasPrimitive.parameters ")>=0)==parameters,c.name);
			enforce((certificate.indexOf("StepSource.HasPrimitive.interval ")>=0)==(!residual&&!parameters&&c.name!="TrigIntegralBounds"),c.name);
			enforce((text.indexOf("∫")>=0)==residual,c.name);
		}
		if(c.name.indexOf("TrigParameter")==0){
			bool residual=c.name=="TrigParameterQuadratic"||c.name=="TrigParameterRay";
			bool constantCase=c.name=="TrigParameterZero"||c.name=="TrigParameterUndefined"||c.name=="TrigParameterUndefinedShift"||
				c.name=="TrigParameterClosedSingleton"||c.name=="TrigParameterOpenSingleton";
			enforce((certificate.indexOf("StepSource.HasPrimitive.parameters ")>=0)==(!residual&&!constantCase),c.name);
			enforce((text.indexOf("∫")>=0)==residual,c.name);
		}
		if(c.name.indexOf("RepeatedIverson")==0){
			bool repeated=c.name!="RepeatedIversonDistinct"&&c.name!="RepeatedIversonDifferentOrder"&&
				c.name!="RepeatedIversonMissing"&&c.name!="RepeatedIversonHidden";
			enforce((certificate.indexOf("Value.UnderMask.sound ")>=0)==repeated,c.name);
			if(c.name=="RepeatedIversonThreeGuards") enforce(certificate.indexOf("Value.UnderMask.nested ")>=0,c.name);
		}
		if(c.name.indexOf("CombinedMass")==0){
			bool combined=c.name=="CombinedMassJump"||c.name=="CombinedMassJumpPeriod"||c.name=="CombinedMassZero"||
				c.name=="CombinedMassThree"||c.name=="CombinedMassFour"||c.name=="CombinedMassSignedInterval";
			enforce((certificate.indexOf("DensityProgram.presentation_extractedWeight ")>=0)==combined,c.name);
		}
		if(c.name.indexOf("CoordinatePuncture")==0){
			bool smooth=c.name!="CoordinatePuncturePointDensity"&&c.name!="CoordinatePunctureJumpHit"&&
				c.name!="CoordinatePunctureJumpExcluded"&&c.name!="CoordinatePunctureHiddenPole";
			enforce((certificate.indexOf("SmoothSource.excluded_mass ")>=0)==smooth,c.name);
			if(smooth) enforce(text.indexOf("∫")<0,c.name);
		}
		if(c.name.indexOf("CoordinateWeight")==0){
			bool scaled=c.name!="CoordinateWeightInfinite"&&c.name!="CoordinateWeightZero";
			enforce((certificate.indexOf("Grid.scale_masked_mass ")>=0)==scaled,c.name);
			if(scaled) enforce(text.indexOf("∫")<0,c.name);
		}
		if(c.name.indexOf("CoordinateInterval")==0||c.name=="CauchyWindowAtan"||c.name=="CauchyWindowAtanScaled"){
			bool directed=c.name!="CoordinateIntervalTurning"&&c.name!="CoordinateIntervalOpposite"&&c.name!="CoordinateIntervalJump";
			enforce((certificate.indexOf("Grid.Directed.interval ")>=0)==directed,c.name);
		}else if(c.name.indexOf("CauchyRay")==0){
			bool integrated=c.name!="CauchyRayMissing"&&c.name!="CauchyRayPole";
			auto law=c.name=="CauchyRayUpperZero"||c.name=="CauchyRayScaledAtan"?"Grid.Directed.ray ":"Distribution.StepSource.cauchyRay ";
			enforce((certificate.indexOf(law)>=0)==integrated,c.name);
		}else if(c.name.indexOf("CauchyWindow")==0||c.name=="QuotientPoleQuadratic"){
			bool integrated=c.name!="CauchyWindowReverse"&&c.name!="CauchyWindowSingleton"&&c.name!="CauchyWindowZeroMask"&&
				c.name!="CauchyWindowMissing"&&c.name!="CauchyWindowPole";
			enforce((certificate.indexOf("IntervalTerms.cauchy")>=0)==integrated,c.name);
		}else if(c.name=="CauchyScaledAtan"||c.name=="CauchyAtanWhole"){
			enforce(certificate.indexOf("Grid.Directed.whole ")>=0,c.name);
		}else if(c.name.indexOf("CauchyScale")==0&&c.name!="CauchyScaledAxis"){
			bool scaled=c.name!="CauchyScalePole"&&c.name!="CauchyScaleZero";
			enforce((certificate.indexOf("StepSource.cauchy_scaled_mass ")>=0)==scaled,c.name);
		}else if(c.name.indexOf("Cauchy")==0){
			bool finite=c.name!="CauchyPole"&&c.name!="CauchyTouch"&&c.name!="CauchyQuartic"&&c.name!="CauchyAffine"&&c.name!="CauchyMeasure";
			enforce((certificate.indexOf("StepSource.cauchy_mass ")>=0)==finite,c.name);
		}
		if(c.name.indexOf("Turning")==0){
			bool whole=certificate.indexOf("Grid.VariationChange.whole ")>=0,half=certificate.indexOf("Grid.VariationChange.ray ")>=0;
			enforce(whole==(c.name.indexOf("TurningWhole")==0)&&half==(c.name.indexOf("TurningRay")==0),c.name);
			if(whole||half) enforce(text.indexOf("∫")<0&&text.indexOf("lim[")<0,c.name);
		}
		if(c.name.indexOf("TanhCoordinate")==0&&c.name!="TanhCoordinateRemovable"&&c.name!="TanhCoordinateHole"&&
			c.name!="TanhCoordinateUnsupported"&&c.name!="TanhCoordinatePole")
			enforce(certificate.indexOf("ScalarChange.tanh")>=0,c.name);
		if(c.name.indexOf("Atan")==0)
			enforce(certificate.indexOf("ScalarChange.arctan")>=0&&text.indexOf("λ[atan(")<0,c.name);
		if(c.name.indexOf("ObservedGuard")==0)
			enforce((certificate.indexOf("Binding.map_guard_of_strict ")>=0)==(c.name!="ObservedGuardMasked"),c.name);
		if(c.name.indexOf("AffineCycle")==0){
			enforce(certificate.indexOf("Distribution.Atomic.dirac_reflection ")>=0&&text.indexOf("μ")<0,c.name);
			if(c.name=="AffineCyclePartial") enforce(text.indexOf("h(1)")>=0&&text.indexOf("h(4)")>=0,c.name);
		}
		if(c.name.indexOf("IndexedVisit")==0)
			enforce(certificate.indexOf("Distribution.observe_indexed_countdown ")>=0&&text.indexOf("μ")<0,c.name);
		if(c.name.indexOf("MaskContext")==0){
			bool erased=c.name!="MaskContextReciprocal"&&c.name!="MaskContextNonstrict"&&c.name!="MaskContextOtherPoint"&&c.name!="MaskContextMissingGuard";
			enforce((certificate.indexOf("Value.mask_nonzero_context ")>=0)==erased,c.name);
		}
		if(c.name=="OpaquePunctureWeight"||c.name=="OpaquePuncturePrefix"||c.name=="OpaquePunctureSquare"||c.name=="OpaquePunctureDensity")
			enforce(certificate.indexOf("Distribution.StepSource.affine_mask_of_zero ")>=0,c.name);
		if(c.name=="OrderedPunctureCoordinate"||c.name=="OrderedPunctureLeft"||c.name=="OrderedPunctureRight"||
			c.name=="OrderedPunctureHiddenPole"||c.name=="OrderedPunctureAfterPartial")
			enforce(certificate.indexOf("Distribution.StepSource.affine_mask_of_zero ")>=0&&
				certificate.indexOf("Distribution.StepSource.mask_mask ")>=0,c.name);
		if(c.name=="MaskRootCoordinate"||c.name=="MaskRootFraction"||c.name=="MaskRootPolynomial"||
			c.name=="MaskRootThree"||c.name=="MaskRootOneKept"||c.name=="MaskRootAfterPartial")
			enforce(certificate.indexOf("Distribution.StepSource.affine_mask_of_zero ")>=0,c.name);
		if(c.name=="MaskRootThree") enforce(certificate.indexOf("Value.mask_and_congr_right ")>=0,c.name);
		if(c.name.indexOf("EraseMask")==0||c.name.indexOf("KeepMask")==0)
			enforce((certificate.indexOf("Value.mask_nonzero_of_zero ")>=0)==(c.name.indexOf("EraseMask")==0),c.name);
		if(c.name.indexOf("UnitEmission")==0||c.name=="EmittingThousand"){
			enforce(certificate.indexOf("Distribution.observe_unit_countdown ")>=0,c.name~" accumulated emission");
			if(c.name=="UnitEmissionMillion") enforce(certificate.length<60_000,c.name~" expanded recursive visits");
		}else if(c.name.indexOf("Emitting")==0)
			enforce(certificate.indexOf("Distribution.observe_emitting_countdown ")>=0&&text.indexOf("μ")<0&&text.indexOf("∑")<0,c.name~" finite geometric observation");
		if(c.name.indexOf("UniformCountdownFive")==0||c.name=="SmallRangePolynomial")
			enforce(certificate.indexOf("Summation.range_step ")<0&&certificate.indexOf("Summation.range_solution_partial ")>=0,c.name);
		if(c.name=="UniformCountdownFive") enforce(certificate.length<225_000,c.name~" expanded scalar visits");
		if(c.name.indexOf("OpaqueUnitPair")==0)
			enforce((certificate.indexOf("Value.mul_pair_one ")>=0)==(c.name!="OpaqueUnitPairZero"),c.name);
		if(c.name=="UniformCountdownProbe")
			enforce(certificate.indexOf("Value.mul_pair_one ")>=0&&text.indexOf("i+1+1")<0,c.name~": "~text);
		if(c.name.indexOf("IntegratingFactor")==0||c.name.indexOf("UniformCountdown")==0){
			bool solved=c.name!="IntegratingFactorPole";
			enforce((certificate.indexOf("Distribution.observe_product_emitting_countdown ")>=0)==solved,c.name);
			enforce((text.indexOf("μ")<0)==solved,c.name);
			bool finiteSum=c.name=="IntegratingFactorHarmonic"||c.name=="IntegratingFactorHigher"||c.name=="UniformCountdownProbe";
			if(solved) enforce((text.indexOf("∑")>=0)==finiteSum,c.name~": "~text);
		}
		if(c.name.indexOf("GapProduct")==0){
			bool solved=c.name!="GapProductPole"&&c.name!="GapProductHitsPole"&&c.name!="GapProductHalfStep";
			enforce((certificate.indexOf("Distribution.product_step_cross ")>=0)==solved,c.name);
			if(c.name!="GapProductHitsPole") enforce((text.indexOf("μ")<0)==solved,c.name);
			if(c.name=="GapProductMillion") enforce(certificate.length<125_000,c.name~" expanded visits");
		}
		if(c.name.indexOf("ProductCross")==0){
			enforce(certificate.indexOf("Distribution.product_step_cross ")>=0&&text.indexOf("μ")<0,c.name);
			if(c.name=="ProductCrossReversedR") enforce(certificate.indexOf("Distribution.product_ratio_comm ")>=0,c.name);
			if(c.name=="ProductCrossReversedQ") enforce(certificate.indexOf("Distribution.product_ratio_cast ")>=0,c.name);
		}
		if(c.name.indexOf("VisitQuotient")==0)
			enforce((certificate.indexOf("Distribution.observe_product_countdown ")>=0)==(c.name!="VisitQuotientCrossesZero"),c.name);
		if(c.name.indexOf("ProductScale")==0){
			bool solved=c.name!="ProductScalePole"&&c.name!="ProductScaleHitsPole";
			enforce((certificate.indexOf("Distribution.observe_product_countdown ")>=0)==solved,c.name);
			if(solved) enforce(text.indexOf("μ")<0,c.name);
			if(c.name=="ProductScalePole") enforce(text.indexOf("μ")>=0,c.name);
			if(c.name=="ProductScaleMillion") enforce(certificate.length<75_000,c.name~" expanded countdown");
		}
		if(c.name.indexOf("Convolution")==0){
			enforce(certificate.indexOf("Distribution.observe_convolution_countdown ")>=0&&text.indexOf("μ")<0,c.name);
			if(c.name=="ConvolutionMissingIndex") enforce(certificate.indexOf("Binding.conditional_undefined ")>=0,c.name);
			if(c.name=="ConvolutionHigher") enforce(text.indexOf("h(1)^")>=0&&text.indexOf("powRN(")<0,c.name);
		}
		if(c.name=="VaryingEmission"||c.name.indexOf("DiscountVisit")==0)
			enforce(certificate.indexOf("Distribution.observe_discounted_countdown ")>=0&&text.indexOf("μ")<0,c.name);
		if(c.name.indexOf("CapturedScale")==0||c.name=="CountdownPartialRatioZero"||c.name=="CountdownPartialRatioOne")
			enforce(certificate.indexOf("Distribution.observe_partial_scale_countdown ")>=0,c.name~" captured recursive scale");
		if(c.name=="VariableScaleByIndex")
			enforce(certificate.indexOf("observe_partial_scale_countdown")<0&&text.indexOf("μ")>=0,c.name~" index-dependent scale");
		if(c.name.indexOf("AffineTurn")==0){
			bool changed=c.name!="AffineTurnNonlinear"&&c.name!="AffineTurnMissingCoefficient"&&c.name!="AffineTurnOpaque";
			enforce((certificate.indexOf("Grid.VariationChange.translate ")>=0)==changed,c.name);
			enforce((certificate.indexOf("Grid.VariationChange.scale ")>=0)==(changed&&c.name!="AffineTurnOffset"),c.name);
			bool missing=c.name=="AffineTurnMissingCoefficient";
			enforce((certificate.indexOf("MissingOutput.mass ")>=0)==missing,c.name);
			enforce((text.indexOf("∫")<0)==(changed||missing),c.name);
		}
		if(c.name.indexOf("PowerWave")==0||c.name=="VariationOscillating"){
			bool solved=c.name!="PowerWaveUnknownVelocity"&&c.name!="PowerWaveInfinite";
			enforce((certificate.indexOf("WaveProfile.power ")>=0)==solved,c.name);
			enforce((text.indexOf("∫")<0)==solved,c.name);
		}
		if(c.name=="SmoothWaveSymbolic")
			enforce(text.indexOf("λ(u:ℝ).")==0&&certificate.indexOf("r_real_cos_nonzero_unit")>=0,c.name);
		if(c.name.indexOf("SmoothWave")==0||c.name=="PeriodicSpanNonmonotone"){
			bool solved=c.name!="SmoothWavePole"&&c.name!="SmoothWaveReciprocal"&&c.name!="SmoothWaveUnknown";
			enforce((certificate.indexOf("WaveProfile.variation ")>=0)==solved,c.name);
			enforce((text.indexOf("∫")<0)==solved,c.name);
		}
		if(c.name.indexOf("PeriodicSpan")==0&&c.name!="PeriodicSpanNonmonotone"){
			bool solved=c.name!="PeriodicSpanUnbounded";
			enforce((text.indexOf("∫")<0)==solved,c.name~": "~text);
			enforce((certificate.indexOf("Grid.VariationChange.sine")>=0||certificate.indexOf("Grid.VariationChange.cosine")>=0)==solved,c.name);
		}
		if(c.name.indexOf("DirectedTotal")==0){
			bool closed=c.name!="DirectedTotalPole"&&c.name!="DirectedTotalOneEnd"&&
				c.name!="DirectedTotalOscillation"&&c.name!="DirectedTotalTurning";
			enforce((certificate.indexOf("Grid.Directed.whole ")>=0)==closed,c.name);
			if(closed) enforce(text.indexOf("∫")<0&&text.indexOf("lim[")<0,c.name);
		}
		if(c.name.indexOf("DirectedRay")==0){
			bool closed=c.name!="DirectedRayPole"&&c.name!="DirectedRayUnbounded";
			enforce((certificate.indexOf("Grid.Directed.ray ")>=0)==closed,c.name);
			if(closed) enforce(text.indexOf("∫")<0&&text.indexOf("lim[")<0,c.name);
		}
		if(c.name.indexOf("ScalarAsymptote")==0){
			bool uses=c.name!="ScalarAsymptoteLogisticRegular"&&c.name!="ScalarAsymptoteOpposite"&&
				c.name!="ScalarAsymptoteOscillation"&&c.name!="ScalarAsymptoteOpaque"&&c.name!="ScalarAsymptoteMissing";
			enforce((certificate.indexOf("Limit.Escapes.")>=0)==uses,c.name);
		}
		if(c.name.indexOf("IndexAddend")==0){
			enforce(text.indexOf("∑")<0,c.name);
			if(c.name!="IndexAddendMissing") enforce(certificate.indexOf("Summation.mask_addend ")>=0,c.name);
		}
		if(c.name.indexOf("RangeProbe")==0||c.name=="VisitFibreMillion"||c.name=="VisitFibreLast"||c.name=="VisitFibreSymbolic"){
			enforce(text.indexOf("∑")<0,c.name);
			if(c.name!="RangeProbeMissingEmpty"&&c.name!="RangeProbeMissingVisit"&&c.name!="RangeProbeLazy")
				enforce(certificate.indexOf("Summation.range_real_N ")>=0||certificate.indexOf("Summation.range_shifted_real_N ")>=0,c.name);
		}
		if(c.name.indexOf("SquareSelector")==0){
			bool selected=c.name!="SquareSelectorInteger";
			enforce((certificate.indexOf("_chart_N Summation.NaturalIndexMap.square")>=0)==selected,c.name);
			if(selected) enforce(text.indexOf("∑")<0,c.name);
		}
		if(c.name.indexOf("SelectedRow")==0||c.name.indexOf("ProductFibreUniformMillion")==0||
			c.name=="ProductFibreUniformSymbolic"||c.name=="ProductFibreUnweighted"){
			enforce(text.indexOf("∑")<0,c.name~": "~text);
			bool total=c.name!="SelectedRowPole"&&c.name!="SelectedRowFreePole"&&c.name!="SelectedRowEmptyPole";
			enforce((certificate.indexOf("Summation.SelectedRow.range ")>=0)==total,c.name);
			if(total) enforce(certificate.indexOf("Summation.range_step ")<0,c.name);
			if(c.name=="SelectedRowNested"||c.name=="SelectedRowOpaque") enforce(certificate.indexOf("Summation.SelectedRow.factor ")>=0,c.name);
		}
		if(c.name.indexOf("ProductFibre")==0){
			bool solved=c.name!="ProductFibreOpaque"&&c.name!="ProductFibrePole";
			enforce((certificate.indexOf("Distribution.RealDensityFibre.product_emitting_countdown ")>=0)==solved,c.name);
			enforce((text.indexOf("μ")<0)==solved,c.name);
		}
		if(c.name.indexOf("PowerSelect")==0||c.name.indexOf("DiscountProbe")==0||c.name=="DiscountFibreCaptured"){
			enforce(text.indexOf("∑")<0&&text.indexOf("μ")<0,c.name~": "~text);
			if(c.name=="PowerSelectIndex"||c.name=="PowerSelectSucc"||c.name=="PowerSelectRemaining"||c.name=="DiscountFibreCaptured")
				enforce(certificate.indexOf("Summation.RangeDefined.mask ")>=0,c.name);
			if(c.name=="PowerSelectZero") enforce(certificate.indexOf("Summation.RangeDefined.zero ")>=0,c.name);
			if(c.name=="PowerSelectUnsafeExponent") enforce(certificate.indexOf("Summation.RangeDefined.")<0,c.name);
		}
		if(c.name.indexOf("DiscountFibre")==0){
			bool solved=c.name!="DiscountFibreOpaqueSeed";
			enforce((certificate.indexOf("Distribution.RealDensityFibre.convolution_countdown ")>=0)==solved,c.name);
			if(solved) enforce(text.indexOf("μ")<0,c.name);
		}
		if(c.name.indexOf("VisitFibre")==0){
			bool indexed=c.name!="VisitFibreOpaqueSeed";
			enforce((certificate.indexOf("Distribution.RealDensityFibre.indexed_countdown ")>=0)==indexed,c.name);
			if(indexed) enforce(text.indexOf("μ")<0,c.name);
		}
		if(c.name.indexOf("FibreWeights")==0){
			bool factored=c.name!="FibreWeightsMoving";
			enforce((certificate.indexOf("Distribution.RealDensityFibre.factored_countdown ")>=0)==factored,c.name);
			if(factored) enforce(text.indexOf("μ")<0,c.name);
		}
		if(c.name.indexOf("FibreEmission")==0){
			bool constant=c.name.indexOf("Geometric")>=0||c.name.indexOf("Signed")>=0||c.name.indexOf("Zero")>=0;
			bool captured=c.name.indexOf("Unknown")>=0||c.name=="FibreEmissionSymbolicScale";
			auto law=constant?"centered_countdown":captured?"emitting_countdown":"unit_countdown";
			enforce(certificate.indexOf("Distribution.RealDensityFibre."~law~" ")>=0&&text.indexOf("μ")<0,c.name);
		}
		if(c.name.indexOf("FibreProduct")==0){
			bool solved=c.name!="FibreProductCrossesPole";
			enforce((certificate.indexOf("Distribution.RealDensityFibre.product_countdown ")>=0)==solved,c.name);
			if(solved) enforce(text.indexOf("μ")<0,c.name);
		}
		if(c.name.indexOf("FibreCountdown")==0){
			auto law=c.name.indexOf("Captured")>=0?"partial_scale_countdown":
				(c.name=="FibreCountdownPartialRegular"||c.name.indexOf("Zero")>=0)?"scale_countdown":"nonzero_scale_countdown";
			enforce(certificate.indexOf("Distribution.RealDensityFibre."~law~" ")>=0&&text.indexOf("μ")<0,c.name);
			if(c.name=="FibreCountdownMillion") enforce(certificate.length<65_000,c.name);
		}
		if(c.name.indexOf("CountdownTest")==0)
			enforce(certificate.indexOf("Distribution.observe_scale_countdown ")>=0,c.name~" checked homogeneous observation");
		else if(c.name.length>=9&&c.name[0..9]=="Countdown"){
			bool fallback=c.name=="CountdownDifferentStride"||c.name=="CountdownPartialRatioZero"||c.name=="CountdownPartialRatioOne";
			enforce((certificate.indexOf("Distribution.mass_scale_countdown")>=0)!=fallback,c.name~" countdown certificate");
		}
		if(c.name=="SymbolicJumpLong"||c.name=="SymbolicJumpReversed"||c.name=="ImageWindowPartial"||c.name=="SymbolicJumpOutside"){
			enforce(certificate.indexOf("Grid.restrictedPartialJump ")>=0,c.name~" partial traversal");
			enforce(text.indexOf("∫")>=0||c.name=="SymbolicJumpOutside",c.name~" retained a partial integrand");
			if(c.name=="SymbolicJumpLong"||c.name=="SymbolicJumpReversed") enforce(text.indexOf("if ")>=0,c.name~" unit weight");
			if(c.name=="ImageWindowPartial") enforce(text.indexOf("if ")<0,c.name~" subunit jump");
		}
		if(c.name=="SymbolicJumpDistant"||c.name=="ImageWindowEndpoint"||c.name=="JumpPartialRestriction"||
			c.name=="TraversalHoleInterior"||c.name=="TraversalHoleReversed"||c.name=="TraversalHoleCell")
			enforce(certificate.indexOf("Grid.restrictedMissingJump ")>=0,c.name~" strict traversal");
		if(c.name=="TraversalHoleMasked"||c.name=="TraversalHoleShortCircuit"||c.name=="SymbolicJumpOutside")
			enforce(certificate.indexOf("Grid.restrictedMissingJump ")<0,c.name~" masked or unreachable pole");
		if(c.name=="UnsplitAbsolute") enforce(text.indexOf("∫")>=0,c.name~": "~text);
		if(c.name.indexOf("PositiveCoordinate")==0)
			enforce(certificate.indexOf("Coordinates.Grid.Lower")>=0&&certificate.indexOf("Grid.Slope.")>=0,c.name);
		if(c.name=="CenteredCoordinateQuartic"||c.name=="PositiveCoordinateNestedInverse")
			enforce(certificate.indexOf(".ofEq (fun ξ _ => (Numeric.calculate_sound ξ ")>=0,c.name~" direct rational evaluation");
		if(c.name.indexOf("FlatCoordinate")==0)
			enforce((certificate.indexOf("Grid.massFlatChange")>=0)==(c.name!="FlatCoordinateGrowing"&&c.name!="FlatCoordinateBoundary"),c.name~" flat mass");
		if(c.name.indexOf("TraceCoordinate")==0)
			enforce((certificate.indexOf("Grid.probeRange")>=0)==(c.name!="TraceCoordinateDomain"),c.name~" traced coordinate domain");
		if(c.name.indexOf("ProbeGrid")==0)
			enforce(certificate.indexOf("Grid.probe")>=0,c.name~" missing direct point observation");
		if(c.name.indexOf("BoundNeutral")==0)
			enforce(certificate.indexOf("Value.add_zero_")>=0||certificate.indexOf("Value.mul_one_")>=0,c.name~" binding scalar identity");
		if(c.name.indexOf("DecreasingSmooth")==0)
			enforce(certificate.indexOf("Grid.magnitudeAt ")>=0,c.name~" normalized negative slope");
		if(c.name.indexOf("WindowProbe")==0||c.name.indexOf("ImageWindowCorner")==0){
			enforce(certificate.indexOf("Grid.probeImageAt ")>=0,c.name~" direct restricted point observation");
			if(c.name.indexOf("ImageWindowCorner")==0)
				enforce(certificate.length<120_000,c.name~" expanded a whole distribution for one point");
		}else if(c.name.indexOf("ImageWindow")==0){
			enforce(certificate.indexOf("Grid.finishImageRestricted ")>=0,c.name~" restricted change");
			if(c.name!="ImageWindowPartial"&&c.name!="ImageWindowEndpoint")
				enforce(certificate.indexOf("Grid.restrictedJumpFromLimits ")>=0,c.name~" clipped traversal");
		}
		if(c.name.indexOf("RootImage")==0||c.name=="ImageCoordinateIrrational")
			enforce((certificate.indexOf("Grid.sqrtImageJump ")>=0)==(c.name!="RootImagePartial"),c.name~" exact radical jump");
		if(c.name.indexOf("ImageCoordinate")==0)
			enforce(certificate.indexOf("Grid.finishImage ")>=0,c.name~" image events");
		if(c.name.indexOf("ChangedCoordinate")==0)
			enforce(certificate.indexOf("Grid.finishChange")>=0||certificate.indexOf("Grid.probeChange")>=0,c.name~" missing smooth change of a grid");
		if(c.name=="UnchangedCoordinateLogZero")
			enforce(certificate.indexOf("Grid.finishChange")<0,c.name~" lost a domain boundary");
		if(c.name.indexOf("NegativeCoordinate")==0)
			enforce(certificate.indexOf("Grid.Slope.inv_nonzero")>=0,c.name~" certified denominator");
		if(c.name=="CoordinateReciprocalPole"||c.name=="CoordinateNegativeLog")
			enforce(certificate.indexOf("Grid.Slope.inv_nonzero")<0&&certificate.indexOf("Grid.Slope.log")<0,c.name~" preserved domain");
		if(c.name.indexOf("CenteredCoordinate")==0)
			enforce(certificate.indexOf("Grid.Lower.centered")>=0,c.name~" rational translation");
		if(c.name=="CoordinateLogPole"||c.name=="CoordinateTouchingLog"||c.name=="CoordinateSignChangeLog")
			enforce(certificate.indexOf("Grid.Slope.log")<0,c.name~" lost the domain boundary");
		if(c.name.indexOf("RestrictedSmooth")==0) enforce(certificate.indexOf("Grid.polynomialRestricted")>=0,c.name);
		if(c.name.indexOf("RestrictedCorner")==0) enforce(certificate.indexOf("Grid.restrictedCorner")>=0,c.name);
		if(c.name.indexOf("RestrictedJump")==0) enforce(certificate.indexOf("Grid.restrictedJump")>=0,c.name);
		if(c.name.indexOf("Grid")==0){
			auto compiled=certificate.indexOf("GraphFibre.Coordinates.Grid.cell ")>=0;
			enforce(compiled==(c.name!="GridSpike"),c.name);
			if(c.name=="GridPartialTest") enforce(certificate.indexOf("Grid.shifted_pairing ")<0,c.name);
		}
		if(c.name=="SheetPartDensityPositive"||c.name=="SheetPartDensityExcluded"||c.name=="SheetPartDensityCritical")
			enforce(certificate.indexOf("GraphFibre.Coordinates.square_density")>=0,c.name);
		if(c.name=="SheetPartPairing"||c.name=="SheetPartCritical"||c.name=="SheetPartMass")
			enforce(certificate.indexOf("GraphFibre.Coordinates.square_"~(c.name=="SheetPartMass"?"mass":"pairing"))>=0,c.name);
		if(c.name.indexOf("CoordinateCorner")==0)
			enforce(certificate.indexOf("GraphFibre.Coordinates.rayLinear ")>=0,c.name);
		if(c.name=="CoordinateCornerPartial")
			enforce(certificate.indexOf("Coordinates.corner_pairing ")<0,c.name);
		if(c.name=="CoordinateCornerMass")
			enforce(certificate.indexOf("Coordinates.corner_pairing ")>=0,c.name);
		if(c.name.indexOf("CoordinateJumps")==0)
			enforce(certificate.indexOf("GraphFibre.Coordinates.twoRayJumps ")>=0,c.name);
		if(c.name.indexOf("CoordinateRay")==0)
			enforce(certificate.indexOf("GraphFibre.Coordinates.rayPower ")>=0,c.name);
		if(c.name=="CoordinateSquareLeftMass"||c.name=="CoordinateSquareRightMass")
			enforce(certificate.indexOf("Grid.VariationChange.square")>=0,c.name);
		else if(c.name.indexOf("CoordinateSquare")==0)
			enforce(certificate.indexOf("GraphFibre.Coordinates.square ")>=0,c.name);
		if(c.name=="CoverRegularSum") enforce(certificate.indexOf("GraphFibre.Coordinates.sinh")>=0&&
			certificate.indexOf("GraphFibre.Coordinates.asinh")>=0,c.name);
		if(c.name=="CoverPairing"||c.name=="CoverPairingMissingEndpoint"||c.name=="CoverPairingShifted"){
			enforce(certificate.indexOf("GraphFibre.radius_sqrt_pairing")>=0,c.name);
			if(c.name!="CoverPairingMissingEndpoint") enforce(text.indexOf("λ[y]")>=0&&text.indexOf("domain(t)")>=0,c.name);
		}
		if(c.name=="CoverAffineSum") enforce(certificate.indexOf("GraphFibre.Coordinates.affine")>=0&&certificate.indexOf("Distribution.addValue")>=0,c.name);
		if(c.name=="CoverPartSum")
			enforce(certificate.indexOf("Distribution.addValue")>=0&&certificate.indexOf("GraphFibre.Coordinates.restricted")>=0,c.name);
		if(c.name=="CoverDensityZero"||c.name=="CoverScaled"||c.name=="CoverShifted"||c.name=="BandAtEdge")
			enforce(certificate.indexOf("GraphFibre.Coordinates.sqrtCover ")>=0,c.name~" requires the inverse-cover certificate");
		if(c.name=="ExpandedSquare"||c.name=="ScaledFour"||c.name=="ExpandedBand")
			enforce(certificate.indexOf("GraphFibre.graph_square_congr")>=0,c.name);
		if(c.name=="OpenSquareWindow"||c.name=="OpenSquareExpanded"||c.name=="OpenSquareArgument")
			enforce(certificate.indexOf("GraphFibre.openBand_square_chart")>=0,c.name);
		if(c.name=="OpenSquareAtCritical"||c.name=="OpenSquareAtEdge"||c.name=="OpenSquareExcludedCritical")
			enforce(certificate.indexOf("GraphFibre.radius_sqrt_window_density true")>=0,c.name);
		if(c.name=="OpenSquareMass")
			enforce(certificate.indexOf("GraphFibre.radius_sqrt_open_sublevel")>=0,c.name);
		if(c.name=="SymmetricBand"||c.name=="ExpandedBand"||c.name=="PointBand")
			enforce(certificate.indexOf("GraphFibre.closedBand_square_chart")>=0,c.name);
		if(c.name=="BandAtEdge"||c.name=="BandAtCritical"||c.name=="BandCutBelow")
			enforce(certificate.indexOf("GraphFibre.radius_sqrt_cutoff_density")>=0,c.name);
		if(c.name=="BareCriticalGraph"||c.name=="RadiusRational"||c.name=="RadiusUnit"){
			enforce(certificate.indexOf("GraphFibre.affineSquare_radius_image")>=0,c.name);
			enforce(s.inspectType(a,text)==c.type&&text.indexOf("∫")<0,c.name);
		}else if(c.name=="RadiusSublevelMissing")
			enforce(certificate.indexOf("Value.le other none = none")>=0,c.name);
		else if(c.name.indexOf("RadiusSublevel")==0)
			enforce(certificate.indexOf("GraphFibre.radius_sqrt_sublevel")>=0&&text.indexOf("∫")<0,c.name~": "~text);
		else if(c.name.indexOf("Radius")==0)
			enforce(certificate.indexOf("GraphFibre.radius_sqrt_density")>=0,c.name);
		if(c.name=="NativeTruePartial")
			enforce(text.indexOf("pushforwardOnD(")>=0&&text.indexOf("[true]")<0,c.name~": "~text);
		if(c.name=="SquareGraph"||c.name=="SquareGraphFour"||c.name=="CubicGraph"){
			enforce(text.indexOf("scaleD")<0&&text.indexOf("graphFibreD")<0,c.name~": "~text);
			enforce(s.inspectType(a,text)==c.type,c.name~" printed type");
		}
		if(c.name.indexOf("MaskedJoint")==0)
			enforce(certificate.indexOf("GraphFibre.maskedKernel")>=0&&certificate.indexOf("GraphFibre.masked_affine_rule")>=0,c.name);
		if(c.name=="MaskedCapture"||c.name=="CubicExcludedFibre") enforce(certificate.indexOf("GraphFibre.oddPower_masked_rule")>=0,c.name);
		if(c.name.indexOf("MaskedSquare")==0&&c.name!="MaskedSquareMissingQuery"){
			enforce(certificate.indexOf("GraphFibre.masked_square")>=0,c.name);
			enforce(text.indexOf("maskedGraphD")<0&&text.indexOf("//")<0,c.name~": "~text);
		}
		if(c.name.indexOf("JointAffine")==0 && c.name.indexOf("Missing")<0){
			auto lemma=c.name.indexOf("JointAffineMass")==0?"affine_mass_rule":"affine_fibre_rule";
			enforce(certificate.indexOf("GraphFibre."~lemma)>=0,c.name);
		}
		if(c.name=="JointConstant") enforce(certificate.indexOf("affine_fibre_rule")<0,c.name);
		if(c.name.indexOf("RestrictedSquare")==0){
			enforce(certificate.indexOf("GraphFibre.realPushforwardOnValue")>=0,c.name);
			if(c.name=="RestrictedSquare") enforce(certificate.indexOf("GraphFibre.square_openUnit_chart")>=0,c.name);
			if(c.name=="RestrictedSquareMass") enforce(certificate.indexOf("realPushforward_mass_total")>=0,c.name);
			else if(c.name!="RestrictedSquare")
				enforce(certificate.indexOf("_openUnit_rule")>=0,c.name~": "~text);
		}
		if(c.name=="NestedPositiveChart"||c.name=="SquareProductChart")
			enforce(text.indexOf("λ₊")<0&&text.indexOf("λ[")>=0&&certificate.indexOf("_openUnit_chart")>=0,c.name);
		if(c.name=="CriticalSquareSource") enforce(text.indexOf("∫")>=0&&text.indexOf("λ₊")<0,c.name);
		if(c.name.indexOf("IdentityGraph")==0) enforce(certificate.indexOf("realPushforward_identity")>=0,c.name);
		if(c.name=="RestrictedRatio") enforce(certificate.indexOf("square_openUnit_rule")>=0,c.name);
		if(c.name=="RestrictedHigherType") enforce(certificate.indexOf("Distribution.pushforwardOnValue")>=0&&certificate.indexOf("_openUnit_rule")<0,c.name);
		if(c.name=="ExplicitRestrictedBind"||c.name=="ExplicitBindQuarter")
			enforce(certificate.indexOf("GraphFibre.realBindValue")>=0&&certificate.indexOf("GraphFibre.bind_openUnit_graph")>=0,c.name);
		if(c.name=="ExplicitWeightedBind") enforce(certificate.indexOf("GraphFibre.weighted_bind_openUnit_graph")>=0,c.name);
		if(c.name=="ExplicitAtomIntegral"||c.name=="ExplicitIdentityRows")
			enforce(certificate.indexOf("GraphFibre.integral_openUnit_graph")>=0,c.name);
		if(c.name=="ExplicitCubicRows") enforce(certificate.indexOf("GraphFibre.integral_openUnit_graph")>=0&&
			certificate.indexOf("GraphFibre.oddPower_chart_rule")>=0,c.name);
		if(c.name.indexOf("TotalRows")==0){
			auto kind=c.name=="TotalRowsPuncture"?"bind":c.name=="TotalRowsMaskedInverse"?"weighted_bind":"integral";
			enforce(certificate.indexOf("GraphFibre."~kind~"_total_graph")>=0&&
				certificate.indexOf("DomainCertificate.domain_correct")>=0,c.name);
		}
		if(c.name=="PartialDiracRows"||c.name=="PartialRowOffSupport"||c.name=="PartialRowPredicate"||c.name=="PartialRowGuardTooLate")
			enforce(certificate.indexOf(c.name=="PartialDiracRows"||c.name=="PartialRowPredicate"?"GraphFibre.realBindValue":"GraphFibre.realIntegralValue")>=0&&
				certificate.indexOf("_total_graph")<0&&certificate.indexOf("_openUnit_graph")<0,c.name);
		if(c.name=="AffineChartUnrestricted"||c.name=="AffineChartBareIntegral"){
			auto kind=c.name=="AffineChartUnrestricted"?"bind":"integral";
			enforce(certificate.indexOf("GraphFibre."~kind~"_dirac_graph")>=0,c.name);
		}
		if(c.name.indexOf("AffineChart")==0||c.name=="TotalRowsAffine")
			enforce(certificate.indexOf("GraphFibre.affine_chart_rule")>=0,c.name);
		if(c.name=="ConstantGraph"||c.name=="PartialAffinePredicate")
			enforce(text.indexOf("∫")>=0&&certificate.indexOf("GraphFibre.affine_chart_rule")<0,c.name);
		if(c.name=="AffineRowMass"||c.name=="NativeTotalMapMass")
			enforce(certificate.indexOf("GraphFibre.mass_total_graph")>=0,c.name);
		if(c.name=="NativePartialMapMass") enforce(certificate.indexOf("GraphFibre.mass_total_graph")<0,c.name);
		if(c.name=="CapturedGraphQuery") enforce(text.indexOf("graphFibreD")>=0,c.name~" would capture the query");
		if(c.name=="SquareGraphMass"||c.name=="SquareGraphIntegral"||c.name=="CubicMarginal")
			enforce(certificate.indexOf("Distribution.GraphFibre.marginal")>=0&&certificate.indexOf("Distribution.GraphFibre.value")<0,c.name);
		if(c.name=="IndirectCubicMarginal") enforce(certificate.indexOf("Distribution.GraphFibre.mass_eq_marginal")>=0,c.name);
		if(c.name=="CubicGraph"||c.name=="FifthSymbolicFibre"||c.name=="FifthNegativeFibre")
			enforce(certificate.indexOf("GraphFibre.oddPower_fibre_rule")>=0,c.name);
		if(c.name=="CubicSymbolicPartialDensity")
			enforce(text.indexOf("guard(")>=0&&certificate.indexOf("Reduction.sound")>=0,c.name~": "~text);
		if(c.name=="CubicMarginal"||c.name=="SeventhPositiveMass") enforce(certificate.indexOf("GraphFibre.oddPower_mass_rule")>=0,c.name);
		if(c.name=="RestrictedCubic"||c.name=="CubicPartialDensity"||c.name=="CubicExcludedDensity"||c.name=="CubicCriticalDensity"||c.name=="CubicPredicateParameter")
			enforce(certificate.indexOf("GraphFibre.oddPower_density_rule")>=0,c.name);
		if(c.name.indexOf("WeightedFibre")==0) enforce(certificate.indexOf("GraphFibre.SquareRows.density")>=0,c.name);
		if(c.name.indexOf("WeightedSquare")==0){
			bool absolute=c.name=="WeightedSquareAbs"||c.name=="WeightedSquareSource";
			bool general=c.name=="WeightedSquareAsymmetric"||c.name=="WeightedSquareNegative"||
				c.name=="WeightedSquareChanging"||c.name=="WeightedSquareMasked";
			enforce((certificate.indexOf("GraphFibre.absSquareChart")>=0)==absolute,c.name);
			enforce((certificate.indexOf("GraphFibre.squareWeightSource_of_product")>=0)==general,c.name~": "~text);
			if(general){
				enforce(text.indexOf("∫")<0&&text.indexOf("bindD")<0,c.name~": "~text);
				string[] expected=c.name=="WeightedSquareNegative"?["0","0","-1/2","-1","-2"]:
					c.name=="WeightedSquareChanging"?["0","0","-15/32","0","30"]:
					c.name=="WeightedSquareMasked"?["0","0","5/4","1","5/4"]:["0","0","5/8","2","10"];
				foreach(i,y;["-1","0","1/4","1","4"]){
					auto obs=s.run(a,"densityAtD("~text~","~y~")",[],Options(DensityMode.preserve,true));
					enforce(s.format(a,obs)==expected[i],c.name~" at "~y~": "~s.format(a,obs));
				}
			}
		}
		if(c.name.indexOf("SquareChart")==0){
			bool fallback=c.name=="SquareChartWrongPuncture"||c.name=="SquareChartActive"||c.name=="SquareChartPartial";
			bool puncture=c.name=="SquareChartScaledPuncture"||c.name=="SquareChartBare"||c.name=="SquareChartBoth";
			auto lemma=puncture?"GraphFibre.affineSquare_puncture_rule":"GraphFibre.affineSquare_chart_rule";
			enforce((certificate.indexOf(lemma)>=0)==!fallback,c.name~": "~text);
			enforce((text.indexOf("∫")>=0)==fallback,c.name~": "~text);
			if(c.name=="SquareChartOverlap"){
				// Observe the printed chart itself at a gap, the critical value,
				// an overlap, and the open endpoint of the negative branch.
				string[] expected=["0","0","1","1/4"];
				foreach(i,y;["-1","0","1","4"]){
					auto obs=s.run(a,"densityAtD("~text~","~y~")",[],Options(DensityMode.preserve,true));
					enforce(s.format(a,obs)==expected[i],c.name~" at "~y~": "~s.format(a,obs));
				}
			}
		}
		if(c.name.indexOf("ClosedSquare")==0||c.name=="AffineSquareMass"){
			auto observer=c.name=="ClosedSquareMass"||c.name=="AffineSquareMass"?"mass":"density";
			enforce(certificate.indexOf("GraphFibre.affineSquare_unrestricted_"~observer)>=0||
				observer=="density"&&certificate.indexOf("GraphFibre.radius_sqrt_density")>=0,c.name);
		}
		else if(c.name=="AffineSquareZeroSlope") enforce(certificate.indexOf("affineSquareExpression")<0,c.name);
		else if(c.name.indexOf("AffineSquare")==0)
			enforce(certificate.indexOf("GraphFibre.affineSquareExpression")>=0,c.name);
		if(c.name=="AffineOddChart")
			enforce(certificate.indexOf("GraphFibre.affineOdd_chart_rule")>=0&&text.indexOf("∫")<0,c.name);
		else if(c.name=="AffineOddCriticalSource")
			enforce(certificate.indexOf("affineOdd_chart_rule")<0&&text.indexOf("∫")>=0,c.name);
		else if(c.name.indexOf("AffineOdd")==0)
			enforce(certificate.indexOf("GraphFibre.affineOddExpression")>=0,c.name);
		if(c.name=="OddNonAffineSource") enforce(certificate.indexOf("GraphFibre.affineOddExpression")<0,c.name);
		if(c.name=="FifthChart") enforce(certificate.indexOf("GraphFibre.oddPower_chart_rule")>=0&&text.indexOf("∫")<0,c.name);
		if(c.name=="CubicPartialSource"||c.name=="CubicCriticalSource"||c.name=="QuarticGraph")
			enforce(certificate.indexOf("GraphFibre.oddPower_")<0,c.name);
		if(c.name.indexOf("SquareGraph")==0&&c.name!="SquareGraphMassMissing") enforce(certificate.indexOf("Distribution.GraphFibre.square_")>=0,c.name~": "~text);
		// A weight that is missing at its atom is now a missing coefficient
		// before any fibre is extracted.
		if(c.name=="SignedFibrePartialWeight")
			enforce(certificate.indexOf("Distribution.weight_diracValue")>=0&&certificate.indexOf("Distribution.add_none_left")>=0,c.name);
		else if(c.name.indexOf("SignedFibre")==0) enforce(certificate.indexOf("Distribution.FibreCertificate.extract")>=0,c.name);
		if(c.name=="MixtureExpectation"||c.name=="MixtureEvent"||c.name=="MixtureSymbolicMean")
			enforce(certificate.indexOf("Distribution.weight_addValue")>=0&&certificate.indexOf("Distribution.weight_scaleValue")>=0&&
				certificate.indexOf("Distribution.weight_diracValue")>=0,c.name);
		if(c.name=="WeightedDirac"||c.name=="MixtureWeightedAtoms") enforce(certificate.indexOf("Distribution.weight_diracValue")>=0,c.name);
		if(c.name=="MixtureAtomBind") enforce(certificate.indexOf("GraphFibre.realBind_diracValue")>=0,c.name);
		if(c.name=="MixtureBind"||c.name=="MixtureBranch")
			enforce(certificate.indexOf("GraphFibre.realBind_addValue")>=0&&certificate.indexOf("GraphFibre.realBind_scaleValue")>=0,c.name);
		if(c.name=="MixtureHigherAtoms") enforce(certificate.indexOf("Distribution.bind_addValue")>=0&&certificate.indexOf("realBind")<0,c.name);
		if(c.name=="MixtureZeroSource") enforce(certificate.indexOf("GraphFibre.realBind_zeroValue")>=0,c.name);
		foreach(lemma;[["MixtureStrictSummand","Distribution.add_none_right"],["MixtureStrictScale","Distribution.scale_none_right"],
			["MixtureStrictWeight","Distribution.weight_none_right"],["MixtureStrictSource","GraphFibre.realBind_none_left"],
			["MixtureStrictHigherSource","Distribution.bind_none_left"],["MixtureStrictQuery","Distribution.densityAt_none_right"],
			["MixtureHigherZero","Distribution.bind_zeroValue"],["MixtureHigherScale","Distribution.bind_scaleValue"],
			["MixtureNaturalWeight","Distribution.weight_addValue"],["MixtureScaledSum","GraphFibre.realBind_addValue"]])
			if(c.name==lemma[0]) enforce(certificate.indexOf(lemma[1])>=0,c.name);
		// The real bind is structural, so a chart below a sum or a scaling
		// is reached and keeps its row interpreter.
		if(c.name=="MixtureChartSummand"||c.name=="MixtureMaskedChart"||c.name=="MixtureMaskedChartMass")
			enforce(certificate.indexOf("GraphFibre.realBind_addValue")>=0&&certificate.indexOf("mixture_")<0,c.name~": "~text);
		if(c.name=="MixtureChartSummand") enforce(text.indexOf("δ(1)[x]")>=0&&text.indexOf("(d)[y]")>=0,c.name~": "~text);
		if(c.name=="MixtureScaledChart") enforce(text.indexOf("∫")<0&&certificate.indexOf("GraphFibre.realBind_scaleValue")>=0,c.name~": "~text);
		if(c.name=="MixtureMaskedChart") enforce(certificate.indexOf("GraphFibre.affine_chart_rule")>=0,c.name);
		// A sum of presentations is observed through the scalar sum of its terms.
		if(c.name=="CountingMass"||c.name=="SumGeometricMass") enforce(certificate.indexOf("Distribution.mass_sumValue")>=0,c.name);
		if(c.name=="SumMean") enforce(certificate.indexOf("Distribution.mass_sumValue")>=0&&certificate.indexOf("Distribution.weight_sumValue")>=0,c.name~": "~text);
		if(c.name=="SumBind") enforce(certificate.indexOf("GraphFibre.realBind_sumValue")>=0,c.name);
		if(c.name=="NaturalCountingMass"||c.name=="NaturalGeometricMass") enforce(certificate.indexOf("Distribution.mass_sumNatValue")>=0,c.name);
		if(c.name=="NaturalGeometricMean"||c.name=="NaturalDieMean"||c.name=="NaturalDieVariance")
			enforce(certificate.indexOf("Distribution.mass_sumNatValue")>=0&&certificate.indexOf("Distribution.weight_sumNatValue")>=0,c.name);
		if(c.name=="NaturalBind") enforce(certificate.indexOf("GraphFibre.realBind_sumNatValue")>=0,c.name);
		if(c.name=="TwoMaskGraph") enforce(certificate.indexOf("GraphFibre.affine_chart_rule")>=0,c.name);
		if(c.name=="TwoMaskJoint") enforce(certificate.indexOf("GraphFibre.masked_affine_rule")>=0,c.name);
		if(c.name.indexOf("MixedDensity")==0) enforce(certificate.indexOf("Distribution.model_density_atom_add")>=0,c.name);
		if(c.name.indexOf("AtomDensity")==0) enforce(certificate.indexOf("Distribution.model_density_dirac")>=0,c.name);
		if(c.name=="DensityRecovery") enforce(certificate.indexOf("Distribution.model_density_weight_lebesgueValue")>=0);
		if(c.name=="DensityOne") enforce(certificate.indexOf("Distribution.model_density_lebesgueValue")>=0);
		if(c.name=="Integral") enforce(certificate.indexOf("Distribution.model_mass_weight_diracValue")>=0);
		if(c.name=="RecursiveAtom") enforce(certificate.indexOf("Distribution.model_mass_diracValue")>=0);
		if(c.name=="Interval"||c.name=="PuncturedInterval"||c.name=="SignedInterval"||c.name=="MixedIntegral"){
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0);
			enforce(certificate.indexOf("Distribution.DensityProgram.weight")>=0);
		}
		if(c.name=="UnboundedPuncture") enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid_null_edit")>=0);
		if(c.name=="BoundRectangle"||c.name=="TripleBind"||c.name=="BoundFunction"||c.name=="BoundDistribution"||c.name=="BoundType")
			enforce(certificate.indexOf("Distribution.model_mass_bind_density")>=0);
		if(c.name=="IntegralRectangle"||c.name=="WeightedRows") enforce(certificate.indexOf("Distribution.model_mass_integralValue")>=0);
		if(c.name=="ParametricWeight"||c.name=="ParametricPartialWeight"||c.name=="ParametricNestedWeights"||c.name=="WeightedRows")
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0);
		if(c.name=="UnboundedParameter"||c.name=="ZeroInfiniteRow"){
			if(c.name=="UnboundedParameter") enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")<0);
			enforce(text.indexOf("∫")>=0,c.name~" must retain its unsupported integral");
		}
		if(c.name=="NestedMaskedRectangle"||c.name=="ReversedMaskedRectangle"||c.name=="SignedMaskedRectangle"||
			c.name=="PuncturedMaskedRectangle"||c.name=="MaskedParameter"||c.name=="MaskedPartialParameter"||
			c.name=="OuterParameterMask"||c.name=="InnerParameterMask"||c.name=="MaskedPartialBranch"||c.name=="MixedParameterMasks")
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0,c.name~" must use a domain-checked parameter certificate");
		if(c.name=="NullPointParameter"||c.name=="ClosedSingletonParameter"||c.name=="EmptyMaskedParameter"||
			c.name=="DisjointPartialWeights"||c.name=="DisjointOpenSupports"||c.name=="DisjointTwoParameters"||c.name=="MaskedNullPoint"||c.name=="ShiftedNullPoint")
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0,c.name~" must check pointwise definedness on null supports");
		if(c.name=="NullPointDensity") enforce(certificate.indexOf("Distribution.model_density_weight_lebesgueValue")>=0);
		if(c.name=="StepSum"||c.name=="StepUnion"||c.name=="StepOverlap"||c.name=="StepSigned"||
			c.name=="StepPartialParameter"||c.name=="StepTwoParameters"||c.name=="StepBoundaryParameter"||c.name=="StepProduct")
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0,c.name~" must use a checked step certificate");
		if(c.name=="StepUnbounded"||c.name=="StepNonconstant"){
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")<0,c.name~" must not invent a step certificate");
			enforce(c.name=="StepNonconstant"||text.indexOf("∫")>=0,c.name~" must retain its unsupported integral");
		}
		// One lower and one upper bound around polynomial and exponential
		// terms. An open side and other integrands keep their integral; a
		// third bound is a case distinction with two such observations.
		if(c.name.indexOf("SymbolicInterval")==0){
			bool retained=c.name=="SymbolicIntervalUnbounded";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_interval")>=0)!=retained,c.name~" interval certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
		}
		// A guard free of the axis leaves the observation, but only when the
		// rest can then be observed.
		if(c.name.indexOf("Guarded")==0){
			enforce((certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0)==(c.name!="GuardedUnobserved"),c.name~" guard certificate");
			enforce((text.indexOf("∫")>=0)==(c.name=="GuardedUnobserved"),c.name~": "~text);
		}
		// A polynomial times an exponential of rational rate has an
		// antiderivative of the same kind. A constant part of the exponent that
		// does not mention the axis is a scale: its exponential leaves the
		// integral. A rate that is a term has the antiderivative of a table
		// instead, with the case of a rate that is zero beside it.
		bool offset=c.name=="ExponentialShifted"||c.name.indexOf("ExponentialOffset")==0||c.name.indexOf("HalfLineOffset")==0||c.name.indexOf("LimitOffset")==0;
		if(c.name.indexOf("Exponential")==0){
			bool symbolic=c.name=="ExponentialSymbolicRate";
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_interval")>=0,c.name~" interval certificate");
			if(c.name!="ExponentialTwoScales"&&!offset) enforce((certificate.indexOf("StepSource.exp_affine")>=0)!=symbolic,c.name~" exponential evidence");
			enforce((certificate.indexOf("Distribution.StepSource.IntervalTerms.rate (")>=0)==symbolic,c.name~" rate that is a term");
			enforce(text.indexOf("∫")<0,c.name~": "~text);
		}
		// Above one lower bound every term must decay; the antiderivative
		// then vanishes at infinity. A growing term keeps its integral.
		if(c.name.indexOf("HalfLine")==0){
			bool retained=c.name=="HalfLineGrowing"||c.name=="HalfLineOffsetGrowing";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_halfline")>=0)!=retained,c.name~" half-line certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
		}
		// Below one upper bound, the mirror image: every term must decay at
		// minus infinity, where the antiderivative then vanishes, so the result
		// is its value at the bound. A term that grows there and a bracket
		// alone keep their integral.
		if(c.name.indexOf("Upper")==0){
			bool retained=c.name=="UpperGrowing"||c.name=="UpperCurveGrowing"||c.name=="UpperBracket";
			bool curved=c.name.indexOf("UpperCurve")==0,scaled=c.name=="UpperStrictScaled"||c.name=="UpperOffset"||c.name=="UpperDomain"||c.name=="UpperCurveScaled";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_upper")>=0)!=retained,c.name~" certificate");
			enforce((certificate.indexOf("Distribution.StepSource.UpperTerms."~(curved?scaled?"scaledCurve ":"curve ":scaled?"scaled ":"pure "))>=0)!=retained,c.name~" antiderivative");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(c.name=="UpperSum") enforce(certificate.indexOf("Distribution.StepSource.UpperTerms.add")>=0,c.name~" terms");
			if(c.name=="UpperDomain") enforce(certificate.indexOf("Distribution.StepSource.UpperTerms.guard")>=0&&certificate.indexOf("Distribution.StepSource.MaskDomain.last")>=0,c.name~" domain");
			if(c.name=="UpperGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
			if(c.name=="UpperOffset") enforce(certificate.indexOf("Distribution.StepSource.scaled_exp_offset")>=0,c.name~" offset");
		}
		// A polynomial times the exponential of a polynomial is integrated
		// between bounds and above a bound where an antiderivative has the same
		// shape: R'+E'·R=P has a polynomial solution. Above a bound the exponent
		// must descend. The constant part of an exponent of degree at most two
		// may be a term that does not mention the axis: its exponential is a
		// scale. With an exponent that grows above a bound and with a
		// curvature that is such a term the integral stays, and without such
		// a solution away from the vertex of a Gaussian. With a mean that is
		// such a term the weight is not of this shape as it is written; it is
		// multiplied out, and is then a sum of moments of a Gaussian above a
		// bound.
		if(c.name=="CurveMean"){
			enforce(text.indexOf("∫")<0,c.name~": "~text);
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_halfline")>=0&&certificate.indexOf("Distribution.StepSource.HalfLineTerms.symbolicErfPolynomial")>=0,
				c.name~" moments above a bound");
		}else if(c.name.indexOf("Curve")==0){
			bool retained=c.name=="CurveHalfLineGrowing"||c.name=="CurveCurvature";
			bool half=c.name!="CurveInterval"&&c.name!="CurveSymbolicBounds"&&c.name!="CurveGrowing"&&c.name!="CurveTwoScales"&&c.name!="CurveCdf"&&
				c.name!="CurveOffsetInterval"&&c.name!="CurveOffsetBounds";
			bool shifted=c.name.indexOf("CurveOffset")==0,scaled=c.name=="CurveScaled"||c.name=="CurveTwoScales"||shifted;
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_"~(half?"halfline":"interval"))>=0)!=retained,c.name~" certificate");
			enforce((certificate.indexOf("Distribution.StepSource."~(half?"HalfLineTerms":"IntervalTerms")~(scaled?".scaledCurve ":".curve "))>=0)!=retained,c.name~" antiderivative");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(c.name=="CurveSum") enforce(certificate.indexOf("HalfLineTerms.pure")>=0&&certificate.indexOf("HalfLineTerms.add")>=0,c.name~" terms");
			enforce((certificate.indexOf("Limit.EventualScaled.exp_curve")>=0)==shifted,c.name~" offset evidence");
			if(shifted) enforce(certificate.indexOf("Distribution.StepSource.Quadratic.")>=0,c.name~" exponent");
			if(c.name=="CurveOffset") enforce(certificate.indexOf("Distribution.StepSource.coefValue_absent")>=0,c.name~" absent coefficient");
			if(c.name=="CurveOffsetSum") enforce(certificate.indexOf("HalfLineTerms.scaled ")>=0&&certificate.indexOf("scaled_exp_offset")>=0,c.name~" terms");
		}
		// A value between bounds may be missing where a term that does not
		// mention the axis is. The mask is then under the guard of its domain:
		// the negations of its comparisons in order, then the domain of the
		// value. That is the mask of the value under the guard of its own
		// domain, so the result is under that guard, inside the test of the
		// bounds. A comparison that does not mention the axis leaves the
		// observation with its negation. Below a binder the value itself is
		// under the guard. A domain that mentions the axis keeps the integral,
		// unless the value is a quotient by a power of the axis: see below.
		if(c.name.indexOf("Domain")==0&&c.name!="DomainAxis"){
			bool retained=c.name=="DomainAxisRoot";
			bool half=c.name=="DomainHalfLine"||c.name=="DomainRoot"||c.name=="DomainLogarithm"||c.name=="DomainSum"||c.name=="DomainGuarded"||c.name=="DomainTwoGuards";
			bool guarded=c.name.indexOf("DomainGuarded")==0||c.name=="DomainTwoGuards",nested=c.name=="DomainNested";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_"~(half?"halfline":"interval"))>=0)!=retained,c.name~" certificate");
			enforce((certificate.indexOf("Distribution.StepSource."~(half?"HalfLineTerms":"IntervalTerms")~".guard ")>=0)!=retained,c.name~" guard of the result");
			enforce((certificate.indexOf("Distribution.StepSource.MaskDomain.mask")>=0)!=(retained||nested),c.name~" domain of the mask");
			enforce((certificate.indexOf("Distribution.StepSource.MaskDomain.cons")>=0)==(!half&&!retained&&!nested),c.name~" comparisons");
			enforce((certificate.indexOf("Distribution.StepSource.mask_domain_split")>=0)==guarded,c.name~" comparison free of the axis");
			if(guarded) enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
		}
		// A polynomial over a power of the axis between two bounds: sums and
		// products of polynomials and of inverses of monomials, of which a
		// negative power is left. It is undefined at zero and not integrable
		// next to it, so the difference of its antiderivative stands under
		// the guard that both bounds are on one side of zero, inside the test
		// of the bounds: with zero between them or next to them the
		// observation is missing. The antiderivative has a polynomial, a
		// polynomial over a power of the bound, in lowest terms, and a
		// logarithm of its absolute value; the certificate has the value as
		// such a quotient by its structure, and the kernel differentiates.
		// Beyond one bound a quotient with no power above the inverse square
		// is observed on that side of zero, by the polynomial over the power
		// alone; any other one is not integrable out there and keeps its
		// integral. Bounds that are terms leave the mask under the guard of
		// its domain, that the axis is not zero: the quotient is undefined
		// there anyway. A polynomial under that guard, another denominator
		// and an exponential keep their integral.
		// Factors that do not mention the axis may stand anywhere in a
		// product with the quotient. Their product `c` does not simply come
		// out: where it is zero the product is zero also next to zero, where
		// the quotient is not integrable. Where a bound is strict the value
		// is under the mask `[c≠0]`, and its guard also holds where `c` is
		// zero and zero is not in the guard of the bounds; where no bound is
		// strict, or the bounds are closed on one side of zero, `c` stands
		// in front. A domain of such a factor is a guard of the observation,
		// inside the mask of two bounds; around the mask it may be joined
		// with the domain of the quotient, in either order. A factor inside
		// a sum and a tail that diverges keep their integral.
		// The powers may be those of the axis minus a rational pole: the
		// inverse of a power of a linear polynomial. Moved along the axis
		// by the pole that is a quotient around zero, between the bounds
		// moved along with it, and the polynomials are moved as well. The
		// domain is then that the axis is not at the pole. Two poles, a
		// denominator without a root and the domain around a mask of closed
		// bounds with the pole between them keep their integral.
		if(c.name.indexOf("Quotient")==0&&c.name!="QuotientPoleQuadratic"||c.name=="DomainAxis"){
			enum src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(src~evidence)>=0; }
			bool retained=among("QuotientDiverges","QuotientAbovePolynomial","QuotientRemovable","QuotientExponential","QuotientScaleSum","QuotientScaleDiverges",
				"QuotientPoleInside","QuotientPoleTwo");
			bool pole=c.name.indexOf("QuotientPole")==0&&!retained;
			bool scaled=c.name.indexOf("QuotientScale")==0&&c.name!="QuotientScaled"||c.name.indexOf("QuotientPoleScale")==0||c.name=="QuotientPoleUniform";
			bool above=c.name.indexOf("QuotientAbove")==0||c.name.indexOf("QuotientScaleAbove")==0||c.name.indexOf("QuotientPoleAbove")==0||
				among("QuotientDomainAbove","QuotientDomainCancelled","QuotientScaleDomainAbove");
			bool below=c.name.indexOf("QuotientBelow")==0||c.name.indexOf("QuotientScaleBelow")==0||
				among("QuotientDomainBelow","QuotientScaleDomainBelow","QuotientPoleBelow","QuotientPoleScaleBelow");
			// With a strict bound that is not closed on one side of the pole
			// the factor is under its mask.
			bool masked=among("QuotientScaleStrict","QuotientScaleEdge","QuotientScaleAboveStrict","QuotientScaleBelowStrict","QuotientScaleDomainBelow","QuotientPoleScaleStrict");
			auto kind=scaled?(masked?"_scaled ":"_scaled_plain "):" ";
			enforce(has("ratio_between"~kind)==(!retained&&!above&&!below),c.name~" quotient between bounds");
			enforce(has("ratio_above"~kind)==(!retained&&above),c.name~" quotient above a bound");
			enforce(has("ratio_below"~kind)==(!retained&&below),c.name~" quotient below a bound");
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_direct")>=0)!=retained,c.name~" certificate");
			enforce(has("ratio_inv ")!=retained,c.name~" inverse of a monomial");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			// The evidence follows the structure of the value.
			bool sums=among("QuotientDifference","QuotientAboveSum","QuotientBelowLowest");
			enforce(has("ratio_add_left ")==among("QuotientSum","QuotientFactors","QuotientDomain","QuotientScaleFactors"),c.name~" polynomial and quotient");
			enforce(has("ratio_add_right ")==among("QuotientMinus"),c.name~" quotient and polynomial");
			enforce(has("ratio_add ")==sums,c.name~" sum of quotients");
			enforce(has("ratio_mul_left ")==(sums||among("QuotientScaled","QuotientPoleProduct","QuotientPoleDivision")),c.name~" polynomial times quotient");
			enforce(has("ratio_mul_right ")==among("QuotientProduct","QuotientDomainStrict","QuotientDomainAbove","QuotientDomainBelow","QuotientScaleDomainFirst"),
				c.name~" quotient times polynomial");
			enforce(has("ratio_mul ")==among("QuotientFactors"),c.name~" product of quotients");
			enforce(has("Fraction.mul ")==(scaled&&!retained),c.name~" product with a factor");
			enforce(has("Fraction.scale ")==(scaled&&!retained),c.name~" factor");
			// Closed bounds on one side of the pole, where one of them is strict.
			enforce(has("side_closed ")==among("QuotientScaleClosed","QuotientPoleScaleClosed"),c.name~" closed bounds");
			enforce(has("above_closed ")==among("QuotientScaleAboveClosed"),c.name~" closed lower bound");
			enforce(has("below_closed ")==among("QuotientScaleBelowClosed"),c.name~" closed upper bound");
			// Under the guard of its domain around the mask it is the same
			// quotient. The domain of a factor is a guard of the observation;
			// the two may be joined.
			bool first=among("QuotientScaleDomainFirst"),nested=among("QuotientScaleDomainNested");
			bool joined=among("QuotientScaleUniform","QuotientScaleDomainAbove","QuotientScaleDomainBelow","QuotientPoleUniform")||nested;
			bool guardedPole=among("QuotientPoleBounds","QuotientPoleReversed","QuotientPoleAboveTerm","QuotientPoleBelow","QuotientPoleFunction");
			bool guardedFactor=among("QuotientPoleScaleStrict","QuotientPoleScaleBelow");
			enforce(has("ratio_guard ")==(c.name.indexOf("QuotientDomain")==0||guardedPole),c.name~" guard of the domain");
			enforce(has("Fraction.guard ")==(joined||first||guardedFactor),c.name~" guard of the domain under a factor");
			enforce(has("MaskDomain.mask ")==(c.name.indexOf("QuotientDomain")==0||among("QuotientScaleDomain")||(joined||first||guardedPole||guardedFactor)&&
				!nested&&!among("QuotientPoleFunction")),c.name~" domain around the mask");
			enforce(has("guard_and_left ")==joined,c.name~" domain of the axis first");
			enforce(has("guard_and_right ")==first,c.name~" domain of the factor first");
			enforce(has("between_guard_integral ")==(among("QuotientScaleDomain","QuotientScaleUniform","QuotientPoleUniform")||first||nested),c.name~" guard inside the mask of the bounds");
			enforce(has("masked_guard_integral ")==among("QuotientScaleDomainAbove","QuotientScaleDomainBelow"),c.name~" guard of the observation");
			// Around a pole that is not zero.
			enforce(has("shift_between ")==(pole&&!above&&!below),c.name~" pole between bounds");
			enforce(has("shift_above ")==(pole&&above),c.name~" pole below a bound");
			enforce(has("shift_below ")==(pole&&below),c.name~" pole above a bound");
			enforce(has("polynomial_translate ")==pole,c.name~" polynomial around the pole");
			enforce(has("shifted_nonzero ")==(guardedPole||guardedFactor||among("QuotientPoleUniform")),c.name~" domain of the pole");
			// Zero between the bounds, next to them or beyond the only one:
			// nothing is observed.
			enforce((text=="undefined(ℝ)")==among("QuotientAcross","QuotientEdge","QuotientAboveZero","QuotientAboveEdge","QuotientScaleAcross"),c.name~": "~text);
			if(among("QuotientGuarded","QuotientAboveGuarded")) enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
		}
		// A polynomial times the logarithm of the axis, plus a polynomial,
		// between two bounds: sums and products of polynomials and of the
		// logarithm in which a logarithm meets polynomials only. The
		// logarithm is defined on the positive axis, so the difference of
		// the antiderivative `x·P₁(x)·log(x) + x·S₁(x)` stands under the
		// guard that the lower bound is positive; with zero or a negative
		// point in the guard of the bounds nothing is observed. Next to
		// zero the value is integrable: a lower bound that is strict may be
		// zero, its guard is `0≤a`, and the part of the antiderivative with
		// the logarithm is under the mask `[a≠0]` there. The certificate
		// has the value by its structure, and the kernel differentiates.
		// The logarithm may be that of the axis minus a rational pole, on
		// either side of the closed term; a guard of the domain around the
		// mask leaves the value as it is. Factors that do not mention the
		// axis may stand anywhere in a product with the value: on the
		// positive axis it is integrable whatever they are, so their
		// product stands in front of the difference, under the same guard,
		// and a domain of such a factor is a guard inside the mask of the
		// bounds. A power of the logarithm, a quotient with it, a single
		// bound and two poles keep their integral.
		if(c.name.indexOf("Logarithm")==0){
			enum src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(src~evidence)>=0; }
			bool retained=among("LogarithmSquare","LogarithmQuotient","LogarithmAbove","LogarithmTwo");
			// A summand that is a term: see below.
			enforce(has("between_add_constant ")==among("LogarithmMultiple","LogarithmScaleConstant"),c.name~" summand that is a term");
			bool scaled=c.name.indexOf("LogarithmScale")==0&&!retained;
			bool pole=c.name.indexOf("LogarithmPole")==0||among("LogarithmScalePole","LogarithmScalePoleBounds");
			enforce(has("log_between"~(scaled?"_scaled ":" "))!=retained,c.name~" logarithm between bounds");
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_direct")>=0)!=retained,c.name~" certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			// The evidence follows the structure of the value.
			enforce(has("log_axis")!=retained,c.name~" logarithm of the axis");
			enforce(has("log_axis_shifted ")==among("LogarithmPoleBounds","LogarithmPoleProduct","LogarithmPoleStrict","LogarithmScalePoleBounds"),c.name~" axis before the closed term");
			enforce(has("log_axis_shifted' ")==among("LogarithmPole","LogarithmScalePole"),c.name~" closed term before the axis");
			enforce(has("log_mul_left ")==among("LogarithmProduct","LogarithmSum","LogarithmMinus","LogarithmEntropy","LogarithmPoleProduct"),c.name~" polynomial times logarithm");
			enforce(has("log_mul_right ")==among("LogarithmPolynomial","LogarithmMixed","LogarithmDomainProduct","LogarithmScaleJoined"),c.name~" logarithm times polynomial");
			enforce(has("log_add ")==among("LogarithmSum","LogarithmMixed"),c.name~" sum of logarithms");
			enforce(has("log_add_left ")==among("LogarithmMixed","LogarithmDomain","LogarithmScaleSum","LogarithmScaleJoinedFirst"),c.name~" polynomial and logarithm");
			enforce(has("log_add_right ")==among("LogarithmMinus"),c.name~" logarithm and polynomial");
			// Factors that do not mention the axis.
			enforce(has("LogFraction.scale ")==scaled,c.name~" factor");
			enforce(has("LogFraction.log ")==scaled,c.name~" value under a factor");
			enforce(has("LogFraction.mul_left ")==scaled,c.name~" product with a factor");
			enforce(has("LogFraction.mul_right ")==among("LogarithmScaleGuarded"),c.name~" product with a factor behind");
			enforce(has("LogFraction.polynomial ")==among("LogarithmScaleFactors","LogarithmScaleGuarded","LogarithmScaleEntropy"),c.name~" polynomial next to a factor");
			// The guard of the domain around the mask, the domain of a
			// factor, and the pole.
			bool guardedFactor=among("LogarithmScaleGuarded","LogarithmScaleJoined","LogarithmScaleJoinedFirst","LogarithmScalePoleBounds");
			bool guarded=among("LogarithmDomain","LogarithmDomainProduct","LogarithmPoleBounds");
			enforce(has("log_guard ")==guarded,c.name~" guard of the domain");
			enforce(has("LogFraction.guard ")==guardedFactor,c.name~" guard of the domain under a factor");
			enforce(has("MaskDomain.mask ")==(guarded||guardedFactor||among("LogarithmScaleDomain")),c.name~" domain around the mask");
			enforce(has("axis_positive ")==among("LogarithmDomain","LogarithmDomainProduct","LogarithmScaleGuarded","LogarithmScaleJoined","LogarithmScaleJoinedFirst"),
				c.name~" domain of the logarithm");
			enforce(has("shifted_positive ")==among("LogarithmPoleBounds","LogarithmScalePoleBounds"),c.name~" domain of the logarithm around the pole");
			enforce(has("between_guard_integral ")==among("LogarithmScaleDomain","LogarithmScaleJoined","LogarithmScaleJoinedFirst"),c.name~" guard inside the mask of the bounds");
			enforce(has("guard_and_left ")==among("LogarithmScaleJoined"),c.name~" domain of the axis first");
			enforce(has("guard_and_right ")==among("LogarithmScaleJoinedFirst"),c.name~" domain of the factor first");
			enforce(has("shift_between ")==pole,c.name~" pole");
			enforce(has("polynomial_translate ")==among("LogarithmPoleProduct"),c.name~" polynomial around the pole");
			// Zero or a negative point in the guard: nothing is observed.
			enforce((text=="undefined(ℝ)")==among("LogarithmClosed","LogarithmAcross"),c.name~": "~text);
		}
		// A summand that does not mention the axis, in front of such a
		// quotient or logarithm between two bounds. The bounds are a bounded
		// set, so the sum is integrable exactly where the other summand is,
		// and it is defined exactly where both are: inside the mask of the
		// bounds the term adds its multiple by their distance to the
		// observation of the other summand, whatever that is. Under the
		// guard of the domain of the other summand the term comes out of
		// that guard first; a domain of the term is a guard inside the
		// mask. Beyond one bound the sum is not integrable, and a term
		// inside a longer sum is not in front: these keep their integral.
		if(c.name.indexOf("Summand")==0){
			enum src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(src~evidence)>=0; }
			bool retained=among("SummandAbove","SummandNested");
			bool guarded=among("SummandBounds","SummandQuotientBounds","SummandScale","SummandPoleStrict","SummandFunction");
			enforce(has("between_add_constant ")!=retained,c.name~" summand that is a term");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			enforce(has("value_add_comm ")==(!retained&&!guarded),c.name~" term in front");
			enforce(has("guard_add_first ")==guarded,c.name~" term under the guard of a domain");
			enforce(has("between_guard_integral ")==among("SummandDomain"),c.name~" domain of the term");
			enforce(has("shift_between ")==among("SummandPole","SummandPoleStrict"),c.name~" pole");
			bool logarithm=among("Summand","SummandBounds","SummandPoleStrict","SummandDomain","SummandFunction");
			enforce(has("log_between ")==logarithm,c.name~" logarithm next to the term");
			enforce(has("ratio_between ")==among("SummandQuotient","SummandQuotientBounds","SummandPole"),c.name~" quotient next to the term");
			enforce(has("ratio_between_scaled_plain ")==among("SummandScale"),c.name~" quotient under a factor next to the term");
		}
		// Several bounds of the axis on one side. A guard is evaluated from
		// the left, so a bound whose term is missing makes the weight
		// missing only where the comparisons before it hold. Two bounds on
		// one side at the front: the observation with the first under the
		// test that the first implies the second, plus that with the second
		// under the negation; a half-line is never empty. A third bound
		// after a lower and an upper one: the same for it and the bound on
		// its side, under the test that the first two leave a point, since
		// otherwise the observation is a zero whatever the third term is.
		// Each case has one bound less, and a guard with more bounds takes
		// as many steps. The weights are the masks of their comparisons
		// around the same rest, by the structure of the guard: a
		// conjunction however it is nested, masks of masks below a binder,
		// the cast of a bracket, or a mask under the guard of its domain.
		// A case that has no closed form keeps the whole integral: a
		// curvature that is a term, a pole between the bounds, a half-line of
		// infinite length.
		if(c.name.indexOf("Competing")==0){
			enum program="Distribution.DensityProgram.",src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(evidence)>=0; }
			bool retained=among("CompetingCurvature","CompetingPole","CompetingUnbounded");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			bool sameLower=among("CompetingHalfLine","CompetingSameSideLower","CompetingDomainHalfLine","CompetingRateHalfLine","CompetingFunctionHalfLine");
			bool sameUpper=among("CompetingBelow","CompetingSameSide","CompetingSameSideUnit","CompetingDomainSameSide");
			enforce(has(program~"mass_same_side true ")==sameLower,c.name~" two lower bounds");
			enforce(has(program~"mass_same_side false ")==sameUpper,c.name~" two upper bounds");
			bool upperFirst=among("CompetingUpperFirst","CompetingUpperFirstLower");
			bool third=!retained&&!sameLower&&!sameUpper&&!upperFirst;
			bool lowerThird=among("CompetingLower","CompetingStrictLower","CompetingFour","CompetingFourValue","CompetingDomainFour");
			enforce(has(program~"mass_third_second true ")==(third&&!among("CompetingLower","CompetingStrictLower")),c.name~" third bound from above");
			enforce(has(program~"mass_third_first true ")==lowerThird,c.name~" third bound from below");
			enforce(has(program~"mass_third_second false ")==among("CompetingUpperFirstLower"),c.name~" third bound from below after an upper one");
			enforce(has(program~"mass_third_first false ")==among("CompetingUpperFirst"),c.name~" third bound from above after an upper one");
			bool bracket=among("Competing","CompetingLower","CompetingStrict","CompetingFour","CompetingSameSideUnit");
			bool domain=among("CompetingDomain","CompetingDomainSameSide","CompetingDomainFour","CompetingDomainHalfLine");
			enforce(has(src~"Masks.bracket ")==bracket,c.name~" cast of a bracket");
			enforce(has(src~"Masks.under ")==domain,c.name~" mask under its domain");
			enforce(has(src~"Masks.under_last ")==domain,c.name~" value under its domain");
			enforce(has(src~"Masks.mask ")==(!retained&&!bracket&&!domain),c.name~" mask of a value");
			bool nested=among("CompetingFunction","CompetingFunctionValue","CompetingFunctionHalfLine","CompetingNested","CompetingNestedValue");
			enforce(has(src~"Conjunction.and ")==among("CompetingFunction","CompetingNested"),c.name~" conjunction nested to the left");
			if(among("CompetingFunctionValue","CompetingFunctionHalfLine","CompetingNestedValue"))
				enforce(has(src~"Masks.mask ("~src~"Conjunction.one "),c.name~" masks of masks");
			enforce(has(src~"Conjunction.cons ")!=(retained||domain||among("CompetingFunctionHalfLine")),c.name~" conjunction nested to the right");
			enforce(has(program~"mass_guard ")==among("CompetingGuard"),c.name~" guard that does not mention the axis");
		}
		// The cast of a bracket of a rational number: the simplifier keeps a
		// constant under a mask in the least sort that has it, a natural
		// number below all three casts to the reals, an integer below two
		// and a rational below one. Each is the real mask of that number, a
		// constant polynomial, and is observed as a polynomial is between
		// two bounds. The rules that take a comparison out of a guard see
		// through the casts that are there. Below a binder the mask is real
		// and was observed before. Beyond a single bound nothing is observed.
		if(c.name.indexOf("Bracket")==0){
			enum src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(src~evidence)>=0; }
			bool retained=among("BracketUnbounded");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			bool natural=among("BracketNatural","BracketGuard","BracketCompetingNatural","BracketSolved");
			bool integer=among("BracketInteger","BracketGuardInteger","BracketCompetingInteger");
			bool rational=among("BracketRational","BracketStrict","BracketGuardRational","BracketCompeting");
			enforce(has("bracket_natural ")==natural,c.name~" natural number below three casts");
			enforce(has("bracket_integer ")==integer,c.name~" integer below two casts");
			enforce(has("bracket_rational ")==rational,c.name~" rational below one cast");
			enforce(has("polynomial_constant ")!=retained,c.name~" constant polynomial");
			enforce(has("cast_mask_and ")==among("BracketGuard"),c.name~" guard out of three casts");
			enforce(has("cast_mask_and_integer ")==among("BracketGuardInteger"),c.name~" guard out of two casts");
			enforce(has("cast_mask_and_rational ")==among("BracketGuardRational"),c.name~" guard out of one cast");
			enforce(has("Masks.bracket ")==among("BracketCompetingNatural"),c.name~" bounds that compete below three casts");
			enforce(has("Masks.bracket_integer ")==among("BracketCompetingInteger"),c.name~" bounds that compete below two casts");
			enforce(has("Masks.bracket_rational ")==among("BracketCompeting"),c.name~" bounds that compete below one cast");
			enforce(has("solve_left ")==among("BracketSolved"),c.name~" comparison solved below the casts");
			if(among("BracketFunction")) enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_interval")>=0,c.name~" real mask below a binder");
		}
		// A sum of brackets: the simplifier keeps it in the least sort that has
		// its numbers, a sum of natural numbers below all three casts to the
		// reals, of integers below two, of rationals below one, also under a
		// mask that the summands share. The casts are additive and commute
		// with a mask for every definedness pattern, so the weight is the sum
		// of the casts of the summands at every point: the brackets of
		// numbers, each an observation between bounds of its own. Under a
		// common mask that mask goes under the sum first, and so does a factor
		// of the sum; the bounds of a summand may then compete. A summand
		// beyond a single bound keeps the integral.
		if(c.name.indexOf("CastSum")==0){
			enum src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(src~evidence)>=0; }
			bool retained=among("CastSumUnbounded");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_pieces")>=0)!=retained,c.name~" sum of observations");
			enforce(has("cast_add_natural ")==among("CastSum","CastSumThree","CastSumCompeting","CastSumClosed","CastSumMany","CastSumOne","CastSumMixed","CastSumBound","CastSumWeight","CastSumExponential","CastSumHalfLine"),c.name~" sum of natural numbers below three casts");
			enforce(has("cast_add_integer ")==among("CastSumInteger","CastSumCompetingInteger"),c.name~" sum of integers below two casts");
			enforce(has("cast_add_rational ")==among("CastSumRational","CastSumMixed"),c.name~" sum of rationals below one cast");
			bool common=!retained&&!among("CastSumThree","CastSumInteger","CastSumClosed");
			enforce((certificate.indexOf("Distribution.DensityProgram.mass_pointwise")>=0)==common,c.name~" mask that the summands share");
			enforce((certificate.indexOf("Value.mul_add ")>=0)==among("CastSumWeight","CastSumExponential","CastSumHalfLine"),c.name~" factor of the sum");
			enforce(has("third_second_piece ")==among("CastSumRational","CastSumCompeting","CastSumCompetingInteger","CastSumMany","CastSumOne","CastSumMixed","CastSumBound","CastSumWeight"),c.name~" bounds of a summand that compete");
			enforce(has("same_side_piece ")==among("CastSumHalfLine"),c.name~" bounds of a summand on one side");
		}
		// A bound whose term is not total, behind other bounds: `[x≤log(a)]`,
		// `[x≤1/a]`, `[x≤sqrt(a)]`. The term is asked for only where the bounds
		// in front hold, and the domain of the weight says so: the negations
		// of those bounds, or the domain of the term, which does not mention
		// the axis. That guard leaves the observation as the guard by the
		// domain of the term, under the test that the bounds in front leave a
		// point: behind a single bound that its term exists, behind a lower
		// and an upper one the test of a third bound. The same shape has the
		// domain of a value that the interval does not read: a sum under its
		// bounds, with such a term in a summand or with a value that is not
		// total. There the guard leaves first, and the summands under the
		// bounds are observed one by one, each under the guard of its own
		// domain. A second such term, one together with the domain of the
		// value, and a sum of summands with bounds of their own under one
		// guard keep the integral: their domain is no longer of that shape.
		if(c.name.indexOf("TermDomain")==0){
			bool among(string[] names...){ foreach(name;names) if(c.name=="TermDomain"~name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(evidence)>=0; }
			bool retained=among("Two","Value","SumApart");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			bool between=c.name.indexOf("TermDomainBetween")==0||among("SumBetween","SumValue");
			enforce(has("Distribution.StepSource.between_domain_piece ")==among("SumBetween","SumValue"),c.name~" domain of a term of a summand behind two bounds");
			enforce(has("Distribution.StepSource.beyond_domain_piece ")==among("Sum"),c.name~" domain of a term of a summand behind a bound");
			enforce(has("Distribution.DensityProgram.mass_between_domain ")==between,c.name~" domain of a term behind a lower and an upper bound");
			enforce(has("Distribution.DensityProgram.mass_beyond_domain ")==(!between&&!retained),c.name~" domain of a term behind a single bound");
		}
		// An integral inside the body of a function of a real number, as the
		// inner one of two integrals is, with a weight that mentions the
		// variable of the function. A step that asks the scalar simplifier
		// does not reach that variable: it is a variable of the binding
		// language, which may be missing, and not a term. But a function
		// evaluates its body at arguments that exist only. So where the body
		// keeps an observation, it is normalized once more with the variable
		// as a scalar variable, a term in the context around the function,
		// where every step treats it as a parameter; the result is the body
		// again. Used where fewer observations are kept then: the weight of
		// an inner integral that is a polynomial in both variables, the two
		// branches of a comparison of the variables, a Gaussian around the
		// outer variable. Where the inner integral is kept either way, the
		// function stays as it is written, and where the steps reach the
		// outer variable as it is, nothing is opened.
		if(c.name.indexOf("Opened")==0){
			bool retained=c.name=="OpenedKept";
			enforce((text.indexOf("∫dy")>=0)==retained,c.name~": "~text);
			bool simplex=c.name=="OpenedSimplex";
			if(simplex) enforce(certificate.indexOf("StepSource.IntervalTerms.factor")>=0,c.name~" factor the outer parameter directly");
			enforce((certificate.indexOf(".lamOpened ")>=0)==(!retained&&!simplex&&c.name!="OpenedDirect"),c.name~" variable of the function as a parameter");
		}
		// A weight whose value is a product or a power of sums that mention
		// the axis: `(a+x)^2`, `(a+x)·(b+x)`, `(1-e^(-2·x))·e^(-x)`. The
		// scalar simplifier keeps such a value as it is written, and the
		// steps of an observation read a sum of terms. So where they have
		// failed, the weight is multiplied out by the expanding mode of the
		// simplifier, the same weight at every point, if it can then be
		// observed: a polynomial whose coefficients are terms, between
		// bounds or in front of a rate, and the product of exponentials that
		// an inner integral leaves. A weight that cannot be observed either
		// way stays as it is written. The variable of an outer integral is
		// not a term for the simplifier; there the weight of the inner
		// integral is read with that variable as a parameter, below.
		if(c.name.indexOf("Multiplied")==0){
			bool retained=c.name=="MultipliedKept";
			enforce((certificate.indexOf(".lamOpened ")>=0)==(c.name=="MultipliedOuter"),c.name~" variable of the outer integral as a parameter");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_")>=0)!=retained,c.name~" certificate");
		}
		// A point that a weight excludes, `[x≠a]`, and a weight on a point
		// only, `[x=a]`: the exclusion is the term `x-a` being not zero, and
		// the other its negation. A term of degree one in the axis vanishes
		// at one point, so the weight differs at that point only from the
		// weight without the exclusion, and the weight on the point only
		// from a zero.
		//
		// Where the exclusion is a condition of the guard right behind a
		// lower and an upper bound, behind a single bound, or at the front,
		// it leaves the observation from there, and the point may be
		// missing, as `log(a)` is and as the variable of an outer integral
		// is in the model: the result is under the test that the point
		// exists, which `t≤t` says of the rest of its term, and that under
		// the test that the bounds in front leave a point, as for a
		// condition that does not mention the axis. What is behind the
		// exclusion exists at every point; the certificate carries that
		// check. The weight on such a point only is a zero under the same
		// tests.
		//
		// Elsewhere, in a summand or with a value behind it whose
		// observation is kept, the exclusion is taken to hold in the whole
		// weight: an equation of partial values where both weights and the
		// rest of the term exist at every point, three checks.
		//
		// A point that is the variable of an outer integral with a value
		// behind it that mentions that variable, or in a summand, is neither:
		// there the weight of the inner integral is read with that variable
		// as a parameter, below.
		//
		// Kept are a weight with a value that is not total, where a missing
		// value could be asked for at the excluded point only; a term that
		// may be missing behind another exclusion or in a summand; and an
		// exclusion whose term is not of degree one.
		if(c.name.indexOf("TermPoint")==0){
			bool among(string[] names...){ foreach(name;names) if(c.name=="TermPoint"~name) return true; return false; }
			import std.algorithm.searching:count;
			size_t steps(string lemma){ return certificate.count("Distribution.DensityProgram."~lemma~" "); }
			bool retained=among("ExcludedDomain","ExcludedSquare","MissingOrder","MissingSum");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(among("ExcludedQuotient")) enforce(certificate.indexOf("Distribution.StepSource.IntervalTerms.cauchy ")>=0,c.name);
			enforce((text.indexOf("≠")>=0)==retained,c.name~": "~text);
			enforce(steps("mass_null_point")==(among("ExcludedSum")?2:among("OnlySummand","Cases","NestedCases")?1:0),c.name~" exclusion in a weight at every point");
			enforce((certificate.indexOf(".lamOpened ")>=0)==among("NestedValue","NestedCases"),c.name~" variable of the outer integral as a parameter");
			bool only=c.name.indexOf("TermPointMissingOnly")==0||among("Only","OnlyValue","NestedOnly");
			bool front=among("ExcludedFirst","ExcludedLine","MissingLine","MissingFront","MissingOnlyLine","NestedFront");
			bool beyond=among("ExcludedBetween","ExcludedHalfLine","MissingHalfLine","MissingOnlyHalfLine");
			bool between=!retained&&!steps("mass_null_point")&&!front&&!beyond;
			size_t twice=among("ExcludedTwo","ExcludedRational","MissingTwo","NestedTwo","NestedThree")?2:1;
			enforce(steps("mass_front_excluded")==(front&&!only?1:0),c.name~" excluded point at the front");
			enforce(steps("mass_beyond_excluded")==(beyond&&!only?1:0),c.name~" excluded point behind a bound");
			enforce(steps("mass_between_excluded")==(between&&!only?twice:0),c.name~" excluded point behind two bounds");
			enforce(steps("mass_front_only")==(front&&only?1:0),c.name~" point only at the front");
			enforce(steps("mass_beyond_only")==(beyond&&only?1:0),c.name~" point only behind a bound");
			enforce(steps("mass_between_only")==(between&&only?1:0),c.name~" point only behind two bounds");
		}
		// An end of an interval that a condition excludes: `[x≤a]·[x≠a]`,
		// `[x≤a]·[a≠x]`, `[x<a]·[x≠a]`. The scalar simplifier knows the two
		// sides to be distinct from the exclusion or from the strict bound,
		// whichever of them the exclusion has on the left and however their
		// difference is split between its sides: the bound becomes strict,
		// the exclusion goes, and what is left is a weight between bounds.
		if(c.name.indexOf("Excluded")==0){
			bool among(string[] names...){ foreach(name;names) if(c.name=="Excluded"~name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(evidence)>=0; }
			enforce(text.indexOf("∫")<0,c.name~": "~text);
			enforce(has("Generated.r_real_le_strict ")==!among("EndStrict"),c.name~" bound made strict");
			enforce(has("Generated.r_real_distinct_reverse ")==among("EndSwapped","Ends","EndsOrigin","EndMoment","EndScaled"),c.name~" exclusion known the other way round");
			enforce(has("Generated.r_real_lt_from_lt ")||!among("EndStrict"),c.name~" distinct below a strict bound");
		}
		// A weight between bounds that meet at the origin exactly where its
		// value is missing: the density of a uniform variable on `[0,a]`,
		// `[0≤x∧x≤a]·a⁻¹`. The simplifier writes its domain as `x≠0∨a≠0`, a
		// guard that can fail at the origin only: it leaves the observation
		// as the guard by `a≠0`. Bounds that meet elsewhere keep the domain
		// in the order of the bounds, which the interval reads as before.
		if(c.name.indexOf("Origin")==0){
			enforce(text.indexOf("∫")<0,c.name~": "~text);
			enforce((certificate.indexOf("Distribution.DensityProgram.mass_guard_origin ")>=0)==(c.name!="OriginOther"),c.name~" guard that can fail at the origin only");
		}
		// A condition that does not mention the axis, behind bounds of the
		// axis in a guard. A guard is evaluated from the left, so the condition
		// is asked for only where the bounds in front of it hold: it leaves
		// the observation as a mask under the test that those bounds leave a
		// point, the test of a third bound behind a lower and an upper one,
		// and behind a single bound, whose half-line is never empty, the test
		// that its term exists. So the factors of a density may come in any
		// order: the condition on the parameter of a uniform density behind
		// its bounds, the bounds of an outer variable behind those of the
		// inner one. The same in a summand of a sum of observations, and
		// under the guard of the domain of the value. Two such conditions
		// behind the bounds are one scalar under such a guard, and so is the
		// rest of the guard: that leaves as a whole first, from behind the
		// bounds, and then the conditions.
		if(c.name.indexOf("Behind")==0){
			bool among(string[] names...){ foreach(name;names) if(c.name=="Behind"~name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(evidence)>=0; }
			bool retained=false;
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			enforce(has("Distribution.DensityProgram.mass_between_domain ")==among("BetweenDomainTwo"),c.name~" rest of the guard of a domain");
			bool pieces=among("Pieces","PiecesHalfLine","PiecesSpread");
			bool between=c.name.indexOf("BehindBetween")==0||among("BoundThenBetween","BoundStrict","Nested");
			bool beyond=c.name.indexOf("BehindBound")==0;
			enforce(has("Distribution.DensityProgram.mass_between_guard ")==(between&&!retained),c.name~" condition behind a lower and an upper bound");
			enforce(has("Distribution.DensityProgram.mass_beyond_guard ")==beyond,c.name~" condition behind a single bound");
			enforce(has("Distribution.StepSource.between_guard_piece ")==among("Pieces","PiecesSpread"),c.name~" condition behind two bounds of a summand");
			enforce(has("Distribution.StepSource.beyond_guard_piece ")==among("PiecesHalfLine","PiecesSpread"),c.name~" condition behind a bound of a summand");
			enforce(has("Distribution.DensityProgram.presentation_mass_pieces")==pieces,c.name~" sum of observations");
			enforce(has("Distribution.StepSource.Masks.under_last ")==among("BetweenDomain","BoundDomain"),c.name~" under the guard of the domain");
		}
		// A product and a power of sums of brackets. Below the casts they are
		// a product and a power of a lesser sort; the casts are multiplicative
		// for every definedness pattern, so they go to the factors and to the
		// base, where they meet the sums. A square and a cube of a sum with a
		// masked summand are two and three factors, and a product of such sums
		// goes under them, one summand of each at a time. The simplifier joins
		// the masks of each product, where a power of a masked term is the
		// masked power, and the summands whose masks exclude each other
		// vanish. A fourth power keeps the integral.
		if(c.name.indexOf("SumFactors")==0){
			enum src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name=="SumFactors"~name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(src~evidence)>=0; }
			bool retained=among("Fourth");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_pieces")>=0)==(!retained&&!among("Masked")),c.name~" sum of observations");
			enforce(has("cast_mul_natural ")==among("Product","ProductSame","Ones","Mixed"),c.name~" product of natural numbers below three casts");
			enforce(has("cast_mul_integer ")==among("Integer"),c.name~" product of integers below two casts");
			enforce(has("cast_mul_rational ")==among("Rational"),c.name~" product of rationals below one cast");
			enforce(has("cast_pow_natural ")==among("Square","SquareWeight","SquareBounds","Cube","Mixed"),c.name~" power of a natural number below three casts");
			enforce(has("cast_pow_integer ")==among("SquareInteger"),c.name~" power of an integer below two casts");
			enforce(has("cast_pow_rational ")==among("SquareRational"),c.name~" power of a rational below one cast");
			enforce(has("power_two ")==among("Square","SquareInteger","SquareRational","SquareWeight","SquareBounds","Mixed","RealSquare"),c.name~" square of a sum");
			enforce(has("power_three ")==among("Cube","RealCube"),c.name~" cube of a sum");
			if(among("Masked","Real")) enforce(certificate.indexOf("r_real_mask_pow")>=0,c.name~" power of a masked term");
		}
		// A summand of a sum of observations with several bounds on one side:
		// the two cases of the order of two of its bounds, each such a summand
		// with one bound less. Observations that add are integrable or
		// missing somewhere, and that stays so under a case distinction: a
		// weight that is a zero is integrable, and one whose test is missing
		// is missing somewhere. So a mask or a factor of a sum goes under the
		// sum also where the bounds of a summand then compete with those of
		// the whole, a sum of a masked and an unmasked summand included, and
		// a comparison in a summand is solved for the axis first. A domain
		// around the whole sum keeps its integral.
		if(c.name.indexOf("PieceCases")==0){
			enum src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(src~evidence)>=0; }
			bool retained=among("PieceCasesDomain");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_pieces")>=0)!=retained,c.name~" sum of observations");
			enforce(has("Piece.add ")!=retained,c.name~" observations that add");
			enforce(has("same_side_piece true ")==among("PieceCasesHalfLine","PieceCasesSameSide"),c.name~" two lower bounds of a summand");
			enforce(has("third_second_piece true ")==among("PieceCases","PieceCasesSpread","PieceCasesNested","PieceCasesHat","PieceCasesAbsolute","PieceCasesSolved"),
				c.name~" third bound of a summand from above");
			enforce(has("third_first_piece true ")==among("PieceCases","PieceCasesSolved"),c.name~" third bound of a summand from below");
			enforce(has("third_second_piece false ")==among("PieceCasesUpperFirst"),c.name~" third bound of a summand from below after an upper one");
			enforce(has("third_first_piece false ")==among("PieceCasesUpperFirstUpper","PieceCasesHat","PieceCasesAbsolute"),
				c.name~" third bound of a summand from above after an upper one");
			if(among("PieceCasesSpread")) enforce(has("Masks.bracket ")&&certificate.indexOf("Value.mask_add")>=0,c.name~" mask of a sum with a bracket");
			enforce(has("solve_left ")==among("PieceCasesSolved"),c.name~" comparison of a summand solved for the axis");
			enforce((certificate.indexOf("Value.split")>=0)==among("PieceCasesAbsolute"),c.name~" split at a change of sign");
		}
		// A comparison that is not solved for the axis: one side is of
		// degree one in the axis, a rational multiple of the axis plus terms
		// that do not mention it, and the other side does not mention it.
		// The comparison is a bound of the axis by the difference of the
		// other side and those terms, times the inverse of the slope, from
		// the other side where the slope is negative; both are missing
		// exactly where a term is, so the weight with the bound is the same
		// at every point. The step is taken only if the observation then has
		// a closed form, by whatever rule: a bound that competes with
		// others, also below a binder. The domain of a value takes the
		// negation of the comparison along, and that is solved with it. A
		// comparison with the axis on both sides, each of degree one, is a
		// bound too: an upper one where the larger slope is on the left, a
		// lower one otherwise, by one term for the comparison and for its
		// negation; with equal slopes the simplifier has taken the axis out
		// before. A slope that is a term and a power of the axis keep their
		// integral.
		if(c.name.indexOf("Solved")==0){
			enum src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(src~evidence)>=0; }
			bool retained=among("SolvedSlope","SolvedSquare");
			bool both=c.name.indexOf("SolvedBoth")==0,cancelled=among("SolvedBothEqual");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			enforce(has("Linear.axis ")==(!retained&&!cancelled),c.name~" axis");
			bool rightNegative=among("SolvedNegative","SolvedRightNegative","SolvedConvolution");
			bool leftNegative=among("SolvedNegativeLeft","SolvedConvolution");
			bool bothUpper=among("SolvedBothUpper","SolvedBothStrict","SolvedBothNegative","SolvedBothTwo","SolvedBothDomain","SolvedBothDomainUpper");
			bool bothLower=both&&!cancelled&&!among("SolvedBothUpper","SolvedBothStrict","SolvedBothNegative");
			enforce(has("solve_both ")==bothUpper,c.name~" upper bound from both sides");
			enforce(has("solve_both_neg ")==bothLower,c.name~" lower bound from both sides");
			enforce(has("solve_both true ")==among("SolvedBothStrict","SolvedBothDomain"),c.name~" strict upper bound from both sides");
			enforce(has("solve_both_neg true ")==among("SolvedBothChain","SolvedBothDomainUpper"),c.name~" strict lower bound from both sides");
			enforce(has("solve_left ")==(!retained&&!both&&!leftNegative&&!rightNegative&&!among("SolvedRight")),c.name~" upper bound from the left");
			enforce(has("solve_left_neg ")==leftNegative,c.name~" lower bound from the left");
			enforce(has("solve_right ")==among("SolvedRight","SolvedDomain"),c.name~" lower bound from the right");
			enforce(has("solve_right_neg ")==rightNegative,c.name~" upper bound from the right");
			enforce(has("solve_left true ")==among("SolvedStrict"),c.name~" strict comparison");
			enforce(has("solve_right true ")==among("SolvedDomain"),c.name~" negation in the domain");
			enforce(has("Linear.add ")==among("SolvedFunctionSum","SolvedNestedSum"),c.name~" axis in two summands");
			if(among("Solved")) enforce(has("Linear.scaled "),c.name~" literal behind the axis");
			if(among("SolvedNegativeLeft")) enforce(has("Linear.scale "),c.name~" literal in front of the axis");
			if(among("SolvedOffset")) enforce(has("Linear.add_left "),c.name~" term behind the axis");
			if(among("SolvedNegative")) enforce(has("Linear.add_right "),c.name~" term in front of the axis");
			enforce((certificate.indexOf("Distribution.DensityProgram.mass_third_")>=0)==(among("SolvedCompeting","SolvedConvolution","SolvedNested")||
				both&&!cancelled&&!among("SolvedBothValue","SolvedBothTwo")),c.name~" competing bounds");
		}
		if(offset){
			bool retained=c.name=="HalfLineOffsetGrowing"||c.name=="LimitOffsetGrowing",limit=c.name.indexOf("Limit")==0;
			enforce((certificate.indexOf(limit?"Limit.EventualScaled.exp_offset":"Distribution.StepSource.scaled_exp_offset")>=0)!=retained,c.name~" offset evidence");
			if(!retained) enforce(certificate.indexOf("Distribution.StepSource.Quadratic.")>=0,c.name~" exponent");
		}
		// A rational polynomial times the exponential of a quadratic whose
		// curvature is a term that does not mention the axis either: the
		// moments are a polynomial in the linear coefficient and in
		// `h = -1/(2·c₂)`, a row for each power of `h`, and the closed form is
		// missing where the curvature is not negative, as the observation is.
		// The coefficients of a polynomial may be terms: each meets the table
		// of the moments of its power. That holds under factors that cannot
		// vanish, a polynomial with a coefficient that is a closed rational
		// other than zero and a scale that is π, an inverse or a product of
		// these. A factor of zero leaves the zero function, which has an
		// integral whatever the curvature is: a scale that may vanish and a
		// polynomial whose coefficients may all vanish have the closed form
		// under their mask, after everything the integrand is strict in. A
		// polynomial of too high a degree keeps its integral. A vanishing
		// integral is missing where the curvature is not negative all the
		// same: under a binder it keeps that domain.
		if(c.name.indexOf("Curvature")==0){
			bool retained=c.name=="CurvatureDegree";
			// The factors that may vanish: a scale, the coefficients, or both.
			bool maskScale=c.name=="CurvatureScale"||c.name=="CurvatureRoot"||c.name=="CurvatureScaleFunction"||c.name=="CurvatureScaleNormal"||
				c.name=="CurvatureVanishing"||c.name=="CurvatureScaleMonic"||c.name=="CurvatureBoth";
			bool maskPolynomial=c.name=="CurvatureEither"||c.name=="CurvatureSteady"||c.name=="CurvatureBoth";
			bool terms=c.name=="CurvatureCentral"||c.name=="CurvatureShifted"||c.name=="CurvatureClosed"||c.name=="CurvatureForm"||c.name=="CurvatureAbsent"||
				c.name=="CurvatureScaleMonic"||c.name=="CurvatureSkippedTerms"||maskPolynomial;
			// A row that is zero is absent; the first has no power of `h`, and
			// stands under its coefficient where that is a term.
			bool mixed=c.name=="CurvatureMixed"||c.name=="CurvatureSkipped";
			bool moments=c.name=="CurvaturePolynomial"||c.name=="CurvatureMean"||c.name=="CurvatureSecond"||c.name=="CurvatureFourth"||c.name=="CurvatureOdd"||
				c.name=="CurvatureLinear"||c.name=="CurvatureOddFunction"||c.name=="CurvatureVanishing"||c.name=="CurvatureSkippedOdd"||terms;
			if(!retained){
				// The statement evaluates the table to decide which rows are
				// zero, so the table is elaborated to its end before the rows
				// meet it. Without a linear coefficient the monomials after the
				// constant are skipped and do not name their coefficients: a
				// row that starts with a zero is then decided by a rational
				// that only the table names, a negative one or a fraction in
				// the last three cases.
				enforce(certificate.indexOf("]] :) ")>=0,c.name~" table elaborated to its end");
				enforce((certificate.indexOf("Distribution.StepSource.MomentTerms.bare")>=0)!=moments,c.name~" constant row");
				enforce((certificate.indexOf("Distribution.StepSource.MomentTerms.present")>=0)==(moments||mixed),c.name~" rows of the powers");
				enforce((certificate.indexOf("Distribution.StepSource.MomentTerms.absent")>=0)==moments,c.name~" rows that are zero");
			}
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_gaussian_curvature")>=0)!=retained,c.name~" certificate");
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_gaussian_curvature_moments")>=0)==terms,c.name~" tables");
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_gaussian_curvature_masked")>=0)==(maskScale&&!terms),c.name~" mask of the scale");
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_gaussian_curvature_moments_masked")>=0)==(terms&&(maskScale||maskPolynomial)),c.name~" mask");
			enforce((certificate.indexOf("Distribution.StepSource.VanishMask.scale")>=0)==(terms&&maskScale&&!maskPolynomial),c.name~" mask of a scale");
			enforce((certificate.indexOf("Distribution.StepSource.VanishMask.polynomial")>=0)==(maskPolynomial&&!maskScale),c.name~" mask of the coefficients");
			enforce((certificate.indexOf("Distribution.StepSource.VanishMask.both")>=0)==(maskPolynomial&&maskScale),c.name~" mask of both");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			enforce((text.indexOf("≠0]")>=0)==(maskScale||maskPolynomial),c.name~": "~text);
			// The coefficient that cannot vanish is the first or a later one.
			bool witness=terms&&!maskPolynomial;
			enforce((certificate.indexOf("Distribution.StepSource.SomeNonvanishing.here")>=0)==witness,c.name~" coefficient that cannot vanish");
			enforce((certificate.indexOf("Distribution.StepSource.SomeNonvanishing.later")>=0)==(witness&&c.name!="CurvatureClosed"),c.name~" its place");
			// The lemma of every shape of a scale is exercised, in a scalar and
			// under a binder; such a coefficient is a closed rational or has one
			// of these shapes.
			bool inverse=c.name=="CurvatureNormal"||c.name=="CurvatureDeviation"||c.name=="CurvatureInverse"||c.name=="CurvatureInverses"||c.name=="CurvatureBound"||
				c.name=="CurvatureMean"||c.name=="CurvatureSecond"||c.name=="CurvatureFourth"||c.name=="CurvatureCentral"||c.name=="CurvatureForm"||c.name=="CurvatureSteady";
			bool product=c.name=="CurvatureDeviation"||c.name=="CurvatureInverses"||c.name=="CurvatureCircle"||c.name=="CurvatureBound"||c.name=="CurvatureForm";
			bool circle=c.name=="CurvatureCircle"||c.name=="CurvatureBound";
			enforce((certificate.indexOf("Distribution.StepSource.Nonvanishing.inv")>=0)==inverse,c.name~" inverse");
			enforce((certificate.indexOf("Distribution.StepSource.Nonvanishing.mul")>=0)==product,c.name~" product");
			enforce((certificate.indexOf("Distribution.StepSource.Nonvanishing.pi")>=0)==circle,c.name~" circle");
			enforce((certificate.indexOf("Distribution.StepSource.Nonvanishing.literal")>=0)==(c.name=="CurvatureCircle"||witness),c.name~" literal");
			if(c.name=="CurvatureGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
		}
		// The whole line under a polynomial times the exponential of a quadratic
		// with negative curvature: the polynomial is a constant up to a
		// derivative that vanishes at both ends. The constant and linear
		// coefficients of the exponent may be terms that do not mention the
		// axis: the exponent is then a quadratic by its structure, and the
		// moments of the polynomial are a polynomial in the linear coefficient,
		// a sum of its monomials. So may the coefficients of a polynomial in
		// front: the integral is linear in them, and each meets the moments of
		// its power. Other exponents and a polynomial of too high a degree keep
		// their integral.
		if(c.name.indexOf("Gaussian")==0){
			bool symbolic=c.name.indexOf("GaussianSymbolic")==0,prefactor=c.name.indexOf("GaussianSymbolicPrefactor")==0;
			bool retained=c.name=="GaussianGrowing"||c.name=="GaussianQuartic"||
				c.name=="GaussianSymbolicLinear"||c.name=="GaussianSymbolicPrefactorDegree";
			auto scaled=c.name=="GaussianNormal"||c.name=="GaussianVariance"||c.name=="GaussianMean"||c.name=="GaussianCentral"||c.name=="GaussianScaled"||c.name=="GaussianPartialScale"||
				c.name=="GaussianSymbolicNested";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_gaussian")>=0)!=retained,c.name~" Gaussian certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(!retained) enforce((certificate.indexOf("presentation_mass_gaussian_scaled")>=0)==scaled,c.name~" scale");
			if(!retained) enforce((certificate.indexOf(prefactor?"presentation_mass_gaussian_moments":"presentation_mass_gaussian_symbolic")>=0&&certificate.indexOf("Distribution.StepSource.Quadratic.")>=0)==symbolic,c.name~" coefficients");
			if(symbolic&&!retained) enforce(certificate.indexOf("Distribution.StepSource.RowTerms.term")>=0&&certificate.indexOf("Distribution.StepSource.Sums.one")>=0,c.name~" monomials");
			if(prefactor&&!retained){
				// The lemma of every shape of such a polynomial is exercised, and
				// those of the monomials that are skipped.
				auto shape=c.name=="GaussianSymbolicPrefactorRoots"?"Bell.cast":c.name=="GaussianSymbolicPrefactorProduct"?"Symbolic.mul":
					c.name=="GaussianSymbolicPrefactorShift"||c.name=="GaussianSymbolicPrefactorPartial"?"RowTerms.vanish":c.name=="GaussianSymbolicPrefactorTilted"?"MomentTerms.absent":
					c.name=="GaussianSymbolicPrefactorMixed"?"polynomial_variable":"Powers.step";
				enforce(certificate.indexOf("Distribution.StepSource."~shape)>=0,c.name~" "~shape);
				enforce(certificate.indexOf("Distribution.StepSource.Symbolic.cast")>=0&&certificate.indexOf("Distribution.StepSource.MomentTerms.present")>=0&&
					certificate.indexOf("Distribution.StepSource.Sums.add")>=0,c.name~" polynomial");
			}
			if(symbolic&&!prefactor&&!retained){
				// The lemma of every shape of an exponent is exercised.
				auto shape=c.name=="GaussianSymbolicProduct"?"Quadratic.product":c.name=="GaussianSymbolicTilt"||c.name=="GaussianSymbolicTwoWeights"?"Quadratic.scale ":
					c.name=="GaussianSymbolicOffset"||c.name=="GaussianSymbolicNested"||c.name=="GaussianSymbolicPartial"?"Quadratic.fill1":c.name=="GaussianSymbolicMixed"?"Quadratic.add":"Quadratic.square";
				enforce(certificate.indexOf("Distribution.StepSource."~shape)>=0,c.name~" "~shape);
				if(c.name=="GaussianSymbolicCubic") enforce(certificate.indexOf("Distribution.StepSource.RowTerms.zero")>=0&&certificate.indexOf("Distribution.StepSource.Sums.add")>=0,c.name);
				if(c.name=="GaussianSymbolicScaled") enforce(certificate.indexOf("Distribution.StepSource.bell_constant")>=0,c.name);
				if(c.name=="GaussianSymbolicGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name);
			}
			if(c.name=="GaussianGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name);
			if(c.name=="GaussianPartialScale") enforce(text.indexOf("a≠0")>=0&&text.indexOf("sqrt(π)")>=0,c.name~": "~text);
		}
		// A half-line that starts or ends at the vertex of a Gaussian: the
		// exponential has half its integral on either side, and the polynomial
		// is a constant up to a derivative that vanishes at the end.
		if(c.name.indexOf("Vertex")==0){
			bool upper=c.name.indexOf("VertexUpper")==0;
			bool scaled=c.name=="VertexScaled"||c.name=="VertexOffset"||c.name=="VertexDomain"||c.name=="VertexNormal";
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_"~(upper?"upper":"halfline"))>=0,c.name~" certificate");
			enforce(certificate.indexOf("Distribution.StepSource."~(upper?"UpperTerms":"HalfLineTerms")~(scaled?".scaledGaussian ":".gaussian "))>=0,c.name~" vertex");
			enforce(text.indexOf("∫")<0,c.name~": "~text);
			if(c.name=="VertexSum") enforce(certificate.indexOf("HalfLineTerms.pure")>=0&&certificate.indexOf("HalfLineTerms.add")>=0,c.name~" terms");
			if(c.name=="VertexOffset") enforce(certificate.indexOf("Limit.EventualScaled.exp_curve")>=0,c.name~" offset");
			if(c.name=="VertexDomain") enforce(certificate.indexOf("HalfLineTerms.guard")>=0,c.name~" domain");
		}
		// A sum of observations between bounds, each with bounds of its own:
		// every summand is integrable or missing somewhere, so the observation
		// of the sum is the sum of the observations. A summand that cannot be
		// observed and a summand on the whole line keep their integral.
		if(c.name.indexOf("Pieces")==0){
			bool retained=c.name=="PiecesGrowing"||c.name=="PiecesWhole";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_pieces")>=0&&certificate.indexOf("Distribution.StepSource.Piece.add")>=0)!=retained,c.name~" certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(!retained){
				// The lemma of every kind of summand is exercised.
				bool interval=c.name=="PiecesInterval"||c.name=="PiecesPolynomial"||c.name=="PiecesThree"||c.name=="PiecesNested";
				bool above=c.name!="PiecesNested",below=c.name!="PiecesShifted"&&c.name!="PiecesInterval"&&c.name!="PiecesPolynomial";
				enforce((certificate.indexOf("Distribution.StepSource.interval_piece")>=0)==interval,c.name~" between two bounds");
				enforce((certificate.indexOf("Distribution.StepSource.halfline_piece")>=0)==above,c.name~" above a bound");
				enforce((certificate.indexOf("Distribution.StepSource.upper_piece")>=0)==below,c.name~" below a bound");
			}
			if(c.name=="PiecesVertex") enforce(certificate.indexOf("Distribution.StepSource.HalfLineTerms.gaussian")>=0,c.name~" vertex");
			if(c.name=="PiecesScaled") enforce(certificate.indexOf("Distribution.StepSource.HalfLineTerms.scaled")>=0&&certificate.indexOf("Distribution.StepSource.UpperTerms.scaled")>=0,c.name~" scale");
			if(c.name=="PiecesGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
		}
		// A factor or a mask of such a sum goes under it, where every summand is
		// then such an observation: a product and a mask distribute over a sum
		// for every definedness pattern, and each summand takes its normal
		// form by itself, the guards of the domains around the sum. A summand
		// that is then not observed, a power of the sum and a domain that
		// mentions the axis keep their integral.
		if(c.name.indexOf("Spread")==0){
			bool retained=c.name=="SpreadGrowing"||c.name=="SpreadPower"||c.name=="SpreadAxisDomain";
			bool mask=c.name.indexOf("SpreadMask")==0||c.name=="SpreadSymbolicBound",guarded=c.name=="SpreadDomain"||c.name=="SpreadRoot";
			enforce((certificate.indexOf("Distribution.DensityProgram.mass_pointwise")>=0)!=retained,c.name~" certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(!retained){
				enforce((certificate.indexOf("Value.mask_add")>=0)==mask,c.name~" mask of a sum");
				enforce(certificate.indexOf("Value.add_mul")>=0||certificate.indexOf("Value.mul_add")>=0||mask,c.name~" factor of a sum");
				enforce((certificate.indexOf("Distribution.DensityProgram.GuardedSum.sound")>=0)==guarded,c.name~" domains");
				enforce(certificate.indexOf("Binding.preserveDomain")>=0,c.name~" normal forms");
				enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_pieces")>=0,c.name~" observations");
			}
			if(c.name=="SpreadNested") enforce(certificate.indexOf("Value.add_mul")>=0&&certificate.indexOf("Value.mul_add")>=0,c.name~" both sides");
			if(c.name=="SpreadGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
		}
		// A weight with absolute values is first split where their arguments
		// change sign: a partial value is the sum of its masks on the pieces
		// between those points, and under the mask of a piece each absolute
		// value is its argument or the opposite. The guards of the domains of
		// the observations beyond a single bound leave their sum. A point
		// that is a term, as in `abs(x-a)`, splits the weight the same way
		// where it exists for every value of the parameters: into its masks
		// below the point and from it on, which asks nothing else of the
		// point. Under the bound of a piece the simplifier knows the sign of
		// the argument, also where the slope is not one. Two such points give
		// four pieces, and with a point that is a number the pieces of the
		// pieces. A piece whose value is a product of sums is multiplied out.
		// An argument that is not of degree one with a rational slope, more
		// than three points that are numbers or two that are terms, a point
		// that may be missing, an absolute value inside another, a rate that
		// is a term and a piece that is not observed keep the integral.
		if(c.name.indexOf("Absolute")==0){
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool term=c.name.indexOf("AbsoluteTerm")==0||c.name=="AbsoluteSymbolic";
			bool retained=among("AbsoluteSquare","AbsoluteGrowing","AbsoluteMany","AbsoluteTermPartial","AbsoluteTermThree","AbsoluteTermInner","AbsoluteTermRateTerm");
			bool number=!term||among("AbsoluteTermMixed","AbsoluteTermFunction");
			bool several=c.name=="AbsoluteTwo"||c.name=="AbsoluteThree"||c.name=="AbsoluteProduct",domain=among("AbsoluteDomain","AbsoluteRoot","AbsoluteTermDomain");
			enforce((certificate.indexOf("Value.split ")>=0)==(number&&!retained),c.name~" split at a number");
			enforce((certificate.indexOf("Value.split_at ")>=0)==(term&&!retained),c.name~" split at a term");
			enforce((certificate.indexOf("Distribution.DensityProgram.mass_pointwise")>=0)!=retained,c.name~" certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(!retained){
				enforce((certificate.indexOf("Value.split_between")>=0)==several,c.name~" pieces between two points");
				enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_pieces")>=0,c.name~" observations");
				enforce((certificate.indexOf("Distribution.DensityProgram.GuardedSum.sound")>=0)==domain,c.name~" domains");
			}
			// The second split is of a sum already: its masks go under that sum.
			if(among("AbsoluteTermTwo","AbsoluteTermMixed","AbsoluteTermFunction")) enforce(certificate.indexOf("Value.mask_add")>=0,c.name~" pieces of pieces");
			// The variable of an outer integral, and of a function, is a
			// parameter where the body is normalized once more.
			if(among("AbsoluteTermFunction","AbsoluteTermNested")) enforce(certificate.indexOf(".lamOpened ")>=0,c.name~" variable of the function as a parameter");
			if(c.name=="AbsoluteTermGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
			if(c.name=="AbsoluteGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
			// A factor of a sum of pieces: the masks of the split go under the
			// sum, and a summand on the other side vanishes.
			if(c.name=="AbsolutePieces") enforce(certificate.indexOf("Value.mask_add")>=0&&certificate.indexOf("Value.mul_add")>=0,c.name~" factor of a sum");
		}
		// Other bounds of a Gaussian: an antiderivative with the error function
		// around the vertex, after that of the polynomial up to its constant.
		// Between two bounds it has the error function itself, beyond a single
		// bound its complement, which vanishes at that end, below a bound with
		// the argument reflected. The constant and linear coefficients of the
		// exponent may be terms that do not mention the axis: the exponent is
		// then a quadratic by its structure, the vertex a multiple of the
		// linear coefficient, and a coefficient that is undefined leaves the
		// observation undefined. A curvature that is not negative or a term,
		// another exponent and a polynomial of too high a degree in front of
		// such coefficients keep their integral.
		if(c.name.indexOf("Erf")==0){
			bool retained=c.name=="ErfGrowing"||c.name=="ErfQuartic"||c.name=="ErfSymbolicCurvature"||c.name=="ErfSymbolicDegree";
			bool symbolic=c.name.indexOf("ErfSymbolic")==0&&c.name!="ErfSymbolicBounds"&&!retained;
			// Under a polynomial the rest of the antiderivative stands beside
			// the error function: a polynomial in the bound and in the linear
			// coefficient times the exponential of the quadratic, at each bound.
			bool polynomial=c.name=="ErfSymbolicPolynomial"||c.name=="ErfSymbolicPositive"||c.name=="ErfSymbolicSecond"||c.name=="ErfSymbolicQuadratic";
			bool above=c.name=="ErfAbove"||c.name=="ErfNormalTail"||c.name=="ErfAboveScaled"||c.name=="ErfVertexSum"||c.name=="ErfGuarded"||
				c.name=="ErfSymbolicTail"||c.name=="ErfSymbolicSum"||c.name=="ErfSymbolicPositive";
			bool below=c.name.indexOf("ErfBelow")==0||c.name=="ErfNormalCdf"||c.name=="ErfSymbolicCdf"||c.name=="ErfSymbolicUndefined"||c.name=="ErfSymbolicFunction"||
				c.name=="ErfSymbolicSecond";
			bool scaled=c.name=="ErfNormalTail"||c.name=="ErfNormalCdf"||c.name=="ErfNormalInterval"||c.name=="ErfScaled"||c.name=="ErfAboveScaled"||c.name=="ErfBelowScaled"||
				c.name=="ErfOffset"||c.name=="ErfDomain";
			auto terms="Distribution.StepSource."~(below?"UpperTerms":above?"HalfLineTerms":"IntervalTerms")~
				(polynomial?".symbolicErfPolynomial ":symbolic?".symbolicErf ":scaled?".scaledErf ":".erf ");
			enforce((certificate.indexOf(terms)>=0)!=retained,c.name~" certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			// The table of the rest is elaborated to its end, and its first
			// row has no power of the linear coefficient in front.
			enforce((certificate.indexOf(".symbolicErfPolynomial ([[")>=0)==polynomial,c.name~" rest");
			enforce((certificate.indexOf("]] :) ([")>=0)==polynomial,c.name~" table elaborated to its end");
			if(polynomial) enforce(certificate.indexOf("Distribution.StepSource.MomentTerms.bare")>=0,c.name~" first row");
			// An exponent without a constant part has a zero in its place.
			if(symbolic) enforce((certificate.indexOf("Distribution.StepSource.Quadratic.fill0")>=0)==(c.name=="ErfSymbolicScaled"),c.name~" constant part");
			if(c.name=="ErfSymbolicSum") enforce(certificate.indexOf("HalfLineTerms.pure")>=0&&certificate.indexOf("HalfLineTerms.add")>=0,c.name~" terms");
			if(c.name=="ErfSymbolicUndefined") enforce(certificate.indexOf("UpperTerms.guard")>=0,c.name~" domain");
			if(c.name=="ErfSum") enforce(certificate.indexOf("IntervalTerms.pure")>=0&&certificate.indexOf("IntervalTerms.add")>=0,c.name~" terms");
			if(c.name=="ErfVertexSum") enforce(certificate.indexOf("HalfLineTerms.gaussian")>=0&&certificate.indexOf("HalfLineTerms.add")>=0,c.name~" vertex");
			if(c.name=="ErfOffset") enforce(certificate.indexOf("Limit.EventualScaled.exp_curve")>=0,c.name~" offset");
			if(c.name=="ErfDomain") enforce(certificate.indexOf("IntervalTerms.guard")>=0,c.name~" domain");
			if(c.name=="ErfGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
		}
		// Beyond a single bound, a constant times the exponential of a
		// quadratic whose curvature is a term that does not mention the axis
		// and cannot vanish, by its form: the exponential is integrable
		// exactly where the curvature is negative, and the closed form with
		// the complement of the error function is missing exactly where it is
		// positive, the root of a negative number. So the distribution function
		// of a normal law whose variance is a term needs no guard but that of
		// its domain. A scale that may vanish has the result under its mask.
		// A curvature that may be zero, where the exponent is linear, and a
		// polynomial in front keep their integral.
		if(c.name.indexOf("Cdf")==0){
			bool retained=c.name=="CdfVanishing"||c.name=="CdfPolynomial";
			bool below=c.name=="CdfNormal"||c.name=="CdfDeviation"||c.name=="CdfFunction"||c.name=="CdfBelowScale";
			bool masked=c.name=="CdfScale"||c.name=="CdfBelowScale";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_direct")>=0)!=retained,c.name~" certificate");
			enforce((certificate.indexOf("Distribution.StepSource.curvature_"~(below?"below":"above")~(masked?"_masked ":" "))>=0)!=retained,c.name~" curvature");
			enforce((certificate.indexOf("Distribution.StepSource.masked_guard_integral")>=0)!=retained,c.name~" domain");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			// An exponent without a constant or a linear part has a zero there.
			if(!retained){
				enforce((certificate.indexOf("Distribution.StepSource.Quadratic.fill0")>=0)==(c.name=="CdfTail"||c.name=="CdfScale"||c.name=="CdfBelowScale"),c.name~" constant part");
				enforce((certificate.indexOf("Distribution.StepSource.Quadratic.fill1")>=0)==(c.name=="CdfTail"||c.name=="CdfScale"),c.name~" linear part");
			}
		}
		// Beyond a single bound, a rational polynomial times the exponential of
		// a linear exponent whose rate is a term that does not mention the
		// axis: it is integrable exactly where the rate has the sign of decay,
		// and the value of the antiderivative at the bound stands under the
		// guard of that sign. That value is the exponential times a polynomial
		// in the bound and in the inverse of the rate: the certificate has its
		// rows as a table, whose first row is zero, and the monomials of the
		// others at the bound. Where the rate has the other sign the integrand
		// is defined and not integrable, so this is the integral of the mask
		// itself and not a term of an observation that adds. A scale that may
		// vanish leaves the zero function: the guard then holds there too,
		// around the mask of the scale. A polynomial of too high a degree or
		// with coefficients that are terms and a summand keep their integral.
		//
		// Between two bounds the same is integrable whatever the rate, and a
		// term like any other, also of a sum. Where the rate is not zero its
		// integral is the difference of that antiderivative at the bounds;
		// where it is zero, the exponential of the constant times the
		// difference of an antiderivative of the polynomial. The two stand
		// under the masks of that test. The certificate has the table and
		// that antiderivative, and at each bound the monomials of both.
		if(c.name=="RateBetweenTermsFactor"){
			// A product with a sum of such terms is not read as it is
			// written: it is multiplied out, and is then a sum of them.
			enforce(text.indexOf("∫")<0,c.name~": "~text);
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_interval")>=0&&certificate.indexOf("Distribution.StepSource.IntervalTerms.rate (")>=0&&
				certificate.indexOf("Distribution.StepSource.IntervalTerms.add")>=0,c.name~" sum of rates between bounds");
		}else if(c.name.indexOf("RateBetween")==0){
			bool retained=c.name=="RateBetweenDegree"||c.name=="RateBetweenTermsDegree";
			// Under a polynomial whose coefficients are terms the integral is
			// linear in them: each meets the table and the antiderivative of
			// its power times the rational polynomial.
			bool terms=c.name.indexOf("RateBetweenTerms")==0&&!retained;
			enforce((certificate.indexOf("Distribution.StepSource.IntervalTerms.rate (")>=0)==(!retained&&!terms),c.name~" rate between bounds");
			enforce((certificate.indexOf("Distribution.StepSource.IntervalTerms.rateTerms (")>=0)==terms,c.name~" coefficients that are terms");
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_interval")>=0)!=retained,c.name~" certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			// The tables and the antiderivatives of the polynomial are
			// elaborated to their end, one after the other.
			enforce((certificate.indexOf("]] :) ([(0 : ℚ), ")>=0)==(!retained&&!terms),c.name~" table and antiderivative");
			enforce((certificate.indexOf("]]] :) ([[(0 : ℚ), ")>=0)==terms,c.name~" tables and antiderivatives");
			// A bound that is a closed zero leaves only the constants; at
			// another one a monomial is skipped where its coefficient is zero.
			bool origin=c.name!="RateBetweenBounds"&&c.name!="RateBetweenScaled"&&c.name!="RateBetweenTermsBounds"&&!retained;
			bool skipped=c.name=="RateBetweenPolynomial"||c.name=="RateBetweenScaled"||c.name=="RateBetweenCircle"||terms;
			enforce((certificate.indexOf("Distribution.StepSource.RowTerms.vanish")>=0)==origin,c.name~" bound that is zero");
			enforce((certificate.indexOf("Distribution.StepSource.RowTerms.zero")>=0)==skipped,c.name~" coefficient that is zero");
			enforce((certificate.indexOf("Distribution.StepSource.IntervalTerms.add")>=0)==(c.name=="RateBetweenSum"),c.name~" sum");
			bool domain=c.name=="RateBetweenInverse"||c.name=="RateBetweenTermsProduct";
			enforce((certificate.indexOf("Distribution.StepSource.IntervalTerms.guard")>=0)==domain,c.name~" domain");
			// A coefficient that is absent meets nothing: neither the rows of
			// its table nor its antiderivative.
			enforce((certificate.indexOf("Distribution.StepSource.MomentTerms.absent [(0 : ℚ), (0 : ℚ), ((1) / (2) : ℚ)]")>=0)==(c.name=="RateBetweenTermsBounds"),c.name~" absent coefficient");
			// The masks of the test stay where the rate may vanish.
			enforce((text.indexOf("≠0]")>=0)==(!retained&&!domain&&c.name!="RateBetweenCircle"),c.name~": "~text);
			if(c.name=="RateBetweenGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
		}else if(c.name.indexOf("Rate")==0){
			bool retained=c.name=="RateSum"||c.name=="RateDegree"||c.name=="RateTerms";
			bool below=c.name=="RateBelow"||c.name=="RateCircle"||c.name=="RateBelowMasked"||c.name=="RateBelowPolynomial"||c.name=="RateBelowZero"||c.name=="RateBelowMean";
			bool masked=c.name=="RateDensity"||c.name=="RateSurvival"||c.name=="RateBelowMasked"||c.name=="RateMean"||c.name=="RateSecond"||c.name=="RateBelowMean"||
				c.name=="RateMeanFunction";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_direct")>=0)!=retained,c.name~" certificate");
			enforce((certificate.indexOf("Distribution.StepSource.rate_"~(below?"below":"above")~(masked?"_masked ":" "))>=0)!=retained,c.name~" rate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			// The table is elaborated to its end before the rows meet it, and
			// its first row is absent. At a bound that is a closed zero only
			// the constants of the rows stand; elsewhere a monomial is skipped
			// where its coefficient is zero.
			bool origin=c.name=="RatePolynomial"||c.name=="RateMean"||c.name=="RateSecond"||c.name=="RateFraction"||c.name=="RateGamma"||c.name=="RateFactorial"||
				c.name=="RateInverse"||c.name=="RateBelowZero";
			enforce((certificate.indexOf("]] :) ")>=0)!=retained,c.name~" table elaborated to its end");
			enforce((certificate.indexOf("Distribution.StepSource.MomentTerms.absent [(0 : ℚ)]")>=0)!=retained,c.name~" row without a power");
			enforce((certificate.indexOf("Distribution.StepSource.RowTerms.vanish")>=0)==origin,c.name~" bound that is zero");
			enforce((certificate.indexOf("Distribution.StepSource.RowTerms.zero")>=0)==(c.name=="RateShifted"),c.name~" coefficient that is zero");
			// The lemma of a scale that cannot vanish is exercised, and the
			// strict guard of the domain of the value.
			enforce((certificate.indexOf("Distribution.StepSource.masked_guard_integral")>=0)==(c.name=="RateScale"||c.name=="RateGamma"||c.name=="RateInverse"),c.name~" domain");
			enforce((certificate.indexOf("Distribution.StepSource.Nonvanishing.")>=0)==(c.name=="RateScale"||c.name=="RateCircle"||c.name=="RateInverse"),c.name~" scale");
			if(c.name=="RateGuarded"||c.name=="RatePolynomialGuarded") enforce(certificate.indexOf("Distribution.DensityProgram.mass_guard")>=0,c.name~" guard free of the axis");
		}
		// A strict guard that does not mention the axis leaves the observation,
		// from the top of a weight or of a factor of it, whether or not the
		// rest is then observed; the scalar under it is simplified there. A
		// guard that mentions the axis as the negation of the bound in front,
		// or else the domain of the value, leaves from behind that bound.
		if(c.name.indexOf("StrictGuard")==0){
			enforce(certificate.indexOf("Distribution.DensityProgram.mass_strict_guard")>=0,c.name~" strict guard certificate");
			enforce(certificate.indexOf("Distribution.DensityProgram.Hoists.here")>=0,c.name~" guard");
			bool retained=c.name=="StrictGuardRetained";
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(!retained&&c.name!="StrictGuardAxis") enforce(certificate.indexOf("presentation_mass_gaussian_")>=0&&certificate.indexOf(".scalarSimplify ")>=0,c.name~" under the guard");
			if(c.name=="StrictGuardTwo") enforce(certificate.indexOf("Hoists.right")>=0,c.name~" factor");
			if(c.name=="StrictGuardAxis") enforce(certificate.indexOf("Hoists.left")>=0&&certificate.indexOf("Distribution.DensityProgram.mass_beyond_domain ")>=0,c.name~": "~text);
		}
		// A limit is evaluated by structure with evidence for every term. A
		// body that has no limit, or one outside the fragment, keeps its binder.
		if(c.name.indexOf("Limit")==0){
			bool retained=c.name=="LimitGrowing"||c.name=="LimitPolynomial"||c.name=="LimitWrongEnd"||c.name=="LimitOscillating"||
				c.name=="LimitGuardOscillating"||c.name=="LimitPiecewiseGrowing"||c.name=="LimitVisibleGrowth"||
				c.name=="LimitReciprocalParameter"||c.name=="LimitInteriorBoundary"||c.name=="LimitQuotientLarger"||c.name=="LimitQuotientParameter"||
				c.name=="LimitExponentCubicGrowing"||c.name=="LimitGaussianSymbolicCurvature"||c.name=="LimitGaussianSymbolicGrowing"||c.name=="LimitOffsetGrowing";
			enforce((certificate.indexOf("Limit.Exact.sound")>=0)!=retained,c.name~" limit certificate");
			enforce((text.indexOf("lim[")>=0)==retained,c.name~": "~text);
			// A bracket or a guard is decided beyond its last cut, and a bound
			// that does not mention the variable is passed where it is defined.
			if(c.name.indexOf("LimitBracket")==0) enforce(certificate.indexOf("Limit.Exact.of_eventual")>=0,c.name);
			if(c.name=="LimitBracket"||c.name=="LimitBracketBottom"||c.name=="LimitBracketAffine") enforce(certificate.indexOf("Limit.Eventual.step")>=0,c.name);
			if(c.name=="LimitBracketBounds"||c.name=="LimitBracketPartialBound")
				enforce(certificate.indexOf("Limit.Eventual.bound_le")>=0&&certificate.indexOf("Limit.Eventual.step")<0,c.name);
			if(c.name=="LimitBracketPartialBound") enforce(text.indexOf("a≠0")>=0,c.name~": "~text);
			// A guard that is eventually false masks whatever it guards, and a
			// piecewise polynomial factor counts beyond its last cut: where it
			// is zero there the product vanishes whatever the exponential does.
			if(c.name.indexOf("LimitHidden")==0||c.name.indexOf("LimitTwoSided")==0||c.name=="LimitConditionalDecay")
				enforce(certificate.indexOf("Limit.Eventual.mask_never")>=0,c.name);
			if(c.name=="LimitHiddenGrowthBound") enforce(certificate.indexOf("Limit.never_bound")>=0,c.name);
			if(c.name.indexOf("LimitAbsolute")==0||c.name=="LimitPiecewiseFactor"||c.name=="LimitPiecewiseZero")
				enforce(certificate.indexOf("Limit.EventualExp.piece ")>=0,c.name);
			if(c.name=="LimitPiecewiseZero") enforce(certificate.indexOf("Limit.vanishes_zero")>=0,c.name);
			if(c.name=="LimitAbsoluteBottom"||c.name=="LimitPiecewiseFactor") enforce(certificate.indexOf("Limit.EventualScaled.")>=0,c.name);
			// Continuous operations keep a limit: builtins that are defined
			// everywhere, partial ones at a rational limit inside their domain,
			// and the reciprocal of a rational limit other than zero. A strict
			// guard that is eventually decided lets its value through.
			if(c.name=="LimitLogistic"||c.name=="LimitReciprocal") enforce(certificate.indexOf("Limit.Exact.inv")>=0&&certificate.indexOf("Limit.nonzero_literal")>=0,c.name);
			if(c.name=="LimitReciprocalStep"||c.name=="LimitReciprocalZero") enforce(certificate.indexOf("Limit.Exact.inv")<0&&certificate.indexOf("Limit.Exact.of_eventual")>=0,c.name);
			if(c.name.indexOf("LimitContinuous")==0||c.name=="LimitComplex") enforce(certificate.indexOf(c.name=="LimitContinuousAbsolute"?"Limit.Exact.abs":"Limit.Exact.regular")>=0,c.name);
			if(c.name.indexOf("LimitInterior")==0&&!retained) enforce(certificate.indexOf("Limit.Exact.interior")>=0,c.name);
			if(c.name=="LimitStrictGuard"||c.name=="LimitStrictGuardUndefined") enforce(certificate.indexOf("Limit.Eventual.binary Binding.guardValue")>=0,c.name);
			if(c.name=="LimitStrictGuardDecay") enforce(certificate.indexOf("Limit.Exact.guard")>=0,c.name);
			// A quotient of polynomials tends at both ends to the quotient of
			// the coefficients at the degree of its denominator, unless the
			// numerator has a larger one.
			if(c.name.indexOf("LimitQuotient")==0&&!retained)
				enforce(certificate.indexOf("Limit.Exact.quotient Limit.Infinite."~(c.name=="LimitQuotientBottom"||c.name=="LimitQuotientPower"?"bottom":"top"))>=0,c.name);
			// The exponential of a polynomial that descends dominates every
			// polynomial: the exponent stays below a decaying linear rate.
			bool symbolic=c.name.indexOf("LimitGaussianSymbolic")==0;
			if((c.name.indexOf("LimitGaussian")==0||c.name.indexOf("LimitExponent")==0)&&!retained&&!symbolic)
				enforce(certificate.indexOf("Limit.EventualExp.exp")>=0&&certificate.indexOf("Limit.decays_at"~(c.name=="LimitGaussianMoment"||
					c.name=="LimitExponentShiftedBottom"||c.name=="LimitExponentCubic"?"Bot":"Top"))>=0,c.name);
			// With a constant or linear coefficient that does not mention the
			// variable the exponent is a quadratic by its structure: a negative
			// rational curvature decides the limit at both ends.
			if(symbolic&&!retained)
				enforce(certificate.indexOf("Limit.Exact.gaussian Limit.Infinite."~(c.name=="LimitGaussianSymbolicMoment"?"bottom":"top"))>=0&&
					certificate.indexOf("Distribution.StepSource.Quadratic.")>=0,c.name);
			// The limit of an integral between bounds is the limit of its
			// closed form behind the guard that orders the bounds.
			if(c.name=="LimitMask"||c.name.indexOf("LimitIntegral")==0) enforce(certificate.indexOf("Limit.Exact.mask")>=0,c.name);
			if(c.name.indexOf("LimitIntegral")==0) enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_interval")>=0,c.name);
		}
		// A total weight is evaluated at the inverse point of an affine graph.
		// A weight that is missing somewhere keeps the ordered rows.
		if(c.name.indexOf("WeightedAffine")==0&&c.name!="WeightedAffineMean"&&c.name!="WeightedAffineMoment")
			enforce((certificate.indexOf("_affine_weighted_rule")>=0)==(c.name!="WeightedAffinePartialWeight"),c.name~": "~text);
		// A polynomial on every cell of a rational grid is integrated cell by
		// cell. Nonzero tails are not.
		if(c.name=="StepNonconstant"||c.name.indexOf("Polynomial")==0){
			bool retained=c.name=="PolynomialUnbounded"||c.name=="PolynomialEverywhere"||c.name=="PolynomialAbsoluteNested";
			// The kink of an absolute value of an affine expression is a cut.
			if(c.name.indexOf("PolynomialAbsolute")==0) enforce((certificate.indexOf("StepSource.polynomial_abs")>=0)!=retained,c.name~" absolute value");
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_polynomial")>=0)!=retained,c.name~" polynomial certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
		}
		write(buildPath(directory,c.name~".lean"),certificate);
	}
	auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
	foreach(source;[
		"μ(d:Distribution(ℝ)).addD(δ((1:ℝ)),scaleD(1/2,bindD(d,λ(x:ℝ).δ(5-2*x))))",
		"μ(d:Distribution(ℝ)).addD(δ((1:ℝ)),scaleD(1/2,bindD(d,λ(x:ℝ).δ(5-x/0))))",
		"μ(d:Distribution(ℕ)).addD(δ(0),scaleD(-1,bindD(d,λ(n:ℕ).δ(n+1))))",
		"μ(d:Distribution(ℕ)).addD(scaleD(-1,δ(0)),scaleD(1/2,bindD(d,λ(n:ℕ).δ(n+1))))",
		"μ(d:Distribution(ℕ)).addD(δ(0),scaleD(1/2,bindD(d,λ(n:ℕ).δ(n+n))))",
		"μ(d:Distribution(ℝ)).scaleD(1/2,addD(δ(massD(d)),d))", "μ(d:Distribution(ℝ)).scaleD(-1,addD(δ(0),d))",
		"μ(d:Distribution(ℝ)).addD(scaleD(-1,d),d)", "μ(d:Distribution(ℝ)).Λx. x·d[x]",
		"μ(d:Distribution(ℝ)).addD(δ(0),scaleD(-1,d))", "μ(d:Distribution(ℝ)).addD(Λx.λ[x],scaleD(1/2,d))",
		"μ(d:Distribution(ℝ)).addD(δ(massD(d)),scaleD(1/2,d))",
		"if x<0 then δ(0)[x] else λ[x]", "(λ[x]·δ(x+y)[y])//λ[y]", "Λ(z:ℝ).(λ[x]·δ(x²)[y])//λ[y]",
		"μ(f:ℝ→ℝ).λ(y:ℝ).massD((λ[x]·δ(f(x))[y])//λ[y])",
		"([x<y]·λ[x]·δ(x)[y])//λ[y]", "([0<x]·λ[x]·δ(x+y)[y])//λ[y]",
		"Λy. λ[y ± sqrt(y)]","Λ(n:ℕ). λ[±n]","Λy. δ(0)[1 ± y]","Λy. λ[1+y,]","λ[±sqrt(y)]","λ[-sqrt(y),sqrt(y)]","Λ(n:ℕ). λ[n,n]","Λy. λ[y,true]","inverseCoverD(3)","Λy. λ[y,y | x. x<y]","Λy. λ[y,y | x. x]",
		"radiusImageD(0)","radiusImageD(true,λ(x:ℝ).x)","radiusImageD(0,λ(x:ℝ).x<0)",
		"maskedGraphD(λ(x:ℝ).x,λ(x:ℝ).x)", "maskedGraphD(λ(x:ℝ).0<x,λ(n:ℕ).n)",
		"pushforwardOnD(λ(x:ℝ).x,λ(x:ℝ).x)", "pushforwardOnD(λ(x:ℝ).x<1,λ(n:ℕ).n)",
		"Λ(x:ℕ).λ[x]", "Λ(x:ℝ).δ(x)[x]", "Λ(x:ℝ).λ[x]*λ[x]",
		"Λx. ∑(q:ℚ). δ(q)[x]", "Λx. ∑_x δ(x)[x]", "sumD(λ(x:ℝ). δ(x))",
		"Λ(x:ℝ).δ(2)[y]", "δ(2)=δ(2)", "(δ(2):Distribution(𝔹))",
			"μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if defined(f(n)) then δ((0:ℝ)) else f(n)",
		"μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).Λy. massD(f(n))*λ[y]",
		"μ(f:ℕ→ℝ).λ(n:ℕ).massD(Λ(x:ℝ).f(n)*λ[x])",
		"μ(f:ℕ→ℝ).λ(n:ℕ).densityAtD(Λ(x:ℝ).f(n)*λ[x],0)"
	]) assertThrown(s.run(a,source),source);
	s.declare("n:ℕ");
	assertThrown(s.run(a,"Λ(n:ℕ).δ(λ(n:ℝ^n).0)[n]"),"output-axis dependency in a shadowing binder annotation");
}

int main(string[] args){
	auto dir=args.length>1?args[1]:"build/distributions"; mkdirRecurse(dir); run(dir);
	writeln(cases().length," distribution syntax certificates and rejection tests"); return 0;
}
