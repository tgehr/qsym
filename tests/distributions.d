module distribution_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,type,expected; }
private Case[] cases(){
	enum retry="(μ(d:Distribution(ℝ)).addD(addD(scaleD(1/4,δ(0)),scaleD(1/4,δ(2))),scaleD(1/2,d)))";
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
	Case("JumpPartialRestriction","∫dy λ[2*[0≤y] | x. x⁻¹<1]","ℝ"),
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
	Case("GuardedUnobserved","∫dx [c≤d]*sin(x)*[0≤x≤1]*λ[x]","ℝ"),
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
	Case("SpreadSymbolicBound","∫dx [x≤t]*([x≤0]*exp(x)+[0≤x]*exp(-x))*λ[x]","ℝ"),
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
	Case("AbsoluteSymbolic","∫dx exp(-abs(x-m))*λ[x]","ℝ"),
	Case("AbsoluteSquare","∫dx exp(-abs(x^2-1))*λ[x]","ℝ"),
	Case("AbsoluteGrowing","∫dx abs(x)*λ[x]","ℝ"),
	Case("AbsoluteMany","∫dx exp(-abs(x)-abs(x-1)-abs(x-2)-abs(x-3))*λ[x]","ℝ"),
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
	Case("StrictGuardAxis","∫dx (x+1/a)*λ[x]*[0≤x]*[x≤1]","ℝ"),
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
	Case("RateGuarded","∫dx [c≤d]*[0≤x]*exp(-r*x)*λ[x]","ℝ","([c≤d]·(guard(0<r,r⁻¹)):ℝ)"),
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
	Case("RatePolynomialGuarded","∫dx [c≤d]*[1≤x]*x*exp(-r*x)*λ[x]","ℝ","([c≤d]·(guard(0<r,(r⁻¹+(r^2)⁻¹)·exp(-r))):ℝ)"),
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
		"([0≤t]·(guard(s≠0,2·m·s^3-m·s^2+s^2+(-m·s·t^2-2·t·m·s^2-2·m·s^3+t·m·s+m·s^2-t·s-s^2+s)·exp(-t·s⁻¹)-s)):ℝ)"),
	Case("RateBetweenTermsDegree","∫dx [0≤x≤1]*(x^17+m)*exp(-r*x)*λ[x]","ℝ"),
	Case("RateBetweenTermsFactor","∫dx [0≤x≤1]*(x+m)*(exp(-r*x)+1)*λ[x]","ℝ"),
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
	Case("CurveMean","∫dx [m≤x]*(x-m)*exp(-(x-m)^2)*λ[x]","ℝ"),
	Case("CurveCurvature","∫dx [0≤x]*x*exp(-a*x^2)*λ[x]","ℝ"),
	Case("DomainHalfLine","∫dx [0≤x]*exp(-x)/a*λ[x]","ℝ","guard(a≠0,a⁻¹)"),
	Case("DomainInterval","∫dx [0≤x]*[x≤1]*exp(x)/a*λ[x]","ℝ","guard(a≠0,(e-1)·a⁻¹)"),
	Case("DomainSwapped","∫dx [x≤1]*[0≤x]*exp(x)/a*λ[x]","ℝ","guard(a≠0,(e-1)·a⁻¹)"),
	Case("DomainStrict","∫dx [0<x]*[x<1]*(x+1/a)*λ[x]","ℝ","guard(a≠0,1/2+a⁻¹)"),
	Case("DomainRoot","∫dx [0≤x]*exp(-x)*sqrt(a)*λ[x]","ℝ","guard(0≤a,sqrt(a))"),
	Case("DomainLogarithm","∫dx [0≤x]*exp(-x)*log(a)*λ[x]","ℝ","guard(0<a,log(a))"),
	Case("DomainSum","∫dx [0≤x]*(x*exp(-x^2)/a+exp(-x)/b)*λ[x]","ℝ","guard(a≠0∧b≠0,b⁻¹+a⁻¹·(1/2))"),
	Case("DomainOffset","∫dx [0≤x≤1]*x*exp(-x^2+1/a)*λ[x]","ℝ","guard(a≠0,(-1/2·exp(-1)+1/2)·exp(a⁻¹))"),
	Case("DomainSymbolicBounds","∫dx [u≤x≤v]*exp(x)/a*λ[x]","ℝ","([u≤v]·(guard(a≠0,(-exp(u)+exp(v))·a⁻¹)):ℝ)"),
	Case("DomainGuarded","∫dx [c≤d]*[0≤x]*exp(-x)/a*λ[x]","ℝ","([c≤d]·(guard(a≠0,a⁻¹)):ℝ)"),
	Case("DomainGuardedStrict","∫dx [c<d]*[0≤x≤1]*sqrt(a)*x*λ[x]","ℝ","([c<d]·(guard(0≤a,1/2·sqrt(a))):ℝ)"),
	Case("DomainTwoGuards","∫dx [c≤d]*[e<f]*[0≤x]*exp(-x)/a*λ[x]","ℝ","([c≤d]·([e<f]·(guard(a≠0,a⁻¹))):ℝ)"),
	Case("DomainNested","λ(t:ℝ).∫dx [0≤x]*[x≤t]*exp(-x)/a*λ[x]","ℝ→ℝ","λ(t:ℝ). ([0≤t]·(guard(a≠0,(-exp(-t)+1)·a⁻¹)):ℝ)"),
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
	Case("QuotientLower","∫dx [a≤x≤1]*(1/x)*λ[x]","ℝ","([a≤1]·(guard(0<a,-log(abs(a)))):ℝ)"),
	Case("QuotientBounds","∫dx [a≤x≤b]*(1/x^2)*λ[x]","ℝ","([a≤b]·(guard(0<a∧b≠0∨b<0∧a≠0,-b⁻¹+a⁻¹)):ℝ)"),
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
	Case("QuotientDomain","∫dx [a≤x≤b]*(1/x+x)*λ[x]","ℝ","([a≤b]·(guard(0<a∧b≠0∨b<0∧a≠0,-1/2·a^2+1/2·b^2-log(abs(a))+log(abs(b)))):ℝ)"),
	Case("QuotientDomainStrict","∫dx [a<x≤b]*(x+1)/x^4*λ[x]","ℝ","([a<b]·(guard(0<a∧b≠0∨b<0∧a≠0,(-b·(1/2)-1/3)·(b^3)⁻¹-(-a·(1/2)-1/3)·(a^3)⁻¹)):ℝ)"),
	Case("QuotientDomainAbove","∫dx [a<x]*(x+1)/x^4*λ[x]","ℝ","guard(0<a,-(-a·(1/2)-1/3)·(a^3)⁻¹)"),
	Case("QuotientDomainBelow","∫dx [x≤b]*(x+1)/x^4*λ[x]","ℝ","guard(b<0,(-b·(1/2)-1/3)·(b^3)⁻¹)"),
	Case("QuotientDomainCancelled","∫dx [a≤x]*x^2/x^5*λ[x]","ℝ","guard(0<a,(a^2)⁻¹·(1/2))"),
	Case("QuotientRemovable","∫dx [a≤x≤b]*x^3/x*λ[x]","ℝ"),
	Case("QuotientPole","∫dx [1≤x≤2]*1/(x+1)*λ[x]","ℝ","-log(2)+log(3)"),
	Case("QuotientPoleBounds","∫dx [a≤x≤b]*1/(x+1)*λ[x]","ℝ","([a≤b]·(guard(-1<a∧b≠-1∨b<-1∧a≠-1,-log(abs(a+1))+log(abs(b+1)))):ℝ)"),
	Case("QuotientPoleSquare","∫dx [1≤x≤2]*(1/(2*x+1)^2)*λ[x]","ℝ","1/15"),
	Case("QuotientPoleProduct","∫dx [1≤x≤2]*x/(x+1)*λ[x]","ℝ","log(2)-log(3)+1"),
	Case("QuotientPoleDivision","∫dx [0≤x≤1]*(x^2+1)/(x+1)*λ[x]","ℝ","2·log(2)-1/2"),
	Case("QuotientPoleReversed","∫dx [a≤x≤b]*1/(1-x)*λ[x]","ℝ","([a≤b]·(guard(1<a∧b≠1∨b<1∧a≠1,log(abs(a-1))-log(abs(b-1)))):ℝ)"),
	Case("QuotientPoleFunction","λ(t:ℝ).∫dx [0≤x]*[x≤t]*1/(x+1)^2*λ[x]","ℝ→ℝ","λ(t:ℝ). [0≤t]·(1-(t+1)⁻¹)"),
	Case("QuotientPoleAbove","∫dx [0≤x]*1/(x+1)^2*λ[x]","ℝ","1"),
	Case("QuotientPoleAboveTerm","∫dx [a≤x]*1/(x-2)^3*λ[x]","ℝ","guard(2<a,((a-2)^2)⁻¹·(1/2))"),
	Case("QuotientPoleBelow","∫dx [x<b]*1/(2-x)^2*λ[x]","ℝ","guard(b<2,-(b-2)⁻¹)"),
	Case("QuotientPoleScale","∫dx [1≤x≤2]*c/(x+1)*λ[x]","ℝ","c·(-log(2)+log(3))"),
	Case("QuotientPoleScaleStrict","∫dx [a<x≤b]*c/(x+1)*λ[x]","ℝ","([a<b]·(guard(c=0∧-1≤a∨(-1<a∧b≠-1∨b<-1∧a≠-1),[c≠0]·(c·(-log(abs(a+1))+log(abs(b+1)))))):ℝ)"),
	Case("QuotientPoleScaleClosed","∫dx [0<x<1]*c/(x+1)*λ[x]","ℝ","c·log(2)"),
	Case("QuotientPoleScaleBelow","∫dx [x≤b]*c/(x-2)^2*λ[x]","ℝ","guard(b<2,-c·(b-2)⁻¹)"),
	Case("QuotientPoleUniform","∫dx [a≤x≤b]*(1/(x+1))/log(b/a)*λ[x]","ℝ","([a≤b]·(guard(a≠0∧(0<b·a⁻¹∧(b≠a∧(-1<a∧b≠-1)))∨a<0∧(b≠a∧(b<-1∧a≠-1)),(-log(abs(a+1))+log(abs(b+1)))·log(b·a⁻¹)⁻¹)):ℝ)"),
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
	Case("LogarithmBounds","∫dx [a≤x≤b]*log(x)*λ[x]","ℝ","([a≤b]·(guard(0<a∧0<b,-a·log(a)+b·log(b)+a-b)):ℝ)"),
	Case("LogarithmStrict","∫dx [a<x≤b]*log(x)*λ[x]","ℝ","([a<b]·(guard(0≤a∧0<b,b·log(b)+a-b+[a≠0]·(-a·log(a)))):ℝ)"),
	Case("LogarithmDomain","∫dx [a≤x≤b]*(log(x)+x)*λ[x]","ℝ","([a≤b]·(guard(0<a∧0<b,-a·(a·(1/2)-1)-a·log(a)+b·(b·(1/2)-1)+b·log(b))):ℝ)"),
	Case("LogarithmDomainProduct","∫dx [a≤x≤b]*(x+1)*log(x)*λ[x]","ℝ","([a≤b]·(guard(0<a∧0<b,-a·(a·(1/2)+1)·log(a)+b·(b·(1/2)+1)·log(b)-a·(-a·(1/4)-1)+b·(-b·(1/4)-1))):ℝ)"),
	Case("LogarithmFunction","λ(t:ℝ).∫dx [1≤x]*[x≤t]*log(x)*λ[x]","ℝ→ℝ","λ(t:ℝ). [1≤t]·(t·log(t)-t+1)"),
	Case("LogarithmPole","∫dx [1≤x≤2]*log(x+1)*λ[x]","ℝ","-2·log(2)+3·log(3)-1"),
	Case("LogarithmPoleBounds","∫dx [a≤x≤b]*log(x+1)*λ[x]","ℝ","([a≤b]·(guard(-1<a∧-1<b,-(a+1)·log(a+1)+(b+1)·log(b+1)+a-b)):ℝ)"),
	Case("LogarithmPoleProduct","∫dx [0≤x≤1]*x*log(x+1)*λ[x]","ℝ","1/4"),
	Case("LogarithmPoleStrict","∫dx [2<x≤3]*log(x-2)*λ[x]","ℝ","-1"),
	Case("LogarithmSquare","∫dx [1≤x≤2]*log(x)^2*λ[x]","ℝ"),
	Case("LogarithmQuotient","∫dx [1≤x≤2]*log(x)/x*λ[x]","ℝ"),
	Case("LogarithmScale","∫dx [1≤x≤2]*c*log(x)*λ[x]","ℝ","c·(2·log(2)-1)"),
	Case("LogarithmScaleFactors","∫dx [1≤x≤2]*x*c*log(x)*d*λ[x]","ℝ","c·d·(2·log(2)-3/4)"),
	Case("LogarithmScaleSum","∫dx [1≤x≤2]*c*(log(x)+x)*λ[x]","ℝ","c·(2·log(2)+1/2)"),
	Case("LogarithmScaleStrict","∫dx [a<x≤b]*c*log(x)*λ[x]","ℝ","([a<b]·(guard(0≤a∧0<b,c·(b·log(b)+a-b+[a≠0]·(-a·log(a))))):ℝ)"),
	Case("LogarithmScaleEntropy","∫dx [0<x≤1]*c*x*log(x)*λ[x]","ℝ","-c·(1/4)"),
	Case("LogarithmScaleDomain","∫dx [1≤x≤2]*log(x)/c*λ[x]","ℝ","guard(c≠0,(2·log(2)-1)·c⁻¹)"),
	Case("LogarithmScaleGuarded","∫dx [a≤x≤b]*c*(x+1)*log(x)*λ[x]","ℝ","([a≤b]·(guard(0<a∧0<b,c·(-a·(a·(1/2)+1)·log(a)+b·(b·(1/2)+1)·log(b)-a·(-a·(1/4)-1)+b·(-b·(1/4)-1)))):ℝ)"),
	Case("LogarithmScaleJoined","∫dx [a≤x≤b]*(x+1)*log(x)/sqrt(c)*λ[x]","ℝ","([a≤b]·(guard(0<c∧(0<a∧0<b),(-a·(a·(1/2)+1)·log(a)+b·(b·(1/2)+1)·log(b)-a·(-a·(1/4)-1)+b·(-b·(1/4)-1))·sqrt(c)⁻¹)):ℝ)"),
	Case("LogarithmScaleJoinedFirst","∫dx [a≤x≤b]*(1/sqrt(c))*(log(x)+x)*λ[x]","ℝ","([a≤b]·(guard(0<c∧(0<a∧0<b),(-a·(a·(1/2)-1)-a·log(a)+b·(b·(1/2)-1)+b·log(b))·sqrt(c)⁻¹)):ℝ)"),
	Case("LogarithmScalePole","∫dx [1≤x≤2]*c*log(x+1)*λ[x]","ℝ","c·(-2·log(2)+3·log(3)-1)"),
	Case("LogarithmScalePoleBounds","∫dx [a≤x≤b]*log(x+1)*exp(m)*λ[x]","ℝ","([a≤b]·(guard(-1<a∧-1<b,(-(a+1)·log(a+1)+(b+1)·log(b+1)+a-b)·exp(m))):ℝ)"),
	Case("LogarithmScaleFunction","λ(t:ℝ).∫dx [1≤x]*[x≤t]*c*log(x)*λ[x]","ℝ→ℝ","λ(t:ℝ). [1≤t]·(c·(t·log(t)-t+1))"),
	Case("LogarithmScaleConstant","∫dx [1≤x≤2]*(c*log(x)+d)*λ[x]","ℝ","c·(2·log(2)-1)+d"),
	Case("LogarithmAbove","∫dx [1≤x]*log(x)*λ[x]","ℝ"),
	Case("LogarithmTwo","∫dx [1≤x≤2]*(log(x)-log(x+1))*λ[x]","ℝ"),
	Case("LogarithmMultiple","∫dx [1≤x≤2]*log(2*x)*λ[x]","ℝ","3·log(2)-1"),
	Case("Summand","∫dx [1≤x≤2]*(log(x)+c)*λ[x]","ℝ","c+2·log(2)-1"),
	Case("SummandQuotient","∫dx [1≤x≤2]*(1/x+c)*λ[x]","ℝ","c+log(2)"),
	Case("SummandBounds","∫dx [a≤x≤b]*(log(x)+c)*λ[x]","ℝ","([a≤b]·(c·(-a+b)+(guard(0<a∧0<b,-a·log(a)+b·log(b)+a-b))):ℝ)"),
	Case("SummandQuotientBounds","∫dx [a≤x≤b]*(1/x+c)*λ[x]","ℝ","([a≤b]·(c·(-a+b)+(guard(0<a∧b≠0∨b<0∧a≠0,-log(abs(a))+log(abs(b))))):ℝ)"),
	Case("SummandScale","∫dx [a≤x≤b]*(c/x+d)*λ[x]","ℝ","([a≤b]·(d·(-a+b)+(guard(0<a∧b≠0∨b<0∧a≠0,c·(-log(abs(a))+log(abs(b)))))):ℝ)"),
	Case("SummandPole","∫dx [1≤x≤2]*(1/(x+1)+c)*λ[x]","ℝ","c-log(2)+log(3)"),
	Case("SummandPoleStrict","∫dx [a<x≤b]*(log(x+1)+c)*λ[x]","ℝ","([a<b]·(c·(-a+b)+(guard(-1<b∧a=-1∨-1<b∧-1<a,(b+1)·log(b+1)+a-b+[a≠-1]·(-(a+1)·log(a+1))))):ℝ)"),
	Case("SummandDomain","∫dx [1≤x≤2]*(log(x)+sqrt(c))*λ[x]","ℝ","guard(0≤c,sqrt(c)+2·log(2)-1)"),
	Case("SummandFunction","λ(t:ℝ).∫dx [1≤x]*[x≤t]*(log(x)+c)*λ[x]","ℝ→ℝ","λ(t:ℝ). [1≤t]·(c·(t-1)+t·log(t)-t+1)"),
	Case("SummandAbove","∫dx [1≤x]*(1/x^2+c)*λ[x]","ℝ"),
	Case("SummandNested","∫dx [1≤x≤2]*(log(2*x)+x)*λ[x]","ℝ"),
	Case("QuotientPoleTwo","∫dx [1≤x≤2]*(1/(x+1)+1/x)*λ[x]","ℝ"),
	Case("QuotientPoleQuadratic","∫dx [1≤x≤2]*(1/(x^2+1))*λ[x]","ℝ"),
	Case("QuotientScale","∫dx [1≤x≤2]*c/x*λ[x]","ℝ","c·log(2)"),
	Case("QuotientScaleBounds","∫dx [a≤x≤b]*c/x*λ[x]","ℝ","([a≤b]·(guard(0<a∧b≠0∨b<0∧a≠0,c·(-log(abs(a))+log(abs(b))))):ℝ)"),
	Case("QuotientScaleStrict","∫dx [a<x≤b]*c/x*λ[x]","ℝ","([a<b]·(guard(c=0∧0≤a∨(0<a∧b≠0∨b<0∧a≠0),[c≠0]·(c·(-log(abs(a))+log(abs(b)))))):ℝ)"),
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
	Case("QuotientScaleUniform","∫dx [a≤x≤b]*(1/x)/log(b/a)*λ[x]","ℝ","([a≤b]·(guard(b≠a∧(0<a∧0<b)∨b≠a∧(b<0∧a<0),(-log(abs(a))+log(abs(b)))·log(b·a⁻¹)⁻¹)):ℝ)"),
	Case("QuotientScaleDomainFirst","∫dx [a≤x≤b]*(1/sqrt(c))*((x+1)/x^2)*λ[x]","ℝ","([a≤b]·(guard(0<c∧(0<a∧b≠0)∨0<c∧(b<0∧a≠0),(-log(abs(a))+log(abs(b))-b⁻¹+a⁻¹)·sqrt(c)⁻¹)):ℝ)"),
	Case("QuotientScaleDomainAbove","∫dx [a≤x]*(1/x^2)/sqrt(c)*λ[x]","ℝ","guard(0<c∧0<a,a⁻¹·sqrt(c)⁻¹)"),
	Case("QuotientScaleDomainBelow","∫dx [x<b]*(1/x^2)/(d-c)*λ[x]","ℝ","guard(d≠c∧b<0,-b⁻¹·(d-c)⁻¹)"),
	Case("QuotientScaleDomainNested","λ(t:ℝ).∫dx [1≤x]*[x≤t]*(1/x)/(b-a)*λ[x]","ℝ→ℝ","λ(t:ℝ). ([1≤t]·(guard(b≠a∧t≠0,(b-a)⁻¹·log(abs(t)))):ℝ)"),
	Case("QuotientScaleSum","∫dx [1≤x≤2]*(c/x+x)*λ[x]","ℝ"),
	Case("QuotientScaleDiverges","∫dx [1≤x]*c/x*λ[x]","ℝ"),
	Case("QuotientExponential","∫dx [1≤x≤2]*(1/x)*exp(x)*λ[x]","ℝ"),
	Case("SymbolicIntervalThreeBounds","∫dx [a≤x]*[x≤b]*[x≤c]*λ[x]","ℝ"),
	Case("SymbolicIntervalUnbounded","∫dx [a≤x]*λ[x]","ℝ"),
	Case("SymbolicIntervalSine","∫dx [a≤x≤b]*sin(x)*λ[x]","ℝ"),
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
	Case("RetryObservationFreeProbe","λ(f:ℝ→ℝ).massD(weightD(f,"~retry~"))","(ℝ→ℝ)→ℝ","λ(f:ℝ→ℝ). (2·(f((0:ℝ))·(1/4)+f((2:ℝ))·(1/4)):ℝ)"),
	Case("RetryObservationMissingProbe","massD(weightD(undefined(ℝ→ℝ),"~retry~"))","ℝ","undefined(ℝ)"),
	Case("RetryObservationMissingKernel","massD(bindD("~retry~",undefined(ℝ→Distribution(ℝ))))","ℝ","undefined(ℝ)"),
	Case("RetryObservationContinuousOutput","massD(bindD("~retry~",λ(x:ℝ).Λy. [0≤y≤1]·λ[y]))","ℝ","1"),
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
	Case("LinearTailUnitGain","μ(d:Distribution(ℝ)).addD(δ(0),d)","Distribution(ℝ)","μ(d:Distribution(ℝ)). addD(δ((0:ℝ)),scaleD(1,d))"),
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
	Case("AtomicRetryUnitRatio","μ(d:Distribution(ℝ)).addD(δ(0),scaleD(1,d))","Distribution(ℝ)","μ(d:Distribution(ℝ)). addD(δ((0:ℝ)),scaleD(1,d))"),
	Case("CountdownGeometric","λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then δ((0:ℝ)) else scaleD(1/2,f(n sub 1)))(k))","ℕ→ℝ","λ(k:ℕ). ((1/2)^k:ℝ)"),
	Case("CountdownSigned","λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℝ)).λ(n:ℕ).if n=0 then scaleD(-3,δ((0:ℝ))) else scaleD(-2,f(n sub 1)))(k))","ℕ→ℝ","λ(k:ℕ). (-3·(-2)^k:ℝ)"),
	Case("CountdownCapturedSeed","λ(d:Distribution(ℕ→ℕ)).λ(k:ℕ).massD((μ(f:ℕ→Distribution(ℕ→ℕ)).λ(n:ℕ).if n=0 then d else scaleD(1/2,f(n sub 1)))(k))",
		"Distribution(ℕ→ℕ)→ℕ→ℝ","λ(d:Distribution(ℕ→ℕ)). λ(k:ℕ). ((∫(x:ℕ→ℕ). (d)[x])·(1/2)^k:ℝ)"),
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
		if(c.name.length>=9&&c.name[0..9]=="Countdown"){
			bool fallback=c.name=="CountdownDifferentStride"||c.name=="CountdownPartialRatioZero"||c.name=="CountdownPartialRatioOne";
			enforce((certificate.indexOf("Distribution.mass_scale_countdown")>=0)!=fallback,c.name~" countdown certificate");
		}
		if(c.name=="JumpPartialRestriction") enforce(certificate.indexOf("Grid.restrictedJump")<0&&text.indexOf("∫")>=0,c.name);
		if(c.name=="UnsplitAbsolute") enforce(text.indexOf("∫")>=0,c.name~": "~text);
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
		if(c.name.indexOf("CoordinateSquare")==0)
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
		}else if(c.name.indexOf("RadiusSublevel")==0)
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
		// terms. More bounds, an open side and other integrands keep their
		// integral.
		if(c.name.indexOf("SymbolicInterval")==0){
			bool retained=c.name=="SymbolicIntervalThreeBounds"||c.name=="SymbolicIntervalUnbounded"||c.name=="SymbolicIntervalSine";
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
		// scale. With an exponent that grows above a bound and with a mean or
		// a curvature that is such a term the integral stays, and without such
		// a solution away from the vertex of a Gaussian.
		if(c.name.indexOf("Curve")==0){
			bool retained=c.name=="CurveHalfLineGrowing"||c.name=="CurveMean"||c.name=="CurveCurvature";
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
		if(c.name.indexOf("Quotient")==0||c.name=="DomainAxis"){
			enum src="Distribution.StepSource.";
			bool among(string[] names...){ foreach(name;names) if(c.name==name) return true; return false; }
			bool has(string evidence){ return certificate.indexOf(src~evidence)>=0; }
			bool retained=among("QuotientDiverges","QuotientAbovePolynomial","QuotientRemovable","QuotientExponential","QuotientScaleSum","QuotientScaleDiverges",
				"QuotientPoleInside","QuotientPoleTwo","QuotientPoleQuadratic");
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
			bool retained=c.name=="SpreadGrowing"||c.name=="SpreadSymbolicBound"||c.name=="SpreadPower"||c.name=="SpreadAxisDomain";
			bool mask=c.name.indexOf("SpreadMask")==0,guarded=c.name=="SpreadDomain"||c.name=="SpreadRoot";
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
		// the observations beyond a single bound leave their sum. An argument
		// that is not of degree one with rational coefficients, more than
		// three such points and a piece that is not observed keep the integral.
		if(c.name.indexOf("Absolute")==0){
			bool retained=c.name=="AbsoluteSymbolic"||c.name=="AbsoluteSquare"||c.name=="AbsoluteGrowing"||c.name=="AbsoluteMany";
			bool several=c.name=="AbsoluteTwo"||c.name=="AbsoluteThree"||c.name=="AbsoluteProduct",domain=c.name=="AbsoluteDomain"||c.name=="AbsoluteRoot";
			enforce((certificate.indexOf("Value.split ")>=0&&certificate.indexOf("Distribution.DensityProgram.mass_pointwise")>=0)!=retained,c.name~" certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(!retained){
				enforce((certificate.indexOf("Value.split_between")>=0)==several,c.name~" pieces between two points");
				enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_pieces")>=0,c.name~" observations");
				enforce((certificate.indexOf("Distribution.DensityProgram.GuardedSum.sound")>=0)==domain,c.name~" domains");
			}
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
		if(c.name.indexOf("RateBetween")==0){
			bool retained=c.name=="RateBetweenDegree"||c.name=="RateBetweenTermsDegree"||c.name=="RateBetweenTermsFactor";
			// Under a polynomial whose coefficients are terms the integral is
			// linear in them: each meets the table and the antiderivative of
			// its power times the rational polynomial. A product with a sum is
			// not distributed.
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
		// guard that mentions the axis stays.
		if(c.name.indexOf("StrictGuard")==0){
			enforce(certificate.indexOf("Distribution.DensityProgram.mass_strict_guard")>=0,c.name~" strict guard certificate");
			enforce(certificate.indexOf("Distribution.DensityProgram.Hoists.here")>=0,c.name~" guard");
			bool retained=c.name=="StrictGuardRetained"||c.name=="StrictGuardAxis";
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
			if(!retained) enforce(certificate.indexOf("presentation_mass_gaussian_")>=0&&certificate.indexOf(".scalarSimplify ")>=0,c.name~" under the guard");
			if(c.name=="StrictGuardTwo") enforce(certificate.indexOf("Hoists.right")>=0,c.name~" factor");
			if(c.name=="StrictGuardAxis") enforce(certificate.indexOf("Hoists.left")>=0&&text.indexOf("guard(a≠0,∫dx (guard(")==0,c.name~": "~text);
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
