module distribution_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,type,expected; }
private Case[] cases(){ return [
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
	Case("HalfLineUpper","∫dx [x≤0]*exp(x)*λ[x]","ℝ"),
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
	Case("LimitStrictGuardDecay","lim[x→∞] exp(-x)*x/x","ℝ","0"),
	Case("LimitGrowing","lim[x→∞] exp(x)","ℝ"),
	Case("LimitPolynomial","lim[x→∞] x^2","ℝ"),
	Case("LimitWrongEnd","lim[x→-∞] exp(-x)","ℝ"),
	Case("LimitOscillating","lim[x→∞] sin(x)","ℝ"),
	Case("LimitComplex","lim[x→∞] ⅈ*exp(-x)","ℂ","0"),
	Case("ExponentialShifted","∫dx [0≤x≤1]*exp(x+1)*λ[x]","ℝ"),
	Case("ExponentialSymbolicRate","∫dx [0≤x≤1]*r*exp(-r*x)*λ[x]","ℝ"),
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
		// antiderivative of the same kind. Shifted exponents and symbolic
		// rates keep their integral.
		if(c.name.indexOf("Exponential")==0){
			bool retained=c.name=="ExponentialShifted"||c.name=="ExponentialSymbolicRate";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_interval")>=0)!=retained,c.name~" interval certificate");
			if(c.name!="ExponentialTwoScales") enforce((certificate.indexOf("StepSource.exp_affine")>=0)!=retained,c.name~" exponential evidence");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
		}
		// Above one lower bound every term must decay; the antiderivative
		// then vanishes at infinity. A growing term and an upper half-line
		// keep their integral.
		if(c.name.indexOf("HalfLine")==0){
			bool retained=c.name=="HalfLineGrowing"||c.name=="HalfLineUpper";
			enforce((certificate.indexOf("Distribution.DensityProgram.presentation_mass_halfline")>=0)!=retained,c.name~" half-line certificate");
			enforce((text.indexOf("∫")>=0)==retained,c.name~": "~text);
		}
		// A limit is evaluated by structure with evidence for every term. A
		// body that has no limit, or one outside the fragment, keeps its binder.
		if(c.name.indexOf("Limit")==0){
			bool retained=c.name=="LimitGrowing"||c.name=="LimitPolynomial"||c.name=="LimitWrongEnd"||c.name=="LimitOscillating"||
				c.name=="LimitGuardOscillating"||c.name=="LimitPiecewiseGrowing"||c.name=="LimitVisibleGrowth"||
				c.name=="LimitReciprocalParameter"||c.name=="LimitInteriorBoundary";
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
				enforce(certificate.indexOf("Limit.EventualExp.of_piece")>=0,c.name);
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
