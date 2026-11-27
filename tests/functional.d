module functional_tests;
import qsym;
import qsym.binding;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,expected,variables; bool domain; }
private Case[] cases(){
	return [
		Case("Curried","(λ(a:ℕ). λ(b:ℕ). a+b)(1)(2)","3"),
		Case("Ascii","(lambda(a:Nat).lambda(b:Nat).a+b)(1)(2)","3"),
		Case("Shadow","(λ(n:ℕ). λ(n:ℕ). n)(1)(2)","2"),
		Case("Capture","(λ(y:ℝ). λ(x:ℝ). y+x)(x)(2)","x+2"),
		Case("HigherOrder","(λ(f:ℕ→ℕ). f(2))(λ(n:ℕ). n+1)","3"),
		Case("ArrowAscription","((λ(n:ℕ). n):ℕ→ℝ)(2)","2"),
		Case("BoolArgument","(λ(p:𝔹). if p then 1 else 2)(false)","2"),
		Case("DecimalBody","(λ(x:ℝ).2.5)(0)","5/2"),
		Case("LeadingDecimal","(λ(x:ℝ). .5)(0)","1/2"),
		Case("PartialApplication","(λ(a:ℕ). λ(b:ℕ). a+b)(1)"),
		Case("RepeatedFactorSign","λ(a:ℝ). λ(b:ℝ). -(a·a)","λ(a:ℝ). λ(b:ℝ). -a·a"),
		Case("RepeatedFactorSignEven","λ(a:ℝ). λ(b:ℝ). b-a·a·a·a","λ(a:ℝ). λ(b:ℝ). -a·a·a·a+b"),
		Case("LimitAscii","lim[x->inf] exp(-x)","0"),
		Case("LimitBinderName","λ(a:ℝ). lim[t→-∞] a·t","λ(a:ℝ). lim[t→-∞] a·t"),
		Case("LimitApplied","(λ(c:ℝ). lim[x→∞] c+exp(-x))(2)","2"),
		Case("LimitScaleDomain","lim[x→∞] exp(-x)/a","a≠0","",true),
		Case("LimitSymbolicFunction","lim[x→∞] f(x)","lim[x→∞] f(x)","f:ℝ→ℝ"),
		Case("LimitInProduct","2·lim[x→∞] sin(x)","2·(lim[x→∞] sin(x))"),
		Case("PartialBooleanAndTrue","λ(h:ℕ→𝔹). h(0)∧true","λ(h:ℕ→𝔹). h(0)"),
		Case("PartialBooleanOrFalse","λ(h:ℕ→𝔹). h(0)∨false","λ(h:ℕ→𝔹). h(0)"),
		Case("PartialBooleanAndFalse","λ(h:ℕ→𝔹). h(0)∧false","λ(h:{h:ℕ→𝔹 | holds((0∈domain(h)))}). false"),
		Case("PartialBooleanOrTrue","λ(h:ℕ→𝔹). h(0)∨true","λ(h:{h:ℕ→𝔹 | holds((0∈domain(h)))}). true"),
		Case("PartialBooleanAndMissing","λ(h:ℕ→𝔹). h(0)∧undefined(𝔹)","λ(h:{h:ℕ→𝔹 | ¬h(0)}). false"),
		Case("PartialBooleanOrMissing","λ(h:ℕ→𝔹). h(0)∨undefined(𝔹)","λ(h:{h:ℕ→𝔹 | h(0)}). true"),
		Case("PartialBooleanLeftMissing","undefined(𝔹)∨true","undefined(𝔹)"),
		Case("PartialBooleanSkippedRight","false∧undefined(𝔹)","false"),
		Case("RestrictedCallSequence","λ(h:ℕ→ℝ).μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 7 else f(seq(h(n),n))","λ(h:ℕ→ℝ). λ(n:{n:ℕ | n=0}). (7:ℝ)"),
		Case("RestrictedCallNested","λ(h:ℕ→𝔹).μ(f:ℕ→ℝ).λ(n:ℕ).if h(n) then 2 else f(guard(h(0),seq(h(1),guard(h(2),n))))","λ(h:ℕ→𝔹). λ(n:{n:ℕ | h(n)}). (2:ℝ)"),
		Case("RestrictedCallRootCall","μ(f:ℕ→ℝ).λ(n:ℕ).f(guard(n≠0,n))","λ(n:ℕ). undefined(ℝ)"),
		Case("RestrictedCallMissing","μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 8 else f(undefined(ℕ))","λ(n:{n:ℕ | n=0}). (8:ℝ)"),
		Case("RestrictedCallPairBranch","λ(h:ℕ→𝔹).μ(f:(ℕ×𝔹)→ℝ).λ(t:ℕ×𝔹).if get(t,1) then get(t,0) else f(if h(0) then t else guard(h(1),t))","λ(h:ℕ→𝔹). λ(t:{t:ℕ×𝔹 | get(t,1)}). ((get(t,0)):ℝ)"),
		Case("RestrictedCallStateChanges","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 7 else f(guard(n≠0,n sub 1)))(2)","7"),
		Case("RestrictedCallOneBranchChanges","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 7 else f(if n=1 then 0 else n sub 1))(2)","7"),
		Case("RestrictedCallRecursiveTest","(μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 9 else f(guard(f(n)<4,n)))(0)","9"),
		Case("StrictMissingGuard","λ(h:ℕ→𝔹).guard(h(0),undefined(ℝ))","λ(h:ℕ→𝔹). undefined(ℝ)"),
		Case("StrictMissingSequence","λ(h:ℕ→ℝ).seq(h(0),undefined(ℕ))","λ(h:ℕ→ℝ). undefined(ℕ)"),
		Case("StrictMissingPairLeft","λ(h:ℕ→𝔹).((undefined(ℝ),h(0)):ℝ×𝔹)","λ(h:ℕ→𝔹). undefined(ℝ×𝔹)"),
		Case("StrictMissingPairRight","λ(h:ℕ→ℝ).((h(0),undefined(𝔹)):ℝ×𝔹)","λ(h:ℕ→ℝ). undefined(ℝ×𝔹)"),
		Case("StrictMissingVectorHead","λ(h:ℕ→ℝ).((undefined(ℝ),h(0)):ℝ^2)","λ(h:ℕ→ℝ). undefined(ℝ^2)"),
		Case("StrictMissingVectorTail","λ(h:ℕ→ℝ).((h(0),undefined(ℝ)):ℝ^2)","λ(h:ℕ→ℝ). undefined(ℝ^2)"),
		Case("StrictMissingFirst","get(undefined(ℝ×𝔹),0)","undefined(ℝ)"),
		Case("StrictMissingSecond","get(undefined(ℝ×𝔹),1)","undefined(𝔹)"),
		Case("StrictMissingPresentSibling","λ(h:ℕ→𝔹).defined(((undefined(ℝ),h(0)):ℝ×𝔹))","λ(h:ℕ→𝔹). false"),
		Case("StrictMissingZeroMaskControl","λ(p:𝔹).[false]·guard(p,undefined(ℝ))","λ(p:𝔹). (0:ℝ)"),
		Case("StrictMissingMissingPredicateControl","λ(h:ℕ→𝔹).if h(0) then undefined(ℝ) else 1","λ(h:{h:ℕ→𝔹 | ¬h(0)}). (1:ℝ)"),
		Case("PointwiseFixBoth","μ(f:ℕ→ℝ).λ(n:ℕ).if n<3 then f(n)+f(n) else n","λ(n:{n:ℕ | 3≤n}). (n:ℝ)"),
		Case("PointwiseFixPredicate","μ(f:ℕ→𝔹).λ(n:ℕ). n=0∨f(n)","λ(n:{n:ℕ | n=0}). true"),
		Case("PointwiseFixConjunction","μ(f:ℕ→𝔹).λ(n:ℕ). n≠0∧f(n)","λ(n:{n:ℕ | n=0}). false"),
		Case("PointwiseFixMask","μ(f:ℕ→ℝ).λ(n:ℕ).[n≠0]·f(n)","λ(n:ℕ). [n≠0]·(undefined(ℝ))"),
		Case("PointwiseFixGuard","μ(f:ℕ→ℝ).λ(n:ℕ).guard(n≠0,f(n))","λ(n:ℕ). undefined(ℝ)"),
		Case("PointwiseFixPair","μ(f:(ℕ×𝔹)→ℝ).λ(t:ℕ×𝔹).if get(t,1) then get(t,0) else f(t)","λ(t:{t:ℕ×𝔹 | get(t,1)}). ((get(t,0)):ℝ)"),
		Case("PointwiseFixReal","μ(f:ℝ→ℝ).λ(x:ℝ).if x<0 then sin(x) else f(x)","λ(x:{x:ℝ | x<0}). sin(x)"),
		Case("PointwiseFixShiftControl","(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 7 else f(n sub 1))(2)","7"),
		Case("MissingChoiceReal","λ(p:𝔹).λ(y:ℝ).[p]·y+[¬p]·undefined(ℝ)","λ(p:𝔹). λ(y:{y:ℝ | p}). y"),
		Case("MissingChoiceReversed","λ(p:𝔹).λ(y:ℝ).[¬p]·undefined(ℝ)+[p]·y","λ(p:𝔹). λ(y:{y:ℝ | p}). y"),
		Case("MissingChoiceNegative","λ(p:𝔹).λ(y:ℝ).[¬p]·y+[p]·undefined(ℝ)","λ(p:𝔹). λ(y:{y:ℝ | ¬p}). y"),
		Case("MissingChoiceNatural","λ(p:𝔹).λ(y:ℕ).[p]·y+[¬p]·undefined(ℕ)","λ(p:𝔹). λ(y:{y:ℕ | p}). y"),
		Case("MissingChoiceInteger","λ(p:𝔹).λ(y:ℤ).[p]·y+[¬p]·undefined(ℤ)","λ(p:𝔹). λ(y:{y:ℤ | p}). y"),
		Case("MissingChoiceRational","λ(p:𝔹).λ(y:ℚ).[p]·y+[¬p]·undefined(ℚ)","λ(p:𝔹). λ(y:{y:ℚ | p}). y"),
		Case("MissingChoiceComplex","λ(p:𝔹).λ(y:ℂ).[p]·y+[¬p]·undefined(ℂ)","λ(p:𝔹). λ(y:{y:ℂ | p}). y"),
		Case("MissingChoicePartialPredicate","λ(h:ℕ→𝔹).λ(y:ℝ).[h(0)]·y+[¬h(0)]·undefined(ℝ)","λ(h:ℕ→𝔹). λ(y:{y:ℝ | h(0)}). y"),
		Case("MissingChoiceNowhere","λ(h:ℕ→ℝ).(λ(x:ℝ).undefined(ℝ))(h(0))","λ(h:ℕ→ℝ). undefined(ℝ)"),
		Case("MissingChoiceOneSided","λ(p:𝔹).λ(q:𝔹).[p]·1+[q]·undefined(ℝ)","λ(p:𝔹). λ(q:𝔹). [p]+[q]·(undefined(ℝ))"),
		Case("FlatFixedIdentity","μ(x:ℝ).x","undefined(ℝ)"),
		Case("FlatFixedConstant","μ(x:ℝ).7","7"),
		Case("FlatFixedStrict","μ(x:ℝ).x+1","undefined(ℝ)"),
		Case("FlatFixedInactive","μ(x:ℝ).[false]·x","0"),
		Case("FlatFixedChosen","μ(x:ℝ).if a<0 then 7 else x","[0≤a]·(undefined(ℝ))+[a<0]·7"),
		Case("FlatFixedReverse","μ(x:ℝ).if a<0 then x else b","[a<0]·(undefined(ℝ))+[0≤a]·b"),
		Case("FlatFixedPartial","λ(h:ℕ→ℝ).μ(x:ℝ).if a<0 then h(0) else x","λ(h:ℕ→ℝ). [a<0]·h(0)+[0≤a]·(undefined(ℝ))"),
		Case("FlatFixedNested","μ(x:ℝ).if a<0 then (μ(y:ℝ).if b<0 then 4 else y) else x","[a<0]·([0≤b]·(undefined(ℝ))+[b<0]·4)+[0≤a]·(undefined(ℝ))"),
		Case("FlatFixedBoolean","μ(p:𝔹). false∧p","false"),
		Case("FlatFixedBooleanStrict","μ(p:𝔹). ¬p","undefined(𝔹)"),
		Case("FlatFixedState","λ(n:ℕ).μ(k:ℕ).if n=0 then 3 else k+1","λ(n:{n:ℕ | n=0}). 3"),
		Case("FlatFixedComplex","μ(z:ℂ).if a<0 then complex(1,2) else conj(z)","[a<0]·(1+2·ⅈ)+[0≤a]·(undefined(ℂ))"),
		Case("FlatFixedTuple","μ(t:ℝ×𝔹).if a<0 then ((1:ℝ),true) else t","guard(a<0,(((1:ℝ),true):ℝ×𝔹))"),
		Case("FlatFixedVector","μ(v:ℝ^2).if a<0 then ((1:ℝ),(2:ℝ)) else v","guard(a<0,((1:ℝ),(2:ℝ)))"),
		Case("FlatFixedPairStrict","μ(t:ℝ×𝔹).((1:ℝ),get(t,1))","undefined(ℝ×𝔹)"),
		Case("FlatFixedUnit","μ(u:Unit).u","undefined(Unit)"),
		Case("FlatFixedUnitInput","(μ(f:Unit→ℝ).λ(u:Unit).if a<0 then 7 else f(u))(())","[0≤a]·(undefined(ℝ))+[a<0]·7"),
		Case("FlatFixedAbsentInput","(μ(f:Unit→ℝ).λ(u:Unit).3)(undefined(Unit))","undefined(ℝ)"),
		Case("FunctionBody","λ(x:ℝ). x/x"),
		Case("GlobalBodyDomain","λ(x:ℝ). y/y","","y:ℝ"),
		Case("FunctionValueDefined","defined(λ(x:ℝ). 1/x)","true"),
		Case("LambdaDomain","λ(x:ℝ). 1/x","","",true),
		Case("LambdaDomainZero","0∈domain(λ(x:ℝ). 1/x)","false"),
		Case("LambdaDomainOne","1∈domain(λ(x:ℝ). 1/x)","true"),
		Case("ApplicationDomainRootMissing","(λ(y:ℝ).0*sqrt(y-1))(0)","undefined(ℝ)"),
		Case("ApplicationDomainRootEndpoint","(λ(y:ℝ).0*sqrt(y-1))(1)","0"),
		Case("ApplicationDomainReciprocalMissing","(λ(y:ℝ).0*(1/y))(0)","undefined(ℝ)"),
		Case("ApplicationDomainReciprocalRegular","(λ(y:ℝ).0*(1/y))(2)","0"),
		Case("ApplicationDomainFalseMask","(λ(y:ℝ).[0<y]*(1/y))(0)","0"),
		Case("ApplicationDomainTrueMask","defined((λ(y:ℝ).[0≤y]*(1/y))(0))","false"),
		Case("ApplicationDomainArgumentMissing","(λ(y:ℝ).(0:ℝ))(undefined(ℝ))","undefined(ℝ)"),
		Case("ApplicationDomainRootDefined","defined((λ(y:ℝ).0*sqrt(y-1))(0))","false"),
		Case("ApplicationDomainNestedSum","(1:ℝ)+(λ(y:ℝ).0*(1/y))(0)","undefined(ℝ)"),
		Case("ApplicationDomainTwoApplications","(λ(y:ℝ).0*sqrt(y-1))((λ(y:ℝ).y)(0))","undefined(ℝ)"),
		Case("ApplicationDomainSymbolic","(λ(y:ℝ).0*(1/y))((x:ℝ))","guard(x≠0,(0:ℝ))"),
		Case("ApplicationDomainReapplied","(λ(f:ℝ→ℝ). f(0))((λ(y:ℝ).0*(1/y)))","undefined(ℝ)"),
		Case("ActiveGuardPredicate","λ(p:𝔹).λ(q:𝔹).λ(z:ℝ).[p]·([guard(p,q)]·z+[guard(p,false)]·guard(p,z))","λ(p:𝔹). λ(q:𝔹). λ(z:ℝ). [p]·([q]·z)"),
		Case("OpenBoundaryZero","λ(h:ℕ→ℝ).[h(0)≤h(1)]·guard(h(0)<h(1),(0:ℝ))","λ(h:{h:ℕ→ℝ | h(0)≠h(1)}). (0:ℝ)"),
		Case("OpenBoundaryRegular","λ(x:ℝ). [x≤1]·guard(x<1,x+2)","λ(x:{x:ℝ | x≠1}). [x<1]·(x+2)"),
		Case("OpenBoundaryZeroReal","λ(x:ℝ). [x≤1]·guard(x<1,(0:ℝ))","λ(x:{x:ℝ | x≠1}). (0:ℝ)"),
		Case("OpenBoundaryPayloadHole","λ(x:ℝ). [x≤1]·guard(x<1,1/x)","λ(x:{x:ℝ | x≠1}). [x<1]·x⁻¹"),
		Case("OpenBoundaryMissingPayload","λ(h:ℕ→ℝ).[h(0)≤h(1)]·guard(h(0)<h(1),undefined(ℝ))","λ(h:ℕ→ℝ). [h(0)≤h(1)]·(undefined(ℝ))"),
		Case("OpenBoundaryLowerAt","(λ(x:ℝ). [x≤1]·guard(x<1,1/x))(0)","0⁻¹"),
		Case("OpenBoundaryAt","(λ(x:ℝ). [x≤1]·guard(x<1,1/x))(1)","undefined(ℝ)"),
		Case("OpenBoundaryAbove","(λ(x:ℝ). [x≤1]·guard(x<1,1/x))(2)","0"),
		Case("OpenBoundaryActive","(λ(x:ℝ). [x≤1]·guard(x<1,1/x))(1/2)","2"),
		Case("OpenBoundaryMissingLeft","(λ(h:ℕ→ℝ).[h(0)≤h(1)]·guard(h(0)<h(1),(0:ℝ)))(λ(n:ℕ).undefined(ℝ))","undefined(ℝ)"),
		Case("OpenBoundaryReversed","λ(h:ℕ→ℝ).[h(0)≤h(1)]·guard(h(1)<h(0),h(2))","λ(h:ℕ→ℝ). [h(0)≤h(1)]·(guard(h(1)<h(0),h(2)))"),
		Case("OpenBoundaryDifferent","λ(h:ℕ→ℝ).[h(0)≤h(1)]·guard(h(0)<h(2),h(2))","λ(h:ℕ→ℝ). [h(0)≤h(1)]·(guard(h(0)<h(2),h(2)))"),
		Case("OrderedMaskWeak","λ(h:ℕ→ℝ).[h(0)<h(1)]·guard(h(0)≤h(1),h(2))","λ(h:ℕ→ℝ). [h(0)<h(1)]·h(2)"),
		Case("OrderedMaskLtLeft","λ(h:ℕ→ℝ).[h(0)<h(1)]·guard(defined(h(0)),h(2))","λ(h:ℕ→ℝ). [h(0)<h(1)]·h(2)"),
		Case("OrderedMaskLtRight","λ(h:ℕ→ℝ).[h(0)<h(1)]·guard(defined(h(1)),h(2))","λ(h:ℕ→ℝ). [h(0)<h(1)]·h(2)"),
		Case("OrderedMaskLeLeft","λ(h:ℕ→ℝ).[h(0)≤h(1)]·guard(defined(h(0)),h(2))","λ(h:ℕ→ℝ). [h(0)≤h(1)]·h(2)"),
		Case("OrderedMaskLeRight","λ(h:ℕ→ℝ).[h(0)≤h(1)]·guard(defined(h(1)),h(2))","λ(h:ℕ→ℝ). [h(0)≤h(1)]·h(2)"),
		Case("OrderedMaskConjunction","λ(h:ℕ→ℝ).[h(0)<h(1)∧h(1)<h(2)]·guard(h(1)≤h(2),h(3))","λ(h:ℕ→ℝ). [h(0)<h(1)∧h(1)<h(2)]·h(3)"),
		Case("OrderedMaskSums","λ(h:ℕ→ℝ).[h(0)<h(1)]·(guard(h(0)≤h(1),h(2))+guard(defined(h(1)),h(3)))","λ(h:ℕ→ℝ). [h(0)<h(1)]·(h(2)+h(3))"),
		Case("OrderedMaskConverse","λ(h:ℕ→ℝ).[h(0)≤h(1)]·guard(h(0)<h(1),h(2))","λ(h:{h:ℕ→ℝ | h(0)≠h(1)}). [h(0)<h(1)]·h(2)"),
		Case("OrderedMaskReversed","λ(h:ℕ→ℝ).[h(0)<h(1)]·guard(h(1)≤h(0),h(2))","λ(h:ℕ→ℝ). [h(0)<h(1)]·(guard(h(1)≤h(0),h(2)))"),
		Case("OrderedMaskUnrelated","λ(h:ℕ→ℝ).[h(0)<h(1)]·guard(defined(h(2)),h(0))","λ(h:ℕ→ℝ). [h(0)<h(1)]·(guard(holds((2∈domain(h))),h(0)))"),
		Case("OrderedMaskDisjunction","λ(h:ℕ→ℝ).[h(0)<h(1)∨h(1)<h(2)]·guard(h(0)≤h(1),h(3))","λ(h:ℕ→ℝ). [h(0)<h(1)∨h(1)<h(2)]·(guard(h(0)≤h(1),h(3)))"),
		Case("OrderedMaskEqualAt","(λ(h:ℕ→ℝ).[h(0)≤h(1)]·guard(h(0)<h(1),h(2)))(λ(n:ℕ).(1:ℝ))","undefined(ℝ)"),
		Case("OrderedMaskMissing","(λ(h:ℕ→ℝ).[h(0)<h(1)]·guard(h(0)≤h(1),h(2)))(λ(n:ℕ).undefined(ℝ))","undefined(ℝ)"),
		Case("ActiveGuardConjLeft","λ(p:𝔹).λ(q:𝔹).λ(z:ℝ).[p∧q]·(guard(p,z)+1)","λ(p:𝔹). λ(q:𝔹). λ(z:ℝ). [p∧q]·(z+1)"),
		Case("ActiveGuardConjRight","λ(p:𝔹).λ(q:𝔹).λ(z:ℝ).[p∧q]·(guard(q,z)+1)","λ(p:𝔹). λ(q:𝔹). λ(z:ℝ). [p∧q]·(z+1)"),
		Case("ActiveGuardRepeated","λ(p:𝔹).λ(q:𝔹).λ(z:ℝ).[p]·(guard(p,z)*guard(p,z)+guard(p,z))","λ(p:𝔹). λ(q:𝔹). λ(z:ℝ). [p]·(z^2+z)"),
		Case("ActiveGuardPartialTest","λ(h:ℕ→𝔹).λ(z:ℝ).[h(0)]·([guard(h(0),h(1))]·z)","λ(h:ℕ→𝔹). λ(z:ℝ). [h(0)]·([h(1)]·z)"),
		Case("ActiveGuardDifferent","λ(p:𝔹).λ(q:𝔹).λ(z:ℝ).[p]·([guard(q,false)]·z)","λ(p:𝔹). λ(q:𝔹). λ(z:ℝ). [p]·([(guard(q,false))]·z)"),
		Case("ActiveGuardDisjunction","λ(p:𝔹).λ(q:𝔹).λ(z:ℝ).[p∨q]·guard(p,z)","λ(p:𝔹). λ(q:𝔹). λ(z:ℝ). [p∨q]·(guard(p,z))"),
		Case("ActiveGuardMaskedMissing","λ(h:ℕ→𝔹).λ(z:ℝ).[h(0)]·([guard(h(0),h(1))]·guard(h(1),z))","λ(h:ℕ→𝔹). λ(z:ℝ). [h(0)]·([h(1)]·z)"),
		Case("ActiveGuardFalseUndefined","(λ(p:𝔹). [p]·guard(p,undefined(ℝ)))(false)","0"),
		Case("ActiveGuardTrueUndefined","(λ(p:𝔹). [p]·guard(p,undefined(ℝ)))(true)","undefined(ℝ)"),
		Case("ActiveGuardMissingPredicate","(λ(p:𝔹). [p]·guard(p,(3:ℝ)))(undefined(𝔹))","undefined(ℝ)"),
		Case("ActiveGuardDifferentAt","(λ(p:𝔹).λ(q:𝔹).λ(z:ℝ).[p]·([guard(q,false)]·z))(true)(false)(1)","undefined(ℝ)"),
		Case("ActiveGuardOrAt","(λ(p:𝔹).λ(q:𝔹).λ(z:ℝ).[p∨q]·guard(p,z))(false)(true)(1)","undefined(ℝ)"),
		Case("QuotientDomainZero","0∈domain(λ(x:ℝ). x/x)","false"),
		Case("QuotientDomainOne","1∈domain(λ(x:ℝ). x/x)","true"),
		Case("UndefinedArgument","(λ(x:ℝ).0)(1/0)","undefined(ℕ)"),
		Case("UndefinedArgumentDomain","(λ(x:ℝ).0)(1/0)","false","",true),
		Case("MaskedArgument","(λ(x:ℝ).0)([false]*(1/0))","0"),
		Case("NaturalPartiality","(λ(n:ℕ). n sub 1)(0)","false","",true),
		Case("NaturalSubtraction","(λ(n:ℕ). n sub 1)(2)","1"),
		Case("GuardVectorLeft","λ(n:ℕ).(guard(n≠0,1),2)","λ(n:{n:ℕ | n≠0}). (1,2)"),
		Case("GuardVectorRight","λ(n:ℕ).(1,guard(n≠0,2))","λ(n:{n:ℕ | n≠0}). (1,2)"),
		Case("GuardVectorShared","λ(n:ℕ).(guard(n≠0,1),guard(n≠0,2))","λ(n:{n:ℕ | n≠0}). (1,2)"),
		Case("GuardVectorNested","λ(n:ℕ).((guard(n≠0,1),2),(3,4))","λ(n:{n:ℕ | n≠0}). ((1,2),(3,4))"),
		Case("GuardPairLeft","λ(n:ℕ).(guard(n≠0,1),true)","λ(n:{n:ℕ | n≠0}). ((1,true):ℕ×𝔹)"),
		Case("GuardPairRight","λ(n:ℕ).(true,guard(n≠0,1))","λ(n:{n:ℕ | n≠0}). ((true,1):𝔹×ℕ)"),
		Case("GuardPairFirst","λ(n:ℕ).get((guard(n≠0,1),true),0)","λ(n:{n:ℕ | n≠0}). 1"),
		Case("GuardPairRest","λ(n:ℕ).get((true,guard(n≠0,1)),1)","λ(n:{n:ℕ | n≠0}). 1"),
		Case("GuardVectorProjection","λ(n:ℕ).get((1,guard(n≠0,2)),0)","λ(n:{n:ℕ | n≠0}). 1"),
		Case("GuardProjectionIndex","λ(n:ℕ).get((1,2),guard(n≠0,0))","λ(n:{n:ℕ | n≠0}). 1"),
		Case("GuardVectorBoundary","defined((λ(n:ℕ).(guard(n≠0,1),2))(0))","false"),
		Case("GuardPairBoundary","defined((λ(n:ℕ).(true,guard(n≠0,2)))(0))","false"),
		Case("GuardMaskedTuple","λ(n:ℕ).([false]*guard(n≠0,1),2)","λ(n:ℕ). (0,2)"),
		Case("GuardCombinedBoundary","defined((λ(n:ℕ).(guard(n≠0,1),guard(n>1,2)))(1))","false"),
		Case("GuardScalarSimplified","guard(b≠0,1/a-1/a)","guard(b≠0∧a≠0,(0:ℝ))"),
		Case("GuardScalarShared","guard(a≠0,exp(1/a-1/a))","guard(a≠0,(1:ℝ))"),
		Case("GuardScalarKept","guard(b≠0,1/a)","guard(b≠0,a⁻¹)"),
		Case("Subset","{n:ℕ | n<3}"),
		Case("SubsetInside","2∈{n:ℕ | n<3}","true"),
		Case("SubsetOutside","3∈{n:ℕ | n<3}","false"),
		Case("SubsetPartialPredicate","0∈{x:ℝ | 1/x>0}","false"),
		Case("SubsetUndefinedElement","(1/0)∈{x:ℝ | true}","false","",true),
		Case("SubsetArgument","(λ(S:Set(ℕ)).2∈S)({i:ℕ | i<3})","true"),
		Case("SubsetOfFunctions","(λ(n:ℕ).n)∈{f:ℕ→ℕ | f(0)=0}","true"),
		Case("RestrictedInside","(λ(x:ℝ | x>0).log(x))(1)","0"),
		Case("RestrictedOutside","(λ(x:ℝ | x>0).log(x))(-1)","false","",true),
		Case("RestrictedLambda","λ(x:ℝ | x>0).log(x)"),
		Case("CurriedDomain","(λ(a:ℕ).λ(b:ℕ).a sub b)(3)","","",true),
		Case("CurriedDomainInside","2∈domain((λ(a:ℕ).λ(b:ℕ).a sub b)(3))","true"),
		Case("CurriedDomainOutside","4∈domain((λ(a:ℕ).λ(b:ℕ).a sub b)(3))","false"),
		Case("SymbolicFunction","f(1)","","f:ℝ→ℝ"),
		Case("SymbolicDomain","domain(f)","domain(f)","f:ℝ→ℝ"),
		Case("SymbolicApplicationDomain","f(1)","","f:ℝ→ℝ",true),
		Case("SymbolicSubset","1∈S","","S:Set(ℝ)"),
		Case("SymbolicSubsetBeta","0∈{n:ℕ | predicate(n)}","","predicate:ℕ→𝔹"),
		Case("CaptureSubset","(λ(n:ℕ).{m:ℕ | predicate(n)(m)})(1)","","predicate:ℕ→ℕ→𝔹"),
		Case("DefinedFunctionVariable","defined(f)","true","f:ℕ→ℕ"),
		Case("DefinedDomain","defined(domain(f))","true","f:ℕ→ℕ"),
		Case("ComplexDomainZero","0∈domain(λ(z:ℂ).log(z))","false"),
		Case("ComplexDomainOne","1∈domain(λ(z:ℂ).log(z))","true")
	];
}
private string[] run(string directory=""){
	string[] names;
	foreach(c;cases()){
		auto session=Session.open(),a=session.arena; FunctionSyntax s;
		if(c.variables.length) s.declare(c.variables);
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true),c.domain),output=s.format(a,r);
		enforce(!r.exhausted,c.name~" exhausted");
		if(c.expected.length) enforce(output==c.expected,c.name~": "~output);
		if(!r.scalarOnly){
			auto normalized=r.bindings.normalize(r.reduction.output,4096,true);
			enforce(normalized.output==r.reduction.output,c.name~" not a normal form");
			enforce(r.bindings.type(r.reduction.input)==r.bindings.type(r.reduction.output),c.name~" changed type");
		}
		auto again=s.run(a,output,[],Options(DensityMode.preserve,true));
		enforce(s.format(a,again)==output,c.name~" round trip: "~output~" -> "~s.format(a,again));
		auto code=s.exportCertificate(a,r);
		import std.string:indexOf;
		if(c.name=="ApplicationDomainRootMissing"||c.name=="ApplicationDomainReciprocalMissing"||
				c.name=="ApplicationDomainNestedSum"||c.name=="ApplicationDomainTwoApplications"||c.name=="ApplicationDomainSymbolic")
			enforce(code.indexOf("namespace QSym.FunctionCertificate")<0&&code.indexOf("#qsym_check_axioms sound")>=0,c.name~" conditional equality");
		if(c.name=="OrderedMaskConverse"||c.name=="OpenBoundaryZero"||c.name=="OpenBoundaryRegular"||
				c.name=="OpenBoundaryZeroReal"||c.name=="OpenBoundaryPayloadHole")
			enforce(code.indexOf("Binding.mask_closed_open")>=0,c.name);
		if(c.name=="OrderedMaskWeak"||c.name=="OrderedMaskConjunction"||c.name=="OrderedMaskSums")
			enforce(code.indexOf("Binding.le_of_lt_true ")>=0,c.name);
		if(c.name=="OrderedMaskLtLeft"||c.name=="OrderedMaskLtRight"||c.name=="OrderedMaskLeLeft"||
				c.name=="OrderedMaskLeRight"||c.name=="OrderedMaskSums")
			enforce(code.indexOf("Binding.defined_of_")>=0,c.name);
		if(c.name=="ActiveGuardConjLeft"||c.name=="ActiveGuardConjRight"||c.name=="ActiveGuardPredicate"||
				c.name=="ActiveGuardPartialTest"||c.name=="ActiveGuardMaskedMissing")
			enforce(code.indexOf("Binding.guard_of_true ")>=0,c.name);
		if(c.name=="ActiveGuardDifferent"||c.name=="ActiveGuardDisjunction")
			enforce(code.indexOf("Binding.guard_of_true ")<0,c.name);
		if(c.name.indexOf("RestrictedCall")==0){
			auto local=c.name!="RestrictedCallStateChanges"&&c.name!="RestrictedCallOneBranchChanges"&&c.name!="RestrictedCallRecursiveTest";
			enforce((code.indexOf("Pointwise.restricted ")>=0)==local,c.name);
		}
		if(c.name.indexOf("PointwiseFix")==0)
			enforce((code.indexOf("Recursion.fixed_pointwise_first ")>=0)==(c.name!="PointwiseFixShiftControl"),c.name);
		if(c.name.indexOf("MissingChoice")==0&&c.name!="MissingChoiceNowhere")
			enforce((code.indexOf("Binding.mask_choice_missing ")>=0)==(c.name!="MissingChoiceOneSided"),c.name);
		if(c.name=="MissingChoiceNowhere") enforce(code.indexOf(".appNowhere ")>=0,c.name);
		if(c.name.indexOf("FlatFixed")==0) enforce(code.indexOf("Recursion.fixed_unit_first")>=0,c.name);
		if(directory.length) write(buildPath(directory,c.name~".lean"),code);
		names~=c.name;
	}
	return names;
}
unittest{
	run(); auto session=Session.open(),a=session.arena; FunctionSyntax s;
	foreach(source;["λ(x:ℕ).missing(0)","(λ(x:ℕ).x)(true)","0∈{p:𝔹 | p}","λ(x:ℕ).x(0)","domain(2)",
		"{x:ℕ | x+1}","λ(x:ℕ).(λ(x:ℕ).x)(0,1)","λ(exp:ℝ).exp", "((λ(x:ℕ).x):ℝ→ℝ)"])
		assertThrown(s.run(a,source));
	foreach(source;["μ(n:ℕ).if defined(n) then 0 else 1","μ(p:𝔹).defined(p)","μ(f:Unit→ℝ).λ(u:Unit).if defined(f(u)) then 1 else 2"])
		assertThrown(s.run(a,source),source);
	assertThrown(s.declare("f:ℕ→ℕ,f:ℝ→ℝ"));
	assertThrown(s.declare("domain:ℕ→ℕ"));
	s.declare("f:ℕ→ℕ,S:Set(ℝ)");
	assertThrown(s.declare("f:ℕ"));
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/functional"; mkdirRecurse(directory);
	writeln(run(directory).length," functional certificates"); return 0;
}
