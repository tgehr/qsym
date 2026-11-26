module qsym.binding;
import qsym.ir;
import qsym.integration:IntegralBounds,integralBounds,integralCutPoints,integralAffine,removeIntegralNullGuards;
import qsym.summation:sumAntidifference,sumAbelAntidifference,SumPrimitive;
import qsym.rational_identity:rationalIdentityZero;
import qsym.polynomial:polynomialAntidifference,polynomialZero,rationalAffineSquare;
import qsym.types:TypeId,TypeKind,TypePool,Dimension;
import qsym.number:Number,BigInt;
import qsym.table:Table;
import qsym.generated.rules:Law,instantiate;
import qsym.proof:ScalarClaims,leanSyntaxCode,leanValueOperation,exportDomainLean,exportPolynomialZeroLean,exportRationalZeroLean,scalarExport=exportLean;
import qsym.domain:simplifyDomain;
import qsym.simplify:Result,ScalarResult=Result,Options,DensityMode,simplify;
import std.string:replace,join;
import qsym.spec:leanSort;
import std.exception:enforce;
import std.conv:to;
@safe:

struct Scope{
	private Bindings owner;
	private uint index=uint.max;
	bool opEquals(Scope rhs)const{ return owner is rhs.owner&&index==rhs.index; }
}
struct BoundTerm{
	private Bindings owner;
	private uint index=uint.max;
	@property uint id()const{ return index; }
	bool opEquals(BoundTerm rhs)const{ return owner is rhs.owner&&index==rhs.index; }
}
enum BoundOp:ubyte{ scalar,variable,primitive,lambda,apply,sequence,global,set,member,domain,defined,holds,guard,subset,typeValue,typeEq,bottom,fixed,equal,unit,vectorNil,vectorCons,pair,first,rest,get,tensor,summation,finiteSum,limit,conditional,distributionDirac,distributionZero,distributionLebesgue,distributionAdd,distributionScale,distributionWeight,distributionIntegral,distributionMass,distributionDensityAt,distributionBind,distributionGraphFibre,distributionGraphMass,distributionPushforwardOn,distributionMaskedGraph,distributionRadiusImage,distributionInverseCover,distributionInversePart,distributionSum,distributionFixed,distributionRetry }
enum TensorOp:ubyte{ add,mul,dot,matvec,matmul,power }
struct BoundNode{
	BoundOp op;
	uint context,type,a=uint.max,b=uint.max,data,c=uint.max;
}
struct BinderHint{ string name,refinement; }
private enum BindingRule:ubyte{
	refl,congr,conditionalTrue,conditionalFalse,conditionalBottom,conditionalSame,conditionalDefined,conditionalBool,conditionalNumeric,conditionalMap,conditionalLeft,conditionalRight,beta,closedRationalValue,seqScalar,seqLam,seqSelf,trans,fold,seqTotal,seqGuard,domainLam,memberSet,
	definedTotal,definedGuardFalse,guardTrue,scalarDomain,scalarHolds,scalarSimplify,
	subsetRefl,subsetEmpty,subsetUniv,subsetUnivEmpty,definedMember,definedSubset,definedGuard,definedApp,domainGuardFalse,definedNot,
	guardAnd,guardLeft,guardRight,guardMap,pointwise,holdsGuard,setHolds,typeEqSelf,typeEqValues,shortCircuit,fixedApp,fixedConstant,fixedIdentity,domainBottom,definedFixed,appBottom,appScalarUndefined,memberDomain,
	equalSelf,equalBottomLeft,equalBottomRight,definedEqual,equalUnivEmpty,equalEmptyUniv,fixedRecurrence,tensorEval,tensorPower,tensorDefined,getBottom,getScalarUndefined,domainFixedTotal,tensorSpectral,getCons,tensorSpectrumCast,tensorDomain,getDomain,sumZero,sumRange,rangeZero,rangeStep,rangeLift,rangeSolution,sumGeometric,sumDelta,sumRangeLe,sumConstant,sumInterval,sumDeltaOffset,rangeGeometric,sumBounds,sumRound,sumMaskAnd,rangeAdd,rangeMaskLt,rangeMaskGe,sumTail,sumMaskEqOffset,sumMaskNeOffset,sumTailNatural,sumTailStrict,sumShiftGeometric,sumRationalBound,sumDeltaZero,sumBoundedAdd,sumCastMask,sumCastAdd,sumExcludeOffset,addBottom,mulBottom,sumMissingConstant,sumMissingGuard,sumPowerNatural,sumPowerNegative,sumAffineNatural,sumNaturalBound,sumExcludeZero,sumTailInclusive,sumMaskMerge,sumAffineInteger,sumShiftInteger,sumRealEquality,sumRealIndex,sumAddLeft,sumAddRight,sumDistribute,sumScaleInteger,sumRealExclude,sumIntegerBound,sumRationalSelector,rangeUndefinedBound,distributionMassDirac,distributionDensityLebesgue,distributionDensityWeight,distributionMassWeightedDirac,rangeConstant,sumElementaryPower,sumElementaryAdd,sumGeneralPower,sumCastMul,sumNaturalPowerMul,sumPowerProduct,sumMulSwap,sumMulAssoc,rangeScale,sumTrigReal,sumHyperbolic,rangeProjection,sumExp2,distributionInterval,distributionIntegralAE,distributionMassZero,distributionMassAdd,distributionMassScale,rangeRootsUnity,rangeGuard,distributionMassIntegral,distributionMassBind,distributionMassCountdown,distributionFixedRetry,distributionFixedAffine,distributionFixedTail,distributionFixedBody,distributionRetryPoint,distributionRetryEmpty,distributionRetryZeroPoint,distributionRetryInfinitePoint,distributionDensityInfiniteSeries,distributionDensitySum,distributionCountingDensity,distributionRetryZero,distributionRetryMissing,distributionRetryMass,distributionRetryDensity,distributionRetryObservation,distributionRetryUnbounded,distributionShiftObservation,distributionShiftMoment,distributionInvolutionObservation,distributionInvolutionUnbounded,distributionDefinedRetry,distributionDefinedDirac,distributionDefinedBinary,
	distributionDensityDirac,distributionDensityAtomAdd,distributionDensityFibre,distributionSquareGraph,distributionSquareMass,distributionGraphMass,distributionRestrictedSquare,distributionPushforwardMass,distributionSquareChart,distributionIdentityChart,distributionAffineChart,distributionWeightedAffine,distributionMassGuard,distributionAffineFibre,distributionAffineMass,distributionMaskedAffine,distributionMaskedSquare,distributionTotalGraphMass,distributionAtomRows,distributionMaskAbsorb,distributionChartMass,
	distributionOddFibre,distributionOddMass,distributionMaskedOdd,distributionOddDensity,distributionOddChart,distributionScaleUndefined,distributionAffineOdd,distributionAffineSquare,distributionWeightedSquare,distributionWeightedSquareDensity,distributionClosedSquare,distributionRadiusChart,distributionRadiusDensity,distributionRadiusSublevel,distributionCutoffDensity,
	distributionWeightDirac,distributionWeightAdd,distributionWeightScale,distributionWeightZero,distributionBindDirac,distributionBindAdd,distributionBindScale,distributionBindZero,distributionStrict,
	distributionCoverRadius,distributionCoverAffine,distributionMassSum,distributionWeightSum,distributionBindSum,
	distributionCoverSinh,distributionCoverAsinh,distributionRadiusPairing,distributionSquarePartPairing,distributionSquarePartMass,distributionSquarePartDensity,distributionCoordinateSquare,distributionWeightWeightLebesgue,distributionCoordinateRayPower,distributionCoordinateRayLinear,distributionCoordinateTwoJumps,distributionCoordinateGrid,distributionSmoothCoordinate,distributionCornerPairing,distributionDensityAddWeight,distributionWeightWeightChart,
	limitTerms,distributionMassStrictGuard,distributionMassSpread,scalarNeutral,conditionalUndefined
}
private struct BindingStep{ BindingRule rule; uint from,to,left=uint.max,right=uint.max,extra=uint.max; }
private struct SummationSolution{ uint source,target,candidate,variable,zero,step; SumPrimitive[] tail; uint[] totals,convergence; }
private struct IntegralCell{ Rational lower,upper,sample; }
// Rational coefficient lists, lowest degree first.
private Rational[] polySum(Rational[] a,Rational[] b) @safe {
	auto r=new Rational[](a.length>b.length?a.length:b.length);
	foreach(i,ref v;r) v=(i<a.length?a[i]:Rational(0))+(i<b.length?b[i]:Rational(0));
	return r;
}
private Rational[] polyProduct(Rational[] a,Rational[] b) @safe {
	if(!a.length||!b.length) return [];
	auto r=new Rational[](a.length+b.length-1);
	foreach(ref v;r) v=Rational(0);
	foreach(i,x;a) foreach(j,y;b) r[i+j]=r[i+j]+x*y;
	return r;
}
// The coefficients of `q(y+s)`.
private Rational[] polyTranslate(Rational[] q,Rational s) @safe {
	if(s.zero) return q;
	Rational[] r;
	foreach_reverse(c;q) r=polySum(polyProduct(r,[s,Rational(1)]),[c]);
	return r;
}
// One summand below an interval guard: a polynomial in the axis with an
// optional factor that does not mention the axis, and its antiderivative.
// With `curved` the summand is a polynomial times the exponential of a
// polynomial; above a single bound that exponent stays below the linear
// `rate`, and their difference has degree `order`. With `vertex` the
// exponent is a quadratic with its vertex at the single bound `point`: `bell`
// is the Gaussian integral, of which `half` is half the constant, and `rest`
// the value of the antiderivative at the vertex with the sign of the end.
// At one bound, the literals of the monomials of the rows of an antiderivative
// and of those of an antiderivative of the polynomial (none for one that is
// skipped), and whether the bound is a closed zero. Under a polynomial whose
// coefficients are terms there is a table and an antiderivative for each of
// them, with the literals of those that are present.
private struct RateEnd{ uint[][] rows; uint[] primitive; bool zero; uint[][][] tables; uint[][] primitives; }
private struct IntervalTerm{
	uint value,primitive=uint.max; bool scaled,curved,vertex; Rational rate; uint order;
	GaussianData bell; Rational point,half,rest; uint restLiteral=uint.max;
	// With the error function: the offset of its argument, and the literals
	// of the negated curvature, of that offset and of minus one. With
	// `symbolic` the constant and linear coefficients of the exponent are
	// terms: `point` is `1/(2·c₂)`, and `offset` the factor of the linear
	// coefficient in the argument.
	bool erf,symbolic; Rational offset; uint sigma=uint.max,offsetLiteral=uint.max,unit=uint.max;
	// A polynomial times the exponential of a linear exponent whose rate is
	// a term, beyond a single bound: the literal of zero that the rate is
	// compared with. The rows of `bell` are those of the antiderivative in
	// the powers of the inverse rate, polynomials in the bound; with
	// `boundZero` the bound is a closed zero and only their constants stand.
	// Between two bounds `bell` also has an antiderivative of the polynomial,
	// for a rate that is zero, and `ends` the literals at the upper and at
	// the lower bound. Under a polynomial whose coefficients are terms `bell`
	// has a table for each of them, and `primitives` the antiderivatives.
	bool rateTerm,boundZero; uint rateZero=uint.max; RateEnd[2] ends; Rational[][] primitives;
	// A polynomial over a power of the axis between two bounds on one side of
	// zero. Its antiderivative is a polynomial, the `primitive` of `bell`,
	// plus another one, the `moments` of `bell`, over the power `ratioShift`
	// of the bound, plus the `constant` of `bell` times the logarithm of the
	// absolute value of the bound. Beyond one bound only the second part is
	// there. Factors that do not mention the axis are `ratioScale`, in their
	// order with `uint.max` for the product of the last two; with
	// `ratioPlain` their product stands in front without its mask, where no
	// bound is strict or, with `ratioClosed`, the bounds are closed on one
	// side of zero.
	bool ratioTerm,ratioPlain,ratioClosed; uint ratioShift; uint[] ratioScale;
	// The quotient may be one around a `ratioPole` that is not zero: then
	// the bounds are moved by the literal `ratioMove` of its negation, and
	// `ratioLower` and `ratioUpper` are the moved bounds.
	Rational ratioPole; uint ratioMove=uint.max,ratioLower=uint.max,ratioUpper=uint.max;
	// A polynomial times the logarithm of the axis minus that pole, plus a
	// polynomial, between two bounds. With `y` for the axis minus the pole
	// its antiderivative is `y·P₁(y)·log(y) + y·S₁(y)`: `P₁` is the
	// `primitive` of `bell` and `S₁` its `moments`.
	bool logTerm;
	// The exponential of a quadratic whose curvature is a term that cannot
	// vanish, beyond a single bound: the literal of the factor of the linear
	// coefficient over the curvature in the argument.
	bool curvatureTerm; uint side=uint.max;
}
// With `domain` the value is under a strict guard that does not mention the
// axis; with `hoisted` that guard stands around the mask, after the negations
// of the comparisons of the mask. With `half` there is a single bound: a
// lower one, or with `below` an upper one. With `axis` the guard around the
// mask is, after those negations, that the axis is not zero: the domain of
// a quotient by a power of it. With `joined` it is the conjunction `both`
// of that and of a `domain` that does not mention the axis, with the axis
// first for 1 and last for 2. The axis may also be kept away from another
// point `axisPoint`: then the guard is that the sum of the axis and the
// closed term `axisClosed` is not zero. With `axisPositive` the guard is
// instead that the axis is above the closed term `axisClosed`, whose value
// is `axisPoint`: the domain of a logarithm.
private struct IntervalData{
	uint guard=uint.max,value=uint.max,unit=uint.max,lower,upper,minusOne,domain=uint.max,axis=uint.max,both=uint.max,axisClosed=uint.max;
	ubyte joined; Rational axisPoint; bool axisPositive;
	// Between two bounds the value may be a summand `constant` that does not
	// mention the axis plus a quotient or a logarithm `inner`.
	uint constant=uint.max,inner=uint.max;
	bool swap,strictLower,strictUpper,nested,half,below,hoisted;
	// With `direct` the only term is observed by the integral of the mask:
	// it may be defined without being integrable.
	bool direct;
	IntervalTerm[] terms;
}
// A Gaussian integral. With `symbolic` the constant and linear coefficients of
// the exponent are terms: `vertex` is `-1/(4·c₂)`, `moments` is the polynomial
// in the linear coefficient with the literals `literals` of its monomials
// (none for one that is skipped), `curvature` is the term of the quadratic
// coefficient, and `zero0`, `zero1` stand for an absent constant or linear
// coefficient. Under a polynomial whose coefficients are terms there is one
// such polynomial for each of them: `rows`, with the literals of those that
// are present.
private struct GaussianData{
	Rational[] primitive; Rational constant,c0,c1,c2,vertex,width; uint factor,exponent,scale,circle;
	bool symbolic; Rational[] moments; uint[] literals; uint curvature=uint.max,zero0=uint.max,zero1=uint.max;
	Rational[][] rows; uint[][] rowLiterals;
	// A curvature that is a term, and the scale that cannot vanish. Under a
	// polynomial whose coefficients are terms there is a table of rows for
	// each of them, and one of them cannot vanish.
	bool curved; uint nonzero=uint.max;
	Rational[][][] tables; uint[][][] tableLiterals; uint witness=uint.max;
	// A scale that may vanish, and a polynomial whose coefficients may all
	// vanish: the result is under their mask.
	bool maskScale,maskPolynomial;
}
private struct IntegralSolution{
	uint[] from,to; Rational[] exceptions,probes; IntegralCell[] cells; bool ae,piecewise,closed,polynomial,interval,gaussian; Rational value; Rational[] values; uint output=uint.max; IntervalData bounds; GaussianData bell;
	// The summands of a sum of observations between bounds, each with its own.
	IntegralSolution[] pieces;
	// The summands of a weight with a factor under its sum: for each the
	// certificate of its normal form, if that differs. Before that the
	// weight may be split where its absolute values change sign.
	uint[] summands; Rational[] kinks; uint split=uint.max;
}
private struct PolynomialGrid{
	Rational[] cuts,points;
	Rational[][] cells;
}
private enum CoordinateGridMode { source, continuousChange, jumpChange }
private enum CoordinateChange { none, exp, sinh, arsinh, log, sqrt, reciprocal }
private enum JoinKind{ smooth,corner,jump }
private enum CornerSelection { dynamic, active, inactive }
private struct CoordinateJoin{
	JoinKind kind;
	Rational left,right,slope;
	uint event=uint.max;
	IntegralSolution* clipped;
	uint traversal=uint.max,missingDomain=uint.max;
	bool missingGuard;
	Rational witness;
	CornerSelection selection;
	Rational leftImage,rightImage;
	bool symbolicRoot;
}
private struct CoordinateGrid{
	PolynomialGrid grid;
	uint body,weight,predicate=uint.max,outerPredicate=uint.max,query=uint.max;
	Rational sampledValue,sampledWeight;
	CoordinateChange change;
	bool traceRange,flatMass,image;
	CoordinateJoin[] joins;
}
private Rational polynomialAt(Rational[] p,Rational x) @safe {
	auto result=Rational(0);
	foreach_reverse(c;p) result=c+x*result;
	return result;
}
private Rational[] derivativeCoefficients(Rational[] p) @safe {
	Rational[] d;
	foreach(i;1..p.length) d~=Rational(cast(long)i)*p[i];
	while(d.length&&d[$-1].zero) --d.length;
	return d;
}
private struct LimitSolution{ uint body,output; bool bottom; }
private struct AffineChart{
	uint map,inverse,jacobian,predicateDomain;
	uint powerDegree,derivativeNumerator=uint.max,derivativeDenominator=uint.max;
	bool squareProduct,openBand;
	uint borelPredicate=uint.max,punctureBody=uint.max,radiusCentre=uint.max;
	uint polynomialCheck=uint.max,bandLo=uint.max,bandHi=uint.max,cutoff=uint.max;
}
private struct CoverStep{ uint coefficient; bool centred,nested,lowerSwap,upperSwap,factorSwap; }
private struct FibreStep{ uint source,charge,regular; uint[] weights; }
private struct ScalarDomain{ Term input; Result result,value; uint variable; Sort sort; uint[] path; BoundOp mode; bool polynomial,rational; Term[] rationalConditions; }
private struct RecurrenceFact{ uint node,index; Term input; Result domain,value; }
private struct RecurrenceSolution{ uint source,target,base,delta; Law law,zero; bool left,cutoff; ubyte band; uint lower; bool affine,prefix; uint order,variable; Term[] seeds; RecurrenceFact[] facts; uint width; uint[] components; bool indexed,cfinite; CFiniteSequence[] cfModels; CFiniteExpression[] cfExpressions; uint cfRoot,cfSize; bool divide,inclusive,mixed; uint radix,seedFunction,tollFunction; DivideExpression[] divideExpressions; }
private enum CFiniteKind:ubyte{ zero,constant,index,geometric,add,mul,left,right,map,power,coordinate }
private struct CFiniteSequence{ CFiniteKind kind; Sort sort; uint source=uint.max,a,b,size,coordinate; Term value; Term[] matrix,initial,output; }
private enum CFiniteExprKind:ubyte{ force,previous,add,left,right }
private struct CFiniteExpression{ CFiniteExprKind kind; uint source,a,b,offset; Term coefficient,value; }
private struct DivideExpression{ CFiniteExprKind kind; uint source,a,b,offset; Term coefficient,value; }
private struct DomainLeaf{ uint node; Term value; Result domain; }
private struct DomainRank{ uint source,variable; Result result,lower,upper; DomainLeaf[] leaves; Result[] iterations; Sort sort; Term slope,bound,step; }
private struct SpectralFact{ Term input; Result domain,value; }
private struct SpectralSolution{ uint source,target,size; bool diagonal; Term[] matrix,vector; Term first,second,minus; SpectralFact[] parameters,checks; uint split; uint[4] blocks; bool repeated,nilpotent,cubeZero,zeroRoot,jordan; Term[] roots,components; }
struct BindingResult{
	BoundTerm input,output;
	bool exhausted;
	uint steps;
	private BindingStep[] proofs;
	private uint proof;
	private ScalarDomain[] domains;
	private RecurrenceSolution[] solutions;
	private DomainRank[] ranks;
	private SpectralSolution[] spectra;
	private SummationSolution[] sums;
	private IntegralSolution[] integrals;
	private FibreStep[][] fibres;
	private AffineChart[] affineCharts;
	private CoverStep[] covers;
	private LimitSolution[] limits;
	private CoordinateGrid[] coordinates;
}

final class Bindings{
	private Arena arena;
	private TypePool pool;
	private TypeId[] types;
	private Table!(uint,uint) typeIds;
	private struct Context{ uint type,parent,length; }
	private struct ContextKey{ uint type,parent; }
	private Context[] contexts;
	private Table!(ContextKey,uint) contextIds;
	private BoundNode[] nodes;
	private Table!(BoundNode,uint) nodeIds;
	private Table!(uint,uint) binderHints;
	private BinderHint[] hints;
	private bool dependent_,telescope_;
	private Table!(uint,string) dimensionParameters;
	void dimensionParameter(string name,uint index){ dimensionParameters.set(index,name); }
	@property bool telescope(){ return telescope_; }
	@property bool dependent(){ return dependent_; }
	this(Arena arena,TypePool pool=null){
		enforce(arena !is null,"scalar arena required");
		this.arena=arena; this.pool=pool is null?new TypePool:pool;
		contexts~=Context(uint.max,uint.max,0);
	}
	@property TypePool typePool(){ return pool; }
	Scope empty(){ return Scope(this,0); }
	private void check(Scope s)const{ enforce(s.owner is this&&s.index<contexts.length,"invalid or foreign context"); }
	private void check(BoundTerm t)const{ enforce(t.owner is this&&t.id<nodes.length,"invalid or foreign bound term"); }
	private uint typeId(TypeId t){
		auto v=pool.view(t); telescope_|=pool.dependent(t);
		if(v.dimension !is null&&v.dimension.names.length) dependent_=true;
		enforce(v.kind==TypeKind.distribution||v.kind==TypeKind.type_||v.kind==TypeKind.pi||v.kind==TypeKind.function_||v.kind==TypeKind.set||v.kind==TypeKind.vector||v.kind==TypeKind.tuple||v.kind<=TypeKind.complex,"unsupported binding type");
		foreach(f;v.fields) typeId(f);
		auto id=typeIds.get(t.id,uint.max);
		if(id!=uint.max) return id;
		enforce(types.length<uint.max,"binding type limit exceeded");
		id=cast(uint)types.length; types~=t; typeIds.set(t.id,id); return id;
	}
	TypeId scalarType(Sort s){
		final switch(s){
			case Sort.natural:return pool.primitive(TypeKind.natural);
			case Sort.integer:return pool.primitive(TypeKind.integer);
			case Sort.rational:return pool.primitive(TypeKind.rational);
			case Sort.real_:return pool.primitive(TypeKind.real_);
			case Sort.complex:return pool.primitive(TypeKind.complex);
			case Sort.boolean:return pool.primitive(TypeKind.boolean);
			case Sort.density,Sort.measure:throw new Exception("unsupported binding scalar type");
		}
	}
	Scope push(Scope s,TypeId t){
		check(s); auto ty=typeId(t),key=ContextKey(ty,s.index);
		auto id=contextIds.get(key,uint.max);
		if(id!=uint.max) return Scope(this,id);
		enforce(contexts[s.index].length<128,"binding depth limit exceeded");
		id=cast(uint)contexts.length; contexts~=Context(ty,s.index,contexts[s.index].length+1);
		contextIds.set(key,id); return Scope(this,id);
	}
	BoundNode node(BoundTerm t){ check(t); return nodes[t.id]; }
	BinderHint binderHint(BoundTerm t){ check(t); auto i=binderHints.get(t.id,uint.max); return i==uint.max?BinderHint.init:hints[i]; }
	BoundTerm hint(BoundTerm t,string name,string refinement=""){
		auto op=node(t).op; enforce(op==BoundOp.lambda||op==BoundOp.set||op==BoundOp.fixed||op==BoundOp.distributionRetry,"binder hint requires a binder");
		if(!binderHint(t).name.length){ binderHints.set(t.id,cast(uint)hints.length); hints~=BinderHint(name,refinement); }
		return t;
	}
	private BoundTerm inheritHint(BoundTerm from,BoundTerm to){
		auto h=binderHint(from); if(h.name.length) hint(to,h.name,h.refinement);
		return to;
	}
	TypeId type(BoundTerm t){ return types[node(t).type]; }
	Scope context(BoundTerm t){ return Scope(this,node(t).context); }
	BoundTerm at(uint id){ enforce(id<nodes.length,"invalid binding index"); return BoundTerm(this,id); }
	private BoundTerm intern(BoundNode n){
		auto id=nodeIds.get(n,uint.max); if(id!=uint.max) return at(id);
		enforce(nodes.length<1_000_000,"binding arena limit exceeded");
		id=cast(uint)nodes.length; nodes~=n; nodeIds.set(n,id); return at(id);
	}
	uint depth(Scope s){ check(s); return contexts[s.index].length; }
	BoundTerm global(Scope s,TypeId t,uint index){
		check(s); return intern(BoundNode(BoundOp.global,s.index,typeId(t),uint.max,uint.max,index));
	}
	BoundTerm typeValue(Scope s,TypeId t){
		check(s); return intern(BoundNode(BoundOp.typeValue,s.index,typeId(pool.primitive(TypeKind.type_)),uint.max,uint.max,typeId(t)));
	}
	TypeId typeDenoted(BoundTerm t){ enforce(node(t).op==BoundOp.typeValue,"a known type is required"); return types[node(t).data]; }
	BoundTerm typeEq(BoundTerm x,BoundTerm y){
		enforce(type(x)==pool.primitive(TypeKind.type_)&&type(y)==type(x)&&context(x)==context(y),"type equality requires types");
		return intern(BoundNode(BoundOp.typeEq,node(x).context,typeId(scalarType(Sort.boolean)),x.id,y.id));
	}
	BoundTerm equal(BoundTerm x,BoundTerm y){
		enforce(type(x)==type(y)&&context(x)==context(y),"equality requires matching types");
		bool hasDistribution(TypeId t){ auto v=pool.view(t); if(v.kind==TypeKind.distribution) return true; foreach(f;v.fields) if(hasDistribution(f)) return true; return false; }
		enforce(!hasDistribution(type(x)),"observational equality of distribution presentations is not supported yet");
		return intern(BoundNode(BoundOp.equal,node(x).context,typeId(scalarType(Sort.boolean)),x.id,y.id));
	}
	BoundTerm bottom(Scope s,TypeId t){ check(s); return intern(BoundNode(BoundOp.bottom,s.index,typeId(t))); }
	BoundTerm tuple(Scope ctx,BoundTerm[] elements,TypeId expected=TypeId.init){
		check(ctx); enforce(elements.length<=256,"aggregate literal size limit exceeded"); TypeId[] fields;
		foreach(e;elements){ enforce(context(e)==ctx,"tuple context mismatch"); fields~=type(e); }
		auto ty=expected==TypeId.init?pool.tuple(fields):expected,v=pool.view(ty);
		enforce(v.kind==TypeKind.unit||v.kind==TypeKind.tuple||v.kind==TypeKind.vector,"expected a tuple or vector type");
		if(v.kind==TypeKind.unit){ enforce(!elements.length,"unit has no elements"); return intern(BoundNode(BoundOp.unit,ctx.index,typeId(ty))); }
		if(v.kind==TypeKind.vector){
			enforce(v.dimension.constant&&v.length==elements.length,"vector literal dimension mismatch");
			foreach(f;fields) enforce(f==v.fields[0],"vector element type mismatch");
			if(!elements.length) return intern(BoundNode(BoundOp.vectorNil,ctx.index,typeId(ty)));
			auto tail=tuple(ctx,elements[1..$],pool.vector(v.fields[0],v.length-1));
			return intern(BoundNode(BoundOp.vectorCons,ctx.index,typeId(ty),elements[0].id,tail.id));
		}
		enforce(fields==v.fields,"tuple element type mismatch");
		auto tail=tuple(ctx,elements[1..$]);
		return intern(BoundNode(BoundOp.pair,ctx.index,typeId(ty),elements[0].id,tail.id));
	}
	BoundTerm get(BoundTerm value,BoundTerm index){
		auto n=node(value),v=pool.view(type(value));
		enforce(context(value)==context(index)&&type(index)==scalarType(Sort.natural),"index must have type ℕ");
		if(v.kind==TypeKind.tuple){
			auto i=node(index); enforce(i.op==BoundOp.scalar&&arena.isNumber(arena.at(i.data)),"heterogeneous tuple indices must be literals");
			auto number=arena.number(arena.at(i.data)); enforce(number.re.small&&number.re.integer>=0&&number.re.numerator<v.fields.length,"tuple index out of range");
			auto k=cast(uint)number.re.integer;
			if(!k) return intern(BoundNode(BoundOp.first,n.context,typeId(v.fields[0]),value.id));
			auto tail=intern(BoundNode(BoundOp.rest,n.context,typeId(pool.tuple(v.fields[1..$])),value.id));
			return get(tail,scalar(context(index),arena.natural_(k-1)));
		}
		enforce(v.kind==TypeKind.vector,"indexing requires a tuple or vector");
		return intern(BoundNode(BoundOp.get,n.context,typeId(v.fields[0]),value.id,index.id));
	}
	private Sort elementSort(TypeId t){
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(t==scalarType(s)) return s;
		throw new Exception("numeric scalar elements required");
	}
	BoundTerm tensor(TensorOp op,BoundTerm x,BoundTerm y){
		auto a=node(x),v=pool.view(type(x)),w=pool.view(type(y)); TypeId output;
		enforce(context(x)==context(y)&&v.kind==TypeKind.vector,"tensor operation requires vectors");
		if(op==TensorOp.add||op==TensorOp.mul){
			enforce(type(x)==type(y),"elementwise shape or type mismatch");
			elementSort(typeLeaf(type(x))); output=type(x);
		}else if(op==TensorOp.dot){
			enforce(type(x)==type(y),"inner product shape or type mismatch"); elementSort(v.fields[0]); output=v.fields[0];
		}else{
			auto row=pool.view(v.fields[0]); enforce(row.kind==TypeKind.vector,"matrix operation requires a matrix"); elementSort(row.fields[0]);
			if(op==TensorOp.power){
				enforce(v.dimension.key==row.dimension.key&&type(y)==scalarType(Sort.natural),"matrix powers require a square matrix and a natural exponent"); output=type(x);
			}else{
				enforce(w.kind==TypeKind.vector&&row.dimension.key==w.dimension.key,"matrix multiplication dimension mismatch");
				if(op==TensorOp.matvec){ enforce(row.fields[0]==w.fields[0],"matrix/vector element type mismatch"); output=pool.vector(row.fields[0],v.dimension); }
				else{ auto other=pool.view(w.fields[0]); enforce(other.kind==TypeKind.vector&&other.fields[0]==row.fields[0],"matrix element type mismatch"); output=pool.vector(pool.vector(row.fields[0],other.dimension),v.dimension); }
			}
		}
		return intern(BoundNode(BoundOp.tensor,a.context,typeId(output),x.id,y.id,cast(uint)op));
	}
	private TypeId typeLeaf(TypeId t){ auto v=pool.view(t); return v.kind==TypeKind.vector?typeLeaf(v.fields[0]):t; }
	private bool concreteType(TypeId t){
		auto v=pool.view(t); if(v.dimension !is null&&!v.dimension.constant) return false;
		foreach(f;v.fields) if(!concreteType(f)) return false; return true;
	}
	private bool literalData(BoundTerm t){
		auto n=node(t);
		if(n.op==BoundOp.unit||n.op==BoundOp.vectorNil) return true;
		if(n.op==BoundOp.scalar){
			bool total(Term t){
				auto q=arena.view(t); if(!q.arity) return true;
				return q.op==Op.builtin&&q.value>=Builtin.castNZ&&q.value<=Builtin.castRC&&total(arena.viewChild(t,0));
			}
			return total(arena.at(n.data));
		}
		return (n.op==BoundOp.pair||n.op==BoundOp.vectorCons)&&literalData(at(n.a))&&literalData(at(n.b));
	}
	private BoundTerm tensorEval(BoundTerm t){
		auto n=node(t); if(n.a==uint.max||!literalData(at(n.a))) return BoundTerm.init;
		BoundTerm entry(BoundTerm x,ulong i){ while(i--){ x=at(node(x).b); } return at(node(x).a); }
		if(n.op==BoundOp.first) return at(nodes[n.a].a);
		if(n.op==BoundOp.rest) return at(nodes[n.a].b);
		if(n.op==BoundOp.get&&nodes[n.b].op==BoundOp.scalar&&arena.isNumber(arena.at(nodes[n.b].data))){
			auto i=arena.number(arena.at(nodes[n.b].data)).re,v=pool.view(type(at(n.a)));
			if(!i.small||i.integer>=v.length) return bottom(context(t),type(t));
			return entry(at(n.a),cast(ulong)i.integer);
		}
		if(n.op!=BoundOp.tensor||!literalData(at(n.b))) return BoundTerm.init;
		auto x=at(n.a),y=at(n.b),v=pool.view(type(x)),op=cast(TensorOp)n.data;
		if(!v.dimension.constant||v.length>32) return BoundTerm.init;
		auto ctx=context(t),leaf=typeLeaf(type(x));
		BoundTerm scalarOp(TensorOp op,BoundTerm a,BoundTerm b){
			if(pool.view(type(a)).kind==TypeKind.vector) return tensor(op,a,b);
			auto prototype=scalarOperator(type(a),op);
			return primitive(prototype,[a,b]);
		}
		BoundTerm dot(BoundTerm[] a,BoundTerm[] b,bool dual){
			auto s=scalar(ctx,arena.number(Number(0),elementSort(leaf)));
			foreach_reverse(i;0..a.length){
				auto term=a[i];
				if(dual&&leaf==scalarType(Sort.complex)) term=primitive(arena.conj(arena.variable(Sort.complex,0)),[term]);
				s=scalarOp(TensorOp.add,scalarOp(TensorOp.mul,term,b[i]),s);
			}
			return s;
		}
		BoundTerm[] elements;
		if(op==TensorOp.add||op==TensorOp.mul){
			foreach(i;0..v.length) elements~=scalarOp(op,entry(x,i),entry(y,i)); return tuple(ctx,elements,type(t));
		}
		if(op==TensorOp.dot){
			BoundTerm[] a,b; foreach(i;0..v.length){ a~=entry(x,i); b~=entry(y,i); } return dot(a,b,true);
		}
		auto row=pool.view(v.fields[0]); if(!row.dimension.constant||row.length>32) return BoundTerm.init;
		if(op==TensorOp.power){
			if(nodes[n.b].op!=BoundOp.scalar||!arena.isNumber(arena.at(nodes[n.b].data))) return BoundTerm.init;
			auto exponent=arena.number(arena.at(nodes[n.b].data)).re; if(!exponent.small||exponent.integer>16) return BoundTerm.init;
			if(exponent.integer) return tensor(TensorOp.matmul,x,tensor(TensorOp.power,x,scalar(ctx,arena.natural_(cast(ulong)exponent.integer-1))));
			foreach(i;0..v.length){
				BoundTerm[] cells; foreach(j;0..v.length) cells~=scalar(ctx,arena.number(Number(i==j?1:0),elementSort(leaf)));
				elements~=tuple(ctx,cells,v.fields[0]);
			}
			return tuple(ctx,elements,type(x));
		}
		auto w=pool.view(type(y));
		auto columns=op==TensorOp.matmul?pool.view(w.fields[0]).length:1;
		if(columns>32) return BoundTerm.init;
		foreach(i;0..v.length){
			BoundTerm[] cells;
			foreach(j;0..columns){
				BoundTerm[] a,b;
				foreach(k;0..row.length){ a~=entry(entry(x,i),k); b~=op==TensorOp.matmul?entry(entry(y,k),j):entry(y,k); }
				cells~=dot(a,b,false);
			}
			elements~=op==TensorOp.matmul?tuple(ctx,cells,pool.view(type(t)).fields[0]):cells[0];
		}
		return tuple(ctx,elements,type(t));
	}
	private bool primitiveOp(uint id,Op op){
		auto n=nodes[id];
		return n.op==BoundOp.primitive&&arena.view(arena.at(n.data)).op==op;
	}
	private struct JumpRays{ uint x,leftTest,rightTest; Term a,b; bool swap; }
	private bool jumpRays(uint fn,out JumpRays outRays){
		if(nodes[fn].op!=BoundOp.lambda||!primitiveOp(nodes[fn].a,Op.add)) return false;
		auto sum=nodes[nodes[fn].a];
		foreach(swap;[false,true]){
			auto left=nodes[swap?sum.b:sum.a],right=nodes[swap?sum.a:sum.b];
			if(!primitiveOp(swap?sum.b:sum.a,Op.mask)||!primitiveOp(swap?sum.a:sum.b,Op.mask)) continue;
			if(!primitiveOp(left.a,Op.lt)||!primitiveOp(right.a,Op.lt)||!primitiveOp(left.b,Op.pow)) continue;
			auto power=nodes[left.b],lt=nodes[left.a],gt=nodes[right.a],x=right.b;
			if(arena.view(arena.at(power.data)).value!=2||power.a!=x||lt.a!=x||gt.b!=x||
				nodes[x].op!=BoundOp.variable||nodes[x].data!=0) continue;
			if(nodes[lt.b].op!=BoundOp.scalar||nodes[gt.a].op!=BoundOp.scalar) continue;
			auto a=arena.at(nodes[lt.b].data),b=arena.at(nodes[gt.a].data);
			if(!arena.isNumber(a)||!arena.isNumber(b)||arena.number(a).re>=Rational(0)||arena.number(b).re<=Rational(0)) continue;
			outRays=JumpRays(x,left.a,right.a,a,b,swap);
			return true;
		}
		return false;
	}
	private bool densityBodies(uint id,ref uint[] bodies){
		auto d=nodes[id];
		if(d.op==BoundOp.distributionLebesgue) return true;
		if(d.op!=BoundOp.distributionWeight||nodes[d.a].op!=BoundOp.lambda||!densityBodies(d.b,bodies)) return false;
		bodies~=nodes[d.a].a; return true;
	}
	private BoundTerm retainedWeight(uint[] bodies,BoundTerm query){
		if(!bodies.length) return sequence(query,scalar(context(query),arena.real_(1)));
		auto weight=at(bodies[0]),mul=scalarOperator(scalarType(Sort.real_),TensorOp.mul);
		foreach(body;bodies[1..$]) weight=primitive(mul,[weight,at(body)]);
		return apply(lambda(weight),query);
	}
	private BoundTerm awayFromAtom(uint location,BoundTerm query){
		auto zero=arena.real_(0);
		auto neg=primitive(arena.mul(zero,zero,true),[scalar(context(query),arena.real_(-1)),at(location)]);
		auto diff=primitive(arena.add(zero,zero,true),[query,neg]);
		return primitive(arena.nonzero(zero),[diff]);
	}
	private BoundTerm indexBuiltin(Builtin op,BoundTerm t){
		return primitive(arena.call(op,[arena.number(Number(0),builtinInfo(op).args[0])]),[t]);
	}
	private BoundTerm realIndex(BoundTerm i){
		if(type(i)==scalarType(Sort.natural)) i=indexBuiltin(Builtin.castNZ,i);
		return indexBuiltin(Builtin.castQR,indexBuiltin(Builtin.castZQ,i));
	}
	// A real equality selects at most one integer or natural index. Test the
	// recovered point before observing the weight, since the weight may be partial.
	private BoundTerm selectRealIndex(BoundTerm function_,out bool swap){
		auto root=node(function_).a;
		if(!primitiveOp(root,Op.mask)) return BoundTerm.init;
		auto row=nodes[root],pred=nodes[row.a];
		if(!primitiveOp(row.a,Op.not_)||!primitiveOp(pred.a,Op.nonzero)) return BoundTerm.init;
		auto difference=nodes[pred.a].a;
		if(!primitiveOp(difference,Op.add)) return BoundTerm.init;
		auto pair=nodes[difference];
		if(!primitiveOp(pair.b,Op.mul)) return BoundTerm.init;
		auto neg=nodes[pair.b],sign=nodes[neg.a];
		if(sign.op!=BoundOp.scalar||arena.at(sign.data)!=arena.real_(-1)) return BoundTerm.init;
		bool natural=naturalIndex(function_.id);
		auto index=realIndex(variable(context(at(root)),0)).id;
		swap=pair.a==index;
		if(!swap&&neg.b!=index) return BoundTerm.init;
		auto bound=at(swap?neg.b:pair.a);
		if(depends(bound,0)) return BoundTerm.init;
		auto query=dropIndex(bound),candidate=indexBuiltin(natural?Builtin.floorN:Builtin.floorR,query);
		auto present=primitive(arena.not_(arena.boolean(false)),[awayFromAtom(realIndex(candidate).id,query)]);
		auto weight=apply(inheritHint(function_,lambda(at(row.b))),candidate);
		return primitive(arena.at(row.data),[present,weight]);
	}
	// Compile the signed singleton charge and regular weight together. Keeping
	// one witness per source node also shares reused summands in the export.
	private BoundTerm extractFibre(uint source,BoundTerm query,ref FibreStep[] steps){
		auto ctx=context(query),zero=scalar(ctx,arena.real_(0)),one=scalar(ctx,arena.real_(1));
		auto add=scalarOperator(type(zero),TensorOp.add),mul=scalarOperator(type(zero),TensorOp.mul);
		auto neg=arena.not_(arena.boolean(false));
		Table!(uint,uint) indices;
		uint visit(uint id){
			auto index=indices.get(id,uint.max);
			if(index!=uint.max) return index;
			auto d=nodes[id];
			BoundTerm charge,regular;
			uint[] weights; Term offset; bool swap;
			if(d.op==BoundOp.distributionAdd){
				auto left=visit(d.a); if(left==uint.max) return uint.max;
				auto right=visit(d.b); if(right==uint.max) return uint.max;
				charge=primitive(add,[at(steps[left].charge),at(steps[right].charge)]);
				regular=primitive(add,[at(steps[left].regular),at(steps[right].regular)]);
			}else if(d.op==BoundOp.distributionScale){
				auto child=visit(d.b); if(child==uint.max) return uint.max;
				charge=primitive(mul,[at(d.a),at(steps[child].charge)]);
				regular=primitive(mul,[at(d.a),at(steps[child].regular)]);
			}else if(d.op==BoundOp.bottom||(d.op==BoundOp.distributionDirac&&nodes[d.a].op==BoundOp.bottom)){
				charge=bottom(ctx,type(zero)); regular=zero;
			}else if(d.op==BoundOp.distributionDirac||
					d.op==BoundOp.distributionWeight&&nodes[d.b].op==BoundOp.distributionDirac){
				auto location=d.op==BoundOp.distributionDirac?d.a:nodes[d.b].a;
				auto atPoint=primitive(neg,[awayFromAtom(location,query)]);
				charge=primitive(arena.mask(arena.boolean(true),arena.real_(1)),[atPoint,one]);
				regular=zero;
				if(d.op==BoundOp.distributionWeight){
					auto coefficient=apply(at(d.a),at(location));
					charge=primitive(mul,[coefficient,charge]);
					regular=primitive(mul,[coefficient,regular]);
				}
			}else if(cornerChart(id,offset,swap)){
				auto location=offset==Term.init?zero:scalar(ctx,offset);
				charge=sequence(query,zero);
				regular=guard(awayFromAtom(location.id,query),zero);
			}else if(d.op==BoundOp.distributionZero||densityBodies(id,weights)){
				charge=sequence(query,zero);
				regular=d.op==BoundOp.distributionZero?zero:retainedWeight(weights,query);
			}else return uint.max;
			index=cast(uint)steps.length;
			steps~=FibreStep(id,charge.id,regular.id,weights); indices.set(id,index);
			return index;
		}
		auto root=visit(source); if(root==uint.max) return BoundTerm.init;
		auto nonzero=primitive(arena.nonzero(arena.real_(0)),[at(steps[root].charge)]);
		return guard(primitive(neg,[nonzero]),at(steps[root].regular));
	}
	private bool depends(BoundTerm t,uint index){
		auto n=node(t); if(n.op==BoundOp.variable) return n.data==index;
		if(n.op==BoundOp.lambda||n.op==BoundOp.set||n.op==BoundOp.fixed) ++index;
		return n.a!=uint.max&&depends(at(n.a),index)||n.b!=uint.max&&depends(at(n.b),index)||n.c!=uint.max&&depends(at(n.c),index);
	}
	// Use the same derivation for source recognition and for proof export.
	// An independent subterm is a constant partial value in this binder.
	private string borelProof(uint root,SourceCertificates c=null){
		Table!(uint,string) visited;
		string visit(uint id){
			auto known=visited.get(id,""); if(known.length) return known;
			auto t=at(id),n=node(t),pred=type(t)==scalarType(Sort.boolean);
			if(!pred&&type(t)!=scalarType(Sort.real_)) return "";
			auto kind=pred?"Distribution.BorelPred":"Distribution.BorelReal";
			string lemma,args;
			if(!depends(t,0)){
				lemma="const";
				if(c) args=" "~c.atPoint(id,Rational(0));
			}else if(n.op==BoundOp.variable){
				lemma="var";
			}else if(n.op==BoundOp.primitive){
				auto op=arena.view(arena.at(n.data));
				switch(op.op){
					case Op.add: lemma="add"; break;
					case Op.mul: lemma="mul"; break;
					case Op.abs: lemma="abs"; break;
					case Op.mask: lemma="mask"; break;
					case Op.inv: lemma="inv"; break;
					case Op.pow: lemma="pow"; if(c) args=" "~to!string(op.value); break;
					case Op.lt: lemma="lt"; break;
					case Op.le: lemma="le"; break;
					case Op.nonzero: lemma="nonzero"; break;
					case Op.not_: lemma="not"; break;
					case Op.and_: lemma="and"; break;
					case Op.or_: lemma="or"; break;
					default:return "";
				}
				foreach(child;[n.a,n.b]) if(child!=uint.max){
					auto proof=visit(child); if(!proof.length) return "";
					if(c) args~=" "~proof;
				}
			}else return "";
			auto result=c?c.save(kind~" "~c.functionAt(id),kind~"."~lemma~args):lemma;
			visited.set(id,result);
			return result;
		}
		return visit(root);
	}
	// Return the positive scale and the expression shape needed by the proof.
	private Term sqrtRadiusScale(uint functionId,out string form){
		auto f=nodes[functionId];
		if(f.op!=BoundOp.lambda) return Term.init;
		bool root(uint id){
			auto n=nodes[id];
			if(n.op!=BoundOp.primitive||n.a==uint.max) return false;
			auto op=arena.view(arena.at(n.data));
			return op.op==Op.builtin&&op.value==Builtin.sqrtR&&nodes[n.a].op==BoundOp.variable&&nodes[n.a].data==0;
		}
		if(root(f.a)){form="one"; return arena.real_(1);}
		auto n=nodes[f.a];
		if(n.op==BoundOp.guard&&root(n.b)){
			auto condition=nodes[n.a];
			if(condition.op==BoundOp.primitive&&arena.view(arena.at(condition.data)).op==Op.le&&
				nodes[condition.a].op==BoundOp.scalar&&arena.at(nodes[condition.a].data)==arena.real_(0)&&
				nodes[condition.b].op==BoundOp.variable&&nodes[condition.b].data==0){
				form="guardedOne"; return arena.real_(1);
			}
		}
		if(n.op!=BoundOp.primitive||arena.view(arena.at(n.data)).op!=Op.mul) return Term.init;
		bool right=root(n.a);
		if(!right&&!root(n.b)) return Term.init;
		auto coeff=nodes[right?n.b:n.a];
		if(coeff.op!=BoundOp.scalar) return Term.init;
		auto value=arena.at(coeff.data);
		if(!arena.isNumber(value)||arena.number(value).re<=Rational(0)) return Term.init;
		form=right?"right":"left"; return value;
	}
	bool printableSquareCover(BoundNode chart){
		string form;
		return nodes[chart.a].op==BoundOp.scalar&&arena.isNumber(arena.at(nodes[chart.a].data))&&
			sqrtRadiusScale(chart.b,form)!=Term.init;
	}
	// sqrt already has exactly the nonnegative domain. Its explicit domain
	// guard and the unguarded spelling denote the same partial radius.
	BoundTerm printedRadiusBody(BoundTerm function_){
		auto f=node(function_);
		enforce(f.op==BoundOp.lambda,"expected a radius lambda");
		auto body=at(f.a);
		if(node(body).op==BoundOp.guard){
			string form;
			sqrtRadiusScale(function_.id,form);
			if(form=="guardedOne") return at(node(body).b);
		}
		return body;
	}
	// A real Iverson bracket is sometimes normalized to three exact casts of
	// a natural mask. In both forms the threshold must be independent of y.
	private BoundTerm sublevelBound(uint functionId,out bool casts,out bool strict){
		auto f=nodes[functionId];
		if(f.op!=BoundOp.lambda) return BoundTerm.init;
		auto mask=nodes[f.a];
		if(mask.op==BoundOp.primitive&&arena.view(arena.at(mask.data)).op==Op.builtin){
			foreach(op;[Builtin.castQR,Builtin.castZQ,Builtin.castNZ]){
				if(mask.op!=BoundOp.primitive) return BoundTerm.init;
				auto v=arena.view(arena.at(mask.data));
				if(v.op!=Op.builtin||v.value!=op) return BoundTerm.init;
				mask=nodes[mask.a];
			}
			casts=true;
		}
		if(mask.op!=BoundOp.primitive||arena.view(arena.at(mask.data)).op!=Op.mask) return BoundTerm.init;
		auto one=nodes[mask.b],test=nodes[mask.a];
		if(one.op!=BoundOp.scalar||arena.at(one.data)!=arena.number(Number(1),casts?Sort.natural:Sort.real_)) return BoundTerm.init;
		strict=primitiveOp(mask.a,Op.lt);
		if((!strict&&!primitiveOp(mask.a,Op.le))||
			nodes[test.a].op!=BoundOp.variable||nodes[test.a].data!=0||depends(at(test.b),0)) return BoundTerm.init;
		return at(test.b);
	}
	// A real weighted Dirac row can place the coefficient on the row itself
	// or on the Lebesgue source of a bind. A plain row has no weight body.
	private bool realAtomRow(BoundTerm t,out uint weight,out uint point){
		weight=uint.max;
		auto n=node(t);
		if(n.op!=BoundOp.distributionBind&&n.op!=BoundOp.distributionIntegral||
			type(t)!=pool.distribution(scalarType(Sort.real_))) return false;
		bool integral=n.op==BoundOp.distributionIntegral;
		auto fn=nodes[integral?n.a:n.b];
		if(fn.op!=BoundOp.lambda) return false;
		auto row=nodes[fn.a];
		if(integral||nodes[n.a].op==BoundOp.distributionLebesgue){
			if(row.op==BoundOp.distributionScale){ weight=row.a; row=nodes[row.b]; }
			if(row.op!=BoundOp.distributionDirac) return false;
			point=row.a;
		}else{
			auto source=nodes[n.a];
			if(row.op!=BoundOp.distributionDirac||source.op!=BoundOp.distributionWeight||
				nodes[source.b].op!=BoundOp.distributionLebesgue||nodes[source.a].op!=BoundOp.lambda) return false;
			weight=nodes[source.a].a; point=row.a;
		}
		return true;
	}
	private bool strictDistribution(BoundOp op){
		switch(op){
			case BoundOp.distributionDirac,BoundOp.distributionAdd,BoundOp.distributionScale,BoundOp.distributionWeight,
				BoundOp.distributionIntegral,BoundOp.distributionSum,BoundOp.distributionMass,BoundOp.distributionDensityAt,BoundOp.distributionBind:return true;
			default:return false;
		}
	}
	private void checkProgram(BoundTerm t){
		if(!depends(t,1)) return;
		auto n=node(t);
		if(strictDistribution(n.op)||n.op==BoundOp.conditional||n.op==BoundOp.primitive||n.op==BoundOp.guard||n.op==BoundOp.sequence||
			n.op==BoundOp.vectorCons||n.op==BoundOp.pair||n.op==BoundOp.first||n.op==BoundOp.rest||n.op==BoundOp.get){
			checkProgram(at(n.a)); if(n.b!=uint.max) checkProgram(at(n.b)); if(n.c!=uint.max) checkProgram(at(n.c)); return;
		}
		if(n.op==BoundOp.apply){
			auto f=nodes[n.a];
			enforce(f.op==BoundOp.variable&&f.data==1,"unsupported higher-order recursion");
			checkProgram(at(n.b)); return;
		}
		throw new Exception("recursive definitions cannot inspect definedness or use higher-order recursion yet");
	}
	/// A source-level continuity capability, relative to one recursion variable.
	enum Continuity:ubyte { constant, continuous, unsupported }
	Continuity continuity(BoundTerm t,uint recursiveIndex=1){
		if(!depends(t,recursiveIndex)) return Continuity.constant;
		auto n=node(t);
		if(n.op==BoundOp.apply){
			auto f=nodes[n.a];
			if(f.op!=BoundOp.variable||f.data!=recursiveIndex) return Continuity.unsupported;
			return continuity(at(n.b),recursiveIndex)==Continuity.unsupported?Continuity.unsupported:Continuity.continuous;
		}
		if(!strictDistribution(n.op)&&n.op!=BoundOp.conditional&&n.op!=BoundOp.primitive&&n.op!=BoundOp.guard&&n.op!=BoundOp.sequence&&
			n.op!=BoundOp.vectorCons&&n.op!=BoundOp.pair&&n.op!=BoundOp.first&&n.op!=BoundOp.rest&&n.op!=BoundOp.get)
			return Continuity.unsupported;
		foreach(id;[n.a,n.b,n.c]) if(id!=uint.max&&continuity(at(id),recursiveIndex)==Continuity.unsupported) return Continuity.unsupported;
		return Continuity.continuous;
	}
	BoundTerm distribution(Scope ctx,BoundOp op,BoundTerm[] args=[],TypeId element=TypeId.init){
		check(ctx); foreach(a;args) enforce(context(a)==ctx,"distribution context mismatch");
		auto realType=scalarType(Sort.real_); TypeId output;
		TypeId distributed(BoundTerm d){ auto v=pool.view(type(d)); enforce(v.kind==TypeKind.distribution,"distribution expected"); return v.fields[0]; }
		switch(op){
			case BoundOp.distributionZero:enforce(!args.length&&element!=TypeId.init,"zero requires an element type"); output=pool.distribution(element); break;
			case BoundOp.distributionLebesgue:enforce(!args.length,"Lebesgue takes no arguments"); output=pool.distribution(realType); break;
			case BoundOp.distributionDirac:enforce(args.length==1,"Dirac takes one value"); output=pool.distribution(type(args[0])); break;
			case BoundOp.distributionAdd:enforce(args.length==2,"distribution sum takes two arguments"); distributed(args[0]); enforce(type(args[0])==type(args[1]),"distribution types differ"); output=type(args[0]); break;
			case BoundOp.distributionFixed:{
				enforce(args.length==1,"distribution fixed point needs one body");
				auto f=pool.view(type(args[0]));
				enforce(f.kind==TypeKind.function_&&f.fields[0]==f.fields[1]&&pool.view(f.fields[0]).kind==TypeKind.distribution,
					"distribution fixed point needs a distribution endofunction");
				output=f.fields[0]; break;
			}
			case BoundOp.distributionRetry:
			case BoundOp.distributionScale:enforce(args.length==2&&type(args[0])==realType,"distribution scale requires a real weight"); distributed(args[1]); output=type(args[1]); break;
			case BoundOp.distributionWeight:enforce(args.length==2,"weight takes a function and a distribution"); element=distributed(args[1]); enforce(type(args[0])==pool.function_(element,realType),"weight function has the wrong type"); output=type(args[1]); break;
			case BoundOp.distributionIntegral:{
				enforce(args.length==1,"integralD takes a real-indexed distribution function"); auto v=pool.view(type(args[0]));
				enforce(v.kind==TypeKind.function_&&v.fields[0]==realType&&pool.view(v.fields[1]).kind==TypeKind.distribution,"integralD requires Real -> Distribution(A)"); output=v.fields[1]; break;
			}
			case BoundOp.distributionSum:{
				enforce(args.length==1,"sumD takes a natural- or integer-indexed distribution function"); auto v=pool.view(type(args[0]));
				enforce(v.kind==TypeKind.function_&&(v.fields[0]==scalarType(Sort.integer)||v.fields[0]==scalarType(Sort.natural))&&
					pool.view(v.fields[1]).kind==TypeKind.distribution,"sumD requires Nat -> Distribution(A) or Int -> Distribution(A)"); output=v.fields[1]; break;
			}
			case BoundOp.distributionBind:{
				enforce(args.length==2,"bindD takes a distribution and a kernel"); element=distributed(args[0]); auto v=pool.view(type(args[1]));
				enforce(v.kind==TypeKind.function_&&v.fields[0]==element&&pool.view(v.fields[1]).kind==TypeKind.distribution,"bindD requires A -> Distribution(B)"); output=v.fields[1]; break;
			}
			case BoundOp.distributionMass:enforce(args.length==1,"mass takes one distribution"); distributed(args[0]); output=realType; break;
			case BoundOp.distributionInverseCover,BoundOp.distributionInversePart:{
				bool part=op==BoundOp.distributionInversePart;
				enforce(args.length==(part?2:1),"expected an inverse coordinate vector");
				if(part) enforce(type(args[0])==pool.function_(realType,scalarType(Sort.boolean)),"inversePartD requires a real source predicate");
				auto v=pool.view(type(args[$-1]));
				enforce(v.kind==TypeKind.vector&&v.fields[0]==pool.function_(realType,realType),"expected a vector of real coordinate functions");
				output=pool.distribution(realType); break;
			}
			case BoundOp.distributionRadiusImage:
				enforce(args.length==2&&type(args[0])==realType&&type(args[1])==pool.function_(realType,realType),
					"radiusImageD takes a real centre and a real radius function");
				output=pool.distribution(realType); break;
			case BoundOp.distributionPushforwardOn:{
				enforce(args.length==2&&type(args[0])==pool.function_(realType,scalarType(Sort.boolean)),
					"pushforwardOnD requires a real source predicate");
				auto map=pool.view(type(args[1]));
				enforce(map.kind==TypeKind.function_&&map.fields[0]==realType,"pushforwardOnD requires a map from the reals");
				output=pool.distribution(map.fields[1]); break;
			}
			case BoundOp.distributionMaskedGraph:
				enforce(args.length==2&&type(args[0])==pool.function_(realType,scalarType(Sort.boolean))&&
					type(args[1])==pool.function_(realType,realType),"maskedGraphD requires a real predicate and real map");
				output=pool.function_(realType,pool.distribution(realType)); break;
			case BoundOp.distributionGraphFibre,BoundOp.distributionGraphMass:
				enforce(args.length==2&&type(args[0])==pool.function_(realType,realType)&&type(args[1])==realType,"graph disintegration requires a real map and query");
				output=op==BoundOp.distributionGraphMass?realType:pool.distribution(realType); break;
			case BoundOp.distributionDensityAt:enforce(args.length==2&&distributed(args[0])==realType&&type(args[1])==realType,"density extraction requires a real distribution and point"); output=realType; break;
			default:throw new Exception("not a distribution operation");
		}
		return intern(BoundNode(op,ctx.index,typeId(output),args.length?args[0].id:uint.max,args.length>1?args[1].id:uint.max));
	}
	private enum Reemit { none, self, plusZero, zeroPlus }
	private Reemit reemitKernel(uint id){
		auto fn=nodes[id];
		if(fn.op!=BoundOp.lambda||nodes[fn.a].op!=BoundOp.distributionDirac) return Reemit.none;
		auto out_=nodes[nodes[fn.a].a];
		bool self(uint i){return nodes[i].op==BoundOp.variable&&nodes[i].data==0;}
		if(out_.op==BoundOp.variable&&out_.data==0) return Reemit.self;
		if(out_.op!=BoundOp.primitive) return Reemit.none;
		auto op=arena.view(arena.at(out_.data));
		if(op.op!=Op.builtin||op.value!=Builtin.addN) return Reemit.none;
		bool zero(uint i){return nodes[i].op==BoundOp.scalar&&arena.at(nodes[i].data)==arena.natural_(0);}
		if(self(out_.a)&&zero(out_.b)) return Reemit.plusZero;
		if(zero(out_.a)&&self(out_.b)) return Reemit.zeroPlus;
		return Reemit.none;
	}
	private enum AffineOp { constant, self, add, scale, weight, reemit }
	private struct AffineForm { AffineOp op; Rational ratio; bool empty; }
	private struct RetryParts {
		uint seed=uint.max,tail;
		Rational ratio;
		bool swapped,weighted,direct;
		AffineForm[uint] forms;
	}
	private bool nonnegativeReal(uint id,out Rational r){
		auto t=nodes[id];
		if(t.op!=BoundOp.scalar) return false;
		auto c=arena.at(t.data);
		if(arena.sort(c)!=Sort.real_||!arena.isNumber(c)) return false;
		r=arena.number(c).re; return r>=Rational(0);
	}
	private bool atomicSeed(uint id){
		auto n=nodes[id]; Rational r;
		switch(n.op){
			case BoundOp.bottom,BoundOp.distributionZero,BoundOp.distributionDirac:return true;
			case BoundOp.distributionScale:return nonnegativeReal(n.a,r)&&atomicSeed(n.b);
			case BoundOp.distributionAdd:return atomicSeed(n.a)&&atomicSeed(n.b);
			default:return false;
		}
	}
	private bool retryFactor(BoundNode n,out uint factor,out Rational coefficient){
		if(n.op!=BoundOp.distributionScale&&n.op!=BoundOp.distributionWeight) return false;
		factor=n.a;
		if(n.op==BoundOp.distributionWeight){
			if(nodes[factor].op!=BoundOp.lambda) return false;
			factor=nodes[factor].a;
		}
		return nonnegativeReal(factor,coefficient);
	}
	/// Every recursive leaf is the distinguished input. Keep a zero coefficient
	/// as a visit, and only combine the weights of branches certified here.
	private bool tailRatio(uint id,out Rational q){
		auto n=nodes[id];
		if(n.op==BoundOp.variable&&n.data==0){ q=Rational(1); return true; }
		Rational a,b;
		if(n.op==BoundOp.distributionAdd){
			if(!tailRatio(n.a,a)||!tailRatio(n.b,b)) return false;
			q=a+b; return true;
		}
		uint factor;
		if(!retryFactor(n,factor,a)||!tailRatio(n.b,b)) return false;
		q=a*b; return true;
	}
	/// The constant and recursive parts of a finite affine expression can
	/// be interleaved. The coefficient is checked at every constructor.
	private bool affineForm(uint id,ref AffineForm[uint] forms){
		if(id in forms) return true;
		auto n=nodes[id]; AffineForm form;
		switch(n.op){
			case BoundOp.bottom,BoundOp.distributionZero:form=AffineForm(AffineOp.constant,Rational(0),n.op==BoundOp.distributionZero); break;
			case BoundOp.distributionDirac:
				if(depends(at(n.a),0)) return false;
				form=AffineForm(AffineOp.constant,Rational(0)); break;
			case BoundOp.variable:
				if(n.data!=0) return false;
				form=AffineForm(AffineOp.self,Rational(1),true); break;
			case BoundOp.distributionBind:
				if(reemitKernel(n.b)==Reemit.none||!affineForm(n.a,forms)) return false;
				form=AffineForm(AffineOp.reemit,forms[n.a].ratio,forms[n.a].empty); break;
			case BoundOp.distributionAdd:
				if(!affineForm(n.a,forms)||!affineForm(n.b,forms)) return false;
				form=AffineForm(AffineOp.add,forms[n.a].ratio+forms[n.b].ratio,forms[n.a].empty&&forms[n.b].empty); break;
			case BoundOp.distributionScale,BoundOp.distributionWeight:{
				uint factor; Rational r;
				if(!retryFactor(n,factor,r)||!affineForm(n.b,forms)) return false;
				form=AffineForm(n.op==BoundOp.distributionScale?AffineOp.scale:AffineOp.weight,r*forms[n.b].ratio,forms[n.b].empty);
				break;
			}
			default:return false;
		}
		forms[id]=form; return true;
	}
	private BoundTerm affineSeed(uint id,Scope ctx,BoundTerm[] env,ref AffineForm[uint] forms,ref BoundTerm[uint] memo){
		if(auto hit=id in memo) return *hit;
		auto n=nodes[id]; BoundTerm seed;
		if(forms[id].empty) return memo[id]=distribution(ctx,BoundOp.distributionZero,[],pool.view(type(at(id))).fields[0]);
		final switch(forms[id].op){
			case AffineOp.constant:seed=substitute(at(id),ctx,env); break;
			case AffineOp.self:assert(false,"the recursive variable has no emission");
			case AffineOp.reemit:seed=affineSeed(n.a,ctx,env,forms,memo); break;
			case AffineOp.add:
				if(forms[n.a].empty) seed=affineSeed(n.b,ctx,env,forms,memo);
				else if(forms[n.b].empty) seed=affineSeed(n.a,ctx,env,forms,memo);
				else seed=distribution(ctx,n.op,[affineSeed(n.a,ctx,env,forms,memo),affineSeed(n.b,ctx,env,forms,memo)]);
				break;
			case AffineOp.scale,AffineOp.weight:{
				uint factor; Rational coefficient; enforce(retryFactor(n,factor,coefficient));
				seed=distribution(ctx,BoundOp.distributionScale,[scalar(ctx,arena.at(nodes[factor].data)),affineSeed(n.b,ctx,env,forms,memo)]);
				break;
			}
		}
		return memo[id]=seed;
	}
	private bool retrySource(uint id,out RetryParts parts){
		auto body=nodes[id];
		if(body.op==BoundOp.distributionAdd) foreach(swap;[false,true]){
			auto seed=swap?body.b:body.a,tail=swap?body.a:body.b;
			Rational q;
			if(depends(at(seed),0)||!atomicSeed(seed)||!tailRatio(tail,q)) continue;
			auto n=nodes[tail];
			bool weighted=n.op==BoundOp.distributionWeight;
			bool direct=(weighted||n.op==BoundOp.distributionScale)&&nodes[n.b].op==BoundOp.variable;
			parts=RetryParts(seed,tail,q,swap,weighted,direct); return true;
		}
		Rational q;
		if(tailRatio(id,q)){ parts=RetryParts(uint.max,id,q); return true; }
		AffineForm[uint] forms;
		if(!affineForm(id,forms)) return false;
		parts=RetryParts(uint.max,id,forms[id].ratio,false,false,false,forms); return true;
	}
	private enum Involution { flip, negLeft, negRight }
	private struct InvolutiveLoop { uint seed,ratio,kernel,unit=uint.max; Involution map; }
	private bool involutiveLoop(uint id,out InvolutiveLoop loop){
		auto body=nodes[id]; Rational ratio;
		if(body.op!=BoundOp.distributionAdd||depends(at(body.a),0)||!atomicSeed(body.a)) return false;
		auto transport=nodes[body.b]; uint factor=uint.max;
		if(transport.op==BoundOp.distributionScale){
			factor=transport.a;
			if(!nonnegativeReal(factor,ratio)) return false;
			transport=nodes[transport.b];
		}
		if(transport.op!=BoundOp.distributionBind||nodes[transport.a].op!=BoundOp.variable||nodes[transport.a].data!=0) return false;
		auto fn=nodes[transport.b];
		if(fn.op!=BoundOp.lambda||nodes[fn.a].op!=BoundOp.distributionDirac) return false;
		auto term=nodes[nodes[fn.a].a];
		if(term.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(term.data));
		bool self(uint i){return nodes[i].op==BoundOp.variable&&nodes[i].data==0;}
		loop=InvolutiveLoop(body.a,factor,transport.b);
		if(op.op==Op.not_&&self(term.a)) return true;
		if(op.op!=Op.mul||types[term.type]!=scalarType(Sort.real_)) return false;
		bool left=self(term.b);
		if(!left&&!self(term.a)) return false;
		loop.unit=left?term.a:term.b;
		if(nodes[loop.unit].op!=BoundOp.scalar||arena.at(nodes[loop.unit].data)!=arena.real_(-1)) return false;
		loop.map=left?Involution.negLeft:Involution.negRight; return true;
	}
	private void involutionEmissions(Scope ctx,BoundNode loop,InvolutiveLoop source,out BoundTerm seed,out BoundTerm reflected){
		BoundTerm[] env=[bottom(ctx,types[loop.type])];
		foreach(i;0..depth(ctx)) env~=variable(ctx,i);
		seed=substitute(at(source.seed),ctx,env);
		auto kernel=substitute(at(source.kernel),ctx,env);
		reflected=distribution(ctx,BoundOp.distributionBind,[seed,kernel]);
	}
	private BoundTerm involutionMass(BoundTerm mass,out BindingRule rule){
		uint[] ops; auto loop=nodes[observationInput(node(mass).a,ops)]; InvolutiveLoop source;
		if(loop.op!=BoundOp.distributionFixed||nodes[loop.a].op!=BoundOp.lambda||!involutiveLoop(nodes[loop.a].a,source)) return BoundTerm.init;
		auto ctx=context(mass);
		BoundTerm seed,reflected; involutionEmissions(ctx,loop,source,seed,reflected);
		BoundTerm observe(BoundTerm d){return observedMass(d,ops);}
		auto r=source.ratio==uint.max?Rational(1):arena.number(arena.at(nodes[source.ratio].data)).re;
		if(r>=Rational(1)){
			rule=BindingRule.distributionInvolutionUnbounded;
			auto zero=arena.real_(0);
			BoundTerm requireZero(BoundTerm d){
				auto nz=primitive(arena.nonzero(zero),[observe(d)]);
				return guard(primitive(arena.not_(arena.boolean(false)),[nz]),scalar(ctx,zero));
			}
			return primitive(arena.add(zero,zero,true),[requireZero(seed),requireZero(reflected)]);
		}
		rule=BindingRule.distributionInvolutionObservation;
		auto a=Rational(1)/(Rational(1)-r*r);
		auto first=distribution(ctx,BoundOp.distributionScale,[scalar(ctx,arena.real_(a)),seed]);
		auto second=distribution(ctx,BoundOp.distributionScale,[scalar(ctx,arena.real_(r*a)),reflected]);
		return observe(distribution(ctx,BoundOp.distributionAdd,[first,second]));
	}
	private struct NatShift {
		uint start, stride, ratio, mass=uint.max;
		bool strideLeft,zeroStart,unitStride;
	}
	private bool naturalShift(uint id,out NatShift shift){
		auto root=nodes[id]; Rational factor;
		if(root.op!=BoundOp.distributionAdd) return false;
		auto emit=nodes[root.a],tail=nodes[root.b];
		if(emit.op==BoundOp.distributionScale){
			if(!nonnegativeReal(emit.a,factor)) return false;
			shift.mass=emit.a; emit=nodes[emit.b];
		}
		if(emit.op!=BoundOp.distributionDirac||type(at(emit.a))!=scalarType(Sort.natural)||depends(at(emit.a),0)||
			tail.op!=BoundOp.distributionScale||!nonnegativeReal(tail.a,factor)) return false;
		auto advance=nodes[tail.b];
		if(advance.op!=BoundOp.distributionBind||nodes[advance.a].op!=BoundOp.variable||nodes[advance.a].data!=0||
			nodes[advance.b].op!=BoundOp.lambda) return false;
		auto atom=nodes[nodes[advance.b].a];
		if(atom.op!=BoundOp.distributionDirac||!primitiveOp(atom.a,Op.builtin)) return false;
		auto add=nodes[atom.a];
		if(arena.view(arena.at(add.data)).value!=Builtin.addN) return false;
		shift.strideLeft=nodes[add.a].op==BoundOp.scalar;
		auto argument=nodes[shift.strideLeft?add.b:add.a];
		shift.stride=shift.strideLeft?add.a:add.b;
		auto stride=nodes[shift.stride];
		if(argument.op!=BoundOp.variable||argument.data!=0||stride.op!=BoundOp.scalar) return false;
		auto k=arena.at(stride.data);
		if(arena.sort(k)!=Sort.natural||!arena.isNumber(k)||arena.number(k).re<=Rational(0)) return false;
		shift.ratio=tail.a; shift.start=emit.a; shift.unitStride=k==arena.natural_(1);
		shift.zeroStart=nodes[emit.a].op==BoundOp.scalar&&arena.at(nodes[emit.a].data)==arena.natural_(0);
		return true;
	}
	private struct MomentPolynomial {
		Rational[] coefficients;
		string polynomial, proof;
	}
	// Reify a total polynomial weight in the emitted natural. The sampled
	// polynomial and its source proof use the same compositional operations.
	private bool momentPolynomial(uint id,out MomentPolynomial result,bool exporting,uint depth=0){
		if(depth>64) return false;
		enum ns="GeometricMoments.NatTest.";
		auto n=nodes[id];
		if(n.op==BoundOp.scalar){
			auto t=arena.at(n.data);
			Rational slope,c;
			if(arena.sort(t)!=Sort.real_||!integralAffine(arena,t,Term.init,slope,c)||c.words>128) return false;
			result.coefficients=[c];
			if(exporting){
				auto q=SourceCertificates.q(c),name="n"~to!string(t.id);
				result.polynomial="(.constant "~q~")";
				result.proof="("~ns~"constant ("~name~".eval ξ) "~q~" (Numeric.calculate_sound ξ "~name~" "~q~" rfl))";
			}
			return true;
		}
		if(n.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(n.data));
		if(op.op==Op.builtin&&op.value==Builtin.castQR){
			auto v=id;
			foreach(c;[Builtin.castQR,Builtin.castZQ,Builtin.castNZ]){
				if(!primitiveOp(v,Op.builtin)||arena.view(arena.at(nodes[v].data)).value!=c) return false;
				v=nodes[v].a;
			}
			if(nodes[v].op!=BoundOp.variable||nodes[v].data!=0) return false;
			result.coefficients=[Rational(0),Rational(1)];
			if(exporting){ result.polynomial=".index"; result.proof=ns~"index"; }
			return true;
		}
		if(op.op!=Op.add&&op.op!=Op.mul&&op.op!=Op.pow) return false;
		MomentPolynomial a,b;
		if(!momentPolynomial(n.a,a,exporting,depth+1)) return false;
		if(op.op==Op.pow){
			if(op.value>32||(a.coefficients.length-1)*op.value>32) return false;
			result.coefficients=[Rational(1)];
			foreach(i;0..op.value) result.coefficients=polyProduct(result.coefficients,a.coefficients);
			if(exporting){
				auto k=to!string(op.value);
				result.polynomial="(.pow "~a.polynomial~" "~k~")";
				result.proof="("~ns~"pow "~k~" "~a.proof~")";
			}
		}else{
			if(!momentPolynomial(n.b,b,exporting,depth+1)) return false;
			if(op.op==Op.mul&&a.coefficients.length+b.coefficients.length>34) return false;
			result.coefficients=op.op==Op.add?polySum(a.coefficients,b.coefficients):polyProduct(a.coefficients,b.coefficients);
			if(exporting){
				auto law=op.op==Op.add?"add":"mul";
				result.polynomial="(."~law~" "~a.polynomial~" "~b.polynomial~")";
				result.proof="("~ns~law~" "~a.proof~" "~b.proof~")";
			}
		}
		foreach(c;result.coefficients) if(c.words>128) return false;
		return true;
	}
	// Solve q*A(i+1)-A(i)=w*P(start+i*stride) from highest degree down.
	// Lean checks the whole polynomial identity and the boundary value -A(0).
	private bool shiftMoment(NatShift shift,uint[] operations,out Rational[] primitive_,out MomentPolynomial polynomial,bool exporting){
		if(operations.length!=1||nodes[operations[0]].op!=BoundOp.distributionWeight) return false;
		auto test=nodes[nodes[operations[0]].a],start=nodes[shift.start];
		if(test.op!=BoundOp.lambda||start.op!=BoundOp.scalar||!arena.isNumber(arena.at(start.data))) return false;
		auto q=arena.number(arena.at(nodes[shift.ratio].data)).re;
		if(q>=Rational(1)) return false;
		if(!momentPolynomial(test.a,polynomial,exporting)) return false;
		auto a=arena.number(arena.at(start.data)).re,k=arena.number(arena.at(nodes[shift.stride].data)).re;
		auto w=shift.mass==uint.max?Rational(1):arena.number(arena.at(nodes[shift.mass].data)).re;
		Rational[] p;
		foreach_reverse(c;polynomial.coefficients){
			p=polySum([c],polyProduct(p,[a,k]));
			foreach(x;p) if(x.words>128) return false;
		}
		primitive_=new Rational[](p.length);
		foreach_reverse(i;0..p.length){
			Rational above,choose=Rational(1);
			foreach(j;i+1..p.length){
				choose=choose*Rational(cast(long)j)/Rational(cast(long)(j-i));
				above=above+choose*primitive_[j];
			}
			primitive_[i]=(w*p[i]-q*above)/(q-Rational(1));
			if(primitive_[i].words>128) return false;
		}
		return true;
	}
	/// Replace an observed shift loop by its orbit while keeping the starting
	/// point strict, including when an outer weight or kernel is missing.
	private BoundTerm shiftMass(BoundTerm mass,out BindingRule rule){
		rule=BindingRule.distributionShiftObservation;
		uint[] ops; auto loop=nodes[observationInput(node(mass).a,ops)]; NatShift shift;
		if(loop.op!=BoundOp.distributionFixed||nodes[loop.a].op!=BoundOp.lambda||!naturalShift(nodes[loop.a].a,shift))
			return BoundTerm.init;
		Rational[] primitive_;MomentPolynomial moment;
		if(shiftMoment(shift,ops,primitive_,moment,false)){
			rule=BindingRule.distributionShiftMoment;
			return scalar(context(mass),arena.real_(-primitive_[0]));
		}
		auto ctx=context(mass),inner=push(ctx,scalarType(Sort.natural));
		BoundTerm[] env=[bottom(ctx,types[loop.type])]; uint[] lifted;
		foreach(i;0..contexts[ctx.index].length){ env~=variable(ctx,i); lifted~=i+1; }
		auto start=substitute(at(shift.start),ctx,env);
		if(!ops.length){
			auto w=shift.mass==uint.max?Rational(1):arena.number(arena.at(nodes[shift.mass].data)).re;
			auto q=arena.number(arena.at(nodes[shift.ratio].data)).re;
			auto total=!w.zero&&q>=Rational(1)?bottom(ctx,scalarType(Sort.real_)):
				scalar(ctx,arena.real_(w.zero?w:w/(Rational(1)-q)));
			return sequence(start,total);
		}
		auto zero=arena.natural_(0),n=variable(inner,0);
		auto offset=shift.unitStride?n:primitive(arena.call(Builtin.mulN,[zero,zero]),[n,scalar(inner,arena.at(nodes[shift.stride].data))]);
		auto point=shift.zeroStart?offset:primitive(arena.call(Builtin.addN,[zero,zero]),[rename(start,inner,lifted),offset]);
		auto d=distribution(inner,BoundOp.distributionDirac,[point]);
		auto power=primitive(arena.call(Builtin.powRN,[arena.real_(0),zero]),[scalar(inner,arena.at(nodes[shift.ratio].data)),n]);
		auto product=arena.mul(arena.real_(0),arena.real_(0),true);
		bool factored=shift.mass!=uint.max&&!arena.number(arena.at(nodes[shift.mass].data)).re.zero;
		auto coefficient=shift.mass==uint.max||factored?power:primitive(product,[scalar(inner,arena.at(nodes[shift.mass].data)),power]);
		foreach_reverse(id;ops){
			auto op=nodes[id]; bool weight=op.op==BoundOp.distributionWeight;
			auto argument=rename(at(weight?op.a:op.b),inner,lifted);
			d=distribution(inner,op.op,weight?[argument,d]:[d,argument]);
		}
		auto row=primitive(product,[coefficient,distribution(inner,BoundOp.distributionMass,[d])]);
		auto total=summation(hint(lambda(row),"i"));
		if(factored) total=primitive(product,[scalar(ctx,arena.at(nodes[shift.mass].data)),total]);
		return sequence(start,total);
	}
	BoundTerm distributionFixed(BoundTerm fn){
		auto n=node(fn); RetryParts parts; NatShift shift; InvolutiveLoop cycle;
		enforce(n.op==BoundOp.lambda&&(retrySource(n.a,parts)||naturalShift(n.a,shift)||involutiveLoop(n.a,cycle)),
			"a distribution fixed point requires a supported atomic retry, positive natural shift, or involution");
		return distribution(context(fn),BoundOp.distributionFixed,[fn]);
	}
	/// Follow the input of an observed chain of weight and bind operations.
	private uint observationInput(uint id,out uint[] operations){
		for(;;){
			auto n=nodes[id];
			if(n.op!=BoundOp.distributionWeight&&n.op!=BoundOp.distributionBind) return id;
			operations~=id;
			id=n.op==BoundOp.distributionWeight?n.b:n.a;
		}
	}
	private BoundTerm observedMass(BoundTerm d,uint[] operations,bool underIndex=false){
		auto ctx=context(d);
		uint[] lifted;
		if(underIndex) foreach(i;0..depth(ctx)-1) lifted~=i+1;
		foreach_reverse(id;operations){
			auto op=nodes[id]; bool weight=op.op==BoundOp.distributionWeight;
			auto fn=at(weight?op.a:op.b);
			if(underIndex) fn=rename(fn,ctx,lifted);
			d=distribution(ctx,op.op,weight?[fn,d]:[d,fn]);
		}
		return distribution(ctx,BoundOp.distributionMass,[d]);
	}
	private enum VisitKind { other, empty, one }
	private struct AtomicVisits { VisitKind kind; uint point; Rational weight; }
	/// Compute the total weight only when all visited atoms coincide. Scaling
	/// by zero keeps the visited set, even when a second atom is present.
	private AtomicVisits atomicVisits(uint id,ref AtomicVisits[uint] memo){
		if(auto hit=id in memo) return *hit;
		auto n=nodes[id]; AtomicVisits v;
		switch(n.op){
			case BoundOp.distributionZero:v.kind=VisitKind.empty; break;
			case BoundOp.distributionDirac:v=AtomicVisits(VisitKind.one,n.a,Rational(1)); break;
			case BoundOp.distributionScale:{
				Rational weight;
				if(nonnegativeReal(n.a,weight)){
					v=atomicVisits(n.b,memo);
					if(v.kind==VisitKind.one) v.weight=weight*v.weight;
				}
				break;
			}
			case BoundOp.distributionAdd:{
				auto a=atomicVisits(n.a,memo),b=atomicVisits(n.b,memo);
				if(a.kind==VisitKind.empty) v=b;
				else if(b.kind==VisitKind.empty) v=a;
				else if(a.kind==VisitKind.one&&b.kind==VisitKind.one&&a.point==b.point)
					v=AtomicVisits(VisitKind.one,a.point,a.weight+b.weight);
				break;
			}
			default:break;
		}
		return memo[id]=v;
	}
	BoundTerm fixed(BoundTerm body){
		auto n=node(body),v=pool.view(type(body));
		enforce(n.op==BoundOp.lambda&&n.context!=0&&contexts[n.context].type==n.type,"fixed-point body must be a lambda of the declared type");
		bool dataType(TypeId t){
			auto shape=pool.view(t);
			if(shape.kind<=TypeKind.complex||shape.kind==TypeKind.distribution) return true;
			if(shape.kind!=TypeKind.tuple&&shape.kind!=TypeKind.vector) return false;
			if(shape.kind==TypeKind.vector&&(!shape.dimension.constant||!shape.length||shape.length>256)) return false;
			foreach(field;shape.fields) if(!dataType(field)) return false;
			return true;
		}
		// A distribution is an ordinary value of the flat result domain.
		// Its sample type is opaque to the recursion certificate.
		enforce(dataType(v.fields[0])&&dataType(v.fields[1]),
			"fixed points require first-order data arguments and results");
		enforce(continuity(at(n.a))!=Continuity.unsupported,"recursive dependency crosses an operation without a continuity certificate");
		checkProgram(at(n.a)); return intern(BoundNode(BoundOp.fixed,contexts[n.context].parent,n.type,body.id));
	}
	BoundTerm variable(Scope s,uint index){
		check(s); auto ctx=s.index;
		foreach(i;0..index){ enforce(ctx!=0,"unbound variable"); ctx=contexts[ctx].parent; }
		enforce(ctx!=0,"unbound variable");
		return intern(BoundNode(BoundOp.variable,s.index,typeId(pool.shift(types[contexts[ctx].type],cast(int)index+1)),uint.max,uint.max,index));
	}
	BoundTerm scalar(Scope s,Term value){
		check(s); auto ty=typeId(scalarType(arena.sort(value)));
		return intern(BoundNode(BoundOp.scalar,s.index,ty,uint.max,uint.max,value.id));
	}
	BoundTerm primitive(Term prototype,BoundTerm[] args){
		auto n=arena.view(prototype);
		enforce(n.arity>0&&n.arity<=2&&args.length==n.arity,"primitive arity mismatch");
		auto ctx=context(args[0]);
		foreach(i,x;args){
			enforce(context(x)==ctx,"primitive context mismatch");
			enforce(type(x)==scalarType(arena.sort(arena.viewChild(prototype,cast(uint)i))),"primitive type mismatch");
		}
		Term[] placeholders;
		foreach(i;0..n.arity){
			auto sort=arena.sort(arena.viewChild(prototype,i));
			placeholders~=sort==Sort.boolean?arena.boolean(false):arena.number(Number(0),sort);
		}
		prototype=arena.viewRebuild(prototype,placeholders,true);
		return intern(BoundNode(BoundOp.primitive,ctx.index,typeId(scalarType(n.sort)),
			args[0].id,args.length==2?args[1].id:uint.max,prototype.id));
	}
	Dimension dimension(BoundTerm t){
		enforce(type(t)==scalarType(Sort.natural),"dependent argument must have type ℕ"); auto n=node(t);
		if(n.op==BoundOp.variable) return Dimension.bound(n.data);
		if(n.op==BoundOp.scalar){
			Dimension scalarDimension(Term x){
				auto q=arena.view(x);
				if(arena.isNumber(x)){ auto v=arena.number(x).re; enforce(v.small&&v.integer>=0,"dimension literal exceeds range"); return Dimension.literal(cast(ulong)v.integer); }
				if(q.op==Op.variable){ auto name=dimensionParameters.get(cast(uint)q.value,""); enforce(name.length,"unknown dimension parameter"); return Dimension.variable(name,cast(uint)q.value); }
				if(q.op==Op.builtin&&(q.value==Builtin.addN||q.value==Builtin.mulN||q.value==Builtin.powNN))
					return Dimension.binary(q.value==Builtin.addN?"+":q.value==Builtin.mulN?"*":"^",scalarDimension(arena.viewChild(x,0)),scalarDimension(arena.viewChild(x,1)));
				throw new Exception("dependent arguments require total natural literals, parameters, sums, products, or powers");
			}
			return scalarDimension(arena.at(n.data));
		}
		if(n.op==BoundOp.primitive){ auto q=arena.view(arena.at(n.data));
			if(q.op==Op.builtin&&(q.value==Builtin.addN||q.value==Builtin.mulN||q.value==Builtin.powNN))
				return Dimension.binary(q.value==Builtin.addN?"+":q.value==Builtin.mulN?"*":"^",dimension(at(n.a)),dimension(at(n.b)));
		}
		throw new Exception("dependent arguments require total natural dimensions");
	}
	BoundTerm lambda(BoundTerm body){
		auto n=node(body); enforce(n.context!=0,"lambda requires a bound variable");
		auto ctx=contexts[n.context],ty=typeId(pool.pi(types[ctx.type],types[n.type]));
		return intern(BoundNode(BoundOp.lambda,ctx.parent,ty,body.id));
	}
	BoundTerm apply(BoundTerm function_,BoundTerm argument){
		auto f=node(function_),x=node(argument),ty=pool.view(types[f.type]);
		enforce(f.context==x.context,"application context mismatch");
		enforce((ty.kind==TypeKind.function_||ty.kind==TypeKind.pi)&&ty.fields[0]==types[x.type],"application type mismatch");
		return intern(BoundNode(BoundOp.apply,f.context,typeId(ty.kind==TypeKind.pi?pool.instantiate(ty.fields[1],dimension(argument)):ty.fields[1]),function_.id,argument.id));
	}
	BoundTerm sequence(BoundTerm x,BoundTerm y){
		auto a=node(x),b=node(y); enforce(a.context==b.context,"sequence context mismatch");
		return intern(BoundNode(BoundOp.sequence,b.context,b.type,x.id,y.id));
	}
	BoundTerm set(BoundTerm predicate){
		auto n=node(predicate); enforce(n.context!=0&&type(predicate)==scalarType(Sort.boolean),"set requires a bound Boolean predicate");
		auto ctx=contexts[n.context];
		return intern(BoundNode(BoundOp.set,ctx.parent,typeId(pool.set(types[ctx.type])),predicate.id));
	}
	BoundTerm member(BoundTerm set_,BoundTerm x){
		auto n=node(set_),v=pool.view(type(set_));
		enforce(v.kind==TypeKind.set&&v.fields[0]==type(x),"membership type mismatch");
		enforce(context(set_)==context(x),"membership context mismatch");
		return intern(BoundNode(BoundOp.member,n.context,typeId(scalarType(Sort.boolean)),set_.id,x.id));
	}
	BoundTerm subset(BoundTerm x,BoundTerm y){
		auto n=node(x); enforce(pool.view(type(x)).kind==TypeKind.set&&type(x)==type(y),"inclusion requires sets of the same type");
		enforce(context(x)==context(y),"inclusion context mismatch");
		return intern(BoundNode(BoundOp.subset,n.context,typeId(scalarType(Sort.boolean)),x.id,y.id));
	}
	BoundTerm finiteSum(BoundTerm f,BoundTerm n){
		auto v=pool.view(type(f));
		enforce(v.kind==TypeKind.function_&&v.fields[0]==scalarType(Sort.natural)&&type(n)==scalarType(Sort.natural)&&context(f)==context(n),"invalid finite sum");
		return intern(BoundNode(BoundOp.finiteSum,node(f).context,typeId(v.fields[1]),f.id,n.id));
	}
	private BoundTerm dropIndex(BoundTerm t){
		auto inner=context(t),parent=Scope(this,contexts[inner.index].parent);
		BoundTerm[] values=[scalar(parent,arena.number(Number(0),elementSort(type(variable(inner,0)))))];
		foreach(i;0..depth(parent)) values~=variable(parent,i);
		return substitute(t,parent,values);
	}
	BoundTerm summation(BoundTerm f){
		auto n=node(f),v=pool.view(type(f));
		enforce(v.kind==TypeKind.function_&&(v.fields[0]==scalarType(Sort.natural)||v.fields[0]==scalarType(Sort.integer)),"summation requires a natural or integer index");
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(v.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		enforce(numeric,"summation requires scalar numeric values");
		return intern(BoundNode(BoundOp.summation,n.context,typeId(v.fields[1]),f.id));
	}
	/// The limit of a function of a real variable at +∞, or at -∞.
	BoundTerm limit(BoundTerm f,bool bottom=false){
		auto n=node(f),v=pool.view(type(f));
		enforce(v.kind==TypeKind.function_&&v.fields[0]==scalarType(Sort.real_),"a limit requires a function of a real variable");
		enforce(v.fields[1]==scalarType(Sort.real_)||v.fields[1]==scalarType(Sort.complex),"a limit requires real or complex values");
		return intern(BoundNode(BoundOp.limit,n.context,typeId(v.fields[1]),f.id,uint.max,bottom));
	}
	BoundTerm domain(BoundTerm f){
		auto n=node(f),v=pool.view(type(f)); enforce(v.kind==TypeKind.function_||v.kind==TypeKind.pi,"domain requires a function");
		return intern(BoundNode(BoundOp.domain,n.context,typeId(pool.set(v.fields[0])),f.id));
	}
	BoundTerm defined(BoundTerm x){
		auto n=node(x); return intern(BoundNode(BoundOp.defined,n.context,typeId(scalarType(Sort.boolean)),x.id));
	}
	BoundTerm holds(BoundTerm p){
		enforce(type(p)==scalarType(Sort.boolean),"holds requires Bool");
		auto n=node(p); return intern(BoundNode(BoundOp.holds,n.context,n.type,p.id));
	}
	BoundTerm guard(BoundTerm p,BoundTerm x){
		enforce(type(p)==scalarType(Sort.boolean)&&context(p)==context(x),"guard requires Bool in the same scope");
		auto n=node(x); return intern(BoundNode(BoundOp.guard,n.context,n.type,p.id,x.id));
	}
	BoundTerm conditional(BoundTerm predicate,BoundTerm yes,BoundTerm no){
		enforce(type(predicate)==scalarType(Sort.boolean)&&context(predicate)==context(yes)&&context(yes)==context(no),"conditional requires Bool in the same scope");
		enforce(type(yes)==type(no),"conditional branch type mismatch");
		return intern(BoundNode(BoundOp.conditional,node(yes).context,node(yes).type,predicate.id,yes.id,0,no.id));
	}
	private BoundTerm rebuild(BoundTerm t,Scope target,BoundTerm[] args,Dimension delegate(uint) @safe dimensions=null){
		auto n=node(t);
		TypeId mapped(uint id){ return dimensions is null?types[id]:pool.map(types[id],dimensions); }
		final switch(n.op){
			case BoundOp.distributionZero:return distribution(target,n.op,[],pool.view(mapped(n.type)).fields[0]);
			case BoundOp.distributionFixed,BoundOp.distributionRetry,BoundOp.distributionLebesgue,BoundOp.distributionDirac,BoundOp.distributionAdd,BoundOp.distributionScale,BoundOp.distributionWeight,BoundOp.distributionIntegral,BoundOp.distributionSum,BoundOp.distributionMass,BoundOp.distributionDensityAt,BoundOp.distributionBind,BoundOp.distributionPushforwardOn,BoundOp.distributionInverseCover,BoundOp.distributionInversePart,BoundOp.distributionRadiusImage,BoundOp.distributionMaskedGraph,BoundOp.distributionGraphFibre,BoundOp.distributionGraphMass:return distribution(target,n.op,args);
			case BoundOp.unit,BoundOp.vectorNil:return tuple(target,[],mapped(n.type));
			case BoundOp.vectorCons,BoundOp.pair:return intern(BoundNode(n.op,target.index,typeId(mapped(n.type)),args[0].id,args[1].id));
			case BoundOp.first,BoundOp.rest:return intern(BoundNode(n.op,target.index,typeId(mapped(n.type)),args[0].id));
			case BoundOp.conditional:return conditional(args[0],args[1],args[2]);
			case BoundOp.get:return get(args[0],args[1]);
			case BoundOp.tensor:return tensor(cast(TensorOp)n.data,args[0],args[1]);
			case BoundOp.scalar:return scalar(target,arena.at(n.data));
			case BoundOp.global:return global(target,mapped(n.type),n.data);
			case BoundOp.variable:assert(0,"variable requires substitution");
			case BoundOp.primitive:return primitive(arena.at(n.data),args);
			case BoundOp.lambda:return inheritHint(t,lambda(args[0]));
			case BoundOp.set:return inheritHint(t,set(args[0]));
			case BoundOp.member:return member(args[0],args[1]);
			case BoundOp.subset:return subset(args[0],args[1]);
			case BoundOp.typeEq:return typeEq(args[0],args[1]);
			case BoundOp.equal:return equal(args[0],args[1]);
			case BoundOp.typeValue:return typeValue(target,mapped(n.data));
			case BoundOp.bottom:return bottom(target,mapped(n.type));
			case BoundOp.fixed:return inheritHint(t,fixed(args[0]));
			case BoundOp.finiteSum:return finiteSum(args[0],args[1]);
			case BoundOp.summation:return summation(args[0]);
			case BoundOp.limit:return limit(args[0],n.data!=0);
			case BoundOp.domain:return domain(args[0]);
			case BoundOp.defined:return defined(args[0]);
			case BoundOp.holds:return holds(args[0]);
			case BoundOp.guard:return guard(args[0],args[1]);
			case BoundOp.apply:return apply(args[0],args[1]);
			case BoundOp.sequence:return sequence(args[0],args[1]);
		}
	}
	BoundTerm rename(BoundTerm term,Scope target,uint[] indices){
		check(term); check(target); auto ctx=node(term).context;
		enforce(indices.length==contexts[ctx].length,"renaming arity mismatch");
		Dimension mapped(uint i){ enforce(i<indices.length,"unbound renamed dimension"); return Dimension.bound(indices[i]); }
		foreach(i,index;indices){
			enforce(type(variable(target,index))==pool.map(type(variable(context(term),cast(uint)i)),&mapped),"renaming type mismatch");
		}
		Table!(uint,uint) memo;
		BoundTerm visit(BoundTerm t){
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return at(old);
			auto n=node(t); BoundTerm result;
			if(n.op==BoundOp.variable) result=variable(target,indices[n.data]);
			else if(n.op==BoundOp.lambda||n.op==BoundOp.set||n.op==BoundOp.fixed){
				uint[] lifted=[0]; foreach(index;indices) lifted~=index+1;
				auto body=rename(at(n.a),push(target,pool.map(types[contexts[nodes[n.a].context].type],&mapped)),lifted);
				result=inheritHint(t,n.op==BoundOp.lambda?lambda(body):n.op==BoundOp.set?set(body):fixed(body));
			}else{
				BoundTerm[] children;
				if(n.a!=uint.max) children~=visit(at(n.a));
				if(n.b!=uint.max) children~=visit(at(n.b));
				if(n.c!=uint.max) children~=visit(at(n.c));
				result=rebuild(t,target,children,&mapped);
			}
			memo.set(t.id,result.id); return result;
		}
		return visit(term);
	}
	BoundTerm substitute(BoundTerm term,Scope target,BoundTerm[] values){
		check(term); check(target); auto ctx=node(term).context;
		enforce(values.length==contexts[ctx].length,"substitution arity mismatch");
		Dimension mapped(uint i){ enforce(i<values.length,"unbound substituted dimension"); return dimension(values[i]); }
		foreach(i,value;values){
			enforce(context(value)==target&&type(value)==pool.map(type(variable(context(term),cast(uint)i)),&mapped),"substitution type mismatch");
		}
		Table!(uint,uint) memo;
		BoundTerm visit(BoundTerm t){
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return at(old);
			auto n=node(t); BoundTerm result;
			if(n.op==BoundOp.variable) result=values[n.data];
			else if(n.op==BoundOp.lambda||n.op==BoundOp.set||n.op==BoundOp.fixed){
				auto inner=push(target,pool.map(types[contexts[nodes[n.a].context].type],&mapped));
				BoundTerm[] lifted=[variable(inner,0)]; uint[] indices;
				foreach(i;0..contexts[target.index].length) indices~=i+1;
				foreach(value;values) lifted~=rename(value,inner,indices);
				auto body=substitute(at(n.a),inner,lifted); result=inheritHint(t,n.op==BoundOp.lambda?lambda(body):n.op==BoundOp.set?set(body):fixed(body));
			}else{
				BoundTerm[] children;
				if(n.a!=uint.max) children~=visit(at(n.a));
				if(n.b!=uint.max) children~=visit(at(n.b));
				if(n.c!=uint.max) children~=visit(at(n.c));
				result=rebuild(t,target,children,&mapped);
			}
			memo.set(t.id,result.id); return result;
		}
		return visit(term);
	}
	BoundTerm beta(BoundTerm body,BoundTerm argument){
		auto target=context(argument); enforce(context(body)==push(target,type(argument)),"beta context mismatch");
		BoundTerm[] values=[argument];
		foreach(i;0..contexts[target.index].length) values~=variable(target,i);
		return sequence(argument,substitute(body,target,values));
	}
	private bool totalScalar(BoundTerm t){
		auto n=node(t); if(n.op!=BoundOp.scalar) return false;
		auto v=arena.node(arena.at(n.data));
		return v.arity==0;
	}
	private bool closedScalar(BoundTerm t){
		auto n=node(t); if(n.op!=BoundOp.scalar) return false;
		foreach(id;arena.viewPostorder(arena.at(n.data))) if(arena.view(arena.at(id)).op==Op.variable) return false;
		return true;
	}
	private bool closedFixedArgument(BoundTerm t){
		auto n=node(t);
		switch(n.op){
			case BoundOp.scalar:return closedScalar(t);
			case BoundOp.unit,BoundOp.vectorNil,BoundOp.distributionZero,BoundOp.distributionLebesgue:return true;
			case BoundOp.distributionDirac:return closedFixedArgument(at(n.a));
			case BoundOp.pair,BoundOp.vectorCons,BoundOp.distributionAdd,BoundOp.distributionScale:
				return closedFixedArgument(at(n.a))&&closedFixedArgument(at(n.b));
			default:return false;
		}
	}
	// An application or a reference to an outer binder keeps this operand
	// outside the single-variable scalar normalizer.
	private bool needsBindingScalar(uint id){
		auto n=nodes[id];
		if(n.op==BoundOp.scalar) return false;
		if(n.op==BoundOp.variable) return n.data!=0;
		return n.op!=BoundOp.primitive||needsBindingScalar(n.a)||(n.b!=uint.max&&needsBindingScalar(n.b));
	}
	private Term scalarBody(BoundTerm term,Term argument){
		auto n=node(term);
		if(n.op==BoundOp.scalar) return arena.at(n.data);
		if(n.op==BoundOp.variable) return n.data==0?argument:Term.init;
		if(n.op!=BoundOp.primitive) return Term.init;
		auto x=scalarBody(at(n.a),argument); if(x==Term.init) return Term.init;
		Term[] args=[x];
		if(n.b!=uint.max){ auto y=scalarBody(at(n.b),argument); if(y==Term.init) return Term.init; args~=y; }
		return arena.viewRebuild(arena.at(n.data),args,true);
	}
	// A comparison that excludes exactly zero of the innermost argument.
	// Surface natural equality can introduce an integer coercion.
	private string binderNonzero(uint id){
		auto pred=nodes[id];
		if(pred.op!=BoundOp.primitive) return "";
		auto op=arena.view(arena.at(pred.data));
		bool argument(uint i){return nodes[i].op==BoundOp.variable&&nodes[i].data==0;}
		if(argument(pred.a)){
			if(op.op==Op.nonzero) return "rfl";
			if(op.op==Op.builtin) switch(cast(Builtin)op.value){
				case Builtin.nonzeroN:return "Functions.nonzeroN_eq";
				case Builtin.nonzeroZ:return "Functions.nonzeroZ_eq";
				case Builtin.nonzeroQ:return "Summation.nonzeroQ";
				default:break;
			}
		}
		if(op.op==Op.builtin&&op.value==Builtin.nonzeroZ&&primitiveOp(pred.a,Op.builtin)){
			auto cast_=nodes[pred.a];
			if(arena.view(arena.at(cast_.data)).value==Builtin.castNZ&&argument(cast_.a))
				return "Functions.nonzeroCastNZ_eq";
		}
		return "";
	}
	// The negation of a comparison: the other comparison of its operands in
	// the other order. Both are primitives, or both scalars.
	private bool negatedComparison(uint id,uint comparison){
		auto x=nodes[id],y=nodes[comparison];
		if(x.op!=y.op||x.op!=BoundOp.primitive&&x.op!=BoundOp.scalar) return false;
		auto p=arena.at(x.data),q=arena.at(y.data); auto f=arena.view(p).op,g=arena.view(q).op;
		if(!(g==Op.le&&f==Op.lt||g==Op.lt&&f==Op.le)) return false;
		if(x.op==BoundOp.primitive) return x.a==y.b&&x.b==y.a;
		return arena.viewChild(p,0)==arena.viewChild(q,1)&&arena.viewChild(p,1)==arena.viewChild(q,0);
	}
	private bool strictComparison(uint id){ return arena.view(arena.at(nodes[id].data)).op==Op.lt; }
	// A guard that does not mention the axis around the only weight of a
	// Lebesgue observation: the guard, the weight body without it, and the
	// lemma that relates the two spellings. Where the value may be missing
	// the mask is under the guard of its domain: a comparison that leaves
	// takes its negation along, and the rest of the domain stays around the
	// rest of the mask.
	private bool axisFreeGuard(uint mass,out uint guard,out BoundTerm rest,out string shape){
		auto n=nodes[mass]; uint[] bodies;
		if(n.op!=BoundOp.distributionMass||!densityBodies(n.a,bodies)||bodies.length!=1) return false;
		bool isOp(BoundNode q,Op op){return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==op;}
		bool call(BoundNode q,Builtin f){return isOp(q,Op.builtin)&&arena.view(arena.at(q.data)).value==f;}
		auto body=nodes[bodies[0]]; uint[] casts;
		if(body.op==BoundOp.guard){
			auto o=nodes[body.a],m=nodes[body.b];
			if(!isOp(o,Op.or_)||!isOp(m,Op.mask)||!isOp(nodes[m.a],Op.and_)) return false;
			guard=nodes[m.a].a;
			if(depends(at(guard),0)||!negatedComparison(o.a,guard)) return false;
			rest=this.guard(at(o.b),primitive(arena.at(m.data),[at(nodes[m.a].b),at(m.b)]));
			shape="(fun _ => Distribution.StepSource.mask_domain_split "~(strictComparison(guard)?"true":"false")~" _ _ _ _ _)";
			return true;
		}
		if(call(body,Builtin.castQR)&&call(nodes[body.a],Builtin.castZQ)&&call(nodes[nodes[body.a].a],Builtin.castNZ)){
			casts=[bodies[0],body.a,nodes[body.a].a]; body=nodes[nodes[nodes[body.a].a].a];
		}
		if(!isOp(body,Op.mask)) return false;
		if(!casts.length&&!depends(at(body.a),0)){ guard=body.a; rest=at(body.b); shape="(fun _ => rfl)"; }
		else if(isOp(nodes[body.a],Op.and_)&&!depends(at(nodes[body.a].a),0)){
			guard=nodes[body.a].a; rest=primitive(arena.at(body.data),[at(nodes[body.a].b),at(body.b)]);
			shape=casts.length?"(fun _ => Distribution.StepSource.cast_mask_and _ _ _)":"(fun _ => (Distribution.StepSource.mask_mask _ _ _).symm)";
		}else return false;
		foreach_reverse(c;casts) rest=primitive(arena.at(nodes[c].data),[rest]);
		return true;
	}
	// The first strict guard that does not mention the innermost variable, at
	// the top of a term or of a factor of it: its condition, and the term
	// without it. A product is strict in both factors.
	private bool axisFreeStrictGuard(uint id,out uint condition,out BoundTerm rest,uint depth=0){
		if(depth>32) return false;
		auto n=nodes[id]; BoundTerm inner;
		if(n.op==BoundOp.guard&&!depends(at(n.a),0)){ condition=n.a; rest=at(n.b); return true; }
		if(n.op!=BoundOp.primitive||arena.view(arena.at(n.data)).op!=Op.mul) return false;
		if(axisFreeStrictGuard(n.a,condition,inner,depth+1)){ rest=primitive(arena.at(n.data),[inner,at(n.b)]); return true; }
		if(!axisFreeStrictGuard(n.b,condition,inner,depth+1)) return false;
		rest=primitive(arena.at(n.data),[at(n.a),inner]); return true;
	}
	// The weights of a Lebesgue observation from the measure outward, and
	// the first with such a guard in its body.
	private bool massStrictGuard(uint mass,out uint[] weights,out size_t position,out uint condition,out BoundTerm rest){
		auto n=nodes[mass]; if(n.op!=BoundOp.distributionMass) return false;
		for(auto id=n.a;nodes[id].op!=BoundOp.distributionLebesgue;id=nodes[id].b){
			auto d=nodes[id];
			if(d.op!=BoundOp.distributionWeight||nodes[d.a].op!=BoundOp.lambda) return false;
			weights=d.a~weights;
		}
		foreach(i,w;weights) if(axisFreeStrictGuard(nodes[w].a,condition,rest)){ position=i; return true; }
		return false;
	}
	// A masked summand: a mask, also under the guard of its domain or as the
	// cast of a bracket, a product with one, or a sum of them.
	private bool maskedSummand(uint id){
		auto q=nodes[id];
		if(q.op==BoundOp.guard) return maskedSummand(q.b);
		if(q.op!=BoundOp.primitive) return false;
		auto v=arena.view(arena.at(q.data));
		if(v.op==Op.mask) return true;
		if(v.op==Op.builtin&&(v.value==Builtin.castQR||v.value==Builtin.castZQ||v.value==Builtin.castNZ)) return maskedSummand(q.a);
		if(type(at(id))!=scalarType(Sort.real_)) return false;
		if(v.op==Op.mul) return maskedSummand(q.a)||maskedSummand(q.b);
		return v.op==Op.add&&maskedSummand(q.a)&&maskedSummand(q.b);
	}
	// The points where the argument of an absolute value in a weight changes
	// its sign: an argument of degree one in the axis with rational
	// coefficients. In order; none if there are more than three.
	private Rational[] absoluteKinks(uint body){
		Rational[] kinks; bool many;
		void visit(uint id,uint depth){
			auto q=nodes[id]; if(depth>64||q.op!=BoundOp.primitive&&q.op!=BoundOp.guard) return;
			Rational[] p;
			if(q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.abs&&type(at(id))==scalarType(Sort.real_)&&axisPolynomial(q.a,p)){
				while(p.length&&p[$-1].zero) p.length=p.length-1;
				if(p.length==2){
					auto kink=Rational(0)-p[0]/p[1]; bool known;
					foreach(k;kinks) known|=k==kink;
					if(!known){ if(kink.words>128||kinks.length==3) many=true; else kinks~=kink; }
				}
			}
			if(q.a!=uint.max) visit(q.a,depth+1);
			if(q.b!=uint.max) visit(q.b,depth+1);
		}
		visit(body,0);
		if(many) return [];
		foreach(i;0..kinks.length) foreach(j;i+1..kinks.length) if(kinks[j]<kinks[i]){ auto k=kinks[i]; kinks[i]=kinks[j]; kinks[j]=k; }
		return kinks;
	}
	// A weight as the sum of its masks on the pieces between such points:
	// below the first, between two neighbours, and from the last on. A
	// partial value is the sum of its masks on the two sides of a point, and
	// from a point on that of its masks up to a later point and from there.
	// With `under` the proof of the equation at a point of the axis is built.
	private Spread splitAt(uint body,Rational[] kinks,scope string delegate(uint) @safe under){
		auto inner=context(at(body)),x=variable(inner,0),zero=arena.real_(0);
		auto addOp=arena.add(zero,zero,true),maskOp=arena.mask(arena.boolean(true),arena.real_(1));
		auto andOp=arena.and_(arena.boolean(true),arena.boolean(true));
		string literal(Rational q){ return "(Numeric.calculate_sound ξ n"~to!string(arena.real_(q).id)~" "~SourceCertificates.q(q)~" rfl)"; }
		BoundTerm from(Rational q){ return primitive(arena.le(zero,zero),[scalar(inner,arena.real_(q)),x]); }
		// The pieces from a point on: the sum, and the proof that the mask from
		// that point on is that sum.
		Spread rest(Rational[] points){
			auto last=primitive(maskOp,[from(points[0]),at(body)]);
			if(points.length==1) return Spread(last.id);
			auto upto=primitive(arena.lt(zero,zero),[x,scalar(inner,arena.real_(points[1]))]);
			auto tail=rest(points[1..$]);
			auto sum=primitive(addOp,[primitive(maskOp,[primitive(andOp,[from(points[0]),upto]),at(body)]),at(tail.id)]);
			if(!under) return Spread(sum.id);
			auto proof="(Value.split_between "~under(body)~" x "~SourceCertificates.q(points[0])~" "~SourceCertificates.q(points[1])~" "~literal(points[0])~" "~literal(points[1])~" rfl)";
			if(tail.proof.length) proof="(Eq.trans "~proof~" (congrArg₂ Value.add rfl "~tail.proof~"))";
			return Spread(sum.id,proof);
		}
		auto below=primitive(arena.lt(zero,zero),[x,scalar(inner,arena.real_(kinks[0]))]),tail=rest(kinks);
		auto sum=primitive(addOp,[primitive(maskOp,[below,at(body)]),at(tail.id)]);
		if(!under) return Spread(sum.id);
		auto proof="(Value.split "~under(body)~" x "~SourceCertificates.q(kinks[0])~" "~literal(kinks[0])~")";
		if(tail.proof.length) proof="(Eq.trans "~proof~" (congrArg₂ Value.add rfl "~tail.proof~"))";
		return Spread(sum.id,proof);
	}
	// Whether a product or a mask in a weight has a sum of masked summands
	// to go under. Decided without building anything.
	private bool spreadsSum(uint id){
		auto real_=scalarType(Sort.real_);
		bool isOp(uint i,Op op){ auto q=nodes[i]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==op&&type(at(i))==real_; }
		bool sum(uint i){ return isOp(i,Op.add)&&maskedSummand(nodes[i].a)&&maskedSummand(nodes[i].b); }
		auto q=nodes[id];
		if(isOp(id,Op.add)) return spreadsSum(q.a)||spreadsSum(q.b);
		if(isOp(id,Op.mul)) return sum(q.a)||sum(q.b)||spreadsSum(q.a)||spreadsSum(q.b);
		return isOp(id,Op.mask)&&(sum(q.b)||spreadsSum(q.b));
	}
	// A product with a factor that is a sum of masked summands, as the sum of
	// the products, and a mask of such a sum as the sum of the masks:
	// `(a+b)·c = a·c+b·c` and `[g]·(a+b) = [g]·a+[g]·b` for all partial
	// values, so the two are equal at every point. With `under`, the
	// evaluation of a subterm of the source at a point, the proof of that
	// equation is built with it.
	private struct Spread{ uint id=uint.max; string proof; }
	private Spread spreadProducts(uint id,size_t limit,scope string delegate(uint) @safe under){
		auto real_=scalarType(Sort.real_);
		bool isOp(uint i,Op op){ auto q=nodes[i]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==op&&type(at(i))==real_; }
		bool sum(uint i){ return isOp(i,Op.add)&&maskedSummand(nodes[i].a)&&maskedSummand(nodes[i].b); }
		auto addOp=arena.add(arena.real_(0),arena.real_(0),true),mulOp=arena.mul(arena.real_(1),arena.real_(1),true);
		auto maskOp=arena.mask(arena.boolean(true),arena.real_(1));
		// The terms of the proof are written over the subterms of the source.
		Table!(uint,bool) source;
		void mark(uint i){
			if(source.get(i,false)) return;
			source.set(i,true); auto mask=isOp(i,Op.mask);
			if(mask) source.set(nodes[i].a,true); else if(isOp(i,Op.add)||isOp(i,Op.mul)) mark(nodes[i].a);
			if(mask||isOp(i,Op.add)||isOp(i,Op.mul)) mark(nodes[i].b);
		}
		if(under) mark(id);
		string value(uint i){
			if(source.get(i,false)) return under(i);
			return "(Value."~(isOp(i,Op.add)?"add":isOp(i,Op.mul)?"mul":"mask")~" "~value(nodes[i].a)~" "~value(nodes[i].b)~")";
		}
		string congr(string f,string a,string b){ return a.length||b.length?"(congrArg₂ "~f~" "~(a.length?a:"rfl")~" "~(b.length?b:"rfl")~")":""; }
		string trans(string a,string b){ return !a.length?b:!b.length?a:"(Eq.trans "~a~" "~b~")"; }
		size_t count;
		// The product of two terms, or with `mask` the mask of the second by the first.
		Spread product(uint a,uint b,bool mask){
			auto left=!mask&&sum(a);
			if(!left&&!sum(b)) return Spread(primitive(mask?maskOp:mulOp,[at(a),at(b)]).id);
			if(++count>limit) return Spread.init;
			auto x=left?nodes[a].a:nodes[b].a,y=left?nodes[a].b:nodes[b].b;
			auto l=left?product(x,b,mask):product(a,x,mask); if(l.id==uint.max) return l;
			auto r=left?product(y,b,mask):product(a,y,mask); if(r.id==uint.max) return r;
			auto step=!under?"":left?"(Value.add_mul "~value(x)~" "~value(y)~" "~value(b)~")":
				"(Value."~(mask?"mask_add ":"mul_add ")~value(a)~" "~value(x)~" "~value(y)~")";
			return Spread(primitive(addOp,[at(l.id),at(r.id)]).id,trans(step,congr("Value.add",l.proof,r.proof)));
		}
		Spread visit(uint i){
			auto mul=isOp(i,Op.mul),mask=isOp(i,Op.mask);
			if(!mul&&!mask&&!isOp(i,Op.add)) return Spread(i);
			auto l=mask?Spread(nodes[i].a):visit(nodes[i].a); if(l.id==uint.max) return l;
			auto r=visit(nodes[i].b); if(r.id==uint.max) return r;
			if(!mul&&!mask) return Spread(primitive(addOp,[at(l.id),at(r.id)]).id,congr("Value.add",l.proof,r.proof));
			auto p=product(l.id,r.id,mask); if(p.id==uint.max) return p;
			return Spread(p.id,trans(congr(mask?"Value.mask":"Value.mul",l.proof,r.proof),p.proof));
		}
		return visit(id);
	}
	// A singleton source parameter maps to a critical point at the offset.
	private bool cornerChart(uint id,out Term offset,out bool swap){
		auto graph=nodes[id];
		if(graph.op!=BoundOp.distributionPushforwardOn||nodes[graph.a].op!=BoundOp.lambda||nodes[graph.b].op!=BoundOp.lambda) return false;
		auto predicate=nodes[graph.a].a,map=nodes[graph.b].a;
		if(!primitiveOp(predicate,Op.not_)||!primitiveOp(nodes[predicate].a,Op.nonzero)) return false;
		if(primitiveOp(map,Op.add)){
			auto m=nodes[map]; swap=nodes[m.a].op==BoundOp.scalar;
			auto c=nodes[swap?m.a:m.b]; map=swap?m.b:m.a;
			if(c.op!=BoundOp.scalar||!arena.isNumber(arena.at(c.data))) return false;
			offset=arena.at(c.data);
		}
		if(!primitiveOp(map,Op.pow)) return false;
		auto x=nodes[map].a;
		return arena.view(arena.at(nodes[map].data)).value==2&&nodes[nodes[predicate].a].a==x&&
			nodes[x].op==BoundOp.variable&&nodes[x].data==0;
	}
	private bool cornerChart(uint id){ Term offset; bool swap; return cornerChart(id,offset,swap); }
	// The analysis of closed piecewise polynomials on a rational grid: the
	// expressions it covers, their cut points, and the polynomial of a cell.
	private bool gridNumerical(uint id,bool calculated=false){
		auto q=nodes[id];
		if(q.op==BoundOp.scalar){
			auto leaf=arena.at(q.data);
			if(arena.isNumber(leaf)||arena.view(leaf).op==Op.boolLit) return true;
			Rational v; Term term;
			return calculated&&arena.sort(leaf)==Sort.real_&&closedRational(at(id),v,term);
		}
		if(q.op==BoundOp.variable)return q.data==0;
		if(q.op!=BoundOp.primitive)return false;
		auto op=arena.view(arena.at(q.data));
		bool allowed=op.op==Op.add||op.op==Op.mul||op.op==Op.pow||op.op==Op.abs||op.op==Op.mask||op.op==Op.lt||op.op==Op.le||op.op==Op.nonzero||op.op==Op.and_||op.op==Op.or_||op.op==Op.not_||
			op.op==Op.builtin&&(op.value>=Builtin.castNZ&&op.value<=Builtin.castQR||op.value==Builtin.addN||op.value==Builtin.addZ||op.value==Builtin.addQ||op.value==Builtin.mulN||op.value==Builtin.mulZ||op.value==Builtin.mulQ);
		return allowed&&gridNumerical(q.a,calculated)&&(q.b==uint.max||gridNumerical(q.b,calculated));
	}
	private bool gridKink(uint id,Term arg,out Rational slope,out Rational offset){
		auto inside=scalarBody(at(id),arg);
		return inside!=Term.init&&integralAffine(arena,inside,arg,slope,offset)&&slope.words<=128&&offset.words<=128;
	}
	// The scalar simplifier proposes rational zeros. Exact division accounts
	// for multiplicities and rejects incomplete lists before choosing any sign.
	private bool gridFactors(uint id,Term arg,out Rational lead,out Rational[] roots){
		Rational[] p;
		if(!axisPolynomial(id,p)) return false;
		while(p.length&&p[$-1].zero) p=p[0..$-1];
		lead=p.length?p[$-1]:Rational(0);
		if(p.length<=1) return true;
		if(p.length>17) return false;
		auto test=simplify(arena,arena.nonzero(scalarBody(at(id),arg)));
		Rational[] candidates;
		if(test.exhausted||!integralCutPoints(arena,test.output,arg,candidates)) return false;
		foreach(a;candidates){
			while(p.length>1&&polynomialAt(p,a).zero){
				auto quotient=new Rational[](p.length-1);
				quotient[$-1]=p[$-1];
				foreach_reverse(i;1..quotient.length) quotient[i-1]=p[i]+a*quotient[i];
				p=quotient; roots~=a;
			}
		}
		return p.length==1;
	}
	// Below a cast the axis occurs only in guards: a step expression.
	private bool gridSteps(uint id,Term arg,ref Rational[] cuts,uint depth){
		auto q=nodes[id];
		if(depth>64) return false;
		if(!depends(at(id),0)) return true;
		if(q.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(q.data));
		if(op.op==Op.mask){
			if(depends(at(q.a),0)){
				auto predicate=scalarBody(at(q.a),arg); Rational[] points;
				if(predicate==Term.init||!integralCutPoints(arena,predicate,arg,points)) return false;
				cuts~=points;
			}
			return gridSteps(q.b,arg,cuts,depth+1);
		}
		if(op.op!=Op.builtin) return false;
		if(op.value>=Builtin.castNZ&&op.value<=Builtin.castQR) return gridSteps(q.a,arg,cuts,depth+1);
		return (op.value==Builtin.addN||op.value==Builtin.addZ||op.value==Builtin.addQ||op.value==Builtin.mulN||op.value==Builtin.mulZ||op.value==Builtin.mulQ)&&gridSteps(q.a,arg,cuts,depth+1)&&gridSteps(q.b,arg,cuts,depth+1);
	}
	private bool gridCuts(uint id,Term arg,ref Rational[] cuts,uint depth=0){
		auto q=nodes[id];
		if(depth>64) return false;
		if(!depends(at(id),0)||q.op==BoundOp.variable) return true;
		if(q.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(q.data));
		if(op.op==Op.mask){
			if(depends(at(q.a),0)){
				auto predicate=scalarBody(at(q.a),arg); Rational[] points;
				if(predicate==Term.init||!integralCutPoints(arena,predicate,arg,points)) return false;
				cuts~=points;
			}
			return gridCuts(q.b,arg,cuts,depth+1);
		}
		if(op.op==Op.add||op.op==Op.mul) return gridCuts(q.a,arg,cuts,depth+1)&&gridCuts(q.b,arg,cuts,depth+1);
		if(op.op==Op.builtin) return op.value>=Builtin.castNZ&&op.value<=Builtin.castQR&&gridSteps(q.a,arg,cuts,depth+1);
		if(op.op==Op.abs){
			Rational slope,offset;
			if(gridKink(q.a,arg,slope,offset)){
				if(!slope.zero) cuts~=-offset/slope;
			}else{
				Rational lead; Rational[] roots;
				if(!gridFactors(q.a,arg,lead,roots)) return false;
				cuts~=roots;
			}
			return true;
		}
		return op.op==Op.pow&&op.value<=16&&gridCuts(q.a,arg,cuts,depth+1);
	}
	private bool gridValue(uint id,Rational point,out Term value){
		auto source=scalarBody(at(id),arena.real_(point)); if(source==Term.init) return false;
		auto r=simplify(arena,source); if(r.exhausted) return false;
		value=r.output; return true;
	}
	// The polynomial of an expression on the cell around a sample. A
	// false guard needs nothing of the value it masks.
	private bool gridPolynomial(uint id,Term arg,Rational sample,out Rational[] p){
		auto q=nodes[id]; Term value;
		if(!depends(at(id),0)){
			if(!gridValue(id,Rational(0),value)||!arena.isNumber(value)||!arena.number(value).im.zero) return false;
			p=[arena.number(value).re]; return true;
		}
		if(q.op==BoundOp.variable){ p=[Rational(0),Rational(1)]; return true; }
		auto op=arena.view(arena.at(q.data)); Rational[] a,b;
		if(op.op==Op.builtin){
			if(!gridValue(id,sample,value)||!arena.isNumber(value)||!arena.number(value).im.zero) return false;
			p=[arena.number(value).re]; return true;
		}
		if(op.op==Op.mask){
			if(!gridValue(q.a,sample,value)||arena.view(value).op!=Op.boolLit) return false;
			if(value==arena.boolean(false)){ p=[]; return true; }
			return gridPolynomial(q.b,arg,sample,p);
		}
		if(op.op==Op.abs){
			Rational slope,offset;
			if(gridKink(q.a,arg,slope,offset)) p=[offset,slope];
			else if(!axisPolynomial(q.a,p)) return false;
			if(polynomialAt(p,sample)<Rational(0)) foreach(ref c;p) c=-c;
			return true;
		}
		if(!gridPolynomial(q.a,arg,sample,a)) return false;
		if(op.op==Op.pow){ p=[Rational(1)]; foreach(i;0..op.value){ p=polyProduct(p,a); if(p.length>64) return false; } }
		else{ if(!gridPolynomial(q.b,arg,sample,b)) return false; p=op.op==Op.add?polySum(a,b):polyProduct(a,b); }
		if(p.length>64) return false;
		foreach(c;p) if(c.words>128) return false;
		return true;
	}
	// A polynomial in the innermost variable. Smooth slope proofs can also replay
	// closed coefficient calculations (for example, a parsed negative product).
	private bool axisPolynomial(uint id,out Rational[] p,uint depth=0,bool calculated=false){
		if(depth>64) return false;
		auto q=nodes[id];
		if(q.op==BoundOp.scalar){
			auto leaf=arena.at(q.data);
			if(arena.sort(leaf)!=Sort.real_) return false;
			if(arena.isNumber(leaf)){
				p=[arena.number(leaf).re]; return arena.number(leaf).im.zero;
			}
			Rational c; Term term;
			if(!calculated||!closedRational(at(id),c,term)) return false;
			p=[c]; return true;
		}
		if(q.op==BoundOp.variable){ p=[Rational(0),Rational(1)]; return q.data==0; }
		if(q.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(q.data)); Rational[] a,b;
		if(op.op!=Op.add&&op.op!=Op.mul&&op.op!=Op.pow||!axisPolynomial(q.a,a,depth+1,calculated)) return false;
		if(op.op==Op.pow){
			if(op.value>16) return false;
			p=[Rational(1)]; foreach(i;0..op.value){ p=polyProduct(p,a); if(p.length>64) return false; }
		}else{
			if(!axisPolynomial(q.b,b,depth+1,calculated)) return false;
			p=op.op==Op.add?polySum(a,b):polyProduct(a,b);
		}
		if(p.length>64) return false;
		foreach(c;p) if(c.words>128) return false;
		return true;
	}
	// Build an ordinary scalar polynomial in the innermost real variable.
	private BoundTerm coordinatePolynomial(Scope inner,Rational[] coefficients){
		auto zero=arena.real_(0),x=variable(inner,0);
		BoundTerm sum;
		foreach(k,c;coefficients){
			if(c.zero) continue;
			auto term=scalar(inner,arena.real_(c));
			if(k){
				auto power=k==1?x:primitive(arena.pow(zero,cast(uint)k),[x]);
				term=c==Rational(1)?power:primitive(arena.mul(zero,zero,true),[term,power]);
			}
			sum=sum==BoundTerm.init?term:primitive(arena.add(zero,zero,true),[sum,term]);
		}
		return sum==BoundTerm.init?scalar(inner,zero):sum;
	}

	// Sign information is conditional on definedness. Both globally smooth
	// coordinates and continuous polynomial grids supply totality separately.
	private final class CoordinateBounds{
		@safe:
		enum ns="Distribution.GraphFibre.Coordinates.Grid.";
		SourceCertificates cert;
		bool calculatedConstants;
		this(SourceCertificates c,bool calculated=false){cert=c;calculatedConstants=calculated;}
		enum Sign { unknown, nonnegative, positive }
		struct Evidence { Sign sign; string proof; }
		Evidence[uint] signs;
		Sign centeredSign(uint id,bool negative,out Rational center){
			Rational[] p;
			if(!axisPolynomial(id,p,0,true)) return Sign.unknown;
			while(p.length&&p[$-1].zero) p=p[0..$-1];
			if(negative) foreach(ref c;p) c=-c;
			if(p.length<3||p.length>17||p.length%2==0||p[$-1]<Rational(0)) return Sign.unknown;
			// This translation cancels the coefficient immediately below the leading term.
			center=-p[$-2]/(Rational(cast(long)(p.length-1))*p[$-1]);
			if(center.words>128) return Sign.unknown;
			auto shifted=polyTranslate(p,center);
			foreach(i,c;shifted) if(c.words>128||(i%2?!c.zero:c<Rational(0))) return Sign.unknown;
			return shifted[0].zero?Sign.nonnegative:Sign.positive;
		}
		Evidence centered(uint id,Sign known){
			Rational center; auto sign=centeredSign(id,false,center);
			if(sign<=known) return Evidence.init;
			Evidence e=Evidence(sign);
			if(cert !is null){
				auto source=cert.piece(id,cert.everywhere,"",Rational(0)),strict=sign==Sign.positive?"true ":"false ";
				e.proof=cert.save(ns~"Lower "~strict~cert.functionAt(id),
					"("~ns~"Lower.centered "~strict~cert.q(center)~" "~source.proof~" rfl)");
			}
			return e;
		}

		Evidence lower(uint id,uint depth){
			if(depth>64) return Evidence.init;
			if(auto hit=id in signs) return *hit;
			signs[id]=Evidence.init;
			auto n=nodes[id];
			Evidence e;
			string law,args;
			if(n.op==BoundOp.scalar){
				auto t=arena.at(n.data); Rational q; Term term;
				if(arena.sort(t)!=Sort.real_) return e;
				if(arena.isNumber(t)) q=arena.number(t).re;
				else if(!calculatedConstants||!closedRational(at(id),q,term)) return e;
				if(q<Rational(0)) return e;
				e.sign=q.zero?Sign.nonnegative:Sign.positive;
				if(cert !is null){
					auto v=cert.q(q),strict=q.zero?"false":"true";
					law="constant"; args=strict~" "~cert.atPoint(id,Rational(0))~" "~v~" (of_decide_eq_true rfl) "~cert.numericProof(id,Rational(0),v);
				}
			}else if(n.op==BoundOp.primitive){
				auto op=arena.view(arena.at(n.data));
				if(op.op==Op.builtin&&(op.value==Builtin.expR||op.value==Builtin.coshR)){
					e.sign=Sign.positive; law=op.value==Builtin.expR?"exp":"cosh";
					if(cert !is null) args=cert.functionAt(n.a);
				}else if(op.op==Op.mask){
					auto a=lower(n.b,depth+1);
					if(a.sign!=Sign.unknown){
						e.sign=Sign.nonnegative; law="mask";
						if(cert !is null) args=cert.functionAt(n.a)~" "~a.proof;
					}
				}else if(op.op==Op.abs){
					e.sign=Sign.nonnegative; law="abs";
					if(cert !is null) args=cert.functionAt(n.a);
				}else if(op.op==Op.add||op.op==Op.mul){
					auto a=lower(n.a,depth+1),b=lower(n.b,depth+1);
					if(a.sign!=Sign.unknown&&b.sign!=Sign.unknown){
						bool pos=op.op==Op.add?a.sign==Sign.positive||b.sign==Sign.positive:a.sign==Sign.positive&&b.sign==Sign.positive;
						e.sign=pos?Sign.positive:Sign.nonnegative;law=op.op==Op.add?"add":"mul";
						if(cert !is null) args=a.proof~" "~b.proof;
					}
				}else if(op.op==Op.pow){
					auto a=lower(n.a,depth+1);
					if(a.sign!=Sign.unknown){
						law="pow";e.sign=a.sign;
						if(cert !is null) args=to!string(op.value)~" "~a.proof;
					}else if(op.value%2==0){
						law="evenPow";e.sign=Sign.nonnegative;
						if(cert !is null) args=cert.functionAt(n.a)~" "~to!string(op.value)~" rfl";
					}
				}else if(op.op==Op.inv||op.op==Op.builtin&&op.value==Builtin.sqrtR){
					auto a=lower(n.a,depth+1);
					if(a.sign==Sign.positive){
						e.sign=Sign.positive;law=op.op==Op.inv?"inv":"sqrt";
						if(cert !is null) args=a.proof;
					}
				}
			}
			if(n.op==BoundOp.primitive&&e.sign!=Sign.positive){
				auto polynomial=centered(id,e.sign);
				if(polynomial.sign!=Sign.unknown) return signs[id]=polynomial;
			}
			if(cert !is null&&e.sign!=Sign.unknown){
				auto strict=e.sign==Sign.positive?"true ":"false ";
				e.proof=cert.save(ns~"Lower "~strict~cert.functionAt(id),"("~ns~"Lower."~law~" "~args~")");
			}
			return signs[id]=e;
		}
		struct NonzeroWitness { bool found; string proof; }
		NonzeroWitness[uint] exclusions;
		NonzeroWitness nonzero(uint id,uint depth){
			if(depth>64) return NonzeroWitness.init;
			if(auto cached=id in exclusions) return *cached;
			NonzeroWitness evidence;
			auto n=nodes[id],sign=lower(id,depth);
			string law,args;
			if(sign.sign==Sign.positive){law="positive";args=sign.proof;}
			else if(n.op==BoundOp.scalar){
				Rational q; Term value;
				if(closedRational(at(id),q,value)&&!q.zero){
					law="literal";
					if(cert !is null) args=cert.atPoint(id,Rational(0))~" "~cert.q(q)~" "~cert.numericProof(id,Rational(0),cert.q(q))~" (of_decide_eq_true rfl)";
				}
			}else if(n.op==BoundOp.primitive){
				auto op=arena.view(arena.at(n.data));
				if(op.op==Op.inv){law="inv";if(cert !is null) args=cert.functionAt(n.a);}
				else if(op.op==Op.mul){
					auto a=nonzero(n.a,depth+1),b=nonzero(n.b,depth+1);
					if(a.found&&b.found){law="mul";if(cert !is null) args=a.proof~" "~b.proof;}
				}else if(op.op==Op.pow){
					auto a=nonzero(n.a,depth+1);
					if(a.found){law="pow";if(cert !is null) args=to!string(op.value)~" "~a.proof;}
				}
				Rational center;
				if(!law.length&&centeredSign(id,true,center)==Sign.positive){
					law="centeredNegative";
					if(cert !is null) args=cert.q(center)~" "~cert.piece(id,cert.everywhere,"",Rational(0)).proof~" rfl";
				}
			}
			evidence.found=law.length!=0;
			if(cert !is null&&evidence.found) evidence.proof=cert.save(ns~"Nonzero "~cert.functionAt(id),"("~ns~"Nonzero."~law~" "~args~")");
			return exclusions[id]=evidence;
		}
	}
	// Iverson masks can introduce jumps even if their scalar simplification
	// no longer has the polynomial form used to certify the source grid.
	private bool hasMask(uint id){
		auto n=nodes[id];
		if(n.op!=BoundOp.primitive) return false;
		if(arena.view(arena.at(n.data)).op==Op.mask) return true;
		return n.a!=uint.max&&hasMask(n.a)||n.b!=uint.max&&hasMask(n.b);
	}
	private CoordinateChange gridChange(uint id){
		auto n=nodes[id];
		if(n.op!=BoundOp.primitive) return CoordinateChange.none;
		auto op=arena.view(arena.at(n.data));
		if(op.op==Op.inv) return CoordinateChange.reciprocal;
		if(op.op!=Op.builtin) return CoordinateChange.none;
		switch(cast(Builtin)op.value){
			case Builtin.expR:return CoordinateChange.exp;
			case Builtin.sinhR:return CoordinateChange.sinh;
			case Builtin.asinhR:return CoordinateChange.arsinh;
			case Builtin.logR:return CoordinateChange.log;
			case Builtin.sqrtR:return CoordinateChange.sqrt;
			default:return CoordinateChange.none;
		}
	}
	private bool admitsTrace(CoordinateChange change,Rational r){
		if(change==CoordinateChange.log||change==CoordinateChange.sqrt) return Rational(0)<r;
		return change!=CoordinateChange.reciprocal||!r.zero;
	}
	// The scalar simplifier proposes a square root. Exact rational
	// arithmetic checks its magnitude and sign before choosing an atom.
	private bool rationalImage(CoordinateChange change,Rational v,out Rational result){
		if(change==CoordinateChange.reciprocal){
			if(v.zero) return false;
			result=Rational(1)/v;
			return true;
		}
		if(change!=CoordinateChange.sqrt) return false;
		auto root=simplify(arena,arena.call(Builtin.sqrtR,[arena.real_(v)]));
		if(root.exhausted||!arena.isNumber(root.output)) return false;
		result=arena.number(root.output).re;
		return result>=Rational(0)&&result*result==v;
	}
	private bool gridChangeRange(CoordinateChange change,uint input,out string proof,SourceCertificates cert=null,bool calculated=false){
		final switch(change){
			case CoordinateChange.none:return false;
			case CoordinateChange.log:case CoordinateChange.sqrt:
				auto h=(new CoordinateBounds(cert,calculated)).lower(input,0);
				proof=h.proof; return h.sign==CoordinateBounds.Sign.positive;
			case CoordinateChange.reciprocal:
				auto h=(new CoordinateBounds(cert,calculated)).nonzero(input,0);
				proof=h.proof; return h.found;
			case CoordinateChange.exp:case CoordinateChange.sinh:case CoordinateChange.arsinh:
				if(cert !is null) proof="(Distribution.GraphFibre.Coordinates.Grid.SourceIn.univ "~cert.functionAt(input)~")";
				return true;
		}
	}
	// The inner grid supplies |f′|. Multiply it by the outer magnitude.
	private BoundTerm gridChangeJacobian(CoordinateChange change,BoundTerm f){
		auto zero=arena.real_(0),ctx=context(f);
		BoundTerm call(Builtin b,BoundTerm v){return primitive(arena.call(b,[zero]),[v]);}
		BoundTerm den;
		final switch(change){
			case CoordinateChange.none:assert(0);
			case CoordinateChange.exp:return call(Builtin.expR,f);
			case CoordinateChange.sinh:return call(Builtin.coshR,f);
			case CoordinateChange.log:den=f; break;
			case CoordinateChange.sqrt:
				den=primitive(arena.mul(zero,zero,true),[scalar(ctx,arena.real_(2)),call(Builtin.sqrtR,f)]);
				break;
			case CoordinateChange.reciprocal:case CoordinateChange.arsinh:
				den=primitive(arena.pow(zero,2),[f]);
				if(change==CoordinateChange.arsinh)
					den=call(Builtin.sqrtR,primitive(arena.add(zero,zero,true),[scalar(ctx,arena.real_(1)),den]));
				break;
		}
		return primitive(arena.inv(zero),[den]);
	}

	// Construct a signed derivative. Replay the identical traversal when
	// emitting evidence so every accepted operation has a checked chain rule.
	private BoundTerm smoothSlope(BoundTerm body,out string witness,SourceCertificates cert=null){
		enum ns="Distribution.GraphFibre.Coordinates.Grid.";
		auto zero=arena.real_(0),sum=arena.add(zero,zero,true),product=arena.mul(zero,zero,true);
		Table!(uint,uint) slopes; Table!(uint,string) proofs;
		auto bounds=new CoordinateBounds(cert);
		BoundTerm visit(uint id,uint depth){
			if(depth>64) return BoundTerm.init;
			if(slopes.contains(id)) return at(slopes.get(id,uint.max));
			auto n=nodes[id],f=at(id),inner=context(f);
			BoundTerm d; string lemma,args;
			Rational[] polynomial;
			if(axisPolynomial(id,polynomial,0,true)){
				d=coordinatePolynomial(inner,derivativeCoefficients(polynomial));
				if(cert !is null){
					auto a=cert.piece(id,cert.everywhere,"",Rational(0));
					auto b=cert.piece(d.id,cert.everywhere,"",Rational(0));
					lemma="polynomial"; args=a.proof~" "~b.proof~" rfl";
				}
			}else{
				if(n.op!=BoundOp.primitive) return BoundTerm.init;
				auto op=arena.view(arena.at(n.data));
				if(op.op!=Op.add&&op.op!=Op.mul&&op.op!=Op.builtin&&op.op!=Op.pow&&op.op!=Op.inv) return BoundTerm.init;
				Builtin outer;
				if(op.op==Op.builtin){
					switch(op.value){
						case Builtin.logR: lemma="log"; break;
						case Builtin.sqrtR: lemma="sqrt"; break;
						case Builtin.expR: outer=Builtin.expR; lemma="exp"; break;
						case Builtin.sinR: outer=Builtin.cosR; lemma="sin"; break;
						case Builtin.cosR: outer=Builtin.sinR; lemma="cos"; break;
						case Builtin.sinhR: outer=Builtin.coshR; lemma="sinh"; break;
						case Builtin.coshR: outer=Builtin.sinhR; lemma="cosh"; break;
						default:return BoundTerm.init;
					}
				}
				auto du=visit(n.a,depth+1);
				if(du==BoundTerm.init) return BoundTerm.init;
				if(cert !is null) args=proofs.get(n.a,"");
				if(op.op==Op.inv||op.op==Op.builtin&&(op.value==Builtin.logR||op.value==Builtin.sqrtR)){
					auto sign=bounds.lower(n.a,depth+1);
					if(sign.sign==CoordinateBounds.Sign.positive){
						if(cert !is null) args~=" "~sign.proof;
					}else{
						if(op.op!=Op.inv) return BoundTerm.init;
						auto evidence=bounds.nonzero(n.a,depth+1);
						if(!evidence.found) return BoundTerm.init;
						if(cert !is null) args~=" "~evidence.proof;
					}
					auto denominator=at(n.a);
					if(op.op==Op.inv){
						lemma=sign.sign==CoordinateBounds.Sign.positive?"inv":"inv_nonzero";
						denominator=primitive(arena.pow(zero,2),[denominator]);
					}else if(op.value==Builtin.sqrtR){
						denominator=primitive(product,[scalar(inner,arena.real_(2)),f]);
					}
					auto outerSlope=primitive(arena.inv(zero),[denominator]);
					if(op.op==Op.inv) outerSlope=primitive(product,[scalar(inner,arena.real_(-1)),outerSlope]);
					d=primitive(product,[outerSlope,du]);
				}else if(op.op==Op.builtin){
					auto outerSlope=primitive(arena.call(outer,[zero]),[at(n.a)]);
					if(op.value==Builtin.cosR) outerSlope=primitive(product,[scalar(inner,arena.real_(-1)),outerSlope]);
					d=primitive(product,[outerSlope,du]);
				}else if(op.op==Op.pow){
					lemma="pow"; args=to!string(op.value)~" "~args;
					auto power=primitive(arena.pow(zero,op.value?cast(uint)op.value-1:0),[at(n.a)]);
					d=primitive(product,[primitive(product,[scalar(inner,arena.real_(op.value)),power]),du]);
				}else{
					auto dv=visit(n.b,depth+1);
					if(dv==BoundTerm.init) return BoundTerm.init;
					if(cert !is null) args~=" "~proofs.get(n.b,"");
					if(op.op==Op.add){ lemma="add"; d=primitive(sum,[du,dv]); }
					else{ lemma="mul"; d=primitive(sum,[primitive(product,[du,at(n.b)]),primitive(product,[at(n.a),dv])]); }
				}
			}
			slopes.set(id,d.id);
			if(cert !is null){
				cert.roots~=d.id;
				proofs.set(id,cert.save(ns~"Slope "~cert.functionAt(id)~" "~cert.functionAt(d.id),
					"("~ns~"Slope."~lemma~" "~args~")"));
			}
			return d;
		}
		auto d=visit(body.id,0);
		if(cert !is null&&d!=BoundTerm.init) witness=proofs.get(body.id,"");
		return d;
	}
	// A polynomial in the innermost variable over a power of it: sums and
	// products of polynomials and of inverses of monomials. With the power
	// zero it is a polynomial. With a `pole` the monomials are powers of the
	// variable minus the pole, and the polynomial is one in that difference.
	private bool axisRatio(uint id,out Rational[] p,out size_t power,Rational pole=Rational(0),uint depth=0){
		if(depth>64) return false;
		if(axisPolynomial(id,p)){ p=polyTranslate(p,pole); foreach(c;p) if(c.words>128) return false; return true; }
		auto q=nodes[id];
		if(q.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(q.data));
		if(op.op==Op.inv){
			Rational[] m; if(!axisPolynomial(q.a,m)) return false;
			m=polyTranslate(m,pole);
			while(m.length&&m[$-1].zero) m.length=m.length-1;
			if(m.length<2) return false;
			foreach(c;m[0..$-1]) if(!c.zero) return false;
			p=[Rational(1)/m[$-1]]; power=m.length-1; return p[0].words<=128;
		}
		if(op.op!=Op.add&&op.op!=Op.mul) return false;
		Rational[] a,b; size_t n,m;
		if(!axisRatio(q.a,a,n,pole,depth+1)||!axisRatio(q.b,b,m,pole,depth+1)) return false;
		static Rational[] shift(Rational[] x,size_t k){ Rational[] r; foreach(i;0..k) r~=Rational(0); return r~x; }
		if(op.op==Op.mul){ p=polyProduct(a,b); power=n+m; }
		else if(n&&m){ p=polySum(shift(a,m),shift(b,n)); power=n+m; }
		else if(n){ p=polySum(a,shift(b,n)); power=n; }
		else{ p=polySum(shift(a,m),b); power=m; }
		if(p.length>64||power>32) return false;
		foreach(c;p) if(c.words>128) return false;
		return true;
	}
	// A product of such quotients and of factors that do not mention the
	// innermost variable: the quotient, and those factors in their order,
	// with `uint.max` for the product of the last two.
	private bool axisFraction(uint id,out Rational[] p,out size_t power,ref uint[] scale,Rational pole=Rational(0),uint depth=0){
		if(depth>64) return false;
		if(axisRatio(id,p,power,pole)) return true;
		if(!depends(at(id),0)){ p=[Rational(1)]; scale~=id; return true; }
		auto q=nodes[id];
		if(q.op!=BoundOp.primitive||arena.view(arena.at(q.data)).op!=Op.mul) return false;
		Rational[] a,b; size_t n,m; auto before=scale.length;
		if(!axisFraction(q.a,a,n,scale,pole,depth+1)) return false;
		auto middle=scale.length;
		if(!axisFraction(q.b,b,m,scale,pole,depth+1)) return false;
		if(middle>before&&scale.length>middle) scale~=uint.max;
		p=polyProduct(a,b); power=n+m;
		if(p.length>64||power>32) return false;
		foreach(c;p) if(c.words>128) return false;
		return true;
	}
	// The pole of the first inverse of a polynomial in the innermost
	// variable in such a product or sum: where a power of a linear
	// polynomial has its root.
	private bool axisPole(uint id,out Rational pole,uint depth=0){
		if(depth>64||!depends(at(id),0)) return false;
		auto q=nodes[id];
		if(q.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(q.data));
		if(op.op==Op.inv){
			Rational[] m; if(!axisPolynomial(q.a,m)) return false;
			while(m.length&&m[$-1].zero) m.length=m.length-1;
			if(m.length<2) return false;
			pole=Rational(0)-m[$-2]/(Rational(cast(long)m.length-1)*m[$-1]);
			return pole.words<=128;
		}
		if(op.op!=Op.add&&op.op!=Op.mul) return false;
		return axisPole(q.a,pole,depth+1)||axisPole(q.b,pole,depth+1);
	}
	// The argument of a logarithm: the innermost variable, or its sum with
	// a closed term, which is minus the pole, in either order.
	private bool logArgument(uint id,out Rational pole,out uint closedTerm){
		auto v=nodes[id]; closedTerm=uint.max;
		bool variable_(uint i){ auto x=nodes[i]; return x.op==BoundOp.variable&&x.data==0; }
		if(variable_(id)){ pole=Rational(0); return true; }
		if(v.op!=BoundOp.primitive||arena.view(arena.at(v.data)).op!=Op.add) return false;
		auto other=variable_(v.a)?v.b:variable_(v.b)?v.a:uint.max; Rational c; Term closed;
		if(other==uint.max||nodes[other].op!=BoundOp.scalar||!closedRational(at(other),c,closed)||c.zero) return false;
		pole=Rational(0)-c; closedTerm=other; return pole.words<=128;
	}
	// The pole of the first logarithm in a sum or product.
	private bool axisLogPole(uint id,out Rational pole,uint depth=0){
		if(depth>64||!depends(at(id),0)) return false;
		auto q=nodes[id];
		if(q.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(q.data));
		if(op.op==Op.builtin){ uint closedTerm; return op.value==Builtin.logR&&logArgument(q.a,pole,closedTerm); }
		if(op.op!=Op.add&&op.op!=Op.mul) return false;
		return axisLogPole(q.a,pole,depth+1)||axisLogPole(q.b,pole,depth+1);
	}
	// A polynomial `p` times the logarithm of the innermost variable minus
	// the pole, plus a polynomial `q`: sums and products of polynomials and
	// of that logarithm in which no two logarithms are multiplied. Both
	// polynomials are in the variable minus the pole. `found` says that
	// there is a logarithm.
	private bool axisLogarithm(uint id,out Rational[] p,out Rational[] q,Rational pole,out bool found,uint depth=0){
		if(depth>64) return false;
		bool small(Rational[] x){ if(x.length>64) return false; foreach(c;x) if(c.words>128) return false; return true; }
		if(axisPolynomial(id,q)){ q=polyTranslate(q,pole); return small(q); }
		auto n=nodes[id];
		if(n.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(n.data));
		if(op.op==Op.builtin){
			Rational at_; uint closedTerm;
			if(op.value!=Builtin.logR||!logArgument(n.a,at_,closedTerm)||!(at_==pole)) return false;
			p=[Rational(1)]; q=[]; found=true; return true;
		}
		if(op.op!=Op.add&&op.op!=Op.mul) return false;
		Rational[] p1,q1,p2,q2; bool f1,f2;
		if(!axisLogarithm(n.a,p1,q1,pole,f1,depth+1)||!axisLogarithm(n.b,p2,q2,pole,f2,depth+1)) return false;
		found=f1||f2;
		if(op.op==Op.add){ p=polySum(p1,p2); q=polySum(q1,q2); }
		else if(f1&&f2) return false;
		else if(f1){ p=polyProduct(p1,q2); q=polyProduct(q1,q2); }
		else{ p=polyProduct(q1,p2); q=polyProduct(q1,q2); }
		return small(p)&&small(q);
	}
	// A product of such a value and of factors that do not mention the
	// innermost variable, in which the logarithm meets polynomials and those
	// factors only: the value, and the factors in their order, with
	// `uint.max` for the product of the last two.
	private bool axisLogFraction(uint id,out Rational[] p,out Rational[] q,Rational pole,out bool found,ref uint[] scale,uint depth=0){
		if(depth>64) return false;
		if(axisLogarithm(id,p,q,pole,found)) return true;
		if(!depends(at(id),0)){ p=[]; q=[Rational(1)]; found=false; scale~=id; return true; }
		auto n=nodes[id];
		if(n.op!=BoundOp.primitive||arena.view(arena.at(n.data)).op!=Op.mul) return false;
		Rational[] p1,q1,p2,q2; bool f1,f2; auto before=scale.length;
		if(!axisLogFraction(n.a,p1,q1,pole,f1,scale,depth+1)) return false;
		auto middle=scale.length;
		if(!axisLogFraction(n.b,p2,q2,pole,f2,scale,depth+1)) return false;
		if(middle>before&&scale.length>middle) scale~=uint.max;
		if(f1&&f2) return false;
		found=f1||f2;
		if(f1){ p=polyProduct(p1,q2); q=polyProduct(q1,q2); }
		else{ p=polyProduct(q1,p2); q=polyProduct(q1,q2); }
		if(p.length>64||q.length>64) return false;
		foreach(c;p~q) if(c.words>128) return false;
		return true;
	}
	// A polynomial in the innermost variable times the exponential of a
	// rational multiple of it. A rate of zero is a polynomial.
	private bool axisExponential(uint id,out Rational[] p,out Rational rate,uint depth=0){
		if(depth>64) return false;
		if(axisPolynomial(id,p)) return true;
		auto q=nodes[id]; if(q.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(q.data));
		if(op.op==Op.builtin&&op.value==Builtin.expR){
			auto arg=arena.variable(Sort.real_,freshScalarIndex(q.a)),inside=scalarBody(at(q.a),arg); Rational offset;
			if(inside==Term.init||!integralAffine(arena,inside,arg,rate,offset)||!offset.zero||rate.words>128) return false;
			p=[Rational(1)]; return true;
		}
		if(op.op!=Op.mul) return false;
		Rational[] a,b; Rational r,t;
		if(!axisExponential(q.a,a,r,depth+1)||!axisExponential(q.b,b,t,depth+1)) return false;
		p=polyProduct(a,b); rate=r+t;
		if(p.length>64||rate.words>128) return false;
		foreach(c;p) if(c.words>128) return false;
		return true;
	}
	// The exponential of a polynomial of degree one in the innermost
	// variable with a rational slope and a constant coefficient that does not
	// mention the variable: `exp(c + r·x) = exp(c)·exp(r·x)`. The slope, and
	// that coefficient outside the binder once the rule builds it.
	private bool offsetExponential(uint id,out Rational rate,out BoundTerm offset,bool build){
		auto n=nodes[id]; if(n.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(n.data)); AxisCoefficient[3] c;
		if(op.op!=Op.builtin||op.value!=Builtin.expR||!axisQuadratic(n.a,c,false)) return false;
		if(c[2].present||!c[1].present||!c[1].closed||!c[0].present||c[1].value.words>128) return false;
		rate=c[1].value;
		if(build){ axisQuadratic(n.a,c,true); offset=c[0].term; }
		return true;
	}
	// The same up to degree two: `exp(c + q(x)) = exp(c)·exp(q(x))` for a
	// polynomial `q` without a constant whose coefficients are rational.
	private bool curveOffset(uint id,out Rational[] exponent,out BoundTerm offset,bool build){
		auto n=nodes[id]; if(n.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(n.data)); AxisCoefficient[3] c;
		if(op.op!=Op.builtin||op.value!=Builtin.expR||!axisQuadratic(n.a,c,false)) return false;
		if(!c[0].present||!c[1].present&&!c[2].present) return false;
		foreach(x;c[1..$]) if(x.present&&(!x.closed||x.value.words>128)) return false;
		exponent=[Rational(0),c[1].present?c[1].value:Rational(0),c[2].present?c[2].value:Rational(0)];
		if(build){ axisQuadratic(n.a,c,true); offset=c[0].term; }
		return true;
	}
	// A product of such factors and of factors that do not mention the
	// innermost variable; these are the scale of the term, with the constant
	// part of an exponential.
	private bool scaledExponential(uint id,out Rational[] p,out Rational rate,out bool scaled,uint depth=0){
		if(depth>16) return false;
		if(axisExponential(id,p,rate)) return true;
		if(!depends(at(id),0)){ scaled=true; p=[Rational(1)]; return true; }
		BoundTerm offset;
		if(offsetExponential(id,rate,offset,false)){ scaled=true; p=[Rational(1)]; return true; }
		auto q=nodes[id];
		if(q.op!=BoundOp.primitive||arena.view(arena.at(q.data)).op!=Op.mul) return false;
		Rational[] a,b; Rational r,t; bool left,right;
		if(!scaledExponential(q.a,a,r,left,depth+1)||!scaledExponential(q.b,b,t,right,depth+1)) return false;
		p=polyProduct(a,b); rate=r+t; scaled=left||right;
		if(p.length>64||rate.words>128) return false;
		foreach(c;p) if(c.words>128) return false;
		return true;
	}
	// The scale of such a product outside the binder of the axis.
	private BoundTerm exponentialScale(uint id){
		Rational[] p; Rational rate; BoundTerm offset;
		if(axisExponential(id,p,rate)) return BoundTerm.init;
		if(!depends(at(id),0)) return dropIndex(at(id));
		if(offsetExponential(id,rate,offset,true)) return primitive(arena.call(Builtin.expR,[arena.real_(0)]),[offset]);
		auto q=nodes[id],left=exponentialScale(q.a),right=exponentialScale(q.b);
		if(left==BoundTerm.init) return right;
		if(right==BoundTerm.init) return left;
		return primitive(arena.mul(arena.real_(1),arena.real_(1),true),[left,right]);
	}
	// A closed piecewise polynomial of the innermost variable is a polynomial
	// beyond its last cut: that cut and the coefficients on that side.
	private bool tailPolynomial(uint id,bool bottom,out Rational cut,out Rational[] p){
		if(!gridNumerical(id)) return false;
		auto arg=arena.variable(Sort.real_,freshScalarIndex(id)); Rational[] cuts;
		if(!gridCuts(id,arg,cuts)||cuts.length>64) return false;
		foreach(i,point;cuts) if(!i||(point<cut)==bottom) cut=point;
		auto sample=bottom?cut-Rational(1):cut+Rational(1);
		return sample.words<=128&&gridPolynomial(id,arg,sample,p);
	}
	// A factor of a polynomial times the exponential of a polynomial, taken
	// at one end: a polynomial, the exponential of one, or a closed piecewise
	// polynomial beyond its last cut.
	private enum TailFactor:ubyte{ none,polynomial,exponential,piece }
	private TailFactor tailFactor(uint id,bool bottom,out Rational[] p,out Rational[] exponent,out Rational cut,bool pieces=true){
		if(axisPolynomial(id,p)) return TailFactor.polynomial;
		auto n=nodes[id];
		if(n.op==BoundOp.primitive){
			auto op=arena.view(arena.at(n.data));
			if(op.op==Op.builtin&&op.value==Builtin.expR&&axisPolynomial(n.a,exponent)){ p=[Rational(1)]; return TailFactor.exponential; }
		}
		return pieces&&tailPolynomial(id,bottom,cut,p)?TailFactor.piece:TailFactor.none;
	}
	// A product of such factors and of factors that do not mention the
	// variable, which are its scale: the polynomial and the exponent. Without
	// `pieces` every factor is what it is on the whole line. With `offsets`
	// the constant part of an exponent of degree at most two may be a term
	// that does not mention the variable: its exponential is a scale.
	private bool tailExponential(uint id,bool bottom,out Rational[] p,out Rational[] exponent,out bool scaled,bool pieces=true,uint depth=0,bool offsets=false){
		if(depth>16) return false;
		Rational cut;
		if(tailFactor(id,bottom,p,exponent,cut,pieces)!=TailFactor.none) return true;
		if(!depends(at(id),0)){ scaled=true; p=[Rational(1)]; return true; }
		Rational rate; BoundTerm offset;
		if(pieces&&offsetExponential(id,rate,offset,false)){ scaled=true; p=[Rational(1)]; exponent=[Rational(0),rate]; return true; }
		if(offsets&&curveOffset(id,exponent,offset,false)){ scaled=true; p=[Rational(1)]; return true; }
		auto q=nodes[id];
		if(q.op!=BoundOp.primitive||arena.view(arena.at(q.data)).op!=Op.mul) return false;
		Rational[] a,b,r,t; bool left,right;
		if(!tailExponential(q.a,bottom,a,r,left,pieces,depth+1,offsets)||!tailExponential(q.b,bottom,b,t,right,pieces,depth+1,offsets)) return false;
		p=polyProduct(a,b); exponent=polySum(r,t); scaled=left||right;
		if(p.length>64||exponent.length>64) return false;
		foreach(c;p~exponent) if(c.words>128) return false;
		return true;
	}
	// The scale of such a product outside the binder of the variable.
	private BoundTerm tailScale(uint id,bool bottom,bool pieces=true,bool offsets=false){
		Rational[] p,exponent; Rational cut,rate; BoundTerm offset;
		if(tailFactor(id,bottom,p,exponent,cut,pieces)!=TailFactor.none) return BoundTerm.init;
		if(!depends(at(id),0)) return dropIndex(at(id));
		if(pieces&&offsetExponential(id,rate,offset,true)||offsets&&curveOffset(id,exponent,offset,true)) return primitive(arena.call(Builtin.expR,[arena.real_(0)]),[offset]);
		auto q=nodes[id],left=tailScale(q.a,bottom,pieces,offsets),right=tailScale(q.b,bottom,pieces,offsets);
		if(left==BoundTerm.init) return right;
		if(right==BoundTerm.init) return left;
		return primitive(arena.mul(arena.real_(1),arena.real_(1),true),[left,right]);
	}
	// The rational value of a closed term made of real literals by sums,
	// products and powers.
	private bool closedValue(uint id,out Rational q,uint depth=0){
		if(depth>32) return false;
		auto n=nodes[id];
		if(n.op==BoundOp.scalar){
			auto leaf=arena.at(n.data);
			if(!arena.isNumber(leaf)||arena.sort(leaf)!=Sort.real_||!arena.number(leaf).im.zero) return false;
			q=arena.number(leaf).re; return true;
		}
		if(n.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(n.data)); Rational a,b;
		if(op.op!=Op.add&&op.op!=Op.mul&&op.op!=Op.pow||!closedValue(n.a,a,depth+1)) return false;
		if(op.op==Op.pow){
			if(op.value>16) return false;
			q=Rational(1); foreach(i;0..op.value){ q=q*a; if(q.words>128) return false; }
		}else{
			if(!closedValue(n.b,b,depth+1)) return false;
			q=op.op==Op.add?a+b:a*b;
		}
		return q.words<=128;
	}
	// A coefficient of a polynomial in the innermost variable that does not
	// mention it: absent, or a term outside the binder, with its value where
	// that is a closed rational. Terms exist only once the rule builds them.
	private struct AxisCoefficient{ bool present,closed; Rational value; BoundTerm term; }
	private AxisCoefficient coefficientSum(AxisCoefficient a,AxisCoefficient b,bool build){
		if(!a.present) return b;
		if(!b.present) return a;
		AxisCoefficient r; r.present=true; r.closed=a.closed&&b.closed;
		if(r.closed) r.value=a.value+b.value;
		if(build) r.term=primitive(arena.add(arena.real_(0),arena.real_(0),true),[a.term,b.term]);
		return r;
	}
	private AxisCoefficient coefficientProduct(AxisCoefficient a,AxisCoefficient b,bool build){
		AxisCoefficient r; if(!a.present||!b.present) return r;
		r.present=true; r.closed=a.closed&&b.closed;
		if(r.closed) r.value=a.value*b.value;
		if(build) r.term=primitive(arena.mul(arena.real_(1),arena.real_(1),true),[a.term,b.term]);
		return r;
	}
	private static size_t coefficientDegree(AxisCoefficient[3] c){ return c[2].present?2:c[1].present?1:0; }
	// The coefficient of the variable itself: a literal one outside its binder.
	private BoundTerm unitCoefficient(uint variable){ return scalar(Scope(this,contexts[nodes[variable].context].parent),arena.real_(1)); }
	// A polynomial of degree at most two in the innermost variable whose
	// coefficients do not mention it, by its structure: sums, products with
	// a factor free of the variable, and products and squares of polynomials
	// of degree one. A coefficient is a sum of products of the parts that
	// are free of the variable, in the order of the certificate lemmas.
	private bool axisQuadratic(uint id,out AxisCoefficient[3] c,bool build,uint depth=0){
		if(depth>32||type(at(id))!=scalarType(Sort.real_)) return false;
		auto n=nodes[id];
		if(!depends(at(id),0)){
			c[0].present=true; c[0].closed=closedValue(id,c[0].value);
			if(build) c[0].term=dropIndex(at(id));
			return true;
		}
		if(n.op==BoundOp.variable){
			c[1].present=true; c[1].closed=true; c[1].value=Rational(1);
			if(build) c[1].term=unitCoefficient(id);
			return true;
		}
		if(n.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(n.data)); AxisCoefficient[3] a,b;
		if(op.op!=Op.add&&op.op!=Op.mul&&(op.op!=Op.pow||op.value!=2)||!axisQuadratic(n.a,a,build,depth+1)) return false;
		if(op.op==Op.pow){ if(coefficientDegree(a)!=1) return false; b=a; }
		else if(!axisQuadratic(n.b,b,build,depth+1)) return false;
		auto left=coefficientDegree(a),right=coefficientDegree(b);
		if(op.op==Op.add) foreach(i;0..3) c[i]=coefficientSum(a[i],b[i],build);
		else if(op.op==Op.mul&&!left) foreach(i;0..3) c[i]=coefficientProduct(a[0],b[i],build);
		else if(op.op==Op.mul&&!right) foreach(i;0..3) c[i]=coefficientProduct(a[i],b[0],build);
		else if(left==1&&right==1){
			c[0]=coefficientProduct(a[0],b[0],build);
			c[1]=coefficientSum(coefficientProduct(a[0],b[1],build),coefficientProduct(a[1],b[0],build),build);
			c[2]=coefficientProduct(a[1],b[1],build);
		}else return false;
		foreach(x;c) if(x.closed&&x.value.words>128) return false;
		return true;
	}
	// Polynomials in the innermost variable by their coefficients, lowest
	// degree first, in the order of the certificate functions: a sum
	// coefficient by coefficient, `u + x·w`, and `(a + x·p)·q = a·q + x·(p·q)`.
	private AxisCoefficient[] symbolicSum(AxisCoefficient[] p,AxisCoefficient[] q,bool build){
		if(!p.length) return q;
		if(!q.length) return p;
		return coefficientSum(p[0],q[0],build)~symbolicSum(p[1..$],q[1..$],build);
	}
	private AxisCoefficient[] symbolicShift(AxisCoefficient[] u,AxisCoefficient[] w,bool build){
		return u.length?u[0]~symbolicSum(u[1..$],w,build):AxisCoefficient.init~w;
	}
	private AxisCoefficient[] symbolicProduct(AxisCoefficient[] p,AxisCoefficient[] q,bool build){
		if(!p.length) return [];
		AxisCoefficient[] scaled; foreach(c;q) scaled~=coefficientProduct(p[0],c,build);
		return symbolicShift(scaled,symbolicProduct(p[1..$],q,build),build);
	}
	// A polynomial in the innermost variable whose coefficients do not
	// mention it, by its structure: sums, products and powers of terms that
	// are free of the variable and of the variable itself.
	private bool axisSymbolic(uint id,out AxisCoefficient[] cs,bool build,uint depth=0){
		if(depth>32||type(at(id))!=scalarType(Sort.real_)) return false;
		auto n=nodes[id]; AxisCoefficient c; c.present=true;
		if(!depends(at(id),0)){
			c.closed=closedValue(id,c.value);
			if(build) c.term=dropIndex(at(id));
			cs=[c]; return true;
		}
		if(n.op==BoundOp.variable){
			c.closed=true; c.value=Rational(1);
			if(build) c.term=unitCoefficient(id);
			cs=[AxisCoefficient.init,c]; return true;
		}
		if(n.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(n.data)); AxisCoefficient[] a,b;
		if(op.op!=Op.add&&op.op!=Op.mul&&op.op!=Op.pow||!axisSymbolic(n.a,a,build,depth+1)) return false;
		if(op.op==Op.pow){
			if(!op.value||op.value>16) return false;
			cs=a; foreach(i;1..op.value){ cs=symbolicProduct(a,cs,build); if(cs.length>17) return false; }
		}else{
			if(!axisSymbolic(n.b,b,build,depth+1)) return false;
			cs=op.op==Op.add?symbolicSum(a,b,build):symbolicProduct(a,b,build);
		}
		if(cs.length>17) return false;
		foreach(x;cs) if(x.closed&&x.value.words>128) return false;
		return true;
	}
	// A factor of a density that is a polynomial times the exponential of
	// such a quadratic: a polynomial with rational coefficients, the
	// exponential of a quadratic, a factor free of the variable, a product
	// of these, or a polynomial with coefficients that do not mention the
	// variable.
	private enum BellFactor:ubyte{ none,polynomial,exponential,scale,product,symbolic }
	private BellFactor bellFactor(uint id,out Rational[] p){
		if(axisPolynomial(id,p)) return BellFactor.polynomial;
		auto n=nodes[id]; bool free=!depends(at(id),0);
		if(n.op!=BoundOp.primitive) return free?BellFactor.scale:BellFactor.none;
		auto op=arena.view(arena.at(n.data)); AxisCoefficient[3] c; AxisCoefficient[] cs;
		if(op.op==Op.builtin&&op.value==Builtin.expR&&axisQuadratic(n.a,c,false)) return BellFactor.exponential;
		if(free) return BellFactor.scale;
		if(op.op==Op.mul) return BellFactor.product;
		return axisSymbolic(id,cs,false)?BellFactor.symbolic:BellFactor.none;
	}
	// The parts of such a factor: its polynomials, the coefficients of its
	// exponent where it has one, and its scale outside the binder.
	private struct BellParts{ Rational[] p; AxisCoefficient[3] c; bool exponent,scaled,symbolic; BoundTerm scale; AxisCoefficient[] poly; }
	private bool bellJoin(BellParts x,BellParts y,out BellParts r,bool build){
		r.p=polyProduct(x.p,y.p); r.exponent=x.exponent||y.exponent; r.scaled=x.scaled||y.scaled; r.symbolic=x.symbolic||y.symbolic;
		if(r.p.length>64) return false;
		foreach(q;r.p) if(q.words>128) return false;
		if(x.exponent&&y.exponent){ foreach(i;0..3) r.c[i]=coefficientSum(x.c[i],y.c[i],build); }
		else r.c=x.exponent?x.c:y.c;
		foreach(q;r.c) if(q.closed&&q.value.words>128) return false;
		r.poly=x.symbolic&&y.symbolic?symbolicProduct(x.poly,y.poly,build):x.symbolic?x.poly:y.poly;
		if(r.poly.length>17) return false;
		if(build) r.scale=!x.scaled?y.scale:!y.scaled?x.scale:primitive(arena.mul(arena.real_(1),arena.real_(1),true),[x.scale,y.scale]);
		return true;
	}
	private bool bellParts(uint id,out BellParts r,bool build,uint depth=0){
		if(depth>16) return false;
		final switch(bellFactor(id,r.p)){
			case BellFactor.none:return false;
			case BellFactor.polynomial:return true;
			case BellFactor.exponential:r.p=[Rational(1)]; r.exponent=true; return axisQuadratic(nodes[id].a,r.c,build);
			case BellFactor.scale:r.p=[Rational(1)]; r.scaled=true; if(build) r.scale=dropIndex(at(id)); return true;
			case BellFactor.symbolic:r.p=[Rational(1)]; r.symbolic=true; return axisSymbolic(id,r.poly,build);
			case BellFactor.product:
				BellParts x,y;
				return bellParts(nodes[id].a,x,build,depth+1)&&bellParts(nodes[id].b,y,build,depth+1)&&bellJoin(x,y,r,build);
		}
	}
	// A comparison of rational affine expressions of the innermost variable
	// is constant beyond its cut: the cut and the truth value on that side.
	private bool tailTruth(uint id,bool bottom,out Rational cut,out bool truth){
		auto arg=arena.variable(Sort.real_,freshScalarIndex(id)),predicate=scalarBody(at(id),arg); Rational[] points;
		if(predicate==Term.init||!integralCutPoints(arena,predicate,arg,points)) return false;
		foreach(i,point;points) if(!i||(point<cut)==bottom) cut=point;
		auto sample=bottom?cut-Rational(1):cut+Rational(1); if(sample.words>128) return false;
		auto value=simplify(arena,scalarBody(at(id),arena.real_(sample)));
		if(value.exhausted||arena.view(value.output).op!=Op.boolLit) return false;
		truth=value.output==arena.boolean(true); return true;
	}
	// A quotient of polynomials of the innermost variable with rational
	// coefficients: numerator, denominator, and a polynomial outside of whose
	// roots the term is that quotient.
	private bool axisQuotient(uint id,out Rational[] n,out Rational[] d,out Rational[] c,uint depth=0){
		if(depth>32) return false;
		if(axisPolynomial(id,n)){ d=[Rational(1)]; c=[Rational(1)]; return true; }
		auto q=nodes[id]; if(q.op!=BoundOp.primitive||type(at(id))!=scalarType(Sort.real_)) return false;
		auto op=arena.view(arena.at(q.data)); Rational[] n1,d1,c1,n2,d2,c2;
		if(op.op!=Op.inv&&op.op!=Op.mul&&(op.op!=Op.pow||op.value>16)||!axisQuotient(q.a,n1,d1,c1,depth+1)) return false;
		if(op.op==Op.inv){ n=d1; d=n1; c=polyProduct(c1,n1); }
		else if(op.op==Op.pow){
			n=[Rational(1)]; d=[Rational(1)]; c=c1;
			foreach(i;0..op.value){ n=polyProduct(n,n1); d=polyProduct(d,d1); if(n.length>64||d.length>64) return false; }
		}else{
			if(!axisQuotient(q.b,n2,d2,c2,depth+1)) return false;
			n=polyProduct(n1,n2); d=polyProduct(d1,d2); c=polyProduct(c1,c2);
		}
		foreach(p;[n,d,c]){ if(p.length>64) return false; foreach(x;p) if(x.words>128) return false; }
		return true;
	}
	// Such a quotient tends at both ends to the quotient of the coefficients
	// at the degree of its denominator, when the numerator has no larger one.
	private bool quotientLimit(uint id,out size_t degree,out Rational value){
		Rational[] n,d,c; if(!axisQuotient(id,n,d,c)) return false;
		static long top(Rational[] p){ foreach_reverse(i,x;p) if(!x.zero) return cast(long)i; return -1; }
		auto b=top(d); if(b<0||top(c)<0||top(n)>b) return false;
		degree=cast(size_t)b; value=(degree<n.length?n[degree]:Rational(0))/d[degree];
		return value.words<=128;
	}
	// Builtins that are defined and continuous everywhere keep a limit.
	private static bool regularBuiltin(ulong value){
		switch(cast(Builtin)value){
			case Builtin.castQR,Builtin.castRC,Builtin.expR,Builtin.sinR,Builtin.cosR,Builtin.sinhR,Builtin.coshR,Builtin.tanhR,Builtin.atanR,Builtin.asinhR,Builtin.exp2R,
				Builtin.expC,Builtin.sinC,Builtin.cosC,Builtin.sinhC,Builtin.coshC,Builtin.reC,Builtin.imC,Builtin.absC,Builtin.cisR,Builtin.expiC:return true;
			default:return false;
		}
	}
	// A partial builtin keeps a rational limit in the interior of its domain.
	private static bool interiorBuiltin(ulong value,Rational q){
		switch(cast(Builtin)value){
			case Builtin.logR,Builtin.log2R,Builtin.log10R,Builtin.sqrtR:return Rational(0)<q;
			case Builtin.asinR,Builtin.acosR:return Rational(-1)<q&&q<Rational(1);
			default:return false;
		}
	}
	private bool numericOperation(Term t){
		auto v=arena.view(t);
		return arena.isNumber(t)||v.op==Op.boolLit||v.op==Op.add||v.op==Op.mul||v.op==Op.pow||v.op==Op.inv||v.op==Op.abs||v.op==Op.mask||
			v.op==Op.lt||v.op==Op.le||v.op==Op.nonzero||v.op==Op.and_||v.op==Op.or_||v.op==Op.not_||
			v.op==Op.builtin&&v.value>=Builtin.castNZ&&v.value<=Builtin.castQR;
	}
	// Inspect bound syntax before building a scalar calculator input. A failed
	// fast path must not intern intermediates in the ordinary certificate.
	private bool numericSyntax(uint id){
		auto n=nodes[id];
		if(n.op==BoundOp.scalar){
			foreach(i;arena.viewPostorder(arena.at(n.data))) if(!numericOperation(arena.at(i))) return false;
			return true;
		}
		return n.op==BoundOp.primitive&&numericOperation(arena.at(n.data))&&numericSyntax(n.a)&&
			(n.b==uint.max||numericSyntax(n.b));
	}
	// The rational value of a closed term that the numeric calculator of the
	// certificates evaluates, as a scalar term for it.
	private bool closedRational(BoundTerm t,out Rational q,out Term term){
		term=scalarBody(t,Term.init); if(term==Term.init) return false;
		foreach(id;arena.viewPostorder(term)) if(!numericOperation(arena.at(id))) return false;
		auto value=simplify(arena,term);
		if(value.exhausted||!arena.isNumber(value.output)||!arena.number(value.output).im.zero) return false;
		q=arena.number(value.output).re; return q.words<=128;
	}
	// A polynomial times the exponential of a polynomial vanishes at that
	// end when the polynomial is zero, or when the exponent descends there:
	// its coefficient of highest degree is negative, counted with the parity
	// of that degree at -∞. The exponent then stays below a decaying linear
	// rate: half its slope when it is linear, and a unit slope otherwise.
	private static bool vanishing(Rational[] p,Rational[] exponent,bool bottom,out bool zero,out Rational rate,out size_t degree){
		zero=true; foreach(c;p) zero=zero&&c.zero;
		if(zero) return true;
		foreach_reverse(i,c;exponent) if(!c.zero){ degree=i; break; }
		if(!degree) return false;
		auto lead=exponent[degree];
		if((lead<Rational(0))==(bottom&&degree%2==1)) return false;
		rate=degree==1?lead/Rational(2):Rational(bottom?1:-1);
		return true;
	}
	// The eventual truth of a guard that is decided at that end: beyond the
	// cuts of its rational affine comparisons, or as the variable against a
	// bound below or above it that does not mention it.
	private enum Decided:ubyte{ no,cuts,lower,upper }
	private Decided decidedGuard(uint id,bool bottom,out bool truth,out Rational cut){
		auto n=nodes[id];
		if(n.op!=BoundOp.primitive||type(at(id))!=scalarType(Sort.boolean)) return Decided.no;
		if(tailTruth(id,bottom,cut,truth)) return Decided.cuts;
		auto op=arena.view(arena.at(n.data)).op;
		if(op!=Op.le&&op!=Op.lt) return Decided.no;
		bool axis(uint x){ return nodes[x].op==BoundOp.variable&&nodes[x].data==0; }
		if(axis(n.b)&&!depends(at(n.a),0)){ truth=!bottom; return Decided.lower; }
		if(axis(n.a)&&!depends(at(n.b),0)){ truth=bottom; return Decided.upper; }
		return Decided.no;
	}
	// The eventual value of a term that is eventually constant in its
	// innermost variable, at +∞ or at -∞, in the context of the binder. A
	// term that does not mention the variable is its own eventual value, a
	// guard of rational affine comparisons is decided beyond its cuts, the
	// variable passes every bound that does not mention it wherever that
	// bound is defined, a guard that is eventually false masks whatever it
	// guards, and every operation on eventually constant terms is
	// eventually constant. Without `build` this only recognizes the term.
	private BoundTerm eventualTerm(uint id,bool bottom,bool build=true,uint depth=0){
		if(depth>64) return BoundTerm.init;
		auto found=at(id);
		if(!depends(found,0)) return build?dropIndex(found):found;
		auto n=nodes[id];
		if(n.op==BoundOp.guard){
			auto holds=eventualTerm(n.a,bottom,build,depth+1); if(holds==BoundTerm.init) return holds;
			auto value=eventualTerm(n.b,bottom,build,depth+1); if(value==BoundTerm.init) return value;
			return build?guard(holds,value):found;
		}
		if(n.op!=BoundOp.primitive) return BoundTerm.init;
		BoundTerm literal(Term value){ return scalar(Scope(this,contexts[context(found).index].parent),value); }
		bool truth; Rational cut; auto decided=decidedGuard(id,bottom,truth,cut);
		if(decided!=Decided.no){
			if(!build) return found;
			auto value=literal(arena.boolean(truth));
			return decided==Decided.cuts?value:sequence(dropIndex(at(decided==Decided.lower?n.a:n.b)),value);
		}
		if(arena.view(arena.at(n.data)).op==Op.mask&&decidedGuard(n.a,bottom,truth,cut)!=Decided.no&&!truth){
			if(!build) return found;
			return primitive(arena.at(n.data),[eventualTerm(n.a,bottom,true,depth+1),literal(arena.number(Number(0),elementSort(type(found))))]);
		}
		auto a=eventualTerm(n.a,bottom,build,depth+1); if(a==BoundTerm.init) return a;
		if(n.b==uint.max) return build?primitive(arena.at(n.data),[a]):found;
		auto b=eventualTerm(n.b,bottom,build,depth+1); if(b==BoundTerm.init) return b;
		return build?primitive(arena.at(n.data),[a,b]):found;
	}
	// The limit of a body in its innermost variable at +∞ or at -∞, by
	// structure: an eventually constant term tends to its eventual value, a
	// polynomial times the exponential of a polynomial that descends tends to
	// zero, also under a scale that does not mention the variable, sums,
	// products and powers of convergent terms converge, and an eventually
	// decided guard masks the limit of its value. A factor of the polynomial
	// may be piecewise: beyond its last cut it is a polynomial, and where
	// that is zero the product vanishes whatever the exponential does.
	// Absolute values and builtins that are defined and continuous everywhere
	// keep a limit. A reciprocal keeps a limit that is a rational number
	// other than zero, and a partial builtin one in the interior of its
	// domain. A quotient of polynomials whose denominator has at least the
	// degree of its numerator tends to the quotient of the coefficients of
	// that degree. The result is in the context of the binder.
	// Nothing is claimed for a body outside this fragment: a limit that does
	// not exist has no value. Without `build` this only recognizes the body.
	// A term that is not zero where it is defined, by its form: a rational
	// other than zero, π, an inverse, or a product of these. An exponential
	// that does not mention the axis is part of the exponent.
	private bool nonvanishingScalar(Term t){
		auto v=arena.view(t);
		if(arena.isNumber(t)) return arena.sort(t)==Sort.real_&&arena.number(t).im.zero&&!arena.number(t).re.zero;
		if(v.op==Op.inv) return arena.sort(t)==Sort.real_;
		if(v.op==Op.builtin) return v.value==Builtin.pi;
		return v.op==Op.mul&&v.arity==2&&arena.sort(t)==Sort.real_&&nonvanishingScalar(arena.viewChild(t,0))&&nonvanishingScalar(arena.viewChild(t,1));
	}
	private bool nonvanishing(uint id){
		auto n=nodes[id];
		if(n.op==BoundOp.scalar) return nonvanishingScalar(arena.at(n.data));
		if(n.op!=BoundOp.primitive||type(at(id))!=scalarType(Sort.real_)) return false;
		auto v=arena.view(arena.at(n.data));
		return v.op==Op.inv||v.op==Op.mul&&nonvanishing(n.a)&&nonvanishing(n.b);
	}
	// A coefficient that is not zero where it is defined: a closed rational
	// other than zero, or such a term by its form.
	private bool nonvanishingCoefficient(BoundTerm t){
		Rational q; Term term;
		return closedRational(t,q,term)?!q.zero:nonvanishing(t.id);
	}
	// The parts of a density: those of its weights, joined from the measure
	// outward.
	private bool gaussianParts(uint[] weights,out BellParts total,bool build){
		total.p=[Rational(1)];
		foreach(id;weights){
			BellParts weight,joined;
			if(!bellParts(id,weight,build)||!bellJoin(total,weight,joined,build)) return false;
			total=joined;
		}
		return true;
	}
	private bool gaussianTail(uint body,out BellParts bell,bool build){
		return bellParts(body,bell,build)&&bell.exponent&&!bell.symbolic&&bell.c[2].present&&bell.c[2].closed&&bell.c[2].value<Rational(0);
	}
	private BoundTerm limitTerms(uint body,bool bottom,bool build=true,uint depth=0){
		if(depth>64) return BoundTerm.init;
		auto found=at(body);
		if(eventualTerm(body,bottom,false)!=BoundTerm.init) return build?eventualTerm(body,bottom):found;
		Rational[] p,exponent; bool scaled;
		if(tailExponential(body,bottom,p,exponent,scaled)){
			bool vanishes; Rational rate; size_t order;
			if(!vanishing(p,exponent,bottom,vanishes,rate,order)) return BoundTerm.init;
			if(!build) return found;
			auto zero=scalar(Scope(this,contexts[context(found).index].parent),arena.real_(0));
			return scaled?primitive(arena.mul(arena.real_(1),arena.real_(1),true),[tailScale(body,bottom),zero]):zero;
		}
		size_t degree; Rational quotient;
		if(quotientLimit(body,degree,quotient))
			return build?scalar(Scope(this,contexts[context(found).index].parent),arena.real_(quotient)):found;
		// A polynomial times the exponential of a quadratic with negative
		// rational curvature vanishes at both ends, whatever its constant and
		// linear coefficients are: zero under the factors that do not mention
		// the variable, and after the coefficients, which must be defined.
		BellParts bell;
		if(gaussianTail(body,bell,false)){
			if(!build) return found;
			gaussianTail(body,bell,true);
			auto result=scalar(Scope(this,contexts[context(found).index].parent),arena.real_(0));
			if(bell.scaled) result=primitive(arena.mul(arena.real_(1),arena.real_(1),true),[bell.scale,result]);
			if(bell.c[1].present) result=sequence(bell.c[1].term,result);
			return bell.c[0].present?sequence(bell.c[0].term,result):result;
		}
		auto n=nodes[body]; if(n.op!=BoundOp.primitive&&n.op!=BoundOp.guard) return BoundTerm.init;
		auto view=n.op==BoundOp.guard?arena.view(arena.boolean(true)):arena.view(arena.at(n.data)),op=view.op;
		if(n.op==BoundOp.guard||op==Op.mask){
			// A guard that is eventually decided: strict, or masking.
			if(eventualTerm(n.a,bottom,false)==BoundTerm.init) return BoundTerm.init;
			auto value=limitTerms(n.b,bottom,build,depth+1); if(value==BoundTerm.init) return value;
			if(!build) return found;
			auto decided=eventualTerm(n.a,bottom);
			return n.op==BoundOp.guard?guard(decided,value):primitive(arena.at(n.data),[decided,value]);
		}
		bool partial=op==Op.builtin&&interiorBuiltin(view.value,Rational(1)/Rational(2));
		if(op==Op.inv||partial){
			// The limit inside must be known: not zero under a reciprocal,
			// and in the interior of the domain of a partial builtin.
			if(type(found)!=scalarType(Sort.real_)||limitTerms(n.a,bottom,false,depth+1)==BoundTerm.init) return BoundTerm.init;
			auto inside=limitTerms(n.a,bottom,true,depth+1); Rational q; Term term;
			if(!closedRational(inside,q,term)||(partial?!interiorBuiltin(view.value,q):q.zero)) return BoundTerm.init;
			return build?primitive(arena.at(n.data),[inside]):found;
		}
		bool continuous=op==Op.pow||op==Op.abs||op==Op.builtin&&regularBuiltin(view.value);
		if(op!=Op.add&&op!=Op.mul&&!continuous) return BoundTerm.init;
		auto left=limitTerms(n.a,bottom,build,depth+1); if(left==BoundTerm.init) return left;
		if(continuous) return build?primitive(arena.at(n.data),[left]):found;
		auto right=limitTerms(n.b,bottom,build,depth+1); if(right==BoundTerm.init) return right;
		return build?primitive(arena.at(n.data),[left,right]):found;
	}
	private uint freshScalarIndex(uint root){
		// Freshness is relative to the binder's free scalar variables, not
		// every temporary ever allocated in the arena. Reusing this witness
		// keeps associative-region grouping stable across pointwise passes.
		uint index; uint[] pending=[root]; Table!(uint,bool) seen;
		while(pending.length){
			auto id=pending[$-1]; --pending.length;
			if(seen.get(id,false)) continue; seen.set(id,true);
			auto n=nodes[id];
			if(n.op==BoundOp.scalar) foreach(scalarId;arena.viewPostorder(arena.at(n.data))){
				auto v=arena.view(arena.at(scalarId));
				if(v.op==Op.variable){ enforce(v.value<uint.max-1,"scalar variable limit exceeded"); if(v.value>=index) index=cast(uint)v.value+1; }
			}
			if(n.a!=uint.max) pending~=n.a;
			if(n.b!=uint.max) pending~=n.b;
			if(n.c!=uint.max) pending~=n.c;
		}
		return index;
	}
	// A successful scalar domain certificate applies at every real parameter
	// and every assignment of the expression's free scalar variables.
	private bool totalRowDomain(uint body,out ScalarDomain check,bool trace=true){
		auto index=freshScalarIndex(body),arg=arena.variable(Sort.real_,index);
		auto expression=scalarBody(at(body),arg);
		if(expression==Term.init) return false;
		auto domain=simplifyDomain(arena,expression,[],Options(DensityMode.preserve,trace));
		if(domain.exhausted||domain.output!=arena.boolean(true)) return false;
		check=ScalarDomain(expression,domain,ScalarResult.init,index,Sort.real_);
		return true;
	}
	// Bare integral syntax reparses as a real bind of Dirac rows. The
	// row theorem identifies it with a native graph only for a total map.
	bool bareGraphSyntax(BoundTerm map){
		auto n=node(map);
		if(n.op!=BoundOp.lambda||type(map)!=pool.function_(scalarType(Sort.real_),scalarType(Sort.real_))) return false;
		ScalarDomain domain;
		return totalRowDomain(n.a,domain,false);
	}
	private BoundTerm restoreBody(Term t,Scope ctx,Term argument){
		if(t==argument) return variable(ctx,0);
		auto n=arena.view(t); if(!n.arity) return scalar(ctx,t);
		BoundTerm[] args; bool plain=true;
		foreach(i;0..n.arity){ auto child=restoreBody(arena.viewChild(t,i),ctx,argument); args~=child; plain&=node(child).op==BoundOp.scalar; }
		return plain?scalar(ctx,t):primitive(t,args);
	}
	// Observe a countdown without constructing each finite presentation.
	// A captured scale is inspected only on positive indices.
	private BoundTerm countdownMass(BoundTerm mass){
		uint[] operations;
		auto application=nodes[observationInput(node(mass).a,operations)];
		if(application.op!=BoundOp.apply||nodes[application.a].op!=BoundOp.fixed) return BoundTerm.init;
		auto f=at(application.a),signature=pool.view(type(f));
		if(signature.fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
		auto branch=nodes[nodes[node(f).a].a];
		bool builtin(uint id,Builtin fn){
			auto n=nodes[id];
			if(n.op!=BoundOp.primitive) return false;
			auto op=arena.view(arena.at(n.data)); return op.op==Op.builtin&&op.value==fn;
		}
		bool variableAt(uint id,uint i){ return nodes[id].op==BoundOp.variable&&nodes[id].data==i; }
		if(branch.op!=BoundOp.conditional||!primitiveOp(branch.a,Op.not_)) return BoundTerm.init;
		auto nz=nodes[branch.a].a;
		if(!builtin(nz,Builtin.nonzeroZ)||!builtin(nodes[nz].a,Builtin.castNZ)||!variableAt(nodes[nodes[nz].a].a,0))
			return BoundTerm.init;
		auto scale=nodes[branch.c];
		uint emission=uint.max;
		if(scale.op==BoundOp.distributionAdd){
			bool first=depends(at(scale.a),1);
			emission=first?scale.b:scale.a;
			if(depends(at(emission),1)) return BoundTerm.init;
			scale=nodes[first?scale.a:scale.b];
		}
		bool bare=emission!=uint.max&&scale.op==BoundOp.apply;
		if(!bare&&(scale.op!=BoundOp.distributionScale||depends(at(scale.a),0)||depends(at(scale.a),1))) return BoundTerm.init;
		auto call=bare?scale:nodes[scale.b];
		if(call.op!=BoundOp.apply||!variableAt(call.a,1)||!builtin(call.b,Builtin.subN)) return BoundTerm.init;
		auto pred=nodes[call.b],one=nodes[pred.b],base=at(branch.b);
		if(!variableAt(pred.a,0)||one.op!=BoundOp.scalar||arena.at(one.data)!=arena.natural_(1)||depends(base,0)||depends(base,1))
			return BoundTerm.init;
		auto ctx=context(mass);
		BoundTerm[] env=[scalar(ctx,arena.natural_(0)),bottom(ctx,type(f))];
		foreach(i;0..contexts[ctx.index].length) env~=variable(ctx,i);
		auto seed=observedMass(substitute(base,ctx,env),operations);
		auto arg=at(application.b),zero=arena.real_(0);
		Number rate;
		bool literalScale=!bare&&nodes[scale.a].op==BoundOp.scalar&&literalNumber(arena.at(nodes[scale.a].data),rate);
		bool unitScale=bare||literalScale&&rate.one;
		if(emission!=uint.max&&depends(at(emission),0)){
			auto inner=push(ctx,scalarType(Sort.natural)),i=variable(inner,0);
			auto oneN=arena.natural_(1);
			auto successor=primitive(arena.call(Builtin.addN,[oneN,oneN]),[i,scalar(inner,oneN)]);
			BoundTerm[] rowEnv=[successor,bottom(inner,type(f))];
			foreach(j;0..depth(ctx)) rowEnv~=variable(inner,j+1);
			auto row=observedMass(substitute(at(emission),inner,rowEnv),operations,true);
			BoundTerm total(BoundTerm initial,BoundTerm summand){
				auto visits=finiteSum(hint(lambda(summand),"i"),arg);
				return primitive(arena.add(zero,zero,true),[initial,visits]);
			}
			if(unitScale) return total(seed,row);
			auto power=arena.call(Builtin.powRN,[zero,oneN]),mul=arena.mul(zero,zero,true);
			auto ratio=substitute(at(scale.a),ctx,env);
			if(!literalScale||rate.zero){
				uint[] lifted; foreach(j;0..depth(ctx)) lifted~=j+1;
				auto remaining=primitive(arena.call(Builtin.subN,[oneN,oneN]),[rename(arg,inner,lifted),successor]);
				auto coefficient=primitive(power,[rename(ratio,inner,lifted),remaining]);
				auto initial=primitive(mul,[primitive(power,[ratio,arg]),seed]);
				auto positive=total(initial,primitive(mul,[coefficient,row]));
				env[0]=arg;
				return conditional(substitute(at(branch.a),ctx,env),seed,positive);
			}
			auto inverse=scalar(inner,arena.real_(Rational(1)/rate.re));
			row=primitive(mul,[primitive(power,[inverse,successor]),row]);
			return primitive(mul,[primitive(power,[ratio,arg]),total(seed,row)]);
		}
		if(emission!=uint.max&&unitScale){
			auto visits=observedMass(substitute(at(emission),ctx,env),operations);
			auto casted=arg;
			foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR])
				casted=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[casted]);
			auto nonzero=primitive(arena.call(Builtin.nonzeroN,[arena.natural_(0)]),[arg]);
			auto amount=primitive(arena.mul(zero,zero,true),[casted,visits]);
			return primitive(arena.add(zero,zero,true),[seed,primitive(arena.mask(arena.boolean(true),zero),[nonzero,amount])]);
		}
		auto r=substitute(at(scale.a),ctx,env);
		auto power=primitive(arena.call(Builtin.powRN,[zero,arena.natural_(0)]),[r,arg]);
		auto product=primitive(arena.mul(zero,zero,true),[power,seed]);
		if(emission!=uint.max){
			auto visits=observedMass(substitute(at(emission),ctx,env),operations);
			auto lit=node(r);
			if(lit.op==BoundOp.scalar&&arena.isNumber(arena.at(lit.data))&&arena.number(arena.at(lit.data)).re!=Rational(1)){
				auto gain=Rational(1)/(Rational(1)-arena.number(arena.at(lit.data)).re);
				auto mul=arena.mul(zero,zero,true),add=arena.add(zero,zero,true);
				auto limit=primitive(mul,[scalar(ctx,arena.real_(gain)),visits]);
				auto neg=primitive(mul,[scalar(ctx,arena.real_(-1)),limit]);
				product=primitive(add,[limit,primitive(mul,[power,primitive(add,[seed,neg])])]);
			}else{
				auto inner=push(ctx,scalarType(Sort.natural)),i=variable(inner,0);
				uint[] shift; foreach(j;0..depth(ctx)) shift~=j+1;
				auto powers=primitive(arena.call(Builtin.powRN,[zero,arena.natural_(0)]),[rename(r,inner,shift),i]);
				auto total=finiteSum(lambda(powers),arg);
				auto term=primitive(arena.mul(zero,zero,true),[total,visits]);
				product=primitive(arena.add(zero,zero,true),[product,term]);
			}
		}else if(node(r).op==BoundOp.scalar&&arena.isNumber(arena.at(node(r).data))) return product;
		env[0]=arg;
		return conditional(substitute(at(branch.a),ctx,env),seed,product);
	}
	private BoundTerm solveRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),body=node(at(n.a)),ty=pool.view(type(t));
		if(ty.fields[0]!=scalarType(Sort.natural)||ty.fields[1]!=scalarType(Sort.natural)) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool unary(uint id,Op op){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==op; }
		bool variableAt(uint id,uint index){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==index; }
		bool previous(uint id){
			auto q=nodes[id]; if(q.op!=BoundOp.apply||!variableAt(q.a,1)||!call(q.b,Builtin.subN)) return false;
			auto arg=nodes[q.b],one=nodes[arg.b];
			return variableAt(arg.a,0)&&one.op==BoundOp.scalar&&arena.isNumber(arena.at(one.data))&&arena.number(arena.at(one.data)).one;
		}
		bool isForward(uint id){
			auto q=nodes[id]; if(q.op!=BoundOp.apply||!variableAt(q.a,1)||!call(q.b,Builtin.addN)) return false;
			auto x=nodes[q.b],one=nodes[x.b]; return variableAt(x.a,0)&&one.op==BoundOp.scalar&&arena.isNumber(arena.at(one.data))&&arena.number(arena.at(one.data)).one;
		}
		bool splitBranch(uint id,out uint p,out uint yes,out uint no){
			if(!call(id,Builtin.addN)) return false; auto q=nodes[id];
			if(!unary(q.a,Op.mask)||!unary(q.b,Op.mask)) return false; auto x=nodes[q.a],y=nodes[q.b];
			if(!unary(y.a,Op.not_)||nodes[y.a].a!=x.a) return false; p=x.a; yes=x.b; no=y.b; return true;
		}
		bool literal(uint id,out ulong value){
			auto q=nodes[id]; if(q.op!=BoundOp.scalar||!arena.isNumber(arena.at(q.data))) return false;
			auto x=arena.number(arena.at(q.data)).re; if(!x.small||x.integer<0) return false; value=cast(ulong)x.integer; return true;
		}
		uint bandLowerTest,bandDown,bandRest,bandEq,bandBase,bandTail,bandUpperTest,bandDownAgain,bandUp; ulong bandLower,bandUpper;
		if(splitBranch(body.a,bandLowerTest,bandDown,bandRest)&&previous(bandDown)&&call(bandLowerTest,Builtin.ltN)&&
			variableAt(nodes[bandLowerTest].a,0)&&literal(nodes[bandLowerTest].b,bandLower)&&
			splitBranch(bandRest,bandEq,bandBase,bandTail)&&totalScalar(at(bandBase))&&splitBranch(bandTail,bandUpperTest,bandDownAgain,bandUp)&&bandDownAgain==bandDown&&isForward(bandUp)&&
			call(bandUpperTest,Builtin.ltN)&&variableAt(nodes[bandUpperTest].a,0)&&literal(nodes[bandUpperTest].b,bandUpper)&&bandLower<bandUpper&&
			unary(bandEq,Op.not_)&&call(nodes[bandEq].a,Builtin.nonzeroZ)&&call(nodes[nodes[bandEq].a].a,Builtin.addZ)){
			auto sum=nodes[nodes[nodes[bandEq].a].a]; bool matches;
			if(call(sum.a,Builtin.castNZ)&&variableAt(nodes[sum.a].a,0)&&nodes[sum.b].op==BoundOp.scalar){
				auto neg=arena.at(nodes[sum.b].data),q=arena.view(neg);
				if(q.op==Op.builtin&&q.value==Builtin.mulZ){
					auto x=arena.viewChild(neg,0),y=arena.viewChild(neg,1);
					matches=arena.isNumber(x)&&arena.isNumber(y)&&arena.number(x).re==Rational(-1)&&arena.number(y).re==Rational(bandLower);
				}
			}
			if(matches){
				auto inner=push(context(t),ty.fields[0]),arg=variable(inner,0);
				auto lo=primitive(arena.le(arena.natural_(0),arena.natural_(0)),[scalar(inner,arena.at(nodes[nodes[bandLowerTest].b].data)),arg]);
				auto hi=primitive(arena.at(nodes[bandUpperTest].data),[arg,scalar(inner,arena.at(nodes[nodes[bandUpperTest].b].data))]);
				auto pred=primitive(arena.and_(arena.boolean(true),arena.boolean(true)),[lo,hi]);
				auto output=inheritHint(at(n.a),lambda(guard(pred,scalar(inner,arena.at(nodes[bandBase].data)))));
				solution=RecurrenceSolution(t.id,output.id,bandBase,nodes[bandUpperTest].b,Law.init,Law.init,false,true,2,nodes[bandLowerTest].b); return output;
			}
		}
		if(!call(body.a,Builtin.addN)) return BoundTerm.init;
		auto sum=nodes[body.a]; if(!unary(sum.a,Op.mask)||!unary(sum.b,Op.mask)) return BoundTerm.init;
		auto yes=nodes[sum.a],no=nodes[sum.b],p=nodes[yes.a];
		if(!unary(yes.a,Op.not_)||!unary(no.a,Op.not_)||nodes[no.a].a!=yes.a) return BoundTerm.init;
		if(!call(p.a,Builtin.nonzeroZ)||!call(nodes[p.a].a,Builtin.castNZ)||!variableAt(nodes[nodes[p.a].a].a,0)) return BoundTerm.init;
		if(!totalScalar(at(yes.b))||!call(no.b,Builtin.addN)&&!call(no.b,Builtin.mulN)) return BoundTerm.init;
		if(call(no.b,Builtin.addN)){
			auto branch=nodes[no.b],down=nodes[branch.a],up=nodes[branch.b];
			if(unary(branch.a,Op.mask)&&unary(branch.b,Op.mask)&&(call(down.a,Builtin.leN)||call(down.a,Builtin.ltN))&&
				unary(up.a,Op.not_)&&nodes[up.a].a==down.a&&previous(down.b)){
				auto condition=nodes[down.a],forward=nodes[up.b];
				if(variableAt(condition.a,0)&&totalScalar(at(condition.b))&&forward.op==BoundOp.apply&&
					variableAt(forward.a,1)&&call(forward.b,Builtin.addN)){
					auto successor=nodes[forward.b],one=nodes[successor.b];
					if(variableAt(successor.a,0)&&one.op==BoundOp.scalar&&arena.isNumber(arena.at(one.data))&&arena.number(arena.at(one.data)).one){
						bool strict=call(down.a,Builtin.ltN); ulong upper; if(strict&&(!literal(condition.b,upper)||!upper)) return BoundTerm.init;
						auto inner=push(context(t),ty.fields[0]);
						auto predicate=primitive(arena.at(condition.data),[variable(inner,0),scalar(inner,arena.at(nodes[condition.b].data))]);
						auto output=inheritHint(at(n.a),lambda(guard(predicate,scalar(inner,arena.at(nodes[yes.b].data)))));
						solution=RecurrenceSolution(t.id,output.id,yes.b,condition.b,Law.init,Law.init,false,true,cast(ubyte)(strict?1:0)); return output;
					}
				}
			}
		}
		auto step=nodes[no.b]; bool left=previous(step.b); auto delta=left?step.a:step.b;
		if(!previous(left?step.b:step.a)||!totalScalar(at(delta))) return BoundTerm.init;
		bool mul=call(no.b,Builtin.mulN);
		auto law=mul?(left?Law.natural_recurrence_mul_left_step:Law.natural_recurrence_mul_step):
			(left?Law.natural_recurrence_add_left_step:Law.natural_recurrence_add_step);
		uint index;
		foreach(id;0..arena.length){ auto q=arena.node(arena.at(cast(uint)id)); if(q.op==Op.variable){ enforce(q.value<uint.max-1,"scalar variable limit exceeded"); if(q.value>=index) index=cast(uint)q.value+1; } }
		auto argument=arena.variable(Sort.natural,index),instance=instantiate(arena,law,[arena.at(nodes[yes.b].data),arena.at(nodes[delta].data),argument],true);
		auto candidate=arena.viewChild(instance.before,left?1:0),inner=push(context(t),ty.fields[0]);
		auto output=inheritHint(at(n.a),lambda(restoreBody(candidate,inner,argument)));
		solution=RecurrenceSolution(t.id,output.id,yes.b,delta,law,mul?Law.natural_recurrence_mul_base:Law.natural_recurrence_add_base,left);
		return output;
	}
	private bool recurrenceConstant(Term t){
		auto q=arena.view(t); if(arena.isNumber(t)||q.op==Op.variable) return true;
		if(q.op!=Op.add&&q.op!=Op.mul&&q.op!=Op.pow&&q.op!=Op.abs&&q.op!=Op.conj&&!(q.op==Op.builtin&&builtinInfo(cast(Builtin)q.value).total)) return false;
		foreach(i;0..q.arity) if(!recurrenceConstant(arena.viewChild(t,i))) return false; return true;
	}
	private bool recurrenceBranches(uint id,out uint test,out uint yes,out uint no,out bool reverse){
		auto q=nodes[id]; if(q.op!=BoundOp.primitive||q.b==uint.max) return false;
		auto kind=arena.view(arena.at(q.data)),add=arena.view(scalarOperator(types[q.type],TensorOp.add));
		if(kind.op!=add.op||kind.value!=add.value) return false;
		bool op(uint id,Op f){ auto n=nodes[id]; return n.op==BoundOp.primitive&&arena.view(arena.at(n.data)).op==f; }
		if(!op(q.a,Op.mask)||!op(q.b,Op.mask)) return false;
		auto x=nodes[q.a],y=nodes[q.b];
		if(op(y.a,Op.not_)&&nodes[y.a].a==x.a){ test=x.a; yes=x.b; no=y.b; return true; }
		if(op(x.a,Op.not_)&&nodes[x.a].a==y.a){ test=y.a; yes=y.b; no=x.b; reverse=true; return true; }
		return false;
	}
	private BoundTerm solveAffineRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),body=node(at(n.a)),ty=pool.view(type(t));
		if(ty.fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(ty.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		if(!numeric) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool op(uint id,Op f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==f; }
		bool variableAt(uint id,uint index){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==index; }
		bool arithmetic(uint id,bool mul){ return sort==Sort.natural?call(id,mul?Builtin.mulN:Builtin.addN):sort==Sort.integer?call(id,mul?Builtin.mulZ:Builtin.addZ):sort==Sort.rational?call(id,mul?Builtin.mulQ:Builtin.addQ):op(id,mul?Op.mul:Op.add); }
		bool constant(uint id){ auto q=nodes[id]; return q.op==BoundOp.scalar&&recurrenceConstant(arena.at(q.data)); }
		if(!arithmetic(body.a,false)) return BoundTerm.init;
		auto sum=nodes[body.a]; if(!op(sum.a,Op.mask)||!op(sum.b,Op.mask)) return BoundTerm.init;
		auto yes=nodes[sum.a],no=nodes[sum.b],p=nodes[yes.a];
		if(!op(yes.a,Op.not_)||!op(no.a,Op.not_)||nodes[no.a].a!=yes.a) return BoundTerm.init;
		if(!call(p.a,Builtin.nonzeroZ)||!call(nodes[p.a].a,Builtin.castNZ)||!variableAt(nodes[nodes[p.a].a].a,0)||!constant(yes.b)) return BoundTerm.init;
		auto zero=arena.number(Number(0),sort),one=arena.number(Number(1),sort); bool recursive;
		Law[3] laws;
		final switch(sort){
			case Sort.natural:laws=[Law.natural_affine_add,Law.natural_affine_left,Law.natural_affine_right]; break;
			case Sort.integer:laws=[Law.integer_affine_add,Law.integer_affine_left,Law.integer_affine_right]; break;
			case Sort.rational:laws=[Law.rational_affine_add,Law.rational_affine_left,Law.rational_affine_right]; break;
			case Sort.real_:laws=[Law.real_affine_add,Law.real_affine_left,Law.real_affine_right]; break;
			case Sort.complex:laws=[Law.complex_affine_add,Law.complex_affine_left,Law.complex_affine_right]; break;
			case Sort.boolean,Sort.density,Sort.measure:assert(0);
		}
		void coefficients(Law law,Term[] args,out Term coefficient,out Term offset){
			auto expression=instantiate(arena,law,args~one,true).result;
			coefficient=arena.viewChild(arena.viewChild(expression,0),0); offset=arena.viewChild(expression,1);
		}
		bool collect(uint id,out Term coefficient,out Term offset){
			auto q=nodes[id];
			if(constant(id)){ coefficient=zero; offset=arena.at(q.data); return true; }
			if(q.op==BoundOp.apply&&variableAt(q.a,1)&&call(q.b,Builtin.subN)){
				auto arg=nodes[q.b],amount=nodes[arg.b];
				if(variableAt(arg.a,0)&&amount.op==BoundOp.scalar&&arena.isNumber(arena.at(amount.data))&&arena.number(arena.at(amount.data)).one){ coefficient=one; offset=zero; recursive=true; return true; }
			}
			if(arithmetic(id,false)){
				Term a,b,c,d; if(!collect(q.a,a,b)||!collect(q.b,c,d)) return false;
				coefficients(laws[0],[a,b,c,d],coefficient,offset); return true;
			}
			if(arithmetic(id,true)){
				bool left=constant(q.a); auto c=left?q.a:q.b,child=left?q.b:q.a;
				if(!constant(c)||!collect(child,coefficient,offset)) return false;
				auto value=arena.at(nodes[c].data);
				coefficients(laws[left?1:2],left?[value,coefficient,offset]:[coefficient,offset,value],coefficient,offset); return true;
			}
			return false;
		}
		Term coefficient,offset; if(!collect(no.b,coefficient,offset)||!recursive) return BoundTerm.init;
		auto inner=push(context(t),ty.fields[0]),vec=pool.vector(ty.fields[1],2),mat=pool.vector(vec,2);
		auto row0=tuple(inner,[scalar(inner,coefficient),scalar(inner,offset)],vec);
		auto row1=tuple(inner,[scalar(inner,zero),scalar(inner,one)],vec);
		auto matrix=tuple(inner,[row0,row1],mat),initial=tuple(inner,[scalar(inner,arena.at(nodes[yes.b].data)),scalar(inner,one)],vec);
		auto output=inheritHint(at(n.a),lambda(get(tensor(TensorOp.matvec,tensor(TensorOp.power,matrix,variable(inner,0)),initial),scalar(inner,arena.natural_(0)))));
		solution=RecurrenceSolution(t.id,output.id,yes.b,no.b); solution.affine=true; return output;
	}
	private bool recurrenceIndex(uint id){
		auto q=nodes[id];
		if(q.op==BoundOp.variable) return q.data==0;
		if(q.op!=BoundOp.primitive) return false;
		auto op=arena.view(arena.at(q.data));
		return op.op==Op.builtin&&op.value>=Builtin.castNZ&&op.value<=Builtin.castRC&&recurrenceIndex(q.a);
	}
	private BoundTerm solveIndexedRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),body=node(at(n.a)),ty=pool.view(type(t));
		if(ty.fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(ty.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		if(!numeric) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool op(uint id,Op f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==f; }
		bool variableAt(uint id,uint index){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==index; }
		bool arithmetic(uint id,bool mul){ return sort==Sort.natural?call(id,mul?Builtin.mulN:Builtin.addN):sort==Sort.integer?call(id,mul?Builtin.mulZ:Builtin.addZ):sort==Sort.rational?call(id,mul?Builtin.mulQ:Builtin.addQ):op(id,mul?Op.mul:Op.add); }
		bool constant(uint id){ auto q=nodes[id]; return q.op==BoundOp.scalar&&recurrenceConstant(arena.at(q.data)); }
		if(!arithmetic(body.a,false)) return BoundTerm.init;
		auto sum=nodes[body.a]; if(!op(sum.a,Op.mask)||!op(sum.b,Op.mask)) return BoundTerm.init;
		auto yes=nodes[sum.a],no=nodes[sum.b],p=nodes[yes.a];
		if(!op(yes.a,Op.not_)||!op(no.a,Op.not_)||nodes[no.a].a!=yes.a) return BoundTerm.init;
		if(!call(p.a,Builtin.nonzeroZ)||!call(nodes[p.a].a,Builtin.castNZ)||!variableAt(nodes[nodes[p.a].a].a,0)||!constant(yes.b)) return BoundTerm.init;
		auto zero=arena.number(Number(0),sort),one=arena.number(Number(1),sort); bool recursive,indexed;
		bool collect(uint id,out Term[] coefficients){
			coefficients=[zero,zero,zero]; auto q=nodes[id];
			if(constant(id)){ coefficients[2]=arena.at(q.data); return true; }
			if(recurrenceIndex(id)){ coefficients[1]=one; indexed=true; return true; }
			if(q.op==BoundOp.apply&&variableAt(q.a,1)&&call(q.b,Builtin.subN)){
				auto arg=nodes[q.b],amount=nodes[arg.b];
				if(variableAt(arg.a,0)&&amount.op==BoundOp.scalar&&arena.isNumber(arena.at(amount.data))&&arena.number(arena.at(amount.data)).one){ coefficients[0]=one; recursive=true; return true; }
			}
			Term[] x,y;
			if(arithmetic(id,false)){
				if(!collect(q.a,x)||!collect(q.b,y)) return false;
				foreach(i;0..3) coefficients[i]=arena.add(x[i],y[i],true); return true;
			}
			if(arithmetic(id,true)){
				auto left=constant(q.a),c=left?q.a:q.b;
				if(!constant(c)||!collect(left?q.b:q.a,x)) return false;
				auto value=arena.at(nodes[c].data);
				foreach(i;0..3) coefficients[i]=left?arena.mul(value,x[i],true):arena.mul(x[i],value,true); return true;
			}
			return false;
		}
		Term[] coefficients; if(!collect(no.b,coefficients)||!recursive||!indexed) return BoundTerm.init;
		// Advance (f(n),n,1). The forcing is evaluated at n+1, so b is
		// included in the constant column of the first row as well.
		auto inner=push(context(t),ty.fields[0]),vec=pool.vector(ty.fields[1],3),mat=pool.vector(vec,3);
		auto row0=tuple(inner,[scalar(inner,coefficients[0]),scalar(inner,coefficients[1]),scalar(inner,arena.add(coefficients[1],coefficients[2],true))],vec);
		auto row1=tuple(inner,[scalar(inner,zero),scalar(inner,one),scalar(inner,one)],vec);
		auto row2=tuple(inner,[scalar(inner,zero),scalar(inner,zero),scalar(inner,one)],vec);
		auto matrix=tuple(inner,[row0,row1,row2],mat),initial=tuple(inner,[scalar(inner,arena.at(nodes[yes.b].data)),scalar(inner,zero),scalar(inner,one)],vec);
		auto output=inheritHint(at(n.a),lambda(get(tensor(TensorOp.matvec,tensor(TensorOp.power,matrix,variable(inner,0)),initial),scalar(inner,arena.natural_(0)))));
		solution=RecurrenceSolution(t.id,output.id,yes.b,no.b); solution.indexed=true; return output;
	}

	// Exact integer subdivision. Every recursion-free leaf is certified total;
	// nonlinear feedback and changing recursive coefficients remain unsupported.
	private BoundTerm solveDivideRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),ty=pool.view(type(t));
		if(ty.fields[0]!=scalarType(Sort.natural)||ty.fields[1]!=scalarType(Sort.natural)||nodes[n.a].op!=BoundOp.lambda) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool variableAt(uint id,uint k){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==k; }
		bool literal(uint id,out uint value){
			auto q=nodes[id]; if(q.op!=BoundOp.scalar||!arena.isNumber(arena.at(q.data)))return false;
			auto x=arena.number(arena.at(q.data)).re; if(!x.small||x.integer<0||x.integer>=uint.max)return false;value=cast(uint)x.integer;return true;
		}
		uint test,base,tail; bool reverse;
		if(!recurrenceBranches(nodes[n.a].a,test,base,tail,reverse)||depends(at(base),1)||!depends(at(tail),1))return BoundTerm.init;
		auto predicate=nodes[test]; uint threshold;
		bool inclusive=call(test,Builtin.leN);
		if(!(inclusive||call(test,Builtin.ltN))||!variableAt(predicate.a,0)||!literal(predicate.b,threshold))return BoundTerm.init;
		auto radix=threshold+(inclusive?1:0);if(radix<2)return BoundTerm.init;
		uint variableIndex;
		foreach(id;0..arena.length){ auto q=arena.view(arena.at(cast(uint)id)); if(q.op==Op.variable){enforce(q.value<uint.max-1,"scalar variable limit exceeded");if(q.value>=variableIndex)variableIndex=cast(uint)q.value+1;} }
		auto argument=arena.variable(Sort.natural,variableIndex);
		RecurrenceFact[] facts; Table!(uint,bool) checked;
		bool totalLeaf(uint id){
			if(checked.get(id,false))return true;
			auto input=scalarBody(at(id),argument);if(input==Term.init)return false;
			auto options=Options(DensityMode.preserve,true),d=simplifyDomain(arena,input,[],options);
			if(d.exhausted||d.output!=arena.boolean(true))return false;
			auto v=simplify(arena,input,options);if(v.exhausted)return false;
			facts~=RecurrenceFact(id,uint.max,input,d,v);checked.set(id,true);return true;
		}
		if(!totalLeaf(base))return BoundTerm.init;
		bool constant(uint id){return nodes[id].op==BoundOp.scalar&&recurrenceConstant(arena.at(nodes[id].data));}
		DivideExpression[] expressions;bool recursive,weighted;uint lowerCalls,upperCalls;
		uint collect(uint id,uint level=0){
			if(level>64||expressions.length>=256)return uint.max;
			auto q=nodes[id];DivideExpression e;e.source=id;
			if(!depends(at(id),1)){
				if(!totalLeaf(id))return uint.max;
				e.kind=CFiniteExprKind.force;e.coefficient=arena.natural_(0);e.offset=id;
			}else if(q.op==BoundOp.apply&&variableAt(q.a,1)&&call(q.b,Builtin.divN)){
				uint divisor;if(!literal(nodes[q.b].b,divisor)||divisor!=radix)return uint.max;
				auto arg=nodes[q.b].a;bool upper;
				if(variableAt(arg,0))++lowerCalls;
				else if(radix==2&&call(arg,Builtin.addN)&&variableAt(nodes[arg].a,0)){
					uint shift;if(!literal(nodes[arg].b,shift)||shift!=1)return uint.max;upper=true;++upperCalls;
				}else return uint.max;
				e.kind=CFiniteExprKind.previous;e.b=upper?1:0;e.coefficient=arena.natural_(1);e.offset=scalar(context(at(id)),arena.natural_(0)).id;recursive=true;
			}else if(call(id,Builtin.addN)){
				e.kind=CFiniteExprKind.add;e.a=collect(q.a,level+1);e.b=collect(q.b,level+1);if(e.a==uint.max||e.b==uint.max)return uint.max;
				e.coefficient=arena.add(expressions[e.a].coefficient,expressions[e.b].coefficient,true);
				e.offset=primitive(arena.at(q.data),[at(expressions[e.a].offset),at(expressions[e.b].offset)]).id;
			}else if(call(id,Builtin.mulN)){
				weighted=true;bool left=constant(q.a);auto c=left?q.a:q.b;if(!constant(c))return uint.max;
				e.kind=left?CFiniteExprKind.left:CFiniteExprKind.right;e.a=collect(left?q.b:q.a,level+1);if(e.a==uint.max)return uint.max;
				e.value=arena.at(nodes[c].data);auto child=expressions[e.a];
				e.coefficient=left?arena.mul(e.value,child.coefficient,true):arena.mul(child.coefficient,e.value,true);
				e.offset=primitive(arena.at(q.data),left?[at(c),at(child.offset)]:[at(child.offset),at(c)]).id;
			}else return uint.max;
			expressions~=e;return cast(uint)expressions.length-1;
		}
		auto root=collect(tail);if(root==uint.max||!recursive)return BoundTerm.init;
		bool mixed=upperCalls!=0;
		if(mixed&&(lowerCalls!=1||upperCalls!=1||weighted))return BoundTerm.init;
		auto outer=context(t),inner=push(outer,scalarType(Sort.natural)),sumScope=push(inner,scalarType(Sort.natural));
		BoundTerm functionAt(uint id){
			BoundTerm[] values=[variable(inner,0),bottom(inner,type(t))];foreach(i;0..depth(outer))values~=variable(inner,i+1);
			return lambda(substitute(at(id),inner,values));
		}
		auto seedFn=functionAt(base),tollFn=functionAt(expressions[root].offset);
		BoundTerm lifted(BoundTerm f,Scope ctx,uint amount){BoundTerm[] values;foreach(i;0..depth(outer))values~=variable(ctx,i+amount);return substitute(f,ctx,values);}
		BoundTerm bin(Builtin f,BoundTerm x,BoundTerm y){return primitive(arena.call(f,[arena.natural_(0),arena.natural_(0)]),[x,y]);}
		auto l=bin(Builtin.logN,scalar(inner,arena.natural_(radix)),variable(inner,0));
		auto terminal=bin(Builtin.divN,variable(inner,0),bin(Builtin.powNN,scalar(inner,arena.natural_(radix)),l));
		auto initial=bin(Builtin.mulN,bin(Builtin.powNN,scalar(inner,expressions[root].coefficient),l),apply(lifted(seedFn,inner,1),terminal));
		auto reduced=bin(Builtin.divN,variable(sumScope,1),bin(Builtin.powNN,scalar(sumScope,arena.natural_(radix)),variable(sumScope,0)));
		auto summand=bin(Builtin.mulN,bin(Builtin.powNN,scalar(sumScope,expressions[root].coefficient),variable(sumScope,0)),apply(lifted(tollFn,sumScope,2),reduced));
		BoundTerm output;
		if(mixed){
			auto d=bin(Builtin.powNN,scalar(sumScope,arena.natural_(2)),variable(sumScope,0));
			auto q=bin(Builtin.divN,variable(sumScope,1),d);
			auto r=bin(Builtin.subN,variable(sumScope,1),bin(Builtin.mulN,q,d));
			BoundTerm charge(BoundTerm v){
				auto pred=bin(Builtin.leN,scalar(sumScope,arena.natural_(2)),v);
				return primitive(arena.mask(arena.boolean(true),arena.natural_(0)),[pred,apply(lifted(tollFn,sumScope,2),v)]);
			}
			auto level=bin(Builtin.addN,bin(Builtin.mulN,bin(Builtin.subN,d,r),charge(q)),
				bin(Builtin.mulN,r,charge(bin(Builtin.addN,q,scalar(sumScope,arena.natural_(1))))));
			auto costs=finiteSum(lambda(level),bin(Builtin.addN,l,scalar(inner,arena.natural_(1))));
			auto seed=apply(lifted(seedFn,inner,1),scalar(inner,arena.natural_(1)));
			auto body=bin(Builtin.addN,bin(Builtin.mulN,variable(inner,0),seed),costs);
			auto atZero=bin(Builtin.leN,variable(inner,0),scalar(inner,arena.natural_(0)));
			auto zero=apply(lifted(seedFn,inner,1),scalar(inner,arena.natural_(0)));
			auto yes=primitive(arena.mask(arena.boolean(true),arena.natural_(0)),[atZero,zero]);
			auto no=primitive(arena.mask(arena.boolean(true),arena.natural_(0)),[primitive(arena.not_(arena.boolean(true)),[atZero]),body]);
			output=inheritHint(at(n.a),lambda(bin(Builtin.addN,yes,no)));
		}else output=inheritHint(at(n.a),lambda(bin(Builtin.addN,initial,finiteSum(lambda(summand),l))));
		solution=RecurrenceSolution(t.id,output.id,base,tail);solution.divide=true;solution.mixed=mixed;solution.radix=radix;solution.inclusive=inclusive;solution.left=reverse;
		solution.variable=variableIndex;solution.facts=facts;solution.divideExpressions=expressions;solution.cfRoot=root;solution.seedFunction=seedFn.id;solution.tollFunction=tollFn.id;return output;
	}

	// Compile total C-finite forcing compositionally. The state cap bounds
	// tensor-product growth; unsupported or larger expressions keep their μ.
	private BoundTerm solveCFiniteRecurrence(BoundTerm t,out RecurrenceSolution solution){
		enum limit=16;
		auto n=node(t),body=nodes[n.a],ty=pool.view(type(t));
		if(ty.fields[0]!=scalarType(Sort.natural)||body.op!=BoundOp.lambda) return BoundTerm.init;
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(ty.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		if(!numeric) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool op(uint id,Op f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==f; }
		bool variableAt(uint id,uint k){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==k; }
		bool constantTerm(Term t){
			if(recurrenceConstant(t)) return true;
			auto q=arena.view(t);
			if(q.op==Op.builtin&&q.value==Builtin.invQ){ Number v; return literalNumber(arena.viewChild(t,0),v)&&!v.zero; }
			if(q.op!=Op.add&&q.op!=Op.mul&&q.op!=Op.pow&&q.op!=Op.abs&&q.op!=Op.conj&&!(q.op==Op.builtin&&builtinInfo(cast(Builtin)q.value).total)) return false;
			foreach(i;0..q.arity) if(!constantTerm(arena.viewChild(t,i))) return false;
			return true;
		}
		bool constant(uint id){ return nodes[id].op==BoundOp.scalar&&constantTerm(arena.at(nodes[id].data)); }
		bool arithmetic(uint id,bool mul){ auto q=nodes[id]; if(q.op!=BoundOp.primitive) return false; auto x=arena.view(arena.at(q.data)),y=arena.view(scalarOperator(type(at(id)),mul?TensorOp.mul:TensorOp.add)); return x.op==y.op&&x.value==y.value; }
		auto tail=body.a; uint test,yes,no; bool reverse;
		while(recurrenceBranches(tail,test,yes,no,reverse)){
			if(depends(at(yes),1)==depends(at(no),1)||depends(at(test),1)) break;
			tail=depends(at(yes),1)?yes:no;
		}
		if(tail==body.a) return BoundTerm.init;
		CFiniteSequence[] models; CFiniteExpression[] expressions;
		uint save(CFiniteSequence s){ if(models.length>=256||s.size>limit) return uint.max; models~=s; return cast(uint)models.length-1; }
		Term zero(Sort s){ return arena.number(Number(0),s); }
		Term one(Sort s){ return arena.number(Number(1),s); }
		uint atom(CFiniteKind kind,Sort s,uint source=uint.max,Term value=Term.init){
			CFiniteSequence m; m.kind=kind; m.sort=s; m.source=source; m.value=value;
			if(kind==CFiniteKind.zero) return save(m);
			if(kind==CFiniteKind.index){ m.size=2; m.matrix=[one(s),one(s),zero(s),one(s)]; m.initial=[zero(s),one(s)]; m.output=[one(s),zero(s)]; }
			else{ m.size=1; m.matrix=[kind==CFiniteKind.geometric?value:one(s)]; m.initial=[kind==CFiniteKind.constant?value:one(s)]; m.output=[one(s)]; }
			return save(m);
		}
		uint combine(CFiniteKind kind,uint a,uint b,uint source=uint.max,Term value=Term.init){
			if(a==uint.max||b==uint.max&&(kind==CFiniteKind.add||kind==CFiniteKind.mul)) return uint.max;
			auto x=models[a]; CFiniteSequence m; m.kind=kind; m.sort=x.sort; m.source=source; m.a=a; m.b=b; m.value=value;
			if(kind==CFiniteKind.left||kind==CFiniteKind.right){
				m.size=x.size; m.matrix=x.matrix; m.initial=x.initial;
				foreach(c;x.output) m.output~=kind==CFiniteKind.left?arena.mul(value,c,true):arena.mul(c,value,true);
			}else{
				auto y=models[b]; m.size=kind==CFiniteKind.add?x.size+y.size:x.size*y.size;
				if(m.size>limit) return uint.max;
				foreach(i;0..m.size){
					if(kind==CFiniteKind.add){ m.initial~=i<x.size?x.initial[i]:y.initial[i-x.size]; m.output~=i<x.size?x.output[i]:y.output[i-x.size]; }
					else{ m.initial~=arena.mul(x.initial[i/y.size],y.initial[i%y.size],true); m.output~=arena.mul(x.output[i/y.size],y.output[i%y.size],true); }
					foreach(j;0..m.size){
						if(kind==CFiniteKind.add) m.matrix~=i<x.size&&j<x.size?x.matrix[i*x.size+j]:i>=x.size&&j>=x.size?y.matrix[(i-x.size)*y.size+j-x.size]:zero(x.sort);
						else m.matrix~=arena.mul(x.matrix[(i/y.size)*x.size+j/y.size],y.matrix[(i%y.size)*y.size+j%y.size],true);
					}
				}
			}
			return save(m);
		}
		Table!(uint,uint) memo;
		uint forcing(uint id,uint depth=0){
			if(depth>64||models.length>=256) return uint.max;
			auto old=memo.get(id,uint.max); if(old!=uint.max) return old;
			auto q=nodes[id]; auto s=elementSort(type(at(id))); uint result=uint.max;
			if(constant(id)) result=atom(CFiniteKind.constant,s,id,arena.at(q.data));
			else if(variableAt(id,0)&&s==Sort.natural) result=atom(CFiniteKind.index,s,id);
			else if(arithmetic(id,false)||arithmetic(id,true)){
				auto a=forcing(q.a,depth+1),b=forcing(q.b,depth+1);
				result=combine(arithmetic(id,false)?CFiniteKind.add:CFiniteKind.mul,a,b,id);
			}else if(q.op==BoundOp.primitive){
				auto f=arena.view(arena.at(q.data));
				if(f.op==Op.builtin&&f.value>=Builtin.castNZ&&f.value<=Builtin.castRC){
					auto a=forcing(q.a,depth+1);
					if(a!=uint.max){ auto x=models[a]; CFiniteSequence m; m.kind=CFiniteKind.map; m.source=id; m.sort=s; m.a=a; m.size=x.size;
						foreach(v;x.matrix)m.matrix~=arena.castTo(v,s); foreach(v;x.initial)m.initial~=arena.castTo(v,s); foreach(v;x.output)m.output~=arena.castTo(v,s); result=save(m); }
				}else if(f.op==Op.builtin&&f.value>=Builtin.powNN&&f.value<=Builtin.powCN&&constant(q.a)&&variableAt(q.b,0)) result=atom(CFiniteKind.geometric,s,id,arena.at(nodes[q.a].data));
				else{
					uint exponent=uint.max;
					if(f.op==Op.pow&&f.value<=8) exponent=cast(uint)f.value;
					if(f.op==Op.builtin&&f.value>=Builtin.powNN&&f.value<=Builtin.powCN&&constant(q.b)){
						auto term=arena.at(nodes[q.b].data); auto v=arena.isNumber(term)?arena.number(term):Number(-1); if(arena.isNumber(term)&&v.re.small&&v.re.integer>=0&&v.re.integer<=8) exponent=cast(uint)v.re.integer;
					}
					if(exponent!=uint.max){
						auto a=forcing(q.a,depth+1);
						if(a!=uint.max){ auto r=atom(CFiniteKind.constant,s,uint.max,one(s)); foreach(k;0..exponent){ r=combine(CFiniteKind.mul,a,r); if(r==uint.max) break; }
							if(r!=uint.max){ auto m=models[r]; m.kind=CFiniteKind.power; m.source=id; m.a=a; m.b=exponent; result=save(m); }
						}
					}
				}
			}
			if(result==uint.max&&q.op==BoundOp.get&&constant(q.b)&&arena.isNumber(arena.at(nodes[q.b].data))){
				auto product=nodes[q.a];
				if(product.op==BoundOp.tensor&&product.data==TensorOp.matvec){
					auto power=nodes[product.a];
					if(power.op==BoundOp.tensor&&power.data==TensorOp.power&&variableAt(power.b,0)){
						auto v=pool.view(type(at(product.b))),idx=arena.number(arena.at(nodes[q.b].data)).re;
						if(v.kind==TypeKind.vector&&v.dimension.constant&&v.length>0&&v.length<=limit&&idx.small&&idx.integer>=0&&idx.integer<v.length){
							CFiniteSequence m; m.kind=CFiniteKind.coordinate; m.source=id; m.sort=s; m.a=power.a; m.b=product.b; m.size=cast(uint)v.length; m.coordinate=cast(uint)idx.integer;
							bool cells(uint id,ref Term[] xs){ foreach(j;0..m.size){ auto z=nodes[id]; if(z.op!=BoundOp.vectorCons||!constant(z.a)) return false; xs~=arena.at(nodes[z.a].data); id=z.b; } return nodes[id].op==BoundOp.vectorNil; }
							bool valid=cells(m.b,m.initial); auto row=m.a;
							foreach(j;0..m.size){ auto z=nodes[row]; if(z.op!=BoundOp.vectorCons||!cells(z.a,m.matrix)){valid=false;break;} row=z.b; }
							if(valid&&nodes[row].op==BoundOp.vectorNil){ foreach(j;0..m.size)m.output~=j==m.coordinate?one(s):zero(s); result=save(m); }
						}
					}
				}
			}

			if(result!=uint.max) memo.set(id,result); return result;
		}
		bool recursive;
		uint collect(uint id,uint depth=0){
			if(depth>64||expressions.length>=256) return uint.max;
			auto q=nodes[id]; CFiniteExpression e; e.source=id;
			auto f=forcing(id);
			if(f!=uint.max){ e.kind=CFiniteExprKind.force; e.a=f; e.offset=f; e.coefficient=zero(sort); }
			else if(q.op==BoundOp.apply&&variableAt(q.a,1)&&call(q.b,Builtin.subN)&&variableAt(nodes[q.b].a,0)&&constant(nodes[q.b].b)&&arena.isNumber(arena.at(nodes[nodes[q.b].b].data))&&arena.number(arena.at(nodes[nodes[q.b].b].data)).one){
				e.kind=CFiniteExprKind.previous; e.coefficient=one(sort); e.offset=atom(CFiniteKind.zero,sort); recursive=true;
			}else if(arithmetic(id,false)){
				e.kind=CFiniteExprKind.add; e.a=collect(q.a,depth+1); e.b=collect(q.b,depth+1); if(e.a==uint.max||e.b==uint.max) return uint.max;
				e.coefficient=arena.add(expressions[e.a].coefficient,expressions[e.b].coefficient,true); e.offset=combine(CFiniteKind.add,expressions[e.a].offset,expressions[e.b].offset);
			}else if(arithmetic(id,true)){
				bool left=constant(q.a); auto c=left?q.a:q.b; if(!constant(c)) return uint.max;
				e.kind=left?CFiniteExprKind.left:CFiniteExprKind.right; e.a=collect(left?q.b:q.a,depth+1); if(e.a==uint.max) return uint.max;
				e.value=arena.at(nodes[c].data); e.coefficient=left?arena.mul(e.value,expressions[e.a].coefficient,true):arena.mul(expressions[e.a].coefficient,e.value,true);
				e.offset=combine(left?CFiniteKind.left:CFiniteKind.right,expressions[e.a].offset,uint.max,uint.max,e.value);
			}else return uint.max;
			if(e.offset==uint.max) return uint.max; expressions~=e; return cast(uint)expressions.length-1;
		}
		auto root=collect(tail); if(root==uint.max||!recursive) return BoundTerm.init;
		// Certify both the entire initial segment and an unconditional tail.
		// Testing only a few numeric indices would miss holes or later branches.
		uint order=1,variableIndex;
		foreach(id;0..arena.length){ auto q=arena.view(arena.at(cast(uint)id)); if(q.op==Op.variable){ enforce(q.value<uint.max-1,"scalar variable limit exceeded"); if(q.value>=variableIndex) variableIndex=cast(uint)q.value+1; } }
		auto argument=arena.variable(Sort.natural,variableIndex);
		RecurrenceFact[] facts; Term[] seeds;
		bool fact(uint id,uint index,out Term output){
			auto arg=index==uint.max?arena.call(Builtin.addN,[argument,arena.natural_(order)]):arena.natural_(index);
			auto input=scalarBody(at(id),arg); if(input==Term.init) return false;
			auto options=Options(DensityMode.preserve,true),d=simplifyDomain(arena,input,[],options),v=simplify(arena,input,options);
			if(d.exhausted||v.exhausted||d.output!=arena.boolean(true)) return false;
			output=arena.castTo(v.output,arena.sort(input)); facts~=RecurrenceFact(id,index,input,d,v); return true;
		}
		bool prefix(){
			facts=null; seeds=null;
			auto id=body.a; Term output;
			while(id!=tail){
				if(!recurrenceBranches(id,test,yes,no,reverse)||!fact(test,uint.max,output)) return false;
				auto next=output==arena.boolean(true)?yes:output==arena.boolean(false)?no:uint.max;
				if(next==uint.max||!depends(at(next),1)) return false; id=next;
			}
			foreach(i;0..order){
				id=body.a;
				while(depends(at(id),1)){
					if(id==tail||!recurrenceBranches(id,test,yes,no,reverse)||!fact(test,i,output)) return false;
					id=output==arena.boolean(true)?yes:output==arena.boolean(false)?no:uint.max; if(id==uint.max) return false;
				}
				if(!fact(id,i,output)||!constantTerm(output)) return false; seeds~=output;
			}
			return true;
		}
		for(;order<=16;++order) if(prefix()) break;
		if(order>16) return BoundTerm.init;
		auto expr=expressions[root],m=models[expr.offset],size=m.size+order;
		// Align the forcing state with the last seed, then prepend the earlier
		// seeds as shift-register slots. The first coordinate is f(n) for all n.
		auto auxiliary=m.initial;
		foreach(k;1..order){
			Term[] next;
			foreach(i;0..m.size){ auto c=zero(sort); foreach_reverse(j;0..m.size) c=arena.add(arena.mul(m.matrix[i*m.size+j],auxiliary[j],true),c,true); next~=c; }
			auxiliary=next;
		}
		auto inner=push(context(t),ty.fields[0]),vec=pool.vector(ty.fields[1],size),mat=pool.vector(vec,size);
		BoundTerm[] rows,initial;
		foreach(i;0..size){
			BoundTerm[] cells;
			foreach(j;0..size){
				auto c=zero(sort);
				if(i+1<order) c=j==i+1?one(sort):zero(sort);
				else if(i+1==order){
					if(j==i)c=expr.coefficient;
					else if(j>=order) foreach_reverse(k;0..m.size) c=arena.add(arena.mul(m.output[k],m.matrix[k*m.size+j-order],true),c,true);
				}else if(j>=order) c=m.matrix[(i-order)*m.size+j-order];
				cells~=scalar(inner,c);
			}
			rows~=tuple(inner,cells,vec); initial~=scalar(inner,i<order?seeds[i]:auxiliary[i-order]);
		}
		auto matrix=tuple(inner,rows,mat),seed=tuple(inner,initial,vec);
		auto output=inheritHint(at(n.a),lambda(get(tensor(TensorOp.matvec,tensor(TensorOp.power,matrix,variable(inner,0)),seed),scalar(inner,arena.natural_(0)))));
		solution=RecurrenceSolution(t.id,output.id,0,tail); solution.cfinite=true; solution.cfModels=models; solution.cfExpressions=expressions; solution.cfRoot=root; solution.cfSize=size;
		solution.order=order; solution.variable=variableIndex; solution.seeds=seeds; solution.facts=facts; return output;
	}

	// Homogenize x(n+1)=A*x(n)+b as (x(n),1). Keep seeds and coefficients
	// total: a strict product cannot recover from an undefined component.
	private BoundTerm solveCoupledRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),ty=pool.view(type(t)),v=pool.view(ty.fields[1]);
		if(ty.fields[0]!=scalarType(Sort.natural)||v.kind!=TypeKind.vector||!v.dimension.constant||!v.length||v.length>8) return BoundTerm.init;
		auto leaf=v.fields[0],width=cast(uint)v.length; Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(leaf==scalarType(s)){ sort=s; numeric=true; }
		if(!numeric) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool variableAt(uint id,uint i){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==i; }
		bool constantTerm(Term t){
			if(recurrenceConstant(t)) return true;
			auto q=arena.view(t);
			if(q.op==Op.builtin&&q.value==Builtin.invQ){
				Number value; return literalNumber(arena.viewChild(t,0),value)&&!value.zero;
			}
			if(q.op!=Op.add&&q.op!=Op.mul&&q.op!=Op.pow&&q.op!=Op.abs&&q.op!=Op.conj&&!(q.op==Op.builtin&&builtinInfo(cast(Builtin)q.value).total)) return false;
			foreach(i;0..q.arity) if(!constantTerm(arena.viewChild(t,i))) return false; return true;
		}
		bool constant(uint id){ auto q=nodes[id]; return q.op==BoundOp.scalar&&constantTerm(arena.at(q.data)); }
		bool arithmetic(uint id,bool mul){ auto q=nodes[id]; if(q.op!=BoundOp.primitive) return false; auto a=arena.view(arena.at(q.data)),b=arena.view(scalarOperator(leaf,mul?TensorOp.mul:TensorOp.add)); return a.op==b.op&&a.value==b.value; }
		auto body=nodes[n.a]; if(body.op!=BoundOp.lambda) return BoundTerm.init;
		auto branch=nodes[body.a]; if(branch.op!=BoundOp.conditional) return BoundTerm.init;
		auto predicate=nodes[branch.a];
		if(predicate.op!=BoundOp.primitive||arena.view(arena.at(predicate.data)).op!=Op.not_||!call(predicate.a,Builtin.nonzeroZ)||!call(nodes[predicate.a].a,Builtin.castNZ)||!variableAt(nodes[nodes[predicate.a].a].a,0)) return BoundTerm.init;
		uint[] bases,steps;
		bool elements(uint id,ref uint[] values){ foreach(i;0..width){ auto q=nodes[id]; if(q.op!=BoundOp.vectorCons) return false; values~=q.a; id=q.b; } return nodes[id].op==BoundOp.vectorNil; }
		if(!elements(branch.b,bases)||!elements(branch.c,steps)) return BoundTerm.init;
		foreach(id;bases) if(!constant(id)) return BoundTerm.init;
		uint previous(uint id){
			auto q=nodes[id]; if(q.op!=BoundOp.get||nodes[q.b].op!=BoundOp.scalar) return uint.max;
			auto index=arena.at(nodes[q.b].data); if(!arena.isNumber(index)) return uint.max;
			auto k=arena.number(index).re; if(!k.small||k.integer<0||k.integer>=width) return uint.max;
			auto f=nodes[q.a]; if(f.op!=BoundOp.apply||!variableAt(f.a,1)||!call(f.b,Builtin.subN)) return uint.max;
			auto arg=nodes[f.b]; if(!variableAt(arg.a,0)||nodes[arg.b].op!=BoundOp.scalar) return uint.max;
			auto amount=arena.at(nodes[arg.b].data); return arena.isNumber(amount)&&arena.number(amount).one?cast(uint)k.integer:uint.max;
		}
		auto zero=arena.number(Number(0),sort),one=arena.number(Number(1),sort); bool recursive;
		bool collect(uint id,out Term[] coefficients){
			coefficients=new Term[width+1]; coefficients[]=zero; auto q=nodes[id];
			if(constant(id)){ coefficients[width]=arena.at(q.data); return true; }
			auto k=previous(id); if(k!=uint.max){ coefficients[k]=one; recursive=true; return true; }
			Term[] x,y;
			if(arithmetic(id,false)){
				if(!collect(q.a,x)||!collect(q.b,y)) return false;
				foreach(i;0..width+1) coefficients[i]=arena.add(x[i],y[i],true); return true;
			}
			if(arithmetic(id,true)){
				auto left=constant(q.a),c=left?q.a:q.b;
				if(!constant(c)||!collect(left?q.b:q.a,x)) return false;
				auto value=arena.at(nodes[c].data);
				foreach(i;0..width+1) coefficients[i]=left?arena.mul(value,x[i],true):arena.mul(x[i],value,true); return true;
			}
			return false;
		}
		auto inner=push(context(t),ty.fields[0]),vec=pool.vector(leaf,width+1),mat=pool.vector(vec,width+1);
		BoundTerm[] rows,initial;
		foreach(i,id;steps){
			Term[] coefficients; if(!collect(id,coefficients)) return BoundTerm.init;
			BoundTerm[] cells; foreach(c;coefficients) cells~=scalar(inner,c);
			rows~=tuple(inner,cells,vec); initial~=scalar(inner,arena.at(nodes[bases[i]].data));
		}
		if(!recursive) return BoundTerm.init;
		BoundTerm[] last; foreach(i;0..width) last~=scalar(inner,zero); last~=scalar(inner,one);
		rows~=tuple(inner,last,vec); initial~=scalar(inner,one);
		auto matrix=tuple(inner,rows,mat),seed=tuple(inner,initial,vec);
		auto state=tensor(TensorOp.matvec,tensor(TensorOp.power,matrix,variable(inner,0)),seed);
		BoundTerm[] result; foreach(i;0..width) result~=get(state,scalar(inner,arena.natural_(i)));
		auto output=inheritHint(at(n.a),lambda(tuple(inner,result,ty.fields[1])));
		solution=RecurrenceSolution(t.id,output.id,branch.b,branch.c); solution.width=width; solution.components=steps; return output;
	}

	// Preserve arbitrary additive forcing as a finite prefix sum. Unlike a
	// closed-form guess, this also handles partial and uninterpreted summands.
	private BoundTerm solvePrefixRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),ty=pool.view(type(t)); if(ty.fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(ty.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		if(!numeric) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool op(uint id,Op f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==f; }
		bool variableAt(uint id,uint index){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==index; }
		bool add(uint id){ return sort==Sort.natural?call(id,Builtin.addN):sort==Sort.integer?call(id,Builtin.addZ):sort==Sort.rational?call(id,Builtin.addQ):op(id,Op.add); }
		auto body=nodes[n.a]; if(body.op!=BoundOp.lambda||!add(body.a)) return BoundTerm.init;
		auto sum=nodes[body.a]; if(!op(sum.a,Op.mask)||!op(sum.b,Op.mask)) return BoundTerm.init;
		auto yes=nodes[sum.a],no=nodes[sum.b],p=nodes[yes.a];
		if(!op(yes.a,Op.not_)||!op(no.a,Op.not_)||nodes[no.a].a!=yes.a||!call(p.a,Builtin.nonzeroZ)||!call(nodes[p.a].a,Builtin.castNZ)||!variableAt(nodes[nodes[p.a].a].a,0)||depends(at(yes.b),0)||depends(at(yes.b),1)||!add(no.b)) return BoundTerm.init;
		auto step=nodes[no.b];
		bool recursive(uint id){
			auto q=nodes[id]; if(q.op!=BoundOp.apply||!variableAt(q.a,1)||!call(q.b,Builtin.subN)) return false;
			auto arg=nodes[q.b],amount=nodes[arg.b];
			return variableAt(arg.a,0)&&amount.op==BoundOp.scalar&&arena.isNumber(arena.at(amount.data))&&arena.number(arena.at(amount.data)).one;
		}
		bool reverse=recursive(step.b); auto forcing=reverse?step.a:step.b;
		if(!(reverse||recursive(step.a))||depends(at(forcing),1)) return BoundTerm.init;
		auto outer=context(t),inner=push(outer,scalarType(Sort.natural)),summandScope=push(inner,scalarType(Sort.natural));
		BoundTerm[] baseValues=[scalar(inner,arena.natural_(0)),bottom(inner,type(t))];
		foreach(i;0..depth(outer)) baseValues~=variable(inner,i+1);
		auto base=substitute(at(yes.b),inner,baseValues);
		auto successor=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(summandScope,0),scalar(summandScope,arena.natural_(1))]);
		BoundTerm[] values=[successor,bottom(summandScope,type(t))];
		foreach(i;0..depth(outer)) values~=variable(summandScope,i+2);
		auto summand=lambda(substitute(at(forcing),summandScope,values));
		auto prefix=finiteSum(summand,variable(inner,0));
		auto output=inheritHint(at(n.a),lambda(primitive(scalarOperator(ty.fields[1],TensorOp.add),[base,prefix])));
		solution=RecurrenceSolution(t.id,output.id,yes.b,forcing); solution.prefix=true; solution.left=reverse; return output;
	}
	private BoundTerm solveLinearRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),ty=pool.view(type(t)); if(ty.fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(ty.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		if(!numeric) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool variableAt(uint id,uint index){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==index; }
		bool constant(uint id){ auto q=nodes[id]; return q.op==BoundOp.scalar&&recurrenceConstant(arena.at(q.data)); }
		bool arithmetic(uint id,bool mul){
			auto q=nodes[id]; if(q.op!=BoundOp.primitive) return false;
			auto a=arena.view(arena.at(q.data)),b=arena.view(scalarOperator(ty.fields[1],mul?TensorOp.mul:TensorOp.add)); return a.op==b.op&&a.value==b.value;
		}
		uint lag(uint id){
			auto q=nodes[id]; if(q.op!=BoundOp.apply||!variableAt(q.a,1)||!call(q.b,Builtin.subN)) return 0;
			auto arg=nodes[q.b],amount=nodes[arg.b]; if(!variableAt(arg.a,0)||amount.op!=BoundOp.scalar) return 0;
			auto v=arena.at(amount.data); if(!arena.isNumber(v)) return 0;
			auto k=arena.number(v).re.integer; return k>0&&k<=16?cast(uint)k:0;
		}
		auto body=nodes[n.a].a,tail=body; uint test,yes,no; bool reverse;
		while(recurrenceBranches(tail,test,yes,no,reverse)){
			if(depends(at(yes),1)==depends(at(no),1)||depends(at(test),1)) break;
			tail=depends(at(yes),1)?yes:no;
		}
		if(tail==body) return BoundTerm.init;
		uint order;
		bool scan(uint id){
			if(constant(id)) return true;
			auto k=lag(id); if(k){ if(k>order) order=k; return true; }
			auto q=nodes[id]; if(arithmetic(id,false)) return scan(q.a)&&scan(q.b);
			return arithmetic(id,true)&&((constant(q.a)&&scan(q.b))||(constant(q.b)&&scan(q.a)));
		}
		if(!scan(tail)||!order) return BoundTerm.init;
		uint variableIndex;
		foreach(id;0..arena.length){ auto q=arena.view(arena.at(cast(uint)id)); if(q.op==Op.variable){ enforce(q.value<uint.max-1,"scalar variable limit exceeded"); if(q.value>=variableIndex) variableIndex=cast(uint)q.value+1; } }
		auto argument=arena.variable(Sort.natural,variableIndex);
		RecurrenceFact[] facts; Term[] seeds;
		bool fact(uint id,uint index,out Term output){
			auto arg=index==uint.max?arena.call(Builtin.addN,[argument,arena.natural_(order)]):arena.natural_(index);
			auto input=scalarBody(at(id),arg); if(input==Term.init) return false;
			auto options=Options(DensityMode.preserve,true),d=simplifyDomain(arena,input,[],options),v=simplify(arena,input,options);
			if(d.exhausted||v.exhausted||d.output!=arena.boolean(true)) return false;
			output=arena.castTo(v.output,arena.sort(input)); facts~=RecurrenceFact(id,index,input,d,v); return true;
		}
		bool prefix(){
			facts=null; seeds=null;
			auto id=body; Term output;
			while(id!=tail){
				if(!recurrenceBranches(id,test,yes,no,reverse)||!fact(test,uint.max,output)) return false;
				auto next=output==arena.boolean(true)?yes:output==arena.boolean(false)?no:uint.max;
				if(next==uint.max||!depends(at(next),1)) return false; id=next;
			}
			foreach(i;0..order){
				id=body;
				while(depends(at(id),1)){
					if(id==tail||!recurrenceBranches(id,test,yes,no,reverse)||!fact(test,i,output)) return false;
					id=output==arena.boolean(true)?yes:output==arena.boolean(false)?no:uint.max; if(id==uint.max) return false;
				}
				if(!fact(id,i,output)||!recurrenceConstant(output)) return false; seeds~=output;
			}
			return true;
		}
		for(;order<=16;++order) if(prefix()) break;
		if(order>16) return BoundTerm.init;
		auto zero=arena.number(Number(0),sort),one=arena.number(Number(1),sort);
		Law[3] laws;
		final switch(sort){
			case Sort.natural:laws=[Law.natural_affine_add,Law.natural_affine_left,Law.natural_affine_right]; break;
			case Sort.integer:laws=[Law.integer_affine_add,Law.integer_affine_left,Law.integer_affine_right]; break;
			case Sort.rational:laws=[Law.rational_affine_add,Law.rational_affine_left,Law.rational_affine_right]; break;
			case Sort.real_:laws=[Law.real_affine_add,Law.real_affine_left,Law.real_affine_right]; break;
			case Sort.complex:laws=[Law.complex_affine_add,Law.complex_affine_left,Law.complex_affine_right]; break;
			case Sort.boolean,Sort.density,Sort.measure:assert(0);
		}
		void coefficients(Law law,Term[] args,out Term coefficient,out Term offset){
			auto expression=instantiate(arena,law,args~one,true).result;
			coefficient=arena.viewChild(arena.viewChild(expression,0),0); offset=arena.viewChild(expression,1);
		}
		void collect(uint id,out Term[] c,out Term b){
			c=new Term[order]; c[]=zero; b=zero; auto q=nodes[id];
			if(constant(id)){ b=arena.at(q.data); return; }
			auto k=lag(id); if(k){ c[order-k]=one; return; }
			Term[] x,y; Term u,v;
			if(arithmetic(id,false)){
				collect(q.a,x,u); collect(q.b,y,v);
				foreach(i;0..order) coefficients(laws[0],[x[i],u,y[i],v],c[i],b);
			}else{
				bool left=constant(q.a); auto value=arena.at(nodes[left?q.a:q.b].data); collect(left?q.b:q.a,x,u);
				foreach(i;0..order) coefficients(laws[left?1:2],left?[value,x[i],u]:[x[i],u,value],c[i],b);
			}
		}
		Term[] coefficients_; Term offset; collect(tail,coefficients_,offset);
		auto inner=push(context(t),ty.fields[0]),vec=pool.vector(ty.fields[1],order+1),mat=pool.vector(vec,order+1);
		BoundTerm[] rows;
		foreach(i;0..order+1){
			BoundTerm[] cells;
			foreach(j;0..order+1){
				auto value=i==order?(j==order?one:zero):i+1==order?(j==order?offset:coefficients_[j]):j==i+1?one:zero;
				cells~=scalar(inner,value);
			}
			rows~=tuple(inner,cells,vec);
		}
		BoundTerm[] values; foreach(seed;seeds) values~=scalar(inner,seed); values~=scalar(inner,one);
		auto matrix=tuple(inner,rows,mat),initial=tuple(inner,values,vec);
		auto output=inheritHint(at(n.a),lambda(get(tensor(TensorOp.matvec,tensor(TensorOp.power,matrix,variable(inner,0)),initial),scalar(inner,arena.natural_(0)))));
		solution=RecurrenceSolution(t.id,output.id,0,tail); solution.order=order; solution.variable=variableIndex; solution.seeds=seeds; solution.facts=facts; return output;
	}
	private bool literalNumber(Term t,out Number value){
		if(arena.isNumber(t)){ value=arena.number(t); return true; }
		auto q=arena.view(t); return q.op==Op.builtin&&q.value>=Builtin.castNZ&&q.value<=Builtin.castRC&&literalNumber(arena.viewChild(t,0),value);
	}
	private BoundTerm spectral(BoundTerm t,out SpectralSolution solution){
		auto n=node(t); if(n.op!=BoundOp.tensor||n.data!=TensorOp.matvec) return BoundTerm.init;
		auto p=nodes[n.a]; if(p.op!=BoundOp.tensor||p.data!=TensorOp.power) return BoundTerm.init;
		auto mt=pool.view(type(at(p.a))),row=pool.view(mt.fields[0]);
		if(!mt.dimension.constant||!row.dimension.constant||!mt.length||mt.length>16||mt.length!=row.length) return BoundTerm.init;
		auto size=cast(uint)mt.length,sort=elementSort(row.fields[0]),ctx=context(t);
		solution=SpectralSolution(t.id,0,size); solution.diagonal=true;
		bool elements(uint id,uint count,out uint[] values){
			foreach(i;0..count){ auto q=nodes[id]; if(q.op!=BoundOp.vectorCons) return false; values~=q.a; id=q.b; }
			return nodes[id].op==BoundOp.vectorNil;
		}
		uint[] rows,values; if(!elements(p.a,size,rows)||!elements(n.b,size,values)) return BoundTerm.init;
		foreach(i,r;rows){
			uint[] cells; if(!elements(r,size,cells)) return BoundTerm.init;
			foreach(j,c;cells){
				if(nodes[c].op!=BoundOp.scalar) return BoundTerm.init;
				auto v=arena.at(nodes[c].data); solution.matrix~=v;
				Number number; if(i!=j&&(!literalNumber(v,number)||!number.zero)) solution.diagonal=false;
			}
		}
		foreach(v;values){ if(nodes[v].op!=BoundOp.scalar) return BoundTerm.init; solution.vector~=arena.at(nodes[v].data); }
		if(!solution.diagonal){
			// Diagonal powers preserve an undefined exponent componentwise, as
			// certified by Spectral.diagonal_value for an arbitrary Option Nat.
			// Keep the totality restriction for the other spectral constructions.
			if(!definitionallyTotal(at(p.b))) return BoundTerm.init;
			if(size==3){
				Number[9] entries; bool numeric=true;
				foreach(i,v;solution.matrix) if(!literalNumber(v,entries[i])) numeric=false;
				if(numeric){
					solution.cubeZero=true;
					foreach(i;0..3) foreach(j;0..3){
						auto entry=Number(0);
						foreach(k;0..3) foreach(l;0..3) entry=entry+entries[i*3+k]*entries[k*3+l]*entries[l*3+j];
						if(!entry.zero) solution.cubeZero=false;
					}
				}
			}
			// Keep unsupported scalar mask normalizations symbolic: nonreal complex coefficients
			// and symbolic real/complex seeds can exhaust the scalar normalizer.
			if(solution.cubeZero&&(sort==Sort.real_||sort==Sort.complex)) foreach(v;solution.vector){
				Number value; if(!literalNumber(v,value)||sort==Sort.complex&&!value.im.zero) solution.cubeZero=false;
			}
			if(solution.cubeZero&&sort==Sort.complex) foreach(v;solution.matrix){
				Number value; if(!literalNumber(v,value)||!value.im.zero) solution.cubeZero=false;
			}
			if(size>3) foreach(k;1..size){
				bool separate=true;
				foreach(i;0..size) foreach(j;0..size) if((i<k)!=(j<k)){
					Number number; if(!literalNumber(solution.matrix[i*size+j],number)||!number.zero) separate=false;
				}
				if(separate){ solution.split=k; break; }
			}
			if(!solution.split&&!solution.cubeZero){
				if(size>3||sort==Sort.natural||sort==Sort.integer) return BoundTerm.init;
				foreach(v;solution.matrix){ Number number; if(!literalNumber(v,number)) return BoundTerm.init; }
				if(size==3){
					bool block=true;
					foreach(i;[2,5,6,7]){ Number number; literalNumber(solution.matrix[i],number); if(!number.zero) block=false; }
					if(!block){
						Number[] a; foreach(v;solution.matrix){ Number number; literalNumber(v,number); a~=number; }
						auto determinant=a[0]*(a[4]*a[8]-a[5]*a[7])-a[1]*(a[3]*a[8]-a[5]*a[6])+a[2]*(a[3]*a[7]-a[4]*a[6]);
						auto trace=a[0]+a[4]+a[8],pairs=a[0]*a[4]+a[0]*a[8]+a[4]*a[8]-a[1]*a[3]-a[2]*a[6]-a[5]*a[7];
						solution.jordan=a[3].zero&&a[6].zero&&a[7].zero&&a[4]==a[8]&&!a[4].zero&&a[0]!=a[4];
						if(!solution.jordan&&(!determinant.zero||pairs.zero||(trace*trace-Number(4)*pairs).zero)) return BoundTerm.init;
						// Literal inputs bound coefficient normalization; every candidate is certified below.
						foreach(v;solution.vector){ Number number; if(!literalNumber(v,number)) return BoundTerm.init; }
						solution.zeroRoot=!solution.jordan;
					}
				}
			}
		}
		auto options=Options(DensityMode.preserve,true);
		Table!(uint,uint) parameters;
		bool parameter(Term t){
			if(parameters.get(t.id,uint.max)!=uint.max) return true;
			auto d=simplifyDomain(arena,t,[],options); if(d.exhausted||d.output!=arena.boolean(true)) return false;
			parameters.set(t.id,cast(uint)solution.parameters.length); solution.parameters~=SpectralFact(t,d); return true;
		}
		foreach(v;solution.matrix) if(!parameter(v)) return BoundTerm.init;
		foreach(v;solution.vector) if(!parameter(v)) return BoundTerm.init;
		if(solution.split){
			BoundTerm[] output;
			foreach(part;0..2){
				auto start=part?solution.split:0,count=part?size-solution.split:solution.split,vec=pool.vector(row.fields[0],count),mat=pool.vector(vec,count);
				BoundTerm[] blockRows,seed;
				foreach(i;start..start+count){
					BoundTerm[] cells; foreach(j;start..start+count) cells~=scalar(ctx,solution.matrix[i*size+j]);
					blockRows~=tuple(ctx,cells,vec); seed~=scalar(ctx,solution.vector[i]);
				}
				auto a=tuple(ctx,blockRows,mat),x=tuple(ctx,seed,vec);
				solution.blocks[part]=a.id; solution.blocks[part+2]=x.id;
				auto value=tensor(TensorOp.matvec,tensor(TensorOp.power,a,at(p.b)),x);
				foreach(i;0..count) output~=get(value,scalar(ctx,arena.natural_(i)));
			}
			auto result=tuple(ctx,output,type(t)); solution.target=result.id; return result;
		}
		auto zero=arena.number(Number(0),sort),neg=arena.number(Number(sort==Sort.natural?0:-1),sort);
		Term difference(Term a,Term b){ return arena.add(a,arena.mul(neg,b,true),true); }
		bool check(Term t,bool isZero){
			auto d=simplifyDomain(arena,t,[],options); if(d.exhausted||d.output!=arena.boolean(true)) return false;
			Result v;
			if(isZero){ v=simplify(arena,t,options); if(v.exhausted||!arena.isNumber(v.output)||!arena.number(v.output).zero) return false; }
			solution.checks~=SpectralFact(t,d,v); return true;
		}
		Term stepWith(Term[] matrix,Term[] vector,uint i){
			return arena.add(arena.add(arena.mul(matrix[i*3],vector[0],true),arena.mul(matrix[i*3+1],vector[1],true),true),arena.mul(matrix[i*3+2],vector[2],true),true);
		}
		Term step(Term[] vector,uint i){ return stepWith(solution.matrix,vector,i); }
		Term[] stepVector(Term[] vector){ Term[] result; foreach(i;0..3) result~=step(vector,i); return result; }
		if(solution.jordan){
			// For [a b c; 0 r d; 0 0 r], split the seed into an a-eigenvector
			// and a length-two r-chain. Check all identities before using them.
			Number[] a,v; foreach(term;solution.matrix){ Number x; literalNumber(term,x); a~=x; } foreach(term;solution.vector){ Number x; literalNumber(term,x); v~=x; }
			auto alpha=a[1]/(a[0]-a[4]),beta=(a[2]+alpha*a[5])/(a[0]-a[4]);
			auto u=v[0]+alpha*v[1]+beta*v[2],d=a[5]*v[2];
			foreach(x;[a[0],a[4],a[4]]) solution.roots~=arena.number(x,sort);
			foreach(x;[u,Number(0),Number(0),v[0]-u,v[1],v[2],-alpha*d,d,Number(0)]) solution.components~=arena.number(x,sort);
			solution.minus=neg;
			foreach(x;solution.roots~solution.components~[neg]) if(!parameter(x)) return BoundTerm.init;
			foreach(i;0..3) if(!check(difference(arena.add(solution.components[i],solution.components[3+i],true),solution.vector[i]),true)) return BoundTerm.init;
			foreach(j;0..3) foreach(i;0..3){
				auto rhs=arena.mul(solution.roots[j],solution.components[j*3+i],true);
				if(j==1) rhs=arena.add(rhs,solution.components[6+i],true);
				if(!check(difference(step(solution.components[j*3..j*3+3],i),rhs),true)) return BoundTerm.init;
			}
			if(!check(arena.inv(solution.roots[1]),false)) return BoundTerm.init;
		}

		if(solution.zeroRoot){
			Number[] a; foreach(v;solution.matrix){ Number number; literalNumber(v,number); a~=number; }
			auto trace=a[0]+a[4]+a[8],pairs=a[0]*a[4]+a[0]*a[8]+a[4]*a[8]-a[1]*a[3]-a[2]*a[6]-a[5]*a[7];
			auto rs=sort==Sort.complex?Sort.complex:Sort.real_;
			auto root=simplify(arena,arena.call(sort==Sort.complex?Builtin.sqrtC:Builtin.sqrtR,[arena.number(trace*trace-Number(4)*pairs,rs)]),options);
			if(root.exhausted||(sort==Sort.rational||sort==Sort.complex)&&!arena.isNumber(root.output)) return BoundTerm.init;
			// Irrational or nonreal complex components currently exceed scalar normalization budgets.
			if(sort==Sort.complex){
				if(!arena.number(root.output).im.zero) return BoundTerm.init;
				foreach(v;solution.matrix~solution.vector){ Number value; if(!literalNumber(v,value)||!value.im.zero) return BoundTerm.init; }
			}
			auto delta=arena.isNumber(root.output)?arena.number(arena.number(root.output),sort):arena.castTo(root.output,sort),half=arena.number(Number(1)/Number(2),sort);
			Term compact(Term x){ auto r=simplify(arena,x,options); return r.exhausted?Term.init:arena.castTo(r.output,sort); }
			auto r=compact(arena.mul(arena.add(arena.number(trace,sort),delta),half)),s=compact(arena.mul(difference(arena.number(trace,sort),delta),half));
			if(r==Term.init||s==Term.init) return BoundTerm.init;
			solution.roots=[zero,r,s]; solution.minus=neg;
			auto first=stepVector(solution.vector),second=stepVector(first); Term[][3] parts;
			foreach(i;0..3){
				auto cr=compact(arena.mul(difference(second[i],arena.mul(s,first[i],true)),arena.inv(arena.mul(r,difference(r,s),true)),true));
				auto cs=compact(arena.mul(difference(arena.mul(r,first[i],true),second[i]),arena.inv(arena.mul(s,difference(r,s),true)),true));
				if(cr==Term.init||cs==Term.init) return BoundTerm.init;
				auto c0=compact(difference(difference(solution.vector[i],cr),cs)); if(c0==Term.init) return BoundTerm.init;
				parts[0]~=c0; parts[1]~=cr; parts[2]~=cs;
			}
			foreach(part;parts) solution.components~=part;
			foreach(v;solution.roots~solution.components~[neg]) if(!parameter(v)) return BoundTerm.init;
			foreach(i;0..3) if(!check(difference(arena.add(arena.add(parts[0][i],parts[1][i],true),parts[2][i],true),solution.vector[i]),true)) return BoundTerm.init;
			foreach(j;0..3) foreach(i;0..3) if(!check(difference(step(parts[j],i),arena.mul(solution.roots[j],parts[j][i],true)),true)) return BoundTerm.init;
		}else if(solution.cubeZero){
			// Numeric detection is only a candidate filter; certify all nine entries of A³.
			foreach(i;0..3) foreach(j;0..3){
				Term[] column; foreach(k;0..3) column~=solution.matrix[k*3+j];
				if(!check(step(stepVector(column),i),true)) return BoundTerm.init;
			}
		}else if(!solution.diagonal&&!solution.jordan){
			auto a=solution.matrix[0],b=solution.matrix[1],c=solution.matrix[size],d=solution.matrix[size+1];
			Number av,bv,cv,dv; literalNumber(a,av); literalNumber(b,bv); literalNumber(c,cv); literalNumber(d,dv);
			auto trace=arena.number(av+dv,sort);
			auto discriminant=(av-dv)*(av-dv)+Number(4)*bv*cv;
			solution.repeated=discriminant.zero;
			solution.nilpotent=solution.repeated&&(av+dv).zero;
			auto rs=sort==Sort.complex?Sort.complex:Sort.real_;
			auto root=arena.call(sort==Sort.complex?Builtin.sqrtC:Builtin.sqrtR,[arena.number(discriminant,rs)]);
			auto simple=simplify(arena,root,options); if(simple.exhausted) return BoundTerm.init;
			if(sort==Sort.rational&&!arena.isNumber(simple.output)) return BoundTerm.init;
			root=arena.isNumber(simple.output)?arena.number(arena.number(simple.output),sort):arena.castTo(simple.output,sort);
			auto half=arena.number(Number(1)/Number(2),sort);
			solution.first=arena.mul(arena.add(trace,root),half); solution.second=arena.mul(difference(trace,root),half); solution.minus=neg;
			if(solution.repeated) solution.first=solution.second=arena.number((av+dv)/Number(2),sort);
			if(!parameter(solution.first)||!parameter(solution.second)||!parameter(neg)) return BoundTerm.init;
			if(!check(difference(arena.add(a,d,true),arena.add(solution.first,solution.second,true)),true)||
				!check(difference(difference(arena.mul(a,d,true),arena.mul(b,c,true)),arena.mul(solution.first,solution.second,true)),true)||
				(!solution.nilpotent&&!check(arena.inv(solution.repeated?solution.first:difference(solution.first,solution.second)),false))) return BoundTerm.init;
		}
		uint index;
		foreach(id;0..arena.length){ auto q=arena.view(arena.at(cast(uint)id)); if(q.op==Op.variable){ enforce(q.value<uint.max-1,"scalar variable limit exceeded"); if(q.value>=index) index=cast(uint)q.value+1; } }
		auto argument=arena.variable(Sort.natural,index),exponent=at(p.b);
		BoundTerm restore(Term v){
			if(v==argument) return exponent;
			auto q=arena.view(v); if(!q.arity) return scalar(ctx,v);
			BoundTerm[] args; bool plain=true;
			foreach(i;0..q.arity){ auto a=restore(arena.viewChild(v,i)); plain&=node(a).op==BoundOp.scalar; args~=a; }
			if(!plain) return primitive(v,args);
			Term[] values; foreach(a;args) values~=arena.at(node(a).data);
			return scalar(ctx,arena.viewRebuild(v,values,true));
		}
		auto power=sort==Sort.natural?Builtin.powNN:sort==Sort.integer?Builtin.powZN:sort==Sort.rational?Builtin.powQN:sort==Sort.real_?Builtin.powRN:Builtin.powCN;
		Term[] square;
		if(solution.cubeZero) foreach(i;0..3) foreach(j;0..3){
			Term[] column; foreach(k;0..3) column~=solution.matrix[k*3+j];
			square~=step(column,i);
		}
		Term[] firstValues,secondValues;
		if(solution.cubeZero){
			// Simplify the coefficients before introducing masks, and retain their equality certificates.
			foreach(matrix;[solution.matrix,square]) foreach(i;0..3){
				auto term=stepWith(matrix,solution.vector,i),domain=simplifyDomain(arena,term,[],options),value=simplify(arena,term,options);
				if(domain.exhausted||domain.output!=arena.boolean(true)||value.exhausted) return BoundTerm.init;
				solution.checks~=SpectralFact(term,domain,value);
				if(solution.checks.length<=12) firstValues~=arena.castTo(value.output,sort); else secondValues~=arena.castTo(value.output,sort);
			}
		}
		BoundTerm[] output;
		foreach(i;0..size){
			Term value;
			if(solution.jordan){
				auto cast_=arena.castTo(argument,sort),r=solution.roots;
				value=arena.add(arena.mul(arena.call(power,[r[0],argument]),solution.components[i],true),
					arena.mul(arena.call(power,[r[1],argument]),arena.add(solution.components[3+i],arena.mul(cast_,arena.mul(arena.inv(r[1]),solution.components[6+i],true),true),true),true),true);
			}else if(solution.zeroRoot){
				Term part(uint j){ return arena.mul(arena.call(power,[solution.roots[j],argument]),solution.components[j*3+i],true); }
				value=arena.add(arena.add(part(0),part(1),true),part(2),true);
			}else if(solution.cubeZero){
				Term atIndex(uint k){ auto literal=arena.natural_(k); return arena.and_(arena.le(literal,argument),arena.le(argument,literal)); }
				value=arena.add(arena.add(arena.mask(atIndex(0),solution.vector[i]),arena.mask(atIndex(1),firstValues[i]),true),arena.mask(atIndex(2),secondValues[i]),true);
			}else if(solution.diagonal||i==2) value=arena.mul(arena.call(power,[solution.matrix[i*size+i],argument]),solution.vector[i],true);
			else{
				auto first=arena.add(arena.mul(solution.matrix[i*size],solution.vector[0],true),arena.mul(solution.matrix[i*size+1],solution.vector[1],true),true);
				if(solution.nilpotent){
					// A²=0: retain both boundary values without dividing by the zero eigenvalue.
					auto one=arena.natural_(1);
					auto atZero=arena.not_(arena.nonzero(argument));
					auto atOne=arena.and_(arena.le(one,argument),arena.le(argument,one));
					value=arena.add(arena.mask(atZero,solution.vector[i]),arena.mask(atOne,first),true);
				}else if(solution.repeated){
					auto law=sort==Sort.rational?Law.rational_spectral_repeated:sort==Sort.real_?Law.real_spectral_repeated:Law.complex_spectral_repeated;
					value=instantiate(arena,law,[solution.vector[i],first,solution.first,argument],true).result;
				}else{
					auto law=sort==Sort.rational?Law.rational_spectral_interpolation:sort==Sort.real_?Law.real_spectral_interpolation:Law.complex_spectral_interpolation;
					value=instantiate(arena,law,[solution.vector[i],first,solution.first,solution.second,argument],true).result;
				}
			}
			output~=restore(value);
		}
		auto result=tuple(ctx,output,type(t)); solution.target=result.id; return result;
	}
	private BoundTerm liftSpectrum(BoundTerm t,out uint promoted){
		auto n=node(t); if(n.op!=BoundOp.tensor||n.data!=TensorOp.matvec) return BoundTerm.init;
		auto p=nodes[n.a]; if(p.op!=BoundOp.tensor||p.data!=TensorOp.power||!definitionallyTotal(at(p.b))) return BoundTerm.init;
		auto mt=pool.view(type(at(p.a))),row=pool.view(mt.fields[0]),sort=elementSort(row.fields[0]);
		if(sort!=Sort.natural&&sort!=Sort.integer||!mt.dimension.constant||!row.dimension.constant||mt.length<2||mt.length>3||mt.length!=row.length) return BoundTerm.init;
		auto ctx=context(t),size=cast(uint)mt.length;
		Term[] coefficients;
		bool entries(uint id,uint depth){
			if(!depth){ if(nodes[id].op!=BoundOp.scalar) return false; coefficients~=arena.at(nodes[id].data); return true; }
			foreach(i;0..size){ auto v=nodes[id]; if(v.op!=BoundOp.vectorCons||!entries(v.a,depth-1)) return false; id=v.b; }
			return nodes[id].op==BoundOp.vectorNil;
		}
		if(!entries(p.a,2)) return BoundTerm.init;
		Number[] values; foreach(c;coefficients){ Number v; if(!literalNumber(c,v)) return BoundTerm.init; values~=v; }
		auto delta=(values[0]-values[size+1])*(values[0]-values[size+1])+Number(4)*values[1]*values[size];
		if(size==3){
			bool block=true; foreach(i;[2,5,6,7]) if(!values[i].zero) block=false;
			if(!block){
				auto a=values,trace=a[0]+a[4]+a[8],pairs=a[0]*a[4]+a[0]*a[8]+a[4]*a[8]-a[1]*a[3]-a[2]*a[6]-a[5]*a[7];
				delta=a[3].zero&&a[6].zero&&a[7].zero&&a[4]==a[8]&&!a[4].zero&&a[0]!=a[4]?(a[0]-a[4])*(a[0]-a[4]):trace*trace-Number(4)*pairs;
			}
		}
		auto target=delta.re<Rational(0)?Sort.complex:Sort.real_,leaf=scalarType(target),vec=pool.vector(leaf,size),mat=pool.vector(vec,size);
		BoundTerm lift(uint id,uint depth){
			auto v=nodes[id];
			if(!depth){ if(v.op!=BoundOp.scalar) return BoundTerm.init; Number value; if(!literalNumber(arena.at(v.data),value)) return BoundTerm.init; return scalar(ctx,arena.castTo(arena.at(v.data),target)); }
			BoundTerm[] xs;
			foreach(i;0..size){ v=nodes[id]; if(v.op!=BoundOp.vectorCons) return BoundTerm.init; auto x=lift(v.a,depth-1); if(x==BoundTerm.init) return x; xs~=x; id=v.b; }
			if(nodes[id].op!=BoundOp.vectorNil) return BoundTerm.init;
			return tuple(ctx,xs,depth==1?vec:mat);
		}
		auto matrix=lift(p.a,2),initial=lift(n.b,1); if(matrix==BoundTerm.init||initial==BoundTerm.init) return BoundTerm.init;
		auto source=tensor(TensorOp.matvec,tensor(TensorOp.power,matrix,at(p.b)),initial);
		SpectralSolution probe; if(spectral(source,probe)==BoundTerm.init) return BoundTerm.init;
		BoundTerm[] output;
		foreach(i;0..size){
			auto value=get(source,scalar(ctx,arena.natural_(i)));
			if(target==Sort.complex) value=primitive(arena.call(Builtin.reC,[arena.complex(0)]),[value]);
			output~=primitive(arena.call(sort==Sort.natural?Builtin.floorN:Builtin.floorR,[arena.real_(0)]),[value]);
		}
		promoted=source.id; return tuple(ctx,output,type(t));
	}
	private bool definitionallyTotal(BoundTerm t){
		auto n=node(t);
		if(n.op==BoundOp.variable||n.op==BoundOp.global||n.op==BoundOp.lambda||n.op==BoundOp.typeValue||n.op==BoundOp.unit||n.op==BoundOp.vectorNil) return true;
		if(n.op==BoundOp.scalar) return totalScalar(t);
		return (n.op==BoundOp.vectorCons||n.op==BoundOp.pair)&&definitionallyTotal(at(n.a))&&definitionallyTotal(at(n.b));
	}
	private bool domainStrict(BoundNode n){
		if(n.op==BoundOp.sequence) return true;
		if(n.op!=BoundOp.primitive) return false;
		auto q=arena.view(arena.at(n.data));
		if(q.op==Op.builtin) return builtinInfo(cast(Builtin)q.value).total;
		return q.op==Op.add||q.op==Op.mul||q.op==Op.lt||q.op==Op.le||q.op==Op.nonzero||q.op==Op.not_||q.op==Op.conj||q.op==Op.abs||q.op==Op.pow;
	}
	// Commuting consumers must preserve bottom in the selected argument.
	// In particular, domain/defined/holds and inactive Boolean branches do not.
	private bool conditionalStrict(BoundNode n,bool right=false){
		switch(n.op){
			case BoundOp.apply,BoundOp.sequence,BoundOp.first,BoundOp.rest,BoundOp.get,
				BoundOp.member,BoundOp.subset,BoundOp.typeEq,BoundOp.equal,BoundOp.tensor:return true;
			case BoundOp.primitive:
				auto q=arena.view(arena.at(n.data));
				return !right||q.op!=Op.mask&&q.op!=Op.and_&&q.op!=Op.or_;
			default:return false;
		}
	}

	private bool rankDomain(BoundTerm fixed_,out DomainRank rank){
		auto n=node(fixed_),ty=pool.view(type(fixed_));
		bool scalar;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean]) if(ty.fields[0]==scalarType(s)){ rank.sort=s; scalar=true; break; }
		if(!scalar) return false;
		uint index;
		foreach(id;0..arena.length){ auto q=arena.view(arena.at(cast(uint)id)); if(q.op==Op.variable){ enforce(q.value<uint.max-1,"scalar variable limit exceeded"); if(q.value>=index) index=cast(uint)q.value+1; } }
		auto argument=arena.variable(rank.sort,index); rank.source=fixed_.id; rank.variable=index;
		Term leaf(uint id){
			foreach(d;rank.leaves) if(d.node==id) return d.domain.output;
			auto value=scalarBody(at(id),argument); if(value==Term.init) return Term.init;
			auto domain=simplifyDomain(arena,value,[],Options(DensityMode.preserve,true));
			if(domain.exhausted) return Term.init;
			rank.leaves~=DomainLeaf(id,value,domain); return domain.output;
		}
		Term substitute(Term t,Term value){
			Table!(uint,uint) memo;
			Term go(Term x){
				if(x==argument) return value;
				auto old=memo.get(x.id,uint.max); if(old!=uint.max) return arena.at(old);
				auto q=arena.view(x); Term[] cs;
				foreach(i;0..q.arity) cs~=go(arena.viewChild(x,i));
				auto y=cs.length?arena.viewRebuild(x,cs,true):x; memo.set(x.id,y.id); return y;
			}
			return go(t);
		}
		Term candidate; bool restricted;
		Term visit(uint id){
			auto q=nodes[id];
			if(!depends(at(id),1)) return leaf(id);
			if(q.op==BoundOp.apply){
				if(nodes[q.a].op!=BoundOp.variable||nodes[q.a].data!=1||depends(at(q.b),1)) return Term.init;
				auto d=leaf(q.b),value=scalarBody(at(q.b),argument);
				if(d==Term.init||value==Term.init) return Term.init;
				if(rank.step!=Term.init){
					auto x=arena.mul(rank.slope,argument,true),y=arena.mul(rank.slope,value,true);
					return arena.and_(d,arena.and_(arena.lt(rank.bound,x),arena.le(arena.add(y,rank.step,true),x)));
				}
				auto test=candidate==Term.init?arena.lt(value,argument):substitute(candidate,value);
				if(restricted) test=arena.and_(arena.lt(value,argument),test);
				return arena.and_(d,test);
			}
			auto op=q.op==BoundOp.primitive?arena.view(arena.at(q.data)).op:Op.variable;
			if(q.op==BoundOp.guard||op==Op.mask||op==Op.and_||op==Op.or_){
				if(depends(at(q.a),1)) return Term.init;
				auto dp=leaf(q.a),p=scalarBody(at(q.a),argument),d=visit(q.b);
				if(dp==Term.init||p==Term.init||d==Term.init) return Term.init;
				return q.op==BoundOp.guard?arena.and_(arena.and_(dp,p),d):arena.and_(dp,arena.or_(op==Op.or_?p:arena.not_(p),d));
			}
			if(!domainStrict(q)) return Term.init;
			auto x=visit(q.a); if(x==Term.init||q.b==uint.max) return x;
			auto y=visit(q.b); return y==Term.init?Term.init:arena.and_(x,y);
		}
		auto options=Options(DensityMode.preserve,true); options.maxRewrites=4096; options.maxAlgebraWork=65536;

		if(rank.sort==Sort.natural){
			auto condition=visit(nodes[n.a].a); if(condition==Term.init) return false;
			rank.result=simplify(arena,condition,[],options);
			auto out_=arena.view(rank.result.output);
			if(!rank.result.exhausted&&out_.op==Op.boolLit&&out_.value) return true;
			if(!rank.result.exhausted){
				candidate=rank.result.output; restricted=true;
				auto lower=simplify(arena,arena.or_(arena.not_(candidate),visit(nodes[n.a].a)),[],options);
				restricted=false;
				if(!lower.exhausted&&lower.output==arena.boolean(true)){
					auto upper=simplify(arena,arena.or_(arena.not_(visit(nodes[n.a].a)),candidate),[],options);
					if(!upper.exhausted&&upper.output==arena.boolean(true)){ rank.lower=lower; rank.upper=upper; return true; }
				}
				candidate=Term.init;
			}
		}
		if(rank.sort==Sort.real_){
			if(visit(nodes[n.a].a)==Term.init) return false;
			auto limit=Rational(0),step=Rational(1);
			foreach(l;rank.leaves){
				auto value=simplify(arena,l.value,options).output;
				foreach(id;arena.viewPostorder(value)) if(arena.isNumber(arena.at(id))){
					auto q=arena.number(arena.at(id)).re; if(q<Rational(0)) q=-q;
					if(q>limit) limit=q;
					if(q>Rational(0)&&q<step) step=q;
				}
			}
			rank.bound=arena.real_(-limit-Rational(1)); rank.step=arena.real_(step);
			foreach(slope;[1L,-1L]){
				rank.slope=arena.real_(slope);
				auto condition=visit(nodes[n.a].a); if(condition==Term.init) break;
				rank.result=simplify(arena,condition,[],options);
				if(!rank.result.exhausted&&rank.result.output==arena.boolean(true)) return true;
			}
			rank.slope=rank.bound=rank.step=Term.init;
		}
		candidate=arena.boolean(false);
		auto initial=arena.length;
		foreach(iteration;0..32){
			auto condition=visit(nodes[n.a].a); if(condition==Term.init) return false;
			auto step=simplify(arena,condition,[],options);
			if(step.exhausted||arena.length-initial>16384||arena.viewPostorder(step.output).length>256) return false;
			rank.iterations~=step;
			if(step.output==candidate) return true;
			candidate=step.output;
		}
		return false;
	}
	private BindingResult normalizeDependent(BoundTerm term,uint budget){
		uint steps; bool exhausted; Table!(uint,uint) memo;
		BoundTerm visit(BoundTerm t,uint depth=0){
			if(depth>=128||steps>=budget){ exhausted=true; return t; }
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return at(old);
			auto n=node(t); BoundTerm[] args;
			if(n.a!=uint.max) args~=visit(at(n.a),depth+1);
			if(n.op==BoundOp.conditional){
				auto predicate=node(args[0]);
				if(predicate.op==BoundOp.scalar&&arena.view(arena.at(predicate.data)).op==Op.boolLit){
					++steps; auto r=visit(at(arena.view(arena.at(predicate.data)).value?n.b:n.c),depth+1); memo.set(t.id,r.id); return r;
				}
				if(predicate.op==BoundOp.bottom){ ++steps; auto r=bottom(context(t),type(t)); memo.set(t.id,r.id); return r; }
			}
			if(n.b!=uint.max) args~=visit(at(n.b),depth+1);
			if(n.c!=uint.max) args~=visit(at(n.c),depth+1);
			auto r=args.length?rebuild(t,context(t),args):t; n=node(r);
			if(n.op==BoundOp.apply&&nodes[n.a].op==BoundOp.lambda&&definitionallyTotal(at(n.b))){
				++steps; r=visit(beta(at(nodes[n.a].a),at(n.b)),depth+1);
			}else if(n.op==BoundOp.sequence&&definitionallyTotal(at(n.a))){ ++steps; r=at(n.b); }
			memo.set(t.id,r.id); return r;
		}
		auto output=visit(term); BindingResult r; r.input=term; r.output=output; r.exhausted=exhausted; return r;
	}
	BindingResult normalize(BoundTerm term,uint budget=4096,bool domains=false){
		if(telescope_) return normalizeDependent(term,budget);
		check(term); uint steps,fixedSteps; bool exhausted; BindingStep[] proofs; ScalarDomain[] scalarDomains; RecurrenceSolution[] solutions; DomainRank[] ranks; SpectralSolution[] spectra; SummationSolution[] sums; IntegralSolution[] integrals; FibreStep[][] fibres; AffineChart[] affineCharts; CoverStep[] covers; LimitSolution[] limits; CoordinateGrid[] coordinates;
		struct Result{ uint output,proof; }
		Table!(uint,Result) memo;
		Table!(uint,bool) active;
		uint emit(BindingRule rule,uint from,uint to,uint left=uint.max,uint right=uint.max,uint extra=uint.max){
			enforce(proofs.length<1_000_000,"binding proof limit exceeded");
			proofs~=BindingStep(rule,from,to,left,right,extra); return cast(uint)proofs.length-1;
		}
		Result delegate(BoundTerm,uint) @safe visit;
		Result sumDefined(BoundTerm sum,uint depth){
			auto value=visit(sum,depth),v=nodes[value.output];
			if(v.op!=BoundOp.scalar)return Result(uint.max,uint.max);
			auto source=arena.at(v.data),opts=Options(DensityMode.preserve,true);
			opts.maxRewrites=512;opts.maxAlgebraWork=16384;
			auto domain=simplifyDomain(arena,source,[],opts);
			if(domain.exhausted||domain.output!=arena.boolean(true))return Result(uint.max,uint.max);
			auto extra=cast(uint)scalarDomains.length;scalarDomains~=ScalarDomain(source,domain);
			auto from=defined(sum),middle=defined(at(value.output)),out_=scalar(context(sum),domain.output);
			auto first=emit(BindingRule.congr,from.id,middle.id,value.proof);
			auto second=emit(BindingRule.scalarDomain,middle.id,out_.id,uint.max,uint.max,extra);
			return Result(out_.id,emit(BindingRule.trans,from.id,out_.id,first,second));
		}
		BoundTerm normalizeNullEdits(BoundTerm t,out IntegralSolution solution){
			auto n=node(t); if(n.op!=BoundOp.distributionMass) return BoundTerm.init;
			auto arg=arena.variable(Sort.real_,cast(uint)arena.length+1); uint[] weights;
			Term gather(uint id) @safe {
				auto d=nodes[id];
				if(d.op==BoundOp.distributionLebesgue) return arena.real_(1);
				if(d.op!=BoundOp.distributionWeight||nodes[d.a].op!=BoundOp.lambda) return Term.init;
				auto tail=gather(d.b); if(tail==Term.init) return Term.init;
				auto body=nodes[d.a].a,head=scalarBody(at(body),arg); if(head==Term.init) return Term.init;
				weights~=body; return arena.mul(tail,head,true);
			}
			auto expression=gather(n.a); IntegralBounds bounds;
			if(expression==Term.init||!integralBounds(arena,expression,arg,bounds)||bounds.zero||bounds.hasLower&&bounds.hasUpper) return BoundTerm.init;
			solution.from=weights; solution.exceptions=bounds.exceptions;
			if(!bounds.nulls.length) return BoundTerm.init;
			auto clean=arena.castTo(simplify(arena,removeIntegralNullGuards(arena,expression,arg)).output,Sort.real_);
			if(clean==expression) return BoundTerm.init;
			auto ctx=context(t),d=distribution(ctx,BoundOp.distributionLebesgue);
			Number constant;
			if(!literalNumber(clean,constant)||!constant.one){
				auto body=restoreBody(clean,push(ctx,scalarType(Sort.real_)),arg);
				solution.to=[body.id]; d=distribution(ctx,BoundOp.distributionWeight,[lambda(body),d]);
			}
			import std.algorithm:sort;
			auto sorted=solution.exceptions.dup;sort(sorted);solution.exceptions=[];
			foreach(q;sorted)if(!solution.exceptions.length||solution.exceptions[$-1]!=q)solution.exceptions~=q;
			solution.ae=true; return distribution(ctx,BoundOp.distributionMass,[d]);
		}
		BoundTerm integrateSteps(BoundTerm t,out IntegralSolution solution){
			auto n=node(t); if(n.op!=BoundOp.distributionMass||!densityBodies(n.a,solution.from)) return BoundTerm.init;
			auto ctx=context(t),arg=arena.variable(Sort.real_,cast(uint)arena.length+1); Rational[] cuts;
			bool collect(uint id){
				auto body=at(id),q=nodes[id];
				if(!depends(body,0)) return true;
				if(q.op!=BoundOp.primitive) return false;
				auto op=arena.view(arena.at(q.data));
				if(op.op==Op.mask){
					if(!collect(q.b)) return false;
					if(!depends(at(q.a),0)) return collect(q.a);
					auto predicate=scalarBody(at(q.a),arg); Rational[] points;
					if(predicate==Term.init||!integralCutPoints(arena,predicate,arg,points)) return false;
					cuts~=points; return true;
				}
				if(op.op==Op.mul||op.op==Op.add||op.op==Op.builtin&&
					(op.value==Builtin.addN||op.value==Builtin.addZ||op.value==Builtin.addQ||
					op.value==Builtin.mulN||op.value==Builtin.mulZ||op.value==Builtin.mulQ)) return collect(q.a)&&collect(q.b);
				return op.op==Op.builtin&&op.value>=Builtin.castNZ&&op.value<=Builtin.castQR&&collect(q.a);
			}
			foreach(id;solution.from) if(!collect(id)) return BoundTerm.init;
			import std.algorithm:sort;
			sort(cuts); Rational[] unique;
			foreach(q;cuts) if(!unique.length||unique[$-1]!=q) unique~=q;
			if(unique.length>16) return BoundTerm.init;
			if(!unique.length) unique=[Rational(0)];
			// Between cuts the guard truth values are constant. Require both
			// tails to vanish when defined; the certificate checks this claim
			// and separately retains failures in every cell and at every cut.
			bool zeroWhenDefined(uint id,Rational point){
				auto q=nodes[id];
				if(!depends(at(id),0)){
					auto value=scalarBody(at(id),arena.real_(point));
					if(value!=Term.init){
						auto normalized=simplify(arena,value);
						if(!normalized.exhausted&&arena.isNumber(normalized.output)&&arena.number(normalized.output).zero) return true;
					}
				}
				if(q.op!=BoundOp.primitive) return false;
				auto op=arena.view(arena.at(q.data));
				if(op.op==Op.mask){
					{
						auto predicate=scalarBody(at(q.a),arena.real_(point));
						if(predicate!=Term.init){
							auto normalized=simplify(arena,predicate);
							if(!normalized.exhausted&&normalized.output==arena.boolean(false)) return true;
						}
					}
					return zeroWhenDefined(q.b,point);
				}
				if(op.op==Op.add||op.op==Op.builtin&&(op.value==Builtin.addN||op.value==Builtin.addZ||op.value==Builtin.addQ))
					return zeroWhenDefined(q.a,point)&&zeroWhenDefined(q.b,point);
				if(op.op==Op.mul||op.op==Op.builtin&&(op.value==Builtin.mulN||op.value==Builtin.mulZ||op.value==Builtin.mulQ))
					return zeroWhenDefined(q.a,point)||zeroWhenDefined(q.b,point);
				return op.op==Op.builtin&&op.value>=Builtin.castNZ&&op.value<=Builtin.castQR&&zeroWhenDefined(q.a,point);
			}
			foreach(point;[unique[0]-Rational(1),unique[$-1]+Rational(1)]){
				bool zero; foreach(id;solution.from) zero|=zeroWhenDefined(id,point);
				if(!zero) return BoundTerm.init;
			}
			solution.exceptions=unique;
			solution.probes~=(unique[0]-Rational(1));
			foreach(i,q;unique){
				solution.probes~=q;
				if(i+1<unique.length){
					auto sample=(q+unique[i+1])/Rational(2);
					solution.probes~=sample; solution.cells~=IntegralCell(q,unique[i+1],sample);
				}
			}
			solution.probes~=(unique[$-1]+Rational(1));
			// Closed numeric weights have compact reflection certificates. Avoid
			// replaying scalar simplification separately for every probe.
			bool numerical(uint id){
				auto n=nodes[id];
				if(n.op==BoundOp.scalar){auto t=arena.at(n.data);return arena.isNumber(t)||arena.view(t).op==Op.boolLit;}
				if(n.op==BoundOp.variable)return n.data==0;
				if(n.op!=BoundOp.primitive)return false;
				auto op=arena.view(arena.at(n.data));
				bool allowed=op.op==Op.add||op.op==Op.mul||op.op==Op.mask||op.op==Op.lt||op.op==Op.le||op.op==Op.nonzero||op.op==Op.and_||op.op==Op.or_||op.op==Op.not_||
					op.op==Op.builtin&&(op.value>=Builtin.castNZ&&op.value<=Builtin.castQR||op.value==Builtin.addN||op.value==Builtin.addZ||op.value==Builtin.addQ||op.value==Builtin.mulN||op.value==Builtin.mulZ||op.value==Builtin.mulQ);
				return allowed&&numerical(n.a)&&(n.b==uint.max||numerical(n.b));
			}
			bool closed=true;foreach(id;solution.from)closed&=numerical(id);
			if(closed){
				Rational[] samples;
				foreach(point;solution.probes){
					auto value=Rational(1);
					foreach(id;solution.from){
						auto source=scalarBody(at(id),arena.real_(point)),r=simplify(arena,source);
						if(r.exhausted||!arena.isNumber(r.output)){closed=false;break;}
						value=value*arena.number(r.output).re;
					}
					if(!closed)break;
					samples~=value;
				}
				if(closed){
					foreach(i,c;solution.cells){solution.values~=samples[2+2*i];solution.value=solution.value+solution.values[$-1]*(c.upper-c.lower);}
					solution.closed=true;solution.piecewise=true;
					auto result=scalar(ctx,arena.real_(solution.value));solution.output=result.id;return result;
				}
			}

			auto result=scalar(ctx,arena.real_(0));
			foreach_reverse(c;solution.cells){
				auto value=scalar(ctx,arena.real_(1)),point=scalar(ctx,arena.real_(c.sample));
				foreach(id;solution.from) value=primitive(arena.mul(arena.real_(1),arena.real_(1),true),[value,apply(lambda(at(id)),point)]);
				auto term=primitive(arena.mul(arena.real_(1),arena.real_(1),true),[value,scalar(ctx,arena.real_(c.upper-c.lower))]);
				result=primitive(arena.add(arena.real_(0),arena.real_(0),true),[term,result]);
			}
			foreach_reverse(q;solution.probes){
				auto point=scalar(ctx,arena.real_(q));
				foreach_reverse(id;solution.from) result=sequence(apply(lambda(at(id)),point),result);
			}
			solution.piecewise=true; solution.output=result.id; return result;
		}
		// Partition the axis once for both mass and coordinate certificates.
		// Probe each singleton independently of the two adjacent formulas.
		bool polynomialGrid(uint[] factors,out PolynomialGrid grid,bool zeroTails=false,bool calculated=false){
			auto arg=arena.variable(Sort.real_,cast(uint)arena.length+1); Rational[] cuts;
			foreach(id;factors) if(!gridNumerical(id,calculated)||!gridCuts(id,arg,cuts)) return false;
			import std.algorithm:sort;
			sort(cuts); Rational[] unique;
			foreach(q;cuts) if(!unique.length||unique[$-1]!=q) unique~=q;
			if(unique.length>16) return false;
			if(!unique.length) unique=[Rational(0)];
			bool density(Rational sample,out Rational[] p){
				p=[Rational(1)];
				foreach(id;factors){ Rational[] w; if(!gridPolynomial(id,arg,sample,w)) return false; p=polyProduct(p,w); }
				return true;
			}
			grid.cuts=unique; grid.cells.length=unique.length+1;
			bool tail(size_t i,Rational sample){
				if(!density(sample,grid.cells[i])) return false;
				if(zeroTails) foreach(c;grid.cells[i]) if(!c.zero) return false;
				return true;
			}
			if(!tail(0,unique[0]-Rational(1))||!tail(unique.length,unique[$-1]+Rational(1))) return false;
			foreach(i;1..unique.length){
				auto sample=(unique[i-1]+unique[i])/Rational(2);
				if(!density(sample,grid.cells[i])) return false;
			}
			foreach(point;unique){
				auto height=Rational(1);
				foreach(id;factors){
					Term value;
					if(!gridValue(id,point,value)||!arena.isNumber(value)||!arena.number(value).im.zero) return false;
					height=height*arena.number(value).re;
				}
				grid.points~=height;
			}
			return true;
		}
		BoundTerm integratePolynomials(BoundTerm t,out IntegralSolution solution){
			auto n=node(t); if(n.op!=BoundOp.distributionMass||!densityBodies(n.a,solution.from)) return BoundTerm.init;
			PolynomialGrid grid; if(!polynomialGrid(solution.from,grid,true)) return BoundTerm.init;
			auto unique=grid.cuts,ctx=context(t);
			auto total=Rational(0);
			foreach(i;0..unique.length-1){
				auto lower=unique[i],upper=unique[i+1],sample=(lower+upper)/Rational(2),p=grid.cells[i+1];
				auto lo=lower,hi=upper;
				foreach(k,c;p){ total=total+c*(hi-lo)/Rational(cast(long)k+1); lo=lo*lower; hi=hi*upper; }
				if(total.words>128) return BoundTerm.init;
				solution.cells~=IntegralCell(lower,upper,sample);
			}
			solution.exceptions=unique; solution.value=total;
			solution.polynomial=true; solution.closed=true; solution.piecewise=true;
			auto result=scalar(ctx,arena.real_(total)); solution.output=result.id; return result;
		}
		// One lower and one upper bound of the axis, in either order, around a
		// sum of polynomials, each optionally times an exponential of rational
		// rate, with optional factors that do not mention the axis. Bounds and factors may be missing; the theorem is an equation
		// of partial values. Each antiderivative is evaluated at the two
		// bounds, and the certificate differentiates it.
		BoundTerm integrateInterval(BoundTerm t,out IntegralSolution solution,uint summand=uint.max,bool construct=true){
			auto n=node(t); if(n.op!=BoundOp.distributionMass) return BoundTerm.init;
			// A summand of the only weight is observed as a weight by itself.
			if(summand!=uint.max) solution.from=[summand];
			else if(!densityBodies(n.a,solution.from)||!solution.from.length) return BoundTerm.init;
			auto ctx=context(t),inner=context(at(solution.from[0])); IntervalData d;
			bool isOp(BoundNode q,Op op){return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==op;}
			bool call(BoundNode q,Builtin f){return isOp(q,Op.builtin)&&arena.view(arena.at(q.data)).value==f;}
			auto body=nodes[solution.from[0]]; uint around=uint.max;
			// The domain of a value that may be missing is a guard around the mask.
			if(body.op==BoundOp.guard){ around=body.a; body=nodes[body.b]; if(!isOp(body,Op.mask)) return BoundTerm.init; }
			if(call(body,Builtin.castQR)&&call(nodes[body.a],Builtin.castZQ)&&call(nodes[nodes[body.a].a],Builtin.castNZ)){
				auto bracket=nodes[nodes[nodes[body.a].a].a];
				if(!isOp(bracket,Op.mask)||nodes[bracket.b].op!=BoundOp.scalar||arena.at(nodes[bracket.b].data)!=arena.natural_(1)) return BoundTerm.init;
				d.guard=bracket.a; d.unit=bracket.b;
			}else if(isOp(body,Op.mask)){ d.guard=body.a; d.value=body.b; }
			else return BoundTerm.init;
			// Below a binder the two guards stay nested masks: their conjunction.
			// A single bound is a half-line.
			uint first=d.guard,second=uint.max;
			if(isOp(nodes[d.guard],Op.and_)){ first=nodes[d.guard].a; second=nodes[d.guard].b; }
			else if(d.unit==uint.max&&isOp(nodes[d.value],Op.mask)){ d.nested=true; second=nodes[d.value].a; d.value=nodes[d.value].b; }
			else d.half=true;
			bool bound(uint id,out bool lower,out bool strict,out uint term){
				auto c=nodes[id]; if(!isOp(c,Op.le)&&!isOp(c,Op.lt)) return false;
				strict=isOp(c,Op.lt);
				bool axis(uint i){auto v=nodes[i];return v.op==BoundOp.variable&&v.data==0;}
				if(axis(c.b)&&!depends(at(c.a),0)){ lower=true; term=c.a; return true; }
				if(axis(c.a)&&!depends(at(c.b),0)){ term=c.b; return true; }
				return false;
			}
			bool lower1,strict1,lower2,strict2; uint term1,term2;
			if(!bound(first,lower1,strict1,term1)) return BoundTerm.init;
			if(d.half){ d.below=!lower1; term2=term1; }
			else if(!bound(second,lower2,strict2,term2)||lower1==lower2) return BoundTerm.init;
			d.swap=!lower1; d.strictLower=lower1?strict1:strict2; d.strictUpper=lower1?strict2:strict1;
			// A value that may be missing where a term that does not mention the
			// axis is: it is under a strict guard of its domain, or the mask is
			// under the guard of its own domain, which holds wherever one of its
			// comparisons fails: their negations in order, then that domain.
			// The domain may also be that the axis is not zero, by itself or
			// with one that does not mention the axis: only around a quotient,
			// below.
			bool domainOf(uint rest){
				if(!depends(at(rest),0)){ d.domain=rest; return true; }
				// The axis is not zero, or its sum with a closed term is not.
				bool nonzeroAxis(uint id){
					auto test=nodes[id]; if(!isOp(test,Op.nonzero)) return false;
					bool variable_(uint i){ auto v=nodes[i]; return v.op==BoundOp.variable&&v.data==0; }
					if(variable_(test.a)){ d.axisPoint=Rational(0); d.axisClosed=uint.max; return true; }
					auto sum=nodes[test.a]; if(!isOp(sum,Op.add)) return false;
					Rational c; Term closed;
					if(!variable_(sum.a)||nodes[sum.b].op!=BoundOp.scalar||!closedRational(at(sum.b),c,closed)||c.zero) return false;
					d.axisPoint=Rational(0)-c; d.axisClosed=sum.b; return true;
				}
				// The axis is above a closed term: the domain of a logarithm.
				bool positiveAxis(uint id){
					auto test=nodes[id]; if(!isOp(test,Op.lt)) return false;
					auto x=nodes[test.b]; Rational c; Term closed;
					if(x.op!=BoundOp.variable||x.data!=0||nodes[test.a].op!=BoundOp.scalar||!closedRational(at(test.a),c,closed)) return false;
					d.axisPoint=c; d.axisClosed=test.a; d.axisPositive=true; return true;
				}
				auto both=nodes[rest];
				if(nonzeroAxis(rest)||positiveAxis(rest)){ d.axis=rest; return true; }
				if(!isOp(both,Op.and_)) return false;
				if(!depends(at(both.b),0)&&(nonzeroAxis(both.a)||positiveAxis(both.a))){ d.axis=both.a; d.domain=both.b; d.both=rest; d.joined=1; return true; }
				if(!depends(at(both.a),0)&&(nonzeroAxis(both.b)||positiveAxis(both.b))){ d.axis=both.b; d.domain=both.a; d.both=rest; d.joined=2; return true; }
				return false;
			}
			if(around!=uint.max){
				if(d.nested) return BoundTerm.init;
				auto o=nodes[around]; if(!isOp(o,Op.or_)||!negatedComparison(o.a,first)) return BoundTerm.init;
				auto rest=o.b;
				if(!d.half){ o=nodes[rest]; if(!isOp(o,Op.or_)||!negatedComparison(o.a,second)) return BoundTerm.init; rest=o.b; }
				if(!domainOf(rest)) return BoundTerm.init;
				d.hoisted=true;
			}else if(d.unit==uint.max&&nodes[d.value].op==BoundOp.guard&&domainOf(nodes[d.value].a)) d.value=nodes[d.value].b;
			auto outer=[Rational(1)],outerRate=Rational(0);
			foreach(id;solution.from[1..$]){
				Rational[] w; Rational rate; if(!axisExponential(id,w,rate)) return BoundTerm.init;
				outer=polyProduct(outer,w); outerRate=outerRate+rate; if(outer.length>64) return BoundTerm.init;
			}
			// Beyond a single bound an exponential must decay: above a lower
			// bound with a negative rate, below an upper one with a positive rate.
			bool decays(Rational rate){ return d.below?Rational(0)<rate:rate<Rational(0); }
			// A polynomial P times the exponential of a polynomial E that is not
			// constant has an antiderivative R·exp(E) exactly when R'+E'·R=P
			// has a polynomial solution: its coefficients follow from the
			// highest down, and then the equations of the lowest degrees must
			// hold. Beyond a single bound the exponent must descend, with the
			// rate and the order of its decay. Only without further weights.
			bool curve(Rational[] p,Rational[] exponent,out Rational[] R,out Rational[] E,out Rational rate,out size_t order){
				if(solution.from.length!=1) return false;
				E=exponent.dup;
				while(E.length&&E[$-1].zero) E.length=E.length-1;
				while(p.length&&p[$-1].zero) p.length=p.length-1;
				if(E.length<2||!p.length) return false;
				auto slope=new Rational[](E.length-1);
				foreach(j,ref c;slope) c=Rational(cast(long)j+1)*E[j+1];
				auto top=slope.length-1;
				if(p.length<=top) return false;
				R=new Rational[](p.length-top);
				foreach(ref c;R) c=Rational(0);
				Rational at(size_t k){ return k<R.length?R[k]:Rational(0); }
				foreach_reverse(n;top..p.length){
					auto rest=p[n]-Rational(cast(long)n+1)*at(n+1);
					foreach(j;0..top) if(n>=j) rest=rest-slope[j]*at(n-j);
					R[n-top]=rest/slope[top];
					if(R[n-top].words>128) return false;
				}
				foreach(n;0..top){
					auto sum=Rational(cast(long)n+1)*at(n+1);
					foreach(j;0..n+1) sum=sum+slope[j]*at(n-j);
					if(!(sum==p[n])) return false;
				}
				bool zero;
				return !d.half||vanishing(R,E,d.below,zero,rate,order)&&!zero;
			}
			// A polynomial times the exponential of a quadratic with negative
			// curvature beyond a single bound that is the vertex of the quadratic.
			// The polynomial is a constant κ up to a derivative, P=κ+R'+Q'·R: the
			// exponential has half its integral on either side of the vertex, and
			// the antiderivative R·exp(Q) vanishes at the end.
			bool vertex(Rational[] p,Rational[] exponent,ref IntervalTerm r){
				if(!d.half||solution.from.length!=1) return false;
				auto E=exponent.dup; Rational bound;
				while(E.length&&E[$-1].zero) E.length=E.length-1;
				while(p.length&&p[$-1].zero) p.length=p.length-1;
				if(E.length!=3||!(E[2]<Rational(0))||!p.length||!closedValue(term1,bound)) return false;
				if(!(bound*Rational(2)*E[2]==Rational(0)-E[1])) return false;
				GaussianData g; g.c0=E[0]; g.c1=E[1]; g.c2=E[2];
				auto R=new Rational[](p.length-1);
				Rational at_(size_t i){ return i<R.length?R[i]:Rational(0); }
				foreach_reverse(j;1..p.length) R[j-1]=(p[j]-Rational(cast(long)j+1)*at_(j+1)-g.c1*at_(j))/(Rational(2)*g.c2);
				g.constant=p[0]-at_(1)-g.c1*at_(0); g.primitive=R;
				g.vertex=g.c0-g.c1*g.c1/(Rational(4)*g.c2); g.width=Rational(-1)/g.c2;
				auto value=Rational(0); foreach_reverse(c;R) value=value*bound+c;
				r.point=bound; r.half=g.constant/Rational(2); r.rest=d.below?value:Rational(0)-value;
				foreach(c;R~[g.constant,g.vertex,g.width,r.half,r.rest,bound]) if(c.words>128) return false;
				r.bell=g; r.vertex=true; return true;
			}
			// The same between other bounds, with the error function around the
			// vertex of the quadratic: R·exp(Q) and the constant times that are an
			// antiderivative. Beyond a single bound the complement of the error
			// function vanishes at that end, below a bound with its argument
			// reflected.
			bool erf(Rational[] p,Rational[] exponent,ref IntervalTerm r){
				if(solution.from.length!=1) return false;
				auto E=exponent.dup;
				while(E.length&&E[$-1].zero) E.length=E.length-1;
				while(p.length&&p[$-1].zero) p.length=p.length-1;
				if(E.length!=3||!(E[2]<Rational(0))||!p.length) return false;
				GaussianData g; g.c0=E[0]; g.c1=E[1]; g.c2=E[2];
				auto R=new Rational[](p.length-1);
				Rational at_(size_t i){ return i<R.length?R[i]:Rational(0); }
				foreach_reverse(j;1..p.length) R[j-1]=(p[j]-Rational(cast(long)j+1)*at_(j+1)-g.c1*at_(j))/(Rational(2)*g.c2);
				g.constant=p[0]-at_(1)-g.c1*at_(0); g.primitive=R.length?R:[Rational(0)];
				g.vertex=g.c0-g.c1*g.c1/(Rational(4)*g.c2); g.width=Rational(-1)/g.c2;
				r.point=Rational(0)-g.c1/(Rational(2)*g.c2); r.half=g.constant/Rational(2); r.offset=d.below?r.point:Rational(0)-r.point;
				foreach(c;R~[g.constant,g.vertex,g.width,r.half,r.point]) if(c.words>128) return false;
				r.bell=g; r.erf=true; return true;
			}
			// The same under a constant where the constant and linear coefficients
			// of the exponent are terms that do not mention the axis: the exponent
			// is a quadratic by its structure, with a curvature that is a negative
			// rational, and its vertex is a multiple of the linear coefficient.
			bool symbolicErf(uint id,ref IntervalTerm r){
				if(solution.from.length!=1) return false;
				BellParts found;
				if(!bellParts(id,found,false)||!found.exponent||found.symbolic) return false;
				auto p=found.p,c=found.c; while(p.length&&p[$-1].zero) p.length=p.length-1;
				if(!p.length||p.length>17||!c[1].present||!c[2].present||!c[2].closed||!(c[2].value<Rational(0))) return false;
				GaussianData g; g.symbolic=true; g.constant=p[0]; g.c2=c[2].value;
				if(p.length>1){
					// A polynomial in front: `P = κ + R' + (c₁+2·c₂·x)·R` for a rest
					// `R` and a constant `κ` that are polynomials in the linear
					// coefficient. The coefficient of `xʲ` in `R` follows from
					// those above it, and `κ` from the lowest two; the rest is
					// kept as its rows in the powers of the linear coefficient.
					auto n=p.length-1,twice=Rational(2)*g.c2;
					auto R=new Rational[][](n);
					// `top - factor·above - c₁·here`, as polynomials in `c₁`.
					Rational[] combine(Rational[] top,Rational factor,Rational[] above,Rational[] here){
						auto sum=top.dup;
						void add(size_t i,Rational x){ while(sum.length<=i) sum~=Rational(0); sum[i]=sum[i]+x; }
						foreach(i,x;above) add(i,Rational(0)-factor*x);
						foreach(i,x;here) add(i+1,Rational(0)-x);
						return sum;
					}
					foreach_reverse(j;0..n){
						R[j]=combine([p[j+1]],Rational(cast(long)j+2),j+2<n?R[j+2]:null,j+1<n?R[j+1]:null);
						foreach(ref x;R[j]){ x=x/twice; if(x.words>128) return false; }
					}
					auto kappa=combine([p[0]],Rational(1),n>1?R[1]:null,R[0]);
					while(kappa.length>1&&kappa[$-1].zero) kappa.length=kappa.length-1;
					foreach(x;kappa) if(x.words>128) return false;
					size_t degree; foreach(j;0..n) if(R[j].length>degree) degree=R[j].length;
					auto rows=new Rational[][](degree);
					foreach(i,ref row;rows){
						foreach(j;0..n) row~=i<R[j].length?R[j][i]:Rational(0);
						while(row.length>1&&row[$-1].zero) row.length=row.length-1;
					}
					while(rows.length>1&&rows[$-1].length==1&&rows[$-1][0].zero) rows.length=rows.length-1;
					g.rows=rows; g.moments=kappa; g.constant=Rational(1);
				}
				g.vertex=Rational(-1)/(Rational(4)*g.c2); g.width=Rational(-1)/g.c2;
				r.point=Rational(1)/(Rational(2)*g.c2); r.half=g.constant/Rational(2); r.offset=d.below?Rational(0)-r.point:r.point;
				foreach(x;[g.constant,g.vertex,g.width,r.half,r.point]) if(x.words>128) return false;
				r.bell=g; r.erf=true; r.symbolic=true; return true;
			}
			// Beyond a single bound, a rational polynomial times the exponential
			// of a linear exponent whose rate is a term that does not mention the
			// axis. It is integrable exactly where the rate has the sign of
			// decay: the value of the antiderivative at the bound stands under
			// the guard of that sign. Only as the whole value, and not as a
			// summand: where the rate has the other sign the value is defined
			// and not integrable. With `h` the inverse of the rate the
			// antiderivative of `P·exp(c₀+c₁·x)` is `(h·P - h²·P' + h³·P'' - …)`
			// times the exponential: the rows are those polynomials, with the
			// sign of the end, after a row of zero for the power that is absent.
			static bool rateRows(Rational[] p,bool positive,out Rational[][] rows){
				rows=[[Rational(0)]]; Rational[] row;
				foreach(x;p) row~=positive?x:Rational(0)-x;
				while(row.length){
					foreach(x;row) if(x.words>128) return false;
					rows~=row;
					Rational[] derivative; foreach(i;1..row.length) derivative~=Rational(0)-Rational(cast(long)i)*row[i];
					row=derivative;
				}
				return true;
			}
			bool symbolicRate(uint id,ref IntervalTerm r){
				if(!d.half||d.unit!=uint.max||summand!=uint.max||solution.from.length!=1) return false;
				BellParts found;
				if(!bellParts(id,found,false)||!found.exponent||found.symbolic) return false;
				auto p=found.p,c=found.c; while(p.length&&p[$-1].zero) p.length=p.length-1;
				if(!p.length||p.length>17||c[2].present||!c[1].present||c[1].closed) return false;
				if(!rateRows(p,d.below,r.bell.rows)) return false;
				r.rateTerm=true; return true;
			}
			// Between two bounds the same is integrable whatever the rate, so
			// it is a term like any other. Where the rate is not zero its
			// integral is the difference of that antiderivative at the bounds.
			// Where it is zero the exponential is that of the constant, in
			// front of the difference of an antiderivative of the polynomial.
			// The integral is linear in the coefficients of a polynomial that
			// are terms: each meets the table and the antiderivative of its
			// power times the rational polynomial.
			bool symbolicRateBetween(uint id,ref IntervalTerm r){
				if(d.half||d.unit!=uint.max||solution.from.length!=1) return false;
				BellParts found;
				if(!bellParts(id,found,false)||!found.exponent) return false;
				auto p=found.p,c=found.c; while(p.length&&p[$-1].zero) p.length=p.length-1;
				auto count=found.symbolic?found.poly.length:1;
				if(!p.length||count+p.length>18||c[2].present||!c[1].present||c[1].closed) return false;
				Rational[][][] tables; Rational[][] primitives;
				foreach(j;0..count){
					Rational[][] rows; if(!rateRows(p,true,rows)) return false;
					auto antiderivative=[Rational(0)];
					foreach(i,x;p){
						auto q=x/Rational(cast(long)i+1); if(q.words>128) return false;
						antiderivative~=q;
					}
					tables~=rows; primitives~=antiderivative; p=Rational(0)~p;
				}
				if(found.symbolic){ r.bell.tables=tables; r.primitives=primitives; }
				else{ r.bell.rows=tables[0]; r.bell.primitive=primitives[0]; }
				r.rateTerm=true; return true;
			}
			// Beyond a single bound, a constant times the exponential of a
			// quadratic whose curvature is a term that does not mention the axis.
			// Where that term cannot vanish, by its form, the exponential is
			// integrable exactly where the curvature is negative, and the closed
			// form with the complement of the error function is missing exactly
			// where it is positive: no guard is needed. As for a rate, only as
			// the whole value.
			bool symbolicCurvature(uint id,ref IntervalTerm r){
				if(!d.half||d.unit!=uint.max||summand!=uint.max||solution.from.length!=1) return false;
				BellParts found;
				if(!bellParts(id,found,false)||!found.exponent||found.symbolic) return false;
				auto p=found.p,c=found.c; while(p.length&&p[$-1].zero) p.length=p.length-1;
				if(p.length!=1||!c[2].present||c[2].closed) return false;
				r.half=p[0]/Rational(2); if(r.half.words>128) return false;
				r.bell.constant=p[0]; r.curvatureTerm=true; return true;
			}
			// Decide before building anything: a refused integral leaves no
			// terms behind. Beyond a single bound every term must decay.
			bool admissible(uint id,uint depth){
				Rational[] p,exponent,R,E; Rational rate; bool scaled; size_t order; IntervalTerm r;
				if(scaledExponential(id,p,rate,scaled)) return !d.half||decays(rate+outerRate);
				if(tailExponential(id,false,p,exponent,scaled,false,0,true)) return curve(p,exponent,R,E,rate,order)||vertex(p,exponent,r)||erf(p,exponent,r);
				if(symbolicErf(id,r)||symbolicRateBetween(id,r)) return true;
				auto q=nodes[id];
				return depth<=16&&solution.from.length==1&&isOp(q,Op.add)&&admissible(q.a,depth+1)&&admissible(q.b,depth+1);
			}
			// Between two bounds, a polynomial over a power of the axis of which
			// a negative power is left. It is undefined at zero and not
			// integrable next to it, so it is observed exactly between bounds
			// on one side of zero: the difference of its antiderivative stands
			// under the guard of that. The antiderivative is
			// `A(x) + C(x)/x^M + κ·log|x|`, the quotient in it in lowest terms.
			// Beyond one bound the value is integrable out to infinity where
			// it has no power above the inverse square: then `A` and `κ` are
			// zero, and `C(x)/x^M` vanishes out there. Factors that do not
			// mention the axis may stand anywhere in a product with the
			// quotient. The powers may be those of the axis minus a rational
			// pole: all of this is then around the pole.
			bool axisQuotient(uint id,ref IntervalTerm r){
				if(d.unit!=uint.max||summand!=uint.max||solution.from.length!=1) return false;
				Rational[] p; size_t power; uint[] scale; Rational pole;
				if(!axisPole(id,pole)) pole=Rational(0);
				if(d.axis!=uint.max&&(d.axisPositive||!(pole==d.axisPoint))) return false;
				if(!axisFraction(id,p,power,scale,pole)||!power) return false;
				r.ratioPole=pole;
				bool left; foreach(k;0..power) if(k<p.length&&!p[k].zero) left=true;
				if(!left) return false;
				if(d.half) foreach(k;power-1..p.length) if(!p[k].zero) return false;
				r.ratioScale=scale;
				Rational at_(size_t k){ return k<p.length?p[k]:Rational(0); }
				auto A=[Rational(0)]; Rational[] C;
				foreach(k;power..p.length) A~=p[k]/Rational(cast(long)(k-power)+1);
				foreach(k;0..power-1) C~=at_(k)/(Rational(cast(long)k+1)-Rational(cast(long)power));
				while(A.length>1&&A[$-1].zero) A.length=A.length-1;
				while(C.length&&C[$-1].zero) C.length=C.length-1;
				// In lowest terms: without the powers of the axis that the
				// polynomial over the power has in common with it.
				size_t common; while(common<C.length&&C[common].zero) ++common;
				auto shift=C.length?power-1-common:1;
				C=C.length?C[common..$]:[Rational(0)];
				foreach(c;A~C) if(c.words>128) return false;
				r.bell.primitive=A; r.bell.moments=C; r.bell.constant=at_(power-1);
				r.ratioShift=cast(uint)shift; r.ratioTerm=true; return true;
			}
			// Between two bounds, a polynomial times the logarithm of the axis
			// minus a rational pole, plus a polynomial. The logarithm is
			// defined above the pole only, so the value is observed exactly
			// where the guard of the bounds is above it: the lower bound is,
			// or it is the pole and strict. With `y` for the axis minus the
			// pole the antiderivative is `y·P₁(y)·log(y) + y·S₁(y)`, where
			// `(y·P₁)' = p` and `(y·S₁)' = q - P₁`. Factors that do not
			// mention the axis may stand anywhere in a product with the
			// value: there it is integrable whatever they are, so their
			// product stands in front of the difference.
			bool axisLog(uint id,ref IntervalTerm r){
				if(d.half||d.unit!=uint.max||summand!=uint.max||solution.from.length!=1) return false;
				Rational pole; if(!axisLogPole(id,pole)) return false;
				if(d.axis!=uint.max&&(!d.axisPositive||!(pole==d.axisPoint))) return false;
				Rational[] p,q; bool found; uint[] scale;
				if(!axisLogFraction(id,p,q,pole,found,scale)||!found) return false;
				r.ratioScale=scale;
				Rational[] P,S;
				foreach(k,c;p) P~=c/Rational(cast(long)k+1);
				auto n=q.length>P.length?q.length:P.length;
				foreach(k;0..n) S~=((k<q.length?q[k]:Rational(0))-(k<P.length?P[k]:Rational(0)))/Rational(cast(long)k+1);
				while(P.length>1&&P[$-1].zero) P.length=P.length-1;
				while(S.length>1&&S[$-1].zero) S.length=S.length-1;
				if(!P.length) P=[Rational(0)];
				if(!S.length) S=[Rational(0)];
				foreach(c;P~S) if(c.words>128) return false;
				r.bell.primitive=P; r.bell.moments=S; r.ratioPole=pole; r.logTerm=true; return true;
			}
			IntervalTerm whole;
			d.direct=d.unit==uint.max&&!admissible(d.value,0)&&(symbolicRate(d.value,whole)||symbolicCurvature(d.value,whole)||axisQuotient(d.value,whole)||
				axisLog(d.value,whole));
			// A summand that is a term next to such a quotient or logarithm:
			// between two bounds the sum is integrable exactly where the other
			// summand is, and the term adds its multiple by the distance of
			// the bounds.
			if(!d.direct&&!d.half&&d.unit==uint.max&&!admissible(d.value,0)&&isOp(nodes[d.value],Op.add)){
				// A sum has such a term in front.
				auto sum=nodes[d.value]; IntervalTerm other;
				if(!depends(at(sum.a),0)&&depends(at(sum.b),0)&&(axisQuotient(sum.b,other)||axisLog(sum.b,other))){
					whole=other; d.direct=true; d.constant=sum.a; d.inner=sum.b;
				}
			}
			if(d.axis!=uint.max&&!(d.direct&&(whole.ratioTerm||whole.logTerm))) return BoundTerm.init;
			if(!d.direct&&(d.unit!=uint.max?d.half&&!decays(outerRate):!admissible(d.value,0))) return BoundTerm.init;
			if(!construct) return t;
			auto lower=dropIndex(at(lower1?term1:term2)),upper=dropIndex(at(lower1?term2:term1));
			auto addOp=arena.add(arena.real_(0),arena.real_(0),true),mulOp=arena.mul(arena.real_(1),arena.real_(1),true);
			auto minusOne=scalar(ctx,arena.real_(Rational(-1)));
			// x·(p₀/1+x·(p₁/2+…)), in Horner form, below the axis binder. With
			// a rate r the antiderivative of P·exp(r·x) is Q·exp(r·x), Q'+r·Q=P.
			BoundTerm antiderivative(Rational[] p,Rational rate){
				auto x=variable(inner,0);
				if(!p.length) return scalar(inner,arena.real_(Rational(0)));
				if(rate.zero){
					auto horner=scalar(inner,arena.real_(p[$-1]/Rational(cast(long)p.length)));
					foreach_reverse(k;0..p.length-1) horner=primitive(addOp,[scalar(inner,arena.real_(p[k]/Rational(cast(long)k+1))),primitive(mulOp,[x,horner])]);
					return primitive(mulOp,[x,horner]);
				}
				auto q=new Rational[](p.length);
				foreach_reverse(k;0..p.length) q[k]=(p[k]-(k+1<p.length?Rational(cast(long)k+1)*q[k+1]:Rational(0)))/rate;
				auto horner=scalar(inner,arena.real_(q[$-1]));
				foreach_reverse(k;0..q.length-1) horner=primitive(addOp,[scalar(inner,arena.real_(q[k])),primitive(mulOp,[x,horner])]);
				auto exponent=primitive(mulOp,[scalar(inner,arena.real_(rate)),x]);
				return primitive(mulOp,[horner,primitive(arena.call(Builtin.expR,[arena.real_(0)]),[exponent])]);
			}
			// The bound itself replaces the axis: no application is left behind.
			BoundTerm evaluate(BoundTerm expression,BoundTerm bound){
				BoundTerm[] values=[bound];
				foreach(i;0..depth(ctx)) values~=variable(ctx,i);
				return substitute(expression,ctx,values);
			}
			BoundTerm difference(IntervalTerm r,Rational[] p,Rational rate){
				p=polyProduct(p,outer); rate=rate+outerRate;
				foreach(c;p) if(c.words>128) return BoundTerm.init;
				if(rate.words>128) return BoundTerm.init;
				// Beyond a single bound every term must decay; its antiderivative
				// then vanishes at that end.
				if(d.half&&!decays(rate)) return BoundTerm.init;
				auto primitive_=antiderivative(p,rate); r.primitive=primitive_.id;
				auto result=d.below?evaluate(primitive_,upper):d.half?primitive(mulOp,[minusOne,evaluate(primitive_,lower)]):
					primitive(addOp,[evaluate(primitive_,upper),primitive(mulOp,[minusOne,evaluate(primitive_,lower)])]);
				if(r.scaled) result=primitive(mulOp,[exponentialScale(r.value),result]);
				d.terms~=r; return result;
			}
			// The same for a polynomial times the exponential of a polynomial,
			// both in Horner form below the axis binder.
			BoundTerm curveDifference(IntervalTerm r,Rational[] p,Rational[] exponent){
				Rational[] R,E; size_t order;
				if(!curve(p,exponent,R,E,r.rate,order)) return BoundTerm.init;
				r.order=cast(uint)order; r.curved=true;
				BoundTerm horner(Rational[] c){
					auto x=variable(inner,0),h=scalar(inner,arena.real_(c[$-1]));
					foreach_reverse(k;0..c.length-1) h=primitive(addOp,[scalar(inner,arena.real_(c[k])),primitive(mulOp,[x,h])]);
					return h;
				}
				auto primitive_=primitive(mulOp,[horner(R),primitive(arena.call(Builtin.expR,[arena.real_(0)]),[horner(E)])]); r.primitive=primitive_.id;
				auto result=d.below?evaluate(primitive_,upper):d.half?primitive(mulOp,[minusOne,evaluate(primitive_,lower)]):
					primitive(addOp,[evaluate(primitive_,upper),primitive(mulOp,[minusOne,evaluate(primitive_,lower)])]);
				if(r.scaled) result=primitive(mulOp,[tailScale(r.value,false,false,true),result]);
				d.terms~=r; return result;
			}
			// At the vertex: half the Gaussian integral under half the constant,
			// and the antiderivative there.
			BoundTerm vertexDifference(IntervalTerm r,Rational[] p,Rational[] exponent){
				if(!vertex(p,exponent,r)) return BoundTerm.init;
				auto half=scalar(ctx,arena.real_(r.half)),rest=scalar(ctx,arena.real_(r.rest)),peak=scalar(ctx,arena.real_(r.bell.vertex));
				auto width=scalar(ctx,arena.real_(r.bell.width)),circle=scalar(ctx,arena.call(Builtin.pi,[]));
				r.bell.factor=half.id; r.restLiteral=rest.id; r.bell.exponent=peak.id; r.bell.scale=width.id; r.bell.circle=circle.id;
				auto height=primitive(arena.call(Builtin.expR,[arena.real_(0)]),[peak]);
				auto result=primitive(addOp,[primitive(mulOp,[half,primitive(mulOp,[height,
					primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[primitive(mulOp,[circle,width])])])]),primitive(mulOp,[rest,height])]);
				if(r.scaled) result=primitive(mulOp,[tailScale(r.value,false,false,true),result]);
				d.terms~=r; return result;
			}
			// With the error function: the antiderivative of the rest, and the
			// constant times the error function of the root of the negated
			// curvature times the distance from the vertex.
			BoundTerm erfDifference(IntervalTerm r,Rational[] p,Rational[] exponent){
				if(!erf(p,exponent,r)) return BoundTerm.init;
				BoundTerm horner(Rational[] c){
					auto x=variable(inner,0),h=scalar(inner,arena.real_(c[$-1]));
					foreach_reverse(k;0..c.length-1) h=primitive(addOp,[scalar(inner,arena.real_(c[k])),primitive(mulOp,[x,h])]);
					return h;
				}
				BoundTerm apply1(Builtin f,BoundTerm x){ return primitive(arena.call(f,[arena.real_(0)]),[x]); }
				auto g=r.bell,x=variable(inner,0);
				auto rest=primitive(mulOp,[horner(g.primitive),apply1(Builtin.expR,horner([g.c0,g.c1,g.c2]))]); r.primitive=rest.id;
				auto half=scalar(inner,arena.real_(r.half)),peak=scalar(inner,arena.real_(g.vertex)),width=scalar(inner,arena.real_(g.width));
				auto circle=scalar(inner,arena.call(Builtin.pi,[])),sigma=scalar(inner,arena.real_(Rational(0)-g.c2));
				auto offset=scalar(inner,arena.real_(r.offset)),unit=scalar(inner,arena.real_(Rational(-1)));
				r.bell.factor=half.id; r.bell.exponent=peak.id; r.bell.scale=width.id; r.bell.circle=circle.id;
				r.sigma=sigma.id; r.offsetLiteral=offset.id; r.unit=unit.id;
				auto constant=primitive(mulOp,[half,primitive(mulOp,[apply1(Builtin.expR,peak),apply1(Builtin.sqrtR,primitive(mulOp,[circle,width]))])]);
				auto argument=d.below?primitive(addOp,[offset,primitive(mulOp,[unit,x])]):primitive(addOp,[x,offset]);
				auto tail=primitive(mulOp,[constant,apply1(d.half?Builtin.erfcR:Builtin.erfR,primitive(mulOp,[apply1(Builtin.sqrtR,sigma),argument]))]);
				if(d.half&&!d.below) tail=primitive(mulOp,[unit,tail]);
				auto primitive_=primitive(addOp,[rest,tail]);
				auto result=d.below?evaluate(primitive_,upper):d.half?primitive(mulOp,[minusOne,evaluate(primitive_,lower)]):
					primitive(addOp,[evaluate(primitive_,upper),primitive(mulOp,[minusOne,evaluate(primitive_,lower)])]);
				if(r.scaled) result=primitive(mulOp,[tailScale(r.value,false,false,true),result]);
				d.terms~=r; return result;
			}
			// With coefficients that are terms the constant in front has the
			// exponential of the value at the vertex, `c₀ + γ·c₁²`, and the
			// argument the linear coefficient times its factor. Everything but
			// the bound is outside the binder: the result is built at the bounds.
			BoundTerm symbolicErfDifference(IntervalTerm r,uint id){
				if(!symbolicErf(id,r)) return BoundTerm.init;
				BellParts built; bellParts(id,built,true);
				BoundTerm apply1(Builtin f,BoundTerm x){ return primitive(arena.call(f,[arena.real_(0)]),[x]); }
				auto linear=built.c[1].term; BoundTerm constant;
				if(built.c[0].present) constant=built.c[0].term;
				else{ constant=scalar(ctx,arena.real_(0)); r.bell.zero0=constant.id; }
				r.bell.curvature=built.c[2].term.id;
				auto half=scalar(ctx,arena.real_(r.half)),peak=scalar(ctx,arena.real_(r.bell.vertex)),width=scalar(ctx,arena.real_(r.bell.width));
				auto circle=scalar(ctx,arena.call(Builtin.pi,[])),sigma=scalar(ctx,arena.real_(Rational(0)-r.bell.c2));
				auto offset=scalar(ctx,arena.real_(r.offset)),unit=scalar(ctx,arena.real_(Rational(-1)));
				r.bell.factor=half.id; r.bell.exponent=peak.id; r.bell.scale=width.id; r.bell.circle=circle.id;
				r.sigma=sigma.id; r.offsetLiteral=offset.id; r.unit=unit.id;
				auto height=apply1(Builtin.expR,primitive(addOp,[constant,primitive(mulOp,[peak,primitive(mulOp,[linear,linear])])]));
				auto front=primitive(mulOp,[half,primitive(mulOp,[height,apply1(Builtin.sqrtR,primitive(mulOp,[circle,width]))])]);
				auto shift=primitive(mulOp,[offset,linear]),root=apply1(Builtin.sqrtR,sigma);
				BoundTerm at_(BoundTerm o){
					auto argument=d.below?primitive(addOp,[shift,primitive(mulOp,[unit,o])]):primitive(addOp,[o,shift]);
					auto tail=primitive(mulOp,[front,apply1(d.half?Builtin.erfcR:Builtin.erfR,primitive(mulOp,[root,argument]))]);
					return d.half&&!d.below?primitive(mulOp,[unit,tail]):tail;
				}
				BoundTerm result;
				if(!r.bell.rows.length) result=d.below?at_(upper):d.half?primitive(mulOp,[minusOne,at_(lower)]):primitive(addOp,[at_(upper),primitive(mulOp,[minusOne,at_(lower)])]);
				else{
					// Under a polynomial: the rest at the bounds, each time times
					// the exponential of the quadratic there, and the polynomial
					// of the constant at the linear coefficient times the
					// antiderivative of the exponential.
					auto curvature=built.c[2].term;
					BoundTerm balanced(BoundTerm[] xs){ return xs.length==1?xs[0]:primitive(addOp,[balanced(xs[0..$/2]),balanced(xs[$/2..$])]); }
					BoundTerm power(BoundTerm x,size_t i){ return i==1?x:primitive(arena.pow(arena.real_(0),cast(uint)i),[x]); }
					BoundTerm[] parts;
					foreach(i,c;r.bell.moments){
						if(i&&c.zero){ r.bell.literals~=uint.max; continue; }
						auto coefficient=scalar(ctx,arena.real_(c)); r.bell.literals~=coefficient.id;
						parts~=!i?coefficient:primitive(mulOp,[coefficient,power(linear,i)]);
					}
					auto kappa=balanced(parts);
					// A row is under its power of the linear coefficient. Its
					// constant always stands, a later monomial where its
					// coefficient is not zero and the bound not a closed zero.
					BoundTerm rest(size_t e,BoundTerm o){
						Rational point; Term closed; auto zero=closedRational(o,point,closed)&&point.zero;
						r.ends[e].zero=zero;
						BoundTerm[] terms;
						foreach(i,row;r.bell.rows){
							uint[] literals;
							if(row.length>1||!row[0].zero) foreach(j,c;row){
								if(j&&(c.zero||zero)){ literals~=uint.max; continue; }
								auto coefficient=scalar(ctx,arena.real_(c)); literals~=coefficient.id;
								auto monomial=!j?coefficient:primitive(mulOp,[coefficient,power(o,j)]);
								terms~=!i?monomial:primitive(mulOp,[power(linear,i),monomial]);
							}
							r.ends[e].rows~=literals;
						}
						auto quadratic=primitive(addOp,[constant,primitive(addOp,[primitive(mulOp,[linear,o]),primitive(mulOp,[curvature,primitive(mulOp,[o,o])])])]);
						return primitive(mulOp,[balanced(terms),apply1(Builtin.expR,quadratic)]);
					}
					BoundTerm tail(BoundTerm o){ return primitive(mulOp,[front,apply1(Builtin.erfcR,primitive(mulOp,[root,primitive(addOp,[o,shift])]))]); }
					if(d.below) result=primitive(addOp,[rest(0,upper),primitive(mulOp,[kappa,at_(upper)])]);
					else if(d.half) result=primitive(addOp,[primitive(mulOp,[unit,rest(1,lower)]),primitive(mulOp,[kappa,tail(lower)])]);
					else{
						auto above=rest(0,upper),below=rest(1,lower);
						result=primitive(addOp,[primitive(addOp,[above,primitive(mulOp,[minusOne,below])]),
							primitive(mulOp,[kappa,primitive(addOp,[at_(upper),primitive(mulOp,[minusOne,at_(lower)])])])]);
					}
				}
				if(built.scaled) result=primitive(mulOp,[built.scale,result]);
				d.terms~=r; return result;
			}
			// `[c₁≠0]·(k(b)·exp(c₀+c₁·b) - k(a)·exp(c₀+c₁·a)) +
			// [c₁=0]·(exp(c₀)·(p(b) - p(a)))` under the scale, where `k` is the
			// sum of the monomials of the rows at a bound, each under its power
			// of the inverse rate, and `p` that of the monomials of the
			// antiderivative of the polynomial. The first summand mentions the
			// inverse of the rate, and its mask hides it where the rate is zero.
			// Under a polynomial whose coefficients are terms the monomials of
			// each table and antiderivative also stand under their coefficient.
			BoundTerm rateBetweenDifference(IntervalTerm r,uint id){
				if(!symbolicRateBetween(id,r)) return BoundTerm.init;
				BellParts built; bellParts(id,built,true);
				auto linear=built.c[1].term; BoundTerm constant;
				if(built.c[0].present) constant=built.c[0].term;
				else{ constant=scalar(ctx,arena.real_(0)); r.bell.zero0=constant.id; }
				auto literal=arena.real_(0),truth=arena.boolean(true);
				BoundTerm apply1(Builtin f,BoundTerm x){ return primitive(arena.call(f,[literal]),[x]); }
				BoundTerm balanced(BoundTerm[] xs){ return xs.length==1?xs[0]:primitive(addOp,[balanced(xs[0..$/2]),balanced(xs[$/2..$])]); }
				BoundTerm power(BoundTerm x,size_t i){ return i==1?x:primitive(arena.pow(arena.real_(0),cast(uint)i),[x]); }
				auto inverse=primitive(arena.inv(arena.real_(1)),[linear]);
				BoundTerm[2] decaying,flat;
				foreach(e,o;[upper,lower]){
					Rational point; Term closed; auto zero=closedRational(o,point,closed)&&point.zero;
					r.ends[e].zero=zero;
					// The constant of a row always, a later monomial where its
					// coefficient is not zero and the bound is not a closed zero.
					BoundTerm[] monomials(Rational[] row,BoundTerm factor,ref uint[] literals){
						BoundTerm[] terms;
						foreach(i,c;row){
							if(i&&(c.zero||zero)){ literals~=uint.max; continue; }
							auto coefficient=scalar(ctx,arena.real_(c)); literals~=coefficient.id;
							auto monomial=!i?coefficient:primitive(mulOp,[coefficient,power(o,i)]);
							terms~=factor==BoundTerm.init?monomial:primitive(mulOp,[factor,monomial]);
						}
						return terms;
					}
					BoundTerm[] terms,antiderivatives;
					if(!r.bell.tables.length) foreach(l,row;r.bell.rows){
						uint[] literals;
						if(l) terms~=monomials(row,power(inverse,l),literals);
						r.ends[e].rows~=literals;
					}else foreach(j,rows;r.bell.tables){
						uint[][] table;
						foreach(l,row;rows){
							uint[] literals;
							if(l&&built.poly[j].present) terms~=monomials(row,primitive(mulOp,[built.poly[j].term,power(inverse,l)]),literals);
							table~=literals;
						}
						r.ends[e].tables~=table;
					}
					decaying[e]=primitive(mulOp,[balanced(terms),apply1(Builtin.expR,primitive(addOp,[constant,primitive(mulOp,[linear,o])]))]);
					if(!r.bell.tables.length) antiderivatives=monomials(r.bell.primitive,BoundTerm.init,r.ends[e].primitive);
					else foreach(j,row;r.primitives){
						uint[] literals;
						if(built.poly[j].present) antiderivatives~=monomials(row,built.poly[j].term,literals);
						r.ends[e].primitives~=literals;
					}
					flat[e]=balanced(antiderivatives);
				}
				BoundTerm between(BoundTerm[2] ends){ return primitive(addOp,[ends[0],primitive(mulOp,[minusOne,ends[1]])]); }
				auto test=primitive(arena.nonzero(arena.real_(1)),[linear]),mask=arena.mask(truth,arena.real_(1));
				auto result=primitive(addOp,[primitive(mask,[test,between(decaying)]),
					primitive(mask,[primitive(arena.not_(truth),[test]),primitive(mulOp,[apply1(Builtin.expR,constant),between(flat)])])]);
				if(built.scaled) result=primitive(mulOp,[built.scale,result]);
				d.terms~=r; return result;
			}
			BoundTerm build(uint id,uint depth){
				IntervalTerm r; Rational[] p,exponent; Rational rate; r.value=id;
				if(scaledExponential(id,p,rate,r.scaled)) return difference(r,p,rate);
				if(tailExponential(id,false,p,exponent,r.scaled,false,0,true)){
					auto curved=curveDifference(r,p,exponent);
					if(curved==BoundTerm.init) curved=vertexDifference(r,p,exponent);
					return curved!=BoundTerm.init?curved:erfDifference(r,p,exponent);
				}
				auto symbolic=symbolicErfDifference(r,id);
				if(symbolic==BoundTerm.init) symbolic=rateBetweenDifference(r,id);
				if(symbolic!=BoundTerm.init) return symbolic;
				// A sum is integrated term by term only without further weights.
				auto q=nodes[id];
				if(depth>16||d.terms.length>16||solution.from.length!=1||!isOp(q,Op.add)) return BoundTerm.init;
				auto a=build(q.a,depth+1); if(a==BoundTerm.init) return a;
				auto b=build(q.b,depth+1); if(b==BoundTerm.init) return b;
				return primitive(addOp,[a,b]);
			}
			// `guard(c₁<0, k·exp(c₀+c₁·a))` above a bound and
			// `guard(0<c₁, k·exp(c₀+c₁·b))` below one, under the scale, where `k`
			// is the sum of the monomials of the rows at the bound, each under
			// its power of the inverse rate: the constant of a row always, a
			// later monomial where its coefficient is not zero and the bound is
			// not a closed zero. A scale that may vanish leaves the zero
			// function where it does: the guard then also holds there, around
			// the mask of the scale and after everything the integrand is
			// strict in.
			BoundTerm rateDifference(IntervalTerm r,uint id){
				BellParts built; bellParts(id,built,true);
				auto linear=built.c[1].term,bound=d.below?upper:lower; BoundTerm constant;
				if(built.c[0].present) constant=built.c[0].term;
				else{ constant=scalar(ctx,arena.real_(0)); r.bell.zero0=constant.id; }
				auto zero=scalar(ctx,arena.real_(0)),literal=arena.real_(0),truth=arena.boolean(true);
				r.rateZero=zero.id; r.value=id;
				auto inverse=primitive(arena.inv(arena.real_(1)),[linear]);
				Rational point; Term closed; r.boundZero=closedRational(bound,point,closed)&&point.zero;
				BoundTerm[] terms;
				foreach(l,row;r.bell.rows){
					uint[] literals;
					if(l){
						auto power=l==1?inverse:primitive(arena.pow(arena.real_(0),cast(uint)l),[inverse]);
						foreach(i,c;row){
							if(i&&(c.zero||r.boundZero)){ literals~=uint.max; continue; }
							auto coefficient=scalar(ctx,arena.real_(c)); literals~=coefficient.id;
							auto monomial=!i?coefficient:primitive(mulOp,[coefficient,i==1?bound:primitive(arena.pow(arena.real_(0),cast(uint)i),[bound])]);
							terms~=primitive(mulOp,[power,monomial]);
						}
					}
					r.bell.rowLiterals~=literals;
				}
				BoundTerm balanced(BoundTerm[] xs){ return xs.length==1?xs[0]:primitive(addOp,[balanced(xs[0..$/2]),balanced(xs[$/2..$])]); }
				auto value=primitive(mulOp,[balanced(terms),
					primitive(arena.call(Builtin.expR,[literal]),[primitive(addOp,[constant,primitive(mulOp,[linear,bound])])])]);
				auto sign=primitive(arena.lt(literal,literal),d.below?[zero,linear]:[linear,zero]);
				r.bell.maskScale=built.scaled&&!nonvanishing(built.scale.id);
				BoundTerm result;
				if(!r.bell.maskScale){
					if(built.scaled){ r.bell.nonzero=built.scale.id; value=primitive(mulOp,[built.scale,value]); }
					result=guard(sign,value);
				}else{
					auto test=primitive(arena.nonzero(arena.real_(1)),[built.scale]);
					auto condition=primitive(arena.or_(truth,truth),[primitive(arena.not_(truth),[test]),sign]);
					result=guard(condition,primitive(arena.mask(truth,arena.real_(1)),[test,primitive(mulOp,[built.scale,value])]));
					foreach_reverse(x;[built.scale,bound,constant,linear]) result=sequence(x,result);
				}
				d.terms~=r; return result;
			}
			// `K·erfc(√(-c₂)·(a + c₁/(2·c₂)))` above a bound and
			// `K·erfc(√(-c₂)·(-c₁/(2·c₂) - b))` below one, where `K` is half the
			// constant times `exp(c₀-c₁²/(4·c₂))·√(-π/c₂)`, under the scale. A
			// scale that may vanish has the result under its mask, after
			// everything the integrand is strict in.
			BoundTerm curvatureDifference(IntervalTerm r,uint id){
				BellParts built; bellParts(id,built,true);
				auto curvature=built.c[2].term,bound=d.below?upper:lower;
				if(!nonvanishing(curvature.id)) return BoundTerm.init;
				BoundTerm coefficient(size_t i,ref uint zero){
					if(built.c[i].present) return built.c[i].term;
					auto filled=scalar(ctx,arena.real_(0)); zero=filled.id; return filled;
				}
				auto constant=coefficient(0,r.bell.zero0),linear=coefficient(1,r.bell.zero1),literal=arena.real_(0),truth=arena.boolean(true);
				BoundTerm apply1(Builtin f,BoundTerm x){ return primitive(arena.call(f,[literal]),[x]); }
				auto half=scalar(ctx,arena.real_(r.half)),quarter=scalar(ctx,arena.real_(Rational(-1)/Rational(4))),minus=scalar(ctx,arena.real_(Rational(-1)));
				auto circle=scalar(ctx,arena.call(Builtin.pi,[])),side=scalar(ctx,arena.real_(Rational(d.below?-1:1)/Rational(2)));
				r.bell.factor=half.id; r.bell.exponent=quarter.id; r.bell.scale=minus.id; r.bell.circle=circle.id; r.bell.curvature=curvature.id; r.side=side.id; r.value=id;
				auto inverse=primitive(arena.inv(arena.real_(1)),[curvature]);
				auto front=primitive(mulOp,[half,primitive(mulOp,[apply1(Builtin.expR,primitive(addOp,[constant,primitive(mulOp,[primitive(mulOp,[quarter,inverse]),primitive(mulOp,[linear,linear])])])),
					apply1(Builtin.sqrtR,primitive(mulOp,[circle,primitive(mulOp,[minus,inverse])]))])]);
				auto shift=primitive(mulOp,[primitive(mulOp,[side,inverse]),linear]);
				auto argument=d.below?primitive(addOp,[shift,primitive(mulOp,[minus,bound])]):primitive(addOp,[bound,shift]);
				auto value=primitive(mulOp,[front,apply1(Builtin.erfcR,primitive(mulOp,[apply1(Builtin.sqrtR,primitive(mulOp,[minus,curvature])),argument]))]);
				r.bell.maskScale=built.scaled&&!nonvanishing(built.scale.id);
				if(built.scaled){ if(!r.bell.maskScale) r.bell.nonzero=built.scale.id; value=primitive(mulOp,[built.scale,value]); }
				if(r.bell.maskScale){
					value=primitive(arena.mask(truth,arena.real_(1)),[primitive(arena.nonzero(arena.real_(1)),[built.scale]),value]);
					foreach_reverse(x;[built.scale,bound,constant,linear,curvature]) value=sequence(x,value);
				}
				d.terms~=r; return value;
			}
			// `guard(0<a ∨ b<0, F(b) - F(a))` with that antiderivative `F`: its
			// polynomials as the sums of their monomials at the bound, the
			// constant always and a later one where its coefficient is not zero.
			// Above one bound it is `guard(0<a, -C(a)/a^M)`, and below one
			// `guard(b<0, C(b)/b^M)`. A factor `c` that does not mention the
			// axis does not simply come out: where it is zero the product is
			// zero wherever the quotient is defined, also next to zero. So
			// the value is `[c≠0]·(c·V)` under the guard that holds also where
			// `c` is zero and zero is not in the guard of the bounds. Where
			// no bound is strict, or the bounds are closed on one side of
			// zero, that is the same as `c·V` under the guard without `c`.
			BoundTerm quotientDifference(IntervalTerm r,uint id){
				auto zero=scalar(ctx,arena.real_(0)),k=scalar(ctx,arena.real_(r.bell.constant)),literal=arena.real_(0),truth=arena.boolean(true);
				r.rateZero=zero.id; r.bell.factor=k.id; r.value=id;
				BoundTerm balanced(BoundTerm[] xs){ return xs.length==1?xs[0]:primitive(addOp,[balanced(xs[0..$/2]),balanced(xs[$/2..$])]); }
				BoundTerm power(BoundTerm x,size_t i){ return i==1?x:primitive(arena.pow(arena.real_(0),cast(uint)i),[x]); }
				BoundTerm row(Rational[] coefficients,BoundTerm o,ref uint[] literals){
					BoundTerm[] terms;
					foreach(i,c;coefficients){
						if(i&&c.zero){ literals~=uint.max; continue; }
						auto coefficient=scalar(ctx,arena.real_(c)); literals~=coefficient.id;
						terms~=!i?coefficient:primitive(mulOp,[coefficient,power(o,i)]);
					}
					return balanced(terms);
				}
				BoundTerm at_(size_t e,BoundTerm o){
					auto polynomial=row(r.bell.primitive,o,r.ends[e].primitive);
					uint[] literals; auto over=row(r.bell.moments,o,literals); r.ends[e].rows=[literals];
					auto quotient=primitive(mulOp,[over,primitive(arena.inv(arena.real_(1)),[power(o,r.ratioShift)])]);
					auto logarithm=primitive(arena.call(Builtin.logR,[literal]),[primitive(arena.abs(literal),[o])]);
					return primitive(addOp,[primitive(addOp,[polynomial,quotient]),primitive(mulOp,[k,logarithm])]);
				}
				BoundTerm compare(bool strict,BoundTerm x,BoundTerm y){ return primitive(strict?arena.lt(literal,literal):arena.le(literal,literal),[x,y]); }
				Rational point; Term closed;
				bool positive(BoundTerm x){ return closedRational(x,point,closed)&&Rational(0)<point; }
				bool negative(BoundTerm x){ return closedRational(x,point,closed)&&point<Rational(0); }
				// `side` is the guard without the factor, `outside` that zero
				// is not in the guard of the bounds.
				BoundTerm finish(BoundTerm side,lazy BoundTerm outside,BoundTerm value,bool strict,lazy bool closedSide){
					if(!r.ratioScale.length){ d.terms~=r; return guard(side,value); }
					BoundTerm[] stack;
					foreach(x;r.ratioScale){
						if(x==uint.max){ auto product=primitive(mulOp,[stack[$-2],stack[$-1]]); stack=stack[0..$-2]~product; }
						else stack~=dropIndex(at(x));
					}
					auto c=stack[0],scaled=primitive(mulOp,[c,value]);
					r.ratioClosed=strict&&closedSide; r.ratioPlain=!strict||r.ratioClosed;
					d.terms~=r;
					if(r.ratioPlain) return guard(side,scaled);
					auto test=primitive(arena.nonzero(arena.real_(1)),[c]);
					auto condition=primitive(arena.or_(truth,truth),[side,primitive(arena.and_(truth,truth),[primitive(arena.not_(truth),[test]),outside])]);
					return guard(condition,primitive(arena.mask(truth,arena.real_(1)),[test,scaled]));
				}
				// Around a pole that is not zero the bounds are moved by it.
				BoundTerm moved(BoundTerm x){
					if(r.ratioPole.zero) return x;
					auto move=scalar(ctx,arena.real_(Rational(0)-r.ratioPole)); r.ratioMove=move.id;
					return primitive(addOp,[x,move]);
				}
				if(d.half){
					auto bound=moved(d.below?upper:lower),strict=d.below?d.strictUpper:d.strictLower; uint[] literals;
					if(d.below) r.ratioUpper=bound.id; else r.ratioLower=bound.id;
					auto over=row(r.bell.moments,bound,literals); r.ends[0].rows=[literals];
					auto value=primitive(mulOp,[over,primitive(arena.inv(arena.real_(1)),[power(bound,r.ratioShift)])]);
					if(!d.below) value=primitive(mulOp,[minusOne,value]);
					return finish(compare(true,d.below?bound:zero,d.below?zero:bound),compare(!strict,d.below?bound:zero,d.below?zero:bound),
						value,strict,d.below?negative(bound):positive(bound));
				}
				auto low=moved(lower),high=moved(upper); r.ratioLower=low.id; r.ratioUpper=high.id;
				auto above=at_(0,high),below=at_(1,low);
				auto side=primitive(arena.or_(truth,truth),[compare(true,zero,low),compare(true,high,zero)]);
				return finish(side,primitive(arena.or_(truth,truth),[compare(!d.strictLower,zero,low),compare(!d.strictUpper,high,zero)]),
					primitive(addOp,[above,primitive(mulOp,[minusOne,below])]),d.strictLower||d.strictUpper,positive(low)||negative(high));
			}
			// `guard(0<a, F(b) - F(a))` with that antiderivative `F`, the
			// bounds moved by the pole. Where the lower bound is strict the
			// guard is `0≤a`, and the part of `F(a)` with the logarithm is
			// under the mask `[a≠0]`: there the antiderivative continues
			// with zero.
			BoundTerm logDifference(IntervalTerm r,uint id){
				auto zero=scalar(ctx,arena.real_(0)),literal=arena.real_(0),truth=arena.boolean(true);
				r.rateZero=zero.id; r.value=id;
				BoundTerm balanced(BoundTerm[] xs){ return xs.length==1?xs[0]:primitive(addOp,[balanced(xs[0..$/2]),balanced(xs[$/2..$])]); }
				BoundTerm row(Rational[] coefficients,BoundTerm o,ref uint[] literals){
					BoundTerm[] terms;
					foreach(i,c;coefficients){
						if(i&&c.zero){ literals~=uint.max; continue; }
						auto coefficient=scalar(ctx,arena.real_(c)); literals~=coefficient.id;
						terms~=!i?coefficient:primitive(mulOp,[coefficient,i==1?o:primitive(arena.pow(arena.real_(0),cast(uint)i),[o])]);
					}
					return balanced(terms);
				}
				BoundTerm moved(BoundTerm x){
					if(r.ratioPole.zero) return x;
					auto move=scalar(ctx,arena.real_(Rational(0)-r.ratioPole)); r.ratioMove=move.id;
					return primitive(addOp,[x,move]);
				}
				BoundTerm at_(size_t e,BoundTerm o,bool masked){
					auto first=row(r.bell.primitive,o,r.ends[e].primitive);
					uint[] literals; auto second=row(r.bell.moments,o,literals); r.ends[e].rows=[literals];
					auto logarithm=primitive(mulOp,[primitive(mulOp,[o,first]),primitive(arena.call(Builtin.logR,[literal]),[o])]);
					if(masked) logarithm=primitive(arena.mask(truth,arena.real_(1)),[primitive(arena.nonzero(arena.real_(1)),[o]),logarithm]);
					return primitive(addOp,[logarithm,primitive(mulOp,[o,second])]);
				}
				auto low=moved(lower),high=moved(upper); r.ratioLower=low.id; r.ratioUpper=high.id;
				auto above=at_(0,high,false),below=at_(1,low,d.strictLower);
				auto side=primitive(d.strictLower?arena.le(literal,literal):arena.lt(literal,literal),[zero,low]);
				auto value=primitive(addOp,[above,primitive(mulOp,[minusOne,below])]);
				if(r.ratioScale.length){
					BoundTerm[] stack;
					foreach(x;r.ratioScale){
						if(x==uint.max){ auto product=primitive(mulOp,[stack[$-2],stack[$-1]]); stack=stack[0..$-2]~product; }
						else stack~=dropIndex(at(x));
					}
					value=primitive(mulOp,[stack[0],value]);
				}
				d.terms~=r; return guard(side,value);
			}
			auto subject=d.inner!=uint.max?d.inner:d.value;
			auto total=d.direct?(whole.logTerm?logDifference(whole,subject):whole.ratioTerm?quotientDifference(whole,subject):whole.rateTerm?rateDifference(whole,d.value):curvatureDifference(whole,d.value)):
				d.unit!=uint.max?difference(IntervalTerm(uint.max),[Rational(1)],Rational(0)):build(d.value,0);
			if(total==BoundTerm.init) return BoundTerm.init;
			if(d.constant!=uint.max) total=primitive(addOp,[total,primitive(mulOp,[dropIndex(at(d.constant)),primitive(addOp,[upper,primitive(mulOp,[minusOne,lower])])])]);
			if(d.domain!=uint.max) total=guard(dropIndex(at(d.domain)),total);
			auto zero=arena.real_(0),strict=d.strictLower||d.strictUpper;
			auto test=primitive(strict?arena.lt(zero,zero):arena.le(zero,zero),[lower,upper]);
			auto result=d.half?total:primitive(arena.mask(arena.boolean(true),arena.real_(1)),[test,total]);
			d.lower=lower.id; d.upper=upper.id; d.minusOne=minusOne.id;
			solution.bounds=d; solution.interval=true; solution.piecewise=true; solution.output=result.id;
			return result;
		}
		// A rational polynomial times the exponential of a quadratic whose
		// curvature is a term that does not mention the axis either. The
		// moments of the polynomial relative to the Gaussian integral are a
		// polynomial in the linear coefficient `c₁` and in `h = -1/(2·c₂)`, a
		// row for each power of `h`: the moment of degree j+1 is
		// h·(c₁·μⱼ + j·μⱼ₋₁). The result is that polynomial times
		// `exp(c₀-c₁²/(4·c₂))·√(-π/c₂)`, which is missing where the curvature is
		// not negative, the inverse at zero and the root above it, as the
		// observation is: the integrand is defined there and not integrable.
		// The coefficients of a polynomial may be terms that do not mention the
		// axis: the integral is linear in them, and each meets the moments of
		// its power. A factor of zero leaves the zero function, which has an
		// integral whatever the curvature is: a scale that may vanish, and a
		// polynomial whose coefficients may all vanish, by their form, have the
		// closed form under their mask.
		BoundTerm integrateCurvature(BoundTerm t,ref IntegralSolution solution,BellParts found){
			auto p=found.p; while(p.length&&p[$-1].zero) p.length=p.length-1;
			auto count=found.symbolic?found.poly.length:1;
			if(!p.length||count+p.length>18) return BoundTerm.init;
			// Polynomials in `h` whose coefficients are polynomials in `c₁`.
			alias Rows=Rational[][];
			Rows add(Rows a,Rows b){ Rows r; foreach(i;0..a.length>b.length?a.length:b.length) r~=polySum(i<a.length?a[i]:null,i<b.length?b[i]:null); return r; }
			Rows scale(Rational c,Rows a){ Rows r; foreach(row;a) r~=polyProduct([c],row); return r; }
			Rows shift(Rows a){ Rows r; foreach(row;a) r~=Rational(0)~row; return r; }
			Rows next(size_t j,Rows mu,Rows before){ Rational[] none; return none~add(shift(mu),scale(Rational(cast(long)j),before)); }
			Rows moments(Rational[] q,size_t j,Rows mu,Rows before){
				if(!q.length) return null;
				return add(scale(q[0],mu),moments(q[1..$],j+1,next(j,mu,before),mu));
			}
			// The moments of xʲ times the rational polynomial, a table of rows
			// for each coefficient that is a term; without them the one of the
			// polynomial itself.
			Rows[] tables; Rows mu=[[Rational(1)]],before;
			foreach(j;0..count){
				auto rows=moments(p,j,mu,before);
				foreach(ref row;rows){
					while(row.length>1&&row[$-1].zero) row.length=row.length-1;
					if(!row.length) row=[Rational(0)];
					foreach(c;row) if(c.words>128) return BoundTerm.init;
				}
				while(rows.length>1&&rows[$-1].length==1&&rows[$-1][0].zero) rows.length=rows.length-1;
				tables~=rows;
				auto after=next(j,mu,before); before=mu; mu=after;
			}
			BellParts built; gaussianParts(solution.from,built,true);
			GaussianData d; d.symbolic=true; d.curved=true;
			d.maskScale=built.scaled&&!nonvanishing(built.scale.id);
			if(found.symbolic){
				foreach(j,c;built.poly) if(c.present&&nonvanishingCoefficient(c.term)){ d.witness=cast(uint)j; break; }
				d.maskPolynomial=d.witness==uint.max;
				d.tables=tables;
			}else d.rows=tables[0];
			auto ctx=context(t),product=arena.mul(arena.real_(1),arena.real_(1),true),sum=arena.add(arena.real_(0),arena.real_(0),true);
			BoundTerm coefficient(size_t i,ref uint zero){
				if(built.c[i].present) return built.c[i].term;
				auto filled=scalar(ctx,arena.real_(0)); zero=filled.id; return filled;
			}
			auto constant=coefficient(0,d.zero0),linear=coefficient(1,d.zero1),curvature=built.c[2].term;
			d.curvature=curvature.id;
			auto half=scalar(ctx,arena.real_(Rational(-1)/Rational(2))),quarter=scalar(ctx,arena.real_(Rational(-1)/Rational(4)));
			auto minus=scalar(ctx,arena.real_(Rational(-1))),circle=scalar(ctx,arena.call(Builtin.pi,[]));
			d.factor=half.id; d.exponent=quarter.id; d.scale=minus.id; d.circle=circle.id;
			auto inverse=primitive(arena.inv(arena.real_(1)),[curvature]),width=primitive(product,[half,inverse]);
			// The monomials of a row that is not zero, under its power of `h`
			// and under its coefficient where that is a term: the constant term
			// always, a later one where its coefficient is not zero and there
			// is a linear coefficient.
			BoundTerm[] terms;
			uint[] monomials(BoundTerm coefficient_,size_t l,Rational[] row){
				uint[] literals;
				if(row.length==1&&row[0].zero) return literals;
				auto power=l==0?BoundTerm.init:l==1?width:primitive(arena.pow(arena.real_(0),cast(uint)l),[width]);
				auto factor=coefficient_==BoundTerm.init?power:power==BoundTerm.init?coefficient_:primitive(product,[coefficient_,power]);
				foreach(i,c;row){
					if(i&&(c.zero||!built.c[1].present)){ literals~=uint.max; continue; }
					auto literal=scalar(ctx,arena.real_(c)); literals~=literal.id;
					auto monomial=!i?literal:primitive(product,[literal,i==1?linear:primitive(arena.pow(arena.real_(0),cast(uint)i),[linear])]);
					terms~=factor==BoundTerm.init?monomial:primitive(product,[factor,monomial]);
				}
				return literals;
			}
			if(!found.symbolic) foreach(l,row;d.rows) d.rowLiterals~=monomials(BoundTerm.init,l,row);
			else foreach(j,rows;d.tables){
				uint[][] table;
				foreach(l,row;rows) table~=built.poly[j].present?monomials(built.poly[j].term,l,row):null;
				d.tableLiterals~=table;
			}
			// The row of the highest power is not zero.
			assert(terms.length,"moments of a polynomial that is not zero");
			BoundTerm balanced(BoundTerm[] xs){ return xs.length==1?xs[0]:primitive(sum,[balanced(xs[0..$/2]),balanced(xs[$/2..$])]); }
			auto exponent=primitive(sum,[constant,primitive(product,[primitive(product,[quarter,inverse]),primitive(product,[linear,linear])])]);
			auto bell=primitive(product,[primitive(arena.call(Builtin.expR,[arena.real_(0)]),[exponent]),
				primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[primitive(product,[circle,primitive(product,[minus,inverse])])])]);
			auto result=primitive(product,[balanced(terms),bell]);
			if(built.scaled){ if(!d.maskScale) d.nonzero=built.scale.id; result=primitive(product,[built.scale,result]); }
			if(d.maskScale||d.maskPolynomial){
				// Under the mask of the factors that may vanish: a scale, the
				// coefficients of a polynomial one after the other, or both. A
				// mask that fails hides what is under it, so the result comes
				// after everything the integrand is strict in.
				BoundTerm nonzero(BoundTerm x){ return primitive(arena.nonzero(arena.real_(1)),[x]); }
				auto truth=arena.boolean(true); BoundTerm condition;
				if(d.maskPolynomial) foreach_reverse(c;built.poly) if(c.present)
					condition=condition==BoundTerm.init?nonzero(c.term):primitive(arena.or_(truth,truth),[nonzero(c.term),condition]);
				if(d.maskScale) condition=condition==BoundTerm.init?nonzero(built.scale):primitive(arena.and_(truth,truth),[nonzero(built.scale),condition]);
				result=primitive(arena.mask(truth,arena.real_(1)),[condition,result]);
				foreach_reverse(x;[constant,linear,curvature]) result=sequence(x,result);
				if(found.symbolic) foreach_reverse(c;built.poly) if(c.present) result=sequence(c.term,result);
				if(built.scaled) result=sequence(built.scale,result);
			}
			solution.bell=d; solution.gaussian=true; solution.piecewise=true; solution.output=result.id; return result;
		}
		// The whole line under a polynomial times the exponential of a quadratic
		// whose constant and linear coefficients do not mention the axis and
		// need not be numbers; its curvature is a negative rational. The
		// moments of the polynomial relative to the Gaussian integral are a
		// polynomial `κ` in the linear coefficient `c₁`: the result is
		// `κ(c₁)·exp(c₀ - c₁²/(4·c₂))·sqrt(π·(-1/c₂))`, times the factors that
		// do not mention the axis. An absent coefficient is a zero. Every
		// coefficient is strict in the exponent and in the result.
		BoundTerm integrateSymbolicGaussian(BoundTerm t,ref IntegralSolution solution){
			BellParts found;
			if(!gaussianParts(solution.from,found,false)||!found.exponent||!found.c[2].present) return BoundTerm.init;
			if(!found.c[2].closed) return integrateCurvature(t,solution,found);
			if(!(found.c[2].value<Rational(0))) return BoundTerm.init;
			GaussianData d; d.symbolic=true; d.c2=found.c[2].value;
			// The moment of degree j+1 is h·(c₁·μⱼ + j·μⱼ₋₁) for h = -1/(2·c₂).
			// The polynomial of xʲ times the rational polynomial sums them
			// from degree j on, one row for each coefficient that is a term.
			auto half=Rational(-1)/(Rational(2)*d.c2); Rational[][] moment=[[Rational(1)]];
			auto count=found.symbolic?found.poly.length:1;
			foreach(j;0..count+found.p.length){
				moment~=polyProduct([half],polySum([Rational(0)]~moment[j],polyProduct([Rational(cast(long)j)],j?moment[j-1]:null)));
				foreach(c;moment[$-1]) if(c.words>128) return BoundTerm.init;
			}
			Rational[][] rows;
			foreach(j;0..count){
				Rational[] row; foreach(i,a;found.p) row=polySum(row,polyProduct([a],moment[j+i]));
				while(row.length>1&&row[$-1].zero) row.length=row.length-1;
				if(!row.length) row=[Rational(0)];
				foreach(c;row) if(c.words>128) return BoundTerm.init;
				rows~=row;
			}
			if(found.symbolic) d.rows=rows; else d.moments=rows[0];
			d.vertex=Rational(-1)/(Rational(4)*d.c2); d.width=Rational(-1)/d.c2;
			foreach(c;[d.vertex,d.width]) if(c.words>128) return BoundTerm.init;
			BellParts built; gaussianParts(solution.from,built,true);
			auto ctx=context(t),product=arena.mul(arena.real_(1),arena.real_(1),true),sum=arena.add(arena.real_(0),arena.real_(0),true);
			BoundTerm coefficient(size_t i,ref uint zero){
				if(built.c[i].present) return built.c[i].term;
				auto filled=scalar(ctx,arena.real_(0)); zero=filled.id; return filled;
			}
			auto constant=coefficient(0,d.zero0),linear=coefficient(1,d.zero1);
			d.curvature=built.c[2].term.id;
			// κ(c₁) as the sum of its monomials: the constant term always, a
			// later one where its coefficient is not zero and there is a linear
			// coefficient. Under coefficients that are terms each that is
			// present multiplies the monomials of its row, so the sum is one of
			// products. The sum is a balanced tree: it stays shallow.
			BoundTerm[] terms;
			void monomials(BoundTerm coefficient_,Rational[] row,ref uint[] literals){
				foreach(i,c;row){
					if(i&&(c.zero||!built.c[1].present)){ literals~=uint.max; continue; }
					auto literal=scalar(ctx,arena.real_(c)); literals~=literal.id;
					auto power=!i?literal:primitive(product,[literal,i==1?linear:primitive(arena.pow(arena.real_(0),cast(uint)i),[linear])]);
					terms~=coefficient_==BoundTerm.init?power:primitive(product,[coefficient_,power]);
				}
			}
			if(!found.symbolic) monomials(BoundTerm.init,d.moments,d.literals);
			else foreach(j,row;d.rows){
				uint[] literals;
				if(built.poly[j].present) monomials(built.poly[j].term,row,literals);
				d.rowLiterals~=literals;
			}
			BoundTerm balanced(BoundTerm[] xs){ return xs.length==1?xs[0]:primitive(sum,[balanced(xs[0..$/2]),balanced(xs[$/2..$])]); }
			auto factor=balanced(terms);
			auto vertex=scalar(ctx,arena.real_(d.vertex)),scale=scalar(ctx,arena.real_(d.width)),circle=scalar(ctx,arena.call(Builtin.pi,[]));
			d.exponent=vertex.id; d.scale=scale.id; d.circle=circle.id;
			auto exponent=primitive(sum,[constant,primitive(product,[vertex,primitive(product,[linear,linear])])]);
			auto bell=primitive(product,[primitive(arena.call(Builtin.expR,[arena.real_(0)]),[exponent]),
				primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[primitive(product,[circle,scale])])]);
			auto result=primitive(product,[factor,bell]);
			if(built.scaled) result=primitive(product,[built.scale,result]);
			solution.bell=d; solution.gaussian=true; solution.piecewise=true; solution.output=result.id; return result;
		}
		// The whole line under a polynomial times the exponential of a
		// quadratic with rational coefficients and negative curvature, with
		// optional factors that do not mention the axis. The polynomial is a
		// constant up to the derivative of a polynomial times that exponential,
		// which vanishes at both ends; the constant multiplies the Gaussian
		// integral. A missing factor is missing in the result: the theorem is
		// an equation of partial values.
		BoundTerm integrateGaussian(BoundTerm t,out IntegralSolution solution){
			auto n=node(t); if(n.op!=BoundOp.distributionMass||!densityBodies(n.a,solution.from)||!solution.from.length) return BoundTerm.init;
			Rational[] p=[Rational(1)],q; bool scaled,closed=true;
			foreach(id;solution.from){
				Rational[] a,r; bool part;
				if(!tailExponential(id,false,a,r,part,false)){ closed=false; break; }
				p=polyProduct(p,a); q=polySum(q,r); scaled=scaled||part;
				if(p.length>64) return BoundTerm.init;
			}
			while(q.length&&q[$-1].zero) q.length=q.length-1;
			if(!closed||q.length!=3) return integrateSymbolicGaussian(t,solution);
			if(!(q[2]<Rational(0))) return BoundTerm.init;
			GaussianData d; d.c0=q[0]; d.c1=q[1]; d.c2=q[2];
			// R' + Q'·R + κ = P, from the highest coefficient down.
			auto m=p.length; auto primitive_=new Rational[](m?m-1:0);
			Rational at_(size_t i){ return i<primitive_.length?primitive_[i]:Rational(0); }
			foreach_reverse(j;1..m) primitive_[j-1]=(p[j]-Rational(cast(long)j+1)*at_(j+1)-d.c1*at_(j))/(Rational(2)*d.c2);
			d.constant=(m?p[0]:Rational(0))-at_(1)-d.c1*at_(0); d.primitive=primitive_;
			d.vertex=d.c0-d.c1*d.c1/(Rational(4)*d.c2); d.width=Rational(-1)/d.c2;
			foreach(c;primitive_~[d.constant,d.vertex,d.width]) if(c.words>128) return BoundTerm.init;
			auto ctx=context(t),product=arena.mul(arena.real_(1),arena.real_(1),true);
			auto factor=scalar(ctx,arena.real_(d.constant)),exponent=scalar(ctx,arena.real_(d.vertex));
			auto scale=scalar(ctx,arena.real_(d.width)),circle=scalar(ctx,arena.call(Builtin.pi,[]));
			d.factor=factor.id; d.exponent=exponent.id; d.scale=scale.id; d.circle=circle.id;
			auto bell=primitive(product,[primitive(arena.call(Builtin.expR,[arena.real_(0)]),[exponent]),
				primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[primitive(product,[circle,scale])])]);
			auto result=primitive(product,[factor,bell]);
			if(scaled){
				BoundTerm outside;
				foreach(id;solution.from){
					Rational[] a,r; bool part; tailExponential(id,false,a,r,part,false);
					if(!part) continue;
					auto here=tailScale(id,false,false); outside=outside==BoundTerm.init?here:primitive(product,[outside,here]);
				}
				result=primitive(product,[outside,result]);
			}
			solution.bell=d; solution.gaussian=true; solution.piecewise=true; solution.output=result.id; return result;
		}
		// A sum of observations between bounds, each with bounds of its own:
		// every summand is observed by itself, and the results add. An integral
		// is additive only where both parts exist; such an observation is
		// integrable or undefined somewhere, so their sum is an equation of
		// partial values. All summands are decided before any is built.
		BoundTerm integratePieces(BoundTerm t,out IntegralSolution solution){
			auto n=node(t); if(n.op!=BoundOp.distributionMass||!densityBodies(n.a,solution.from)||solution.from.length!=1) return BoundTerm.init;
			bool sum(uint id){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.add; }
			bool observed(uint id){ IntegralSolution trial; return integrateInterval(t,trial,id,false)!=BoundTerm.init; }
			size_t count;
			bool admissible(uint id,uint depth){
				if(observed(id)){ ++count; return count<=16; }
				return depth<16&&sum(id)&&admissible(nodes[id].a,depth+1)&&admissible(nodes[id].b,depth+1);
			}
			if(!sum(solution.from[0])||!admissible(solution.from[0],0)||count<2) return BoundTerm.init;
			IntegralSolution[] pieces; BoundTerm[] guards;
			BoundTerm build(uint id){
				if(observed(id)){
					IntegralSolution piece; auto value=integrateInterval(t,piece,id);
					if(value==BoundTerm.init) return value;
					// Beyond a single bound the result is under the guard of its
					// domain, which leaves the sum: a sum is missing where a
					// summand is.
					if(piece.bounds.half&&piece.bounds.domain!=uint.max){ guards~=at(node(value).a); value=at(node(value).b); }
					pieces~=piece; return value;
				}
				auto a=build(nodes[id].a); if(a==BoundTerm.init) return a;
				auto b=build(nodes[id].b); if(b==BoundTerm.init) return b;
				return primitive(arena.add(arena.real_(0),arena.real_(0),true),[a,b]);
			}
			auto total=build(solution.from[0]);
			if(total==BoundTerm.init) return BoundTerm.init;
			foreach_reverse(g;guards) total=guard(g,total);
			solution.pieces=pieces; solution.interval=true; solution.piecewise=true; solution.output=total.id;
			return total;
		}
		// A strict guard that does not mention the axis leaves the observation:
		// where it does not hold the density is undefined everywhere, and so
		// is the observation. This needs nothing of the inner observation.
		BoundTerm unguardMass(BoundTerm t){
			uint[] weights; size_t position; uint condition; BoundTerm rest;
			if(!massStrictGuard(t.id,weights,position,condition,rest)) return BoundTerm.init;
			auto ctx=context(t),d=distribution(ctx,BoundOp.distributionLebesgue);
			foreach(i,w;weights) d=distribution(ctx,BoundOp.distributionWeight,[i==position?inheritHint(at(w),lambda(rest)):at(w),d]);
			return guard(dropIndex(at(condition)),distribution(ctx,BoundOp.distributionMass,[d]));
		}
		// A factor or a mask of a sum of masked summands goes under the sum: a
		// product and a mask distribute over a sum for every definedness
		// pattern. Before that a weight is split where the arguments of its
		// absolute values change sign: under the mask of a side the absolute
		// value is its argument or the opposite. Each summand then takes its
		// normal form by itself, under the guard of its domain; that of the
		// whole sum would put a common mask back in front. Only where every
		// summand is then an observation between bounds of its own, under its
		// domain where that mentions the axis.
		BoundTerm distributeMass(BoundTerm t,out IntegralSolution solution,bool commit){
			auto n=node(t);
			if(n.op!=BoundOp.distributionMass||!densityBodies(n.a,solution.from)||solution.from.length!=1) return BoundTerm.init;
			auto body=solution.from[0],kinks=absoluteKinks(body);
			if(!kinks.length&&!spreadsSum(body)) return BoundTerm.init;
			auto source=kinks.length?splitAt(body,kinks,null).id:body,spread=spreadProducts(source,16,null);
			if(spread.id==uint.max||spread.id==body) return BoundTerm.init;
			auto opts=Options(DensityMode.preserve,true),inner=context(at(body));
			auto index=freshScalarIndex(body),argument=arena.variable(Sort.real_,index);
			auto addOp=arena.add(arena.real_(0),arena.real_(0),true);
			ScalarDomain[] checks; uint[] summands; BoundTerm[] conditions;
			bool observed(BoundTerm x){ IntegralSolution trial; return integrateInterval(t,trial,x.id,false)!=BoundTerm.init; }
			BoundTerm normal(uint id){
				auto q=nodes[id];
				if(q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.add&&type(at(id))==scalarType(Sort.real_)){
					auto a=normal(q.a); if(a==BoundTerm.init) return a;
					auto b=normal(q.b); if(b==BoundTerm.init) return b;
					return primitive(addOp,[a,b]);
				}
				auto source=scalarBody(at(id),argument); if(source==Term.init) return BoundTerm.init;
				// A summand that the simplifier cannot take leaves the weight as it is.
				ScalarResult value,domain;
				try{ value=simplify(arena,source,opts); domain=simplifyDomain(arena,source,[],opts); }
				catch(Exception){ return BoundTerm.init; }
				if(value.exhausted||domain.exhausted) return BoundTerm.init;
				auto output=arena.castTo(value.output,arena.sort(source));
				if(output==source){ summands~=uint.max; return observed(at(id))?at(id):BoundTerm.init; }
				auto simplified=restoreBody(output,inner,argument);
				summands~=cast(uint)(scalarDomains.length+checks.length); checks~=ScalarDomain(source,domain,value,index,Sort.real_,[],BoundOp.scalar);
				// A summand that vanishes, on a piece that its mask excludes, stays
				// as the zero that it is.
				bool vanishes=arena.isNumber(value.output)&&arena.number(value.output).re.zero&&arena.number(value.output).im.zero;
				if(domain.output==arena.boolean(true)) return vanishes||observed(simplified)?simplified:BoundTerm.init;
				// A domain that mentions the axis stays around its summand, which
				// is observed under it; another leaves the sum.
				auto condition=restoreBody(domain.output,inner,argument);
				if(depends(condition,0)){ auto guarded=guard(condition,simplified); return observed(guarded)?guarded:BoundTerm.init; }
				if(!observed(simplified)) return BoundTerm.init;
				conditions~=condition; return simplified;
			}
			auto target=normal(spread.id);
			if(target==BoundTerm.init) return BoundTerm.init;
			// The guards leave the sum together, in the order of the summands.
			foreach_reverse(condition;conditions) target=guard(condition,target);
			if(commit) scalarDomains~=checks;
			solution.to=[target.id]; solution.summands=summands;
			if(kinks.length){ solution.kinks=kinks; solution.split=source; }
			auto ctx=context(t),weight=inheritHint(at(nodes[n.a].a),lambda(target));
			return distribution(ctx,BoundOp.distributionMass,[distribution(ctx,BoundOp.distributionWeight,[weight,distribution(ctx,BoundOp.distributionLebesgue)])]);
		}
		// A guard that does not mention the axis leaves the observation. The
		// mask is not strict, so this is an equation even where the inner
		// observation is missing. Used only if the rest can then be observed.
		BoundTerm massGuard(BoundTerm t,uint depth){
			uint guard; BoundTerm rest; string shape;
			if(depth>8||!axisFreeGuard(t.id,guard,rest,shape)) return BoundTerm.init;
			auto ctx=context(t),weight=inheritHint(at(nodes[node(t).a].a),lambda(rest));
			auto inside=distribution(ctx,BoundOp.distributionMass,[distribution(ctx,BoundOp.distributionWeight,[weight,distribution(ctx,BoundOp.distributionLebesgue)])]);
			IntegralSolution trial; bool observed=integrateSteps(inside,trial)!=BoundTerm.init;
			if(!observed){ trial=IntegralSolution.init; observed=integratePolynomials(inside,trial)!=BoundTerm.init; }
			if(!observed){ trial=IntegralSolution.init; observed=integrateInterval(inside,trial)!=BoundTerm.init; }
			if(!observed){ trial=IntegralSolution.init; observed=integrateGaussian(inside,trial)!=BoundTerm.init; }
			if(!observed){ trial=IntegralSolution.init; observed=integratePieces(inside,trial)!=BoundTerm.init; }
			if(!observed){ trial=IntegralSolution.init; observed=distributeMass(inside,trial,false)!=BoundTerm.init; }
			if(!observed&&massGuard(inside,depth+1)==BoundTerm.init) return BoundTerm.init;
			return primitive(arena.mask(arena.boolean(true),arena.real_(1)),[dropIndex(at(guard)),inside]);
		}
		bool affineNaturalParts(BoundTerm t,out BoundTerm coefficient,out BoundTerm offset,out BoundTerm index){
			bool call(BoundNode q,Builtin f){return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f;}
			auto n=node(t);if(!call(n,Builtin.addN)||depends(at(n.b),0))return false;
			auto mul=nodes[n.a];if(!call(mul,Builtin.mulN)||nodes[mul.b].op!=BoundOp.variable||nodes[mul.b].data!=0)return false;
			auto c=nodes[mul.a];if(c.op!=BoundOp.scalar||!arena.isNumber(arena.at(c.data))||arena.number(arena.at(c.data)).re<=Number(0).re)return false;
			coefficient=at(mul.a);offset=at(n.b);index=at(mul.b);return true;
		}
		uint indexedPower(uint id){
			while(primitiveOp(id,Op.builtin)){
				auto n=nodes[id],op=arena.view(arena.at(n.data)).value;
				if(op>=Builtin.powNN&&op<=Builtin.powCN) return id;
				if(op<Builtin.castNZ||op>Builtin.castRC) break;
				id=n.a;
			}
			return uint.max;
		}
		BoundTerm indexedBase(uint id,uint power){
			auto n=nodes[id];
			return id==power?at(n.a):primitive(arena.at(n.data),[indexedBase(n.a,power)]);
		}
		// Round real comparisons only in a summand. These are equalities on
		// partial values, including negative and undefined bounds.
		Result roundSumBounds(BoundTerm t,bool splitMasks=false,bool expandExponent=false){
			auto n=node(t);
			if((n.op==BoundOp.scalar||n.op==BoundOp.primitive)&&!depends(t,0)&&scalarBody(t,arena.natural_(0))!=Term.init) return visit(t,0);
			if(n.op==BoundOp.primitive){
				auto scalarOp=arena.view(arena.at(n.data)),op=scalarOp.op;
				if(op==Op.mul||op==Op.builtin&&(scalarOp.value==Builtin.mulN||scalarOp.value==Builtin.mulZ||scalarOp.value==Builtin.mulQ)){
					auto left=indexedPower(n.a),right=indexedPower(n.b);
					if(left!=uint.max&&right!=uint.max&&nodes[left].b==nodes[right].b&&depends(at(nodes[left].b),0)){
						auto a=indexedBase(n.a,left),b=indexedBase(n.b,right),index=at(nodes[left].b);
						auto sort=elementSort(type(t)),zero=arena.number(Number(0),sort);
						auto pow=sort==Sort.natural?Builtin.powNN:sort==Sort.integer?Builtin.powZN:sort==Sort.rational?Builtin.powQN:sort==Sort.real_?Builtin.powRN:Builtin.powCN;
						auto base=primitive(arena.at(n.data),[a,b]),product=primitive(arena.call(pow,[zero,arena.natural_(0)]),[base,index]);
						return Result(product.id,emit(BindingRule.sumPowerProduct,t.id,product.id));
					}
				}
				if(op==Op.builtin){
					auto cmp=arena.view(arena.at(n.data)).value;
					// Expose geometric structure only inside sums. Ordinary scalar
					// normalization deliberately prefers exp/cis over their powers.
					BoundTerm naturalArgument(BoundTerm x){
						foreach(c;[Builtin.castRC,Builtin.castQR,Builtin.castZQ,Builtin.castNZ]){
							auto v=node(x);
							if(v.op==BoundOp.primitive&&arena.view(arena.at(v.data)).op==Op.builtin&&arena.view(arena.at(v.data)).value==c)x=at(v.a);
						}
						return type(x)==scalarType(Sort.natural)?x:BoundTerm.init;
					}
					if(cmp==Builtin.exp2R){
						auto logTwo=scalar(context(t),arena.call(Builtin.logR,[arena.real_(2)]));
						auto argument=primitive(arena.mul(arena.real_(0),arena.real_(0),true),[logTwo,at(n.a)]);
						auto out_=primitive(arena.call(Builtin.expR,[arena.real_(0)]),[argument]);
						return Result(out_.id,emit(BindingRule.sumExp2,t.id,out_.id));
					}
					if(splitMasks&&(cmp==Builtin.sinR||cmp==Builtin.cosR)){
						auto phase=primitive(arena.call(Builtin.cisR,[arena.real_(0)]),[at(n.a)]);
						auto out_=primitive(arena.call(cmp==Builtin.sinR?Builtin.imC:Builtin.reC,[arena.complex(0)]),[phase]);
						return Result(out_.id,emit(BindingRule.sumTrigReal,t.id,out_.id));
					}
					if(splitMasks&&(cmp==Builtin.sinhR||cmp==Builtin.coshR||cmp==Builtin.sinhC||cmp==Builtin.coshC||cmp==Builtin.sinC||cmp==Builtin.cosC)){
						auto sort=elementSort(type(t)),z=arena.number(Number(0),sort),minus=scalar(context(t),arena.number(Number(-1),sort));
						auto exp=arena.call(sort==Sort.real_?Builtin.expR:Builtin.expC,[z]);
						auto argument=at(n.a);
						if(cmp==Builtin.sinC||cmp==Builtin.cosC)argument=primitive(arena.mul(z,z,true),[scalar(context(t),arena.complex(0,1)),argument]);
						auto positive=primitive(exp,[argument]),negative=primitive(exp,[primitive(arena.mul(z,z,true),[minus,argument])]);
						if(cmp==Builtin.sinhR||cmp==Builtin.sinhC||cmp==Builtin.sinC)negative=primitive(arena.mul(z,z,true),[minus,negative]);
						auto sum=primitive(arena.add(z,z,true),[positive,negative]);
						auto half=cmp==Builtin.sinC?arena.complex(Rational(0),Rational(-1)/Rational(2)):arena.number(Number(Rational(1)/Rational(2)),sort);
						auto out_=primitive(arena.mul(z,z,true),[scalar(context(t),half),sum]);
						return Result(out_.id,emit(BindingRule.sumHyperbolic,t.id,out_.id));
					}
					if(cmp==Builtin.expR||cmp==Builtin.expC||cmp==Builtin.cisR||cmp==Builtin.expiC){
						auto arg=at(n.a),v=node(arg),index=naturalArgument(arg),coefficient=BoundTerm.init;
						uint form;
						if(index!=BoundTerm.init)coefficient=scalar(context(t),arena.number(Number(1),elementSort(type(arg))));
						else if(v.op==BoundOp.primitive&&arena.view(arena.at(v.data)).op==Op.mul){
							foreach(reverse;0..2){
								auto candidate=naturalArgument(at(reverse?v.a:v.b)),other=at(reverse?v.b:v.a);
								if(candidate!=BoundTerm.init&&!depends(other,0)){index=candidate;coefficient=other;form=1+reverse;break;}
							}
						}
						if(index!=BoundTerm.init){
							auto ratio=primitive(arena.at(n.data),[coefficient]),sort=elementSort(type(t));
							auto out_=primitive(arena.call(sort==Sort.real_?Builtin.powRN:Builtin.powCN,[arena.number(Number(0),sort),arena.natural_(0)]),[ratio,index]);
							return Result(out_.id,emit(BindingRule.sumElementaryPower,t.id,out_.id,uint.max,uint.max,form));
						}
						Result gather(BoundTerm x){
							auto m=node(x);if(m.op!=BoundOp.primitive||arena.view(arena.at(m.data)).op!=Op.mul)return Result(x.id,emit(BindingRule.refl,x.id,x.id));
							auto l=gather(at(m.a)),r=gather(at(m.b)),out_=primitive(arena.at(m.data),[at(l.output),at(r.output)]);
							auto proof=emit(BindingRule.congr,x.id,out_.id,l.proof,r.proof);
							if(depends(at(l.output),0)&&!depends(at(r.output),0)){
								auto swap=primitive(arena.at(m.data),[at(r.output),at(l.output)]);
								proof=emit(BindingRule.trans,x.id,swap.id,proof,emit(BindingRule.sumMulSwap,out_.id,swap.id));out_=swap;
							}
							auto q=node(out_),right=nodes[q.b];
							if(!depends(at(q.a),0)&&right.op==BoundOp.primitive&&arena.view(arena.at(right.data)).op==Op.mul&&!depends(at(right.a),0)){
								auto coefficient=primitive(arena.at(m.data),[at(q.a),at(right.a)]),flat=primitive(arena.at(m.data),[coefficient,at(right.b)]);
								proof=emit(BindingRule.trans,x.id,flat.id,proof,emit(BindingRule.sumMulAssoc,out_.id,flat.id));out_=flat;
							}
							return Result(out_.id,proof);
						}
						auto grouped=gather(arg);
						if(grouped.output!=arg.id){
							auto out_=primitive(arena.at(n.data),[at(grouped.output)]);
							return Result(out_.id,emit(BindingRule.congr,t.id,out_.id,grouped.proof));
						}
						if(v.op==BoundOp.primitive&&arena.view(arena.at(v.data)).op==Op.add&&(!depends(at(v.a),0)||!depends(at(v.b),0))){
							auto x=primitive(arena.at(n.data),[at(v.a)]),y=primitive(arena.at(n.data),[at(v.b)]),z=arena.number(Number(0),elementSort(type(t)));
							auto out_=primitive(arena.mul(z,z,true),[x,y]);
							return Result(out_.id,emit(BindingRule.sumElementaryAdd,t.id,out_.id));
						}
					}
					if(cmp==Builtin.powerR||cmp==Builtin.powerC){
						auto index=naturalArgument(at(n.b));
						if(index!=BoundTerm.init){
							auto sort=elementSort(type(t)),z=arena.number(Number(0),sort);
							auto out_=primitive(arena.call(sort==Sort.real_?Builtin.powRN:Builtin.powCN,[z,arena.natural_(0)]),[at(n.a),index]);
							return Result(out_.id,emit(BindingRule.sumGeneralPower,t.id,out_.id));
						}
					}
					if(expandExponent&&cmp>=Builtin.castNZ&&cmp<=Builtin.castRC){
						auto child=nodes[n.a];
						if(child.op==BoundOp.primitive){
							auto v=arena.view(arena.at(child.data));
							bool add=v.op==Op.add||v.op==Op.builtin&&(v.value==Builtin.addN||v.value==Builtin.addZ||v.value==Builtin.addQ);
							bool mul=v.op==Op.mul||v.op==Op.builtin&&(v.value==Builtin.mulN||v.value==Builtin.mulZ||v.value==Builtin.mulQ);
							if(add||mul){
								auto x=primitive(arena.at(n.data),[at(child.a)]),y=primitive(arena.at(n.data),[at(child.b)]);
								auto out_=primitive(scalarOperator(type(t),add?TensorOp.add:TensorOp.mul),[x,y]);
								return Result(out_.id,emit(add?BindingRule.sumCastAdd:BindingRule.sumCastMul,t.id,out_.id));
							}
						}
					}
					if(cmp>=Builtin.powNN&&cmp<=Builtin.powCN){
						auto e=nodes[n.b];
						if(e.op==BoundOp.primitive&&arena.view(arena.at(e.data)).op==Op.builtin&&arena.view(arena.at(e.data)).value==Builtin.mulN){
							foreach(reverse;0..2){
								auto c=at(reverse?e.b:e.a),i=at(reverse?e.a:e.b);
								if(depends(c,0)||!depends(i,0))continue;
								auto q=primitive(arena.at(n.data),[at(n.a),c]),out_=primitive(arena.at(n.data),[q,i]);
								return Result(out_.id,emit(BindingRule.sumNaturalPowerMul,t.id,out_.id,uint.max,uint.max,reverse));
							}
						}
					}
					if(cmp>=Builtin.powQZ&&cmp<=Builtin.powCZ){
						bool call(BoundNode q,Builtin f){return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f;}
						auto exponent=nodes[n.b],pow=cast(Builtin)(Builtin.powQN+cmp-Builtin.powQZ),zero=arena.number(Number(0),elementSort(type(t)));
						if(call(exponent,Builtin.castNZ)){
							auto out_=primitive(arena.call(pow,[zero,arena.natural_(0)]),[at(n.a),at(exponent.a)]);
							return Result(out_.id,emit(BindingRule.sumPowerNatural,t.id,out_.id));
						}
						if(call(exponent,Builtin.addZ))foreach(reverse;0..2){
							auto offset=nodes[reverse?exponent.b:exponent.a],product=nodes[reverse?exponent.a:exponent.b];
							if(offset.op!=BoundOp.scalar||!arena.isNumber(arena.at(offset.data))||arena.number(arena.at(offset.data)).re>=Number(0).re||!call(product,Builtin.mulZ))continue;
							auto minus=nodes[product.a],cast_=nodes[product.b];
							if(minus.op!=BoundOp.scalar||!arena.isNumber(arena.at(minus.data))||arena.number(arena.at(minus.data))!=Number(-1)||!call(cast_,Builtin.castNZ))continue;
							auto count=scalar(context(t),arena.number(-arena.number(arena.at(offset.data)),Sort.natural));
							auto power=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[at(cast_.a),count]);
							auto out_=primitive(arena.call(pow,[zero,arena.natural_(0)]),[primitive(arena.inv(zero),[at(n.a)]),power]);
							return Result(out_.id,emit(BindingRule.sumPowerNegative,t.id,out_.id,uint.max,uint.max,reverse));
						}
					}
					if(cmp==Builtin.nonzeroQ){
						auto add=nodes[n.a];
						if(add.op==BoundOp.primitive&&arena.view(arena.at(add.data)).op==Op.builtin&&arena.view(arena.at(add.data)).value==Builtin.addQ&&depends(at(add.a),0)&&!depends(at(add.b),0)){
							auto cast_=arena.call(Builtin.castQR,[arena.number(Number(0),Sort.rational)]),z=arena.real_(0);
							auto value=primitive(arena.add(z,z,true),[primitive(cast_,[at(add.a)]),primitive(cast_,[at(add.b)])]);
							auto out_=primitive(arena.nonzero(z),[value]);
							return Result(out_.id,emit(BindingRule.sumRationalSelector,t.id,out_.id));
						}
					}
					if(cmp==Builtin.ltZ||cmp==Builtin.leZ){
						bool call(BoundNode v,Builtin f){return v.op==BoundOp.primitive&&arena.view(arena.at(v.data)).op==Op.builtin&&arena.view(arena.at(v.data)).value==f;}
						bool index(uint id){auto v=nodes[id];if(call(v,Builtin.castNZ))v=nodes[v.a];return v.op==BoundOp.variable&&v.data==0;}
						bool affine(uint id){
							auto v=nodes[id];if(call(v,Builtin.addZ)&&!depends(at(v.b),0)){if(index(v.a))return true;v=nodes[v.a];}
							if(!call(v,Builtin.mulZ)||!index(v.b))return false;
							auto c=nodes[v.a];return c.op==BoundOp.scalar&&arena.isNumber(arena.at(c.data))&&arena.number(arena.at(c.data)).re>Rational(0);
						}
						if(affine(n.a)&&!depends(at(n.b),0)||affine(n.b)&&!depends(at(n.a),0)){
							BoundTerm asReal(BoundTerm x){foreach(c;[Builtin.castZQ,Builtin.castQR])x=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[x]);return x;}
							auto out_=primitive(cmp==Builtin.ltZ?arena.lt(arena.real_(0),arena.real_(0)):arena.le(arena.real_(0),arena.real_(0)),[asReal(at(n.a)),asReal(at(n.b))]);
							return Result(out_.id,emit(BindingRule.sumIntegerBound,t.id,out_.id));
						}
					}
					if(cmp==Builtin.ltN||cmp==Builtin.leN){
						BoundTerm a,b,i;
						if(affineNaturalParts(at(n.a),a,b,i)&&!depends(at(n.b),0)||affineNaturalParts(at(n.b),a,b,i)&&!depends(at(n.a),0)){
							BoundTerm asReal(BoundTerm x){foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR])x=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[x]);return x;}
							auto out_=primitive(cmp==Builtin.ltN?arena.lt(arena.real_(0),arena.real_(0)):arena.le(arena.real_(0),arena.real_(0)),[asReal(at(n.a)),asReal(at(n.b))]);
							return Result(out_.id,emit(BindingRule.sumNaturalBound,t.id,out_.id));
						}
					}
					if(cmp==Builtin.ltQ||cmp==Builtin.leQ){
						auto cast_=arena.call(Builtin.castQR,[arena.number(Number(0),Sort.rational)]);
						auto left=primitive(cast_,[at(n.a)]),right=primitive(cast_,[at(n.b)]);
						auto out_=primitive(cmp==Builtin.ltQ?arena.lt(arena.real_(0),arena.real_(0)):arena.le(arena.real_(0),arena.real_(0)),[left,right]);
						return Result(out_.id,emit(BindingRule.sumRationalBound,t.id,out_.id));
					}
				}
				if(op==Op.mask){
					auto pred=nodes[n.a];
					if(pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.nonzero){
						auto add=nodes[pred.a];
						if(add.op==BoundOp.primitive&&arena.view(arena.at(add.data)).op==Op.add&&!depends(at(add.b),0)){
							auto z=arena.real_(0),minus=scalar(context(t),arena.real_(-1));
							auto bound=primitive(arena.mul(z,z,true),[minus,at(add.b)]);
							auto left=primitive(arena.at(n.data),[primitive(arena.lt(z,z),[at(add.a),bound]),at(n.b)]);
							auto right=primitive(arena.at(n.data),[primitive(arena.lt(z,z),[bound,at(add.a)]),at(n.b)]);
							auto out_=primitive(scalarOperator(type(t),TensorOp.add),[left,right]);
							return Result(out_.id,emit(BindingRule.sumRealExclude,t.id,out_.id));
						}
					}
				}
				if(op==Op.not_){
					auto nz=nodes[n.a];
					if(nz.op==BoundOp.primitive&&arena.view(arena.at(nz.data)).op==Op.nonzero){
						auto add=nodes[nz.a];
						if(add.op==BoundOp.primitive&&arena.view(arena.at(add.data)).op==Op.add&&!depends(at(add.b),0)){
							auto z=arena.real_(0),minus=scalar(context(t),arena.real_(-1));
							auto bound=primitive(arena.mul(z,z,true),[minus,at(add.b)]);
							auto left=primitive(arena.le(z,z),[at(add.a),bound]),right=primitive(arena.le(z,z),[bound,at(add.a)]);
							auto out_=primitive(arena.and_(arena.boolean(false),arena.boolean(false)),[right,left]);
							return Result(out_.id,emit(BindingRule.sumRealEquality,t.id,out_.id));
						}
					}
				}
				if(!splitMasks&&op==Op.mask){
					auto inner=nodes[n.b];
					bool comparison(uint id){auto p=nodes[id];if(p.op!=BoundOp.primitive)return false;auto op=arena.view(arena.at(p.data));return op.op==Op.le||op.op==Op.lt||op.op==Op.builtin&&(op.value==Builtin.leN||op.value==Builtin.ltN||op.value==Builtin.leZ||op.value==Builtin.ltZ||op.value==Builtin.leQ||op.value==Builtin.ltQ);}
					// Keep upper-first and intersected upper masks nested: their
					// outer mask already gives a finite range. Merge only a lower
					// bound followed by an upper bound for interval reindexing.
					bool index(uint id){
						auto v=nodes[id];
						while(v.op==BoundOp.primitive){auto op=arena.view(arena.at(v.data));if(op.op!=Op.builtin||op.value<Builtin.castNZ||op.value>Builtin.castQR)return false;v=nodes[v.a];}
						return v.op==BoundOp.variable&&v.data==0;
					}
					bool lower(uint id){auto p=nodes[id];return comparison(id)&&!depends(at(p.a),0)&&index(p.b);}
					bool upper(uint id){auto p=nodes[id];return comparison(id)&&index(p.a)&&!depends(at(p.b),0);}
					auto pred=nodes[n.a];
					if(pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.and_&&(!lower(pred.a)||!upper(pred.b))){
						auto inside=primitive(arena.at(n.data),[at(pred.b),at(n.b)]);
						auto out_=primitive(arena.at(n.data),[at(pred.a),inside]);
						return Result(out_.id,emit(BindingRule.sumMaskAnd,t.id,out_.id));
					}
					if(inner.op==BoundOp.primitive&&arena.view(arena.at(inner.data)).op==Op.mask&&lower(n.a)&&upper(inner.a)){
						auto combined=primitive(arena.and_(arena.boolean(false),arena.boolean(false)),[at(n.a),at(inner.a)]);
						auto out_=primitive(arena.at(n.data),[combined,at(inner.b)]);
						return Result(out_.id,emit(BindingRule.sumMaskMerge,t.id,out_.id));
					}
				}
				if(splitMasks&&op==Op.mask){
					auto pred=nodes[n.a];
					if(pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.and_){
						auto inside=primitive(arena.at(n.data),[at(pred.b),at(n.b)]);
						auto out_=primitive(arena.at(n.data),[at(pred.a),inside]);
						return Result(out_.id,emit(BindingRule.sumMaskAnd,t.id,out_.id));
					}
				}
				if(op==Op.mask){
					auto pred=at(n.a),pn=node(pred);bool equality=pn.op==BoundOp.primitive&&arena.view(arena.at(pn.data)).op==Op.not_;
					if(equality) pn=nodes[pn.a];
					if((equality||splitMasks)&&pn.op==BoundOp.primitive&&arena.view(arena.at(pn.data)).op==Op.builtin&&arena.view(arena.at(pn.data)).value==Builtin.nonzeroZ){
						auto diff=nodes[pn.a];
						if(diff.op==BoundOp.primitive&&arena.view(arena.at(diff.data)).op==Op.builtin&&arena.view(arena.at(diff.data)).value==Builtin.addZ){
							auto cast_=nodes[diff.a];
							if(equality&&(nodes[diff.b].op!=BoundOp.scalar||!arena.isNumber(arena.at(nodes[diff.b].data)))) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
							if(cast_.op==BoundOp.primitive&&arena.view(arena.at(cast_.data)).op==Op.builtin&&arena.view(arena.at(cast_.data)).value==Builtin.castNZ&&nodes[cast_.a].op==BoundOp.variable&&nodes[cast_.a].data==0&&!depends(at(diff.b),0)){
								auto ctx=context(t),iv=at(cast_.a),c=at(diff.b);
								BoundTerm unary(Builtin op,BoundTerm x){return primitive(arena.call(op,[arena.number(Number(0),builtinInfo(op).args[0])]),[x]);}
								auto negative=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[scalar(ctx,arena.integer(-1)),c]);
								auto plus=primitive(arena.add(arena.integer(0),arena.integer(0),true),[negative,scalar(ctx,arena.integer(1))]);
								BoundTerm count(BoundTerm x){return unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,x)));}
								auto lo=count(negative),hi=count(plus),zero=arena.natural_(0);
								BoundTerm lt(BoundTerm a,BoundTerm b){return primitive(arena.call(Builtin.ltN,[zero,zero]),[a,b]);}
								BoundTerm le(BoundTerm a,BoundTerm b){return primitive(arena.call(Builtin.leN,[zero,zero]),[a,b]);}
								BoundTerm mask(BoundTerm p){return primitive(arena.at(n.data),[p,at(n.b)]);}
								auto out_=equality?mask(primitive(arena.and_(arena.boolean(false),arena.boolean(false)),[le(lo,iv),lt(iv,hi)])):
									primitive(scalarOperator(type(t),TensorOp.add),[mask(lt(iv,lo)),mask(le(hi,iv))]);
								return Result(out_.id,emit(equality?BindingRule.sumMaskEqOffset:BindingRule.sumMaskNeOffset,t.id,out_.id,uint.max,uint.max,c.id));
							}
						}
					}
				}
				if(op==Op.lt||op==Op.le)foreach(reverse;0..2){
					auto expression=at(reverse?n.b:n.a),bound=at(reverse?n.a:n.b);
					bool call(BoundNode q,Builtin f){return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f;}
					foreach(c;[Builtin.castQR,Builtin.castZQ]){
						auto v=node(expression);if(!call(v,c)){expression=BoundTerm.init;break;}expression=at(v.a);
					}
					if(expression==BoundTerm.init||depends(bound,0))continue;
					auto add=node(expression);bool scale=call(add,Builtin.mulZ);
					if(!scale&&(!call(add,Builtin.addZ)||depends(at(add.b),0)))continue;
					auto i=scale?expression:at(add.a),a=BoundTerm.init,b=scale?scalar(context(t),arena.integer(0)):at(add.b),mul=node(i);
					if(call(mul,Builtin.mulZ)&&!depends(at(mul.a),0)){
						a=at(mul.a);i=at(mul.b);auto c=node(a);
						if(c.op!=BoundOp.scalar||!arena.isNumber(arena.at(c.data))||arena.number(arena.at(c.data)).re<=Rational(0))continue;
					}
					auto iv=node(i);if(call(iv,Builtin.castNZ))iv=nodes[iv.a];
					if(iv.op!=BoundOp.variable||iv.data!=0)continue;
					BoundTerm realZ(BoundTerm x){foreach(c;[Builtin.castZQ,Builtin.castQR])x=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[x]);return x;}
					auto ctx=context(t),z=arena.real_(0);
					auto negative=primitive(arena.mul(z,z,true),[scalar(ctx,arena.real_(-1)),realZ(b)]);
					auto threshold=primitive(arena.add(z,z,true),[bound,negative]);
					if(scale)threshold=bound;
					if(a!=BoundTerm.init)threshold=primitive(arena.mul(z,z,true),[threshold,primitive(arena.inv(z),[realZ(a)])]);
					auto out_=primitive(arena.at(n.data),reverse?[threshold,realZ(i)]:[realZ(i),threshold]);
					return Result(out_.id,emit(scale?BindingRule.sumScaleInteger:a==BoundTerm.init?BindingRule.sumShiftInteger:BindingRule.sumAffineInteger,t.id,out_.id,uint.max,uint.max,reverse));
				}
				if(op==Op.lt||op==Op.le)foreach(reverse;0..2){
					auto expression=at(reverse?n.b:n.a),bound=at(reverse?n.a:n.b);
					foreach(c;[Builtin.castQR,Builtin.castZQ,Builtin.castNZ]){
						auto v=node(expression);
						if(v.op!=BoundOp.primitive||arena.view(arena.at(v.data)).op!=Op.builtin||arena.view(arena.at(v.data)).value!=c){expression=BoundTerm.init;break;}
						expression=at(v.a);
					}
					BoundTerm a,b,i;if(expression==BoundTerm.init||depends(bound,0)||!affineNaturalParts(expression,a,b,i))continue;
					BoundTerm asReal(BoundTerm x){foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR])x=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[x]);return x;}
					auto ctx=context(t),z=arena.real_(0);
					auto negative=primitive(arena.mul(z,z,true),[scalar(ctx,arena.real_(-1)),asReal(b)]);
					auto shifted=primitive(arena.add(z,z,true),[bound,negative]);
					auto threshold=primitive(arena.mul(z,z,true),[shifted,primitive(arena.inv(z),[asReal(a)])]);
					auto out_=primitive(arena.at(n.data),reverse?[threshold,asReal(i)]:[asReal(i),threshold]);
					return Result(out_.id,emit(BindingRule.sumAffineNatural,t.id,out_.id,uint.max,uint.max,reverse));
				}
				if(op==Op.lt||op==Op.le) foreach(reverse;0..2){
					auto index=at(reverse?n.b:n.a),bound=at(reverse?n.a:n.b);
					foreach(c;[Builtin.castQR,Builtin.castZQ]){
						auto v=node(index);
						if(v.op!=BoundOp.primitive||arena.view(arena.at(v.data)).op!=Op.builtin||arena.view(arena.at(v.data)).value!=c){ index=BoundTerm.init; break; }
						index=at(v.a);
					}
					if(index==BoundTerm.init) continue;
					bool natural; auto v=node(index);
					if(v.op==BoundOp.primitive&&arena.view(arena.at(v.data)).op==Op.builtin&&arena.view(arena.at(v.data)).value==Builtin.castNZ){ natural=true;index=at(v.a);v=node(index); }
					if(v.op!=BoundOp.variable||v.data!=0||depends(bound,0)) continue;
					auto ctx=context(t);
					BoundTerm unary(Builtin f,BoundTerm x){ return primitive(arena.call(f,[arena.number(Number(0),builtinInfo(f).args[0])]),[x]); }
					bool ceiling=(op==Op.lt)!=cast(bool)reverse;
					auto rounded=unary(ceiling?Builtin.ceilR:Builtin.floorR,bound);
					if(!ceiling) rounded=primitive(arena.add(arena.integer(0),arena.integer(0),true),[rounded,scalar(ctx,arena.integer(1))]);
					if(natural) rounded=unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,rounded)));
					auto cmp=natural?(reverse?Builtin.leN:Builtin.ltN):(reverse?Builtin.leZ:Builtin.ltZ),zero=arena.number(Number(0),natural?Sort.natural:Sort.integer);
					auto out_=primitive(arena.call(cmp,[zero,zero]),reverse?[rounded,index]:[index,rounded]);
					auto flags=cast(uint)(!natural)*4+reverse*2+cast(uint)(op==Op.le);
					return Result(out_.id,emit(BindingRule.sumRound,t.id,out_.id,uint.max,uint.max,flags));
				}
			}
			// Do not cross another binder: its de Bruijn zero is a different index.
			if(n.op!=BoundOp.primitive) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
			auto op=arena.view(arena.at(n.data));
			auto elementary=op.op==Op.builtin&&(op.value==Builtin.expR||op.value==Builtin.expC||op.value==Builtin.cisR||op.value==Builtin.expiC||op.value==Builtin.exp2R);
			auto x=roundSumBounds(at(n.a),splitMasks,expandExponent||elementary); auto y=n.b==uint.max?Result(uint.max,uint.max):roundSumBounds(at(n.b),splitMasks,expandExponent);
			if(x.output==n.a&&y.output==n.b) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
			auto out_=rebuild(t,context(t),n.b==uint.max?[at(x.output)]:[at(x.output),at(y.output)]);
			return Result(out_.id,emit(BindingRule.congr,t.id,out_.id,x.proof,y.proof));
		}
		// Every lattice point is tested at its actual index and only a false
		// guard is used. Neighbours of affine cuts cover open and closed edges.
		BoundTerm missingGuardWitness(BoundTerm term){
			auto sum=node(term),fn=nodes[sum.a];
			if(fn.op!=BoundOp.lambda||nodes[fn.a].op!=BoundOp.guard) return BoundTerm.init;
			auto body=nodes[fn.a],indexSort=elementSort(type(variable(context(at(fn.a)),0)));
			bool finite=sum.op==BoundOp.finiteSum;
			Rational count;
			if(finite){
				auto bound=nodes[sum.b];
				if(bound.op!=BoundOp.scalar||!arena.isNumber(arena.at(bound.data))) return BoundTerm.init;
				count=arena.number(arena.at(bound.data)).re;
			}
			auto marker=arena.variable(indexSort,freshScalarIndex(body.a));
			auto pred=scalarBody(at(body.a),marker); Rational[] cuts;
			if(pred==Term.init||!integralCutPoints(arena,pred,marker,cuts)) return BoundTerm.init;
			BoundTerm test(Rational index){
				if(indexSort==Sort.natural&&index<Rational(0)||finite&&index>=count) return BoundTerm.init;
				auto k=arena.number(Number(index),indexSort),raw=scalarBody(at(body.a),k);
				auto check=simplify(arena,raw);
				if(check.exhausted||check.output!=arena.boolean(false)) return BoundTerm.init;
				auto ctx=context(term); return tuple(ctx,[scalar(ctx,k),scalar(ctx,raw)]);
			}
			auto witness=test(Rational(0));
			foreach(cut;cuts){
				if(witness!=BoundTerm.init) break;
				auto near=Rational(cut.numerator/cut.denominator,BigInt(1));
				foreach(offset;[0,-1,1]){
					witness=test(near+Rational(offset));
					if(witness!=BoundTerm.init) break;
				}
			}
			return witness;
		}
		bool boundedMask(BoundNode x){
			if(x.op!=BoundOp.primitive||arena.view(arena.at(x.data)).op!=Op.mask) return false;
			auto p=nodes[x.a]; if(p.op!=BoundOp.primitive) return false;
			auto op=arena.view(arena.at(p.data));
			return op.op==Op.builtin&&(op.value==Builtin.ltN||op.value==Builtin.leN)&&nodes[p.a].op==BoundOp.variable&&nodes[p.a].data==0&&!depends(at(p.b),0);
		}
		bool zeroSelector(BoundNode x){
			if(x.op!=BoundOp.primitive||arena.view(arena.at(x.data)).op!=Op.mask)return false;
			auto p=nodes[x.a];if(p.op!=BoundOp.primitive||arena.view(arena.at(p.data)).op!=Op.not_)return false;
			auto nz=nodes[p.a];if(nz.op!=BoundOp.primitive)return false;
			auto op=arena.view(arena.at(nz.data));if(op.op!=Op.builtin||(op.value!=Builtin.nonzeroN&&op.value!=Builtin.nonzeroZ))return false;
			auto iv=nodes[nz.a];
			if(iv.op==BoundOp.primitive&&arena.view(arena.at(iv.data)).op==Op.builtin&&arena.view(arena.at(iv.data)).value==Builtin.castNZ)iv=nodes[iv.a];
			return iv.op==BoundOp.variable&&iv.data==0;
		}
		bool additive(BoundNode x){
			if(x.op!=BoundOp.primitive) return false;
			auto a=arena.view(arena.at(x.data));
			return a.op==Op.add||a.op==Op.builtin&&(a.value==Builtin.addN||a.value==Builtin.addZ||a.value==Builtin.addQ);
		}
		bool multiplicative(BoundNode x){
			if(x.op!=BoundOp.primitive) return false;
			auto op=arena.view(arena.at(x.data));
			return op.op==Op.mul||op.op==Op.builtin&&(op.value==Builtin.mulN||op.value==Builtin.mulZ||op.value==Builtin.mulQ);
		}
		// Expose finite masks across numeric embeddings, but commit this direction
		// only when the resulting sum can immediately become a finite sum.
		Result exposeSumMasks(BoundTerm t){
			auto n=node(t); if(n.op!=BoundOp.primitive) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
			auto op=arena.view(arena.at(n.data));
			bool cast_=op.op==Op.builtin&&op.value>=Builtin.castNZ&&op.value<=Builtin.castRC;
			bool mul=multiplicative(n);
			if(!cast_&&!mul&&!additive(n)) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
			auto x=exposeSumMasks(at(n.a)),y=n.b==uint.max?Result(uint.max,uint.max):exposeSumMasks(at(n.b));
			auto out_=rebuild(t,context(t),n.b==uint.max?[at(x.output)]:[at(x.output),at(y.output)]);
			auto proof=emit(BindingRule.congr,t.id,out_.id,x.proof,y.proof);
			if(mul){
				bool masked(uint id){auto v=nodes[id];if(v.op!=BoundOp.primitive)return false;if(arena.view(arena.at(v.data)).op==Op.mask)return true;return v.a!=uint.max&&masked(v.a)||v.b!=uint.max&&masked(v.b);}
				foreach(reverse;0..2){
					auto sum=nodes[reverse?y.output:x.output],other=at(reverse?x.output:y.output);
					if(!additive(sum)||!masked(reverse?y.output:x.output))continue;
					auto left=primitive(arena.at(n.data),reverse?[other,at(sum.a)]:[at(sum.a),other]);
					auto right=primitive(arena.at(n.data),reverse?[other,at(sum.b)]:[at(sum.b),other]);
					auto next=primitive(arena.at(sum.data),[left,right]),step=emit(BindingRule.sumDistribute,out_.id,next.id,uint.max,uint.max,reverse);
					return Result(next.id,emit(BindingRule.trans,t.id,next.id,proof,step));
				}
			}
			auto child=nodes[x.output];
			if(cast_&&child.op==BoundOp.primitive){
				bool mask=arena.view(arena.at(child.data)).op==Op.mask;
				if(mask||additive(child)){
					auto left=mask?at(child.a):primitive(arena.at(n.data),[at(child.a)]),right=primitive(arena.at(n.data),[at(child.b)]);
					auto op2=mask?arena.mask(arena.boolean(false),arena.number(Number(0),elementSort(type(t)))):scalarOperator(type(t),TensorOp.add);
					auto next=primitive(op2,[left,right]),step=emit(mask?BindingRule.sumCastMask:BindingRule.sumCastAdd,out_.id,next.id);
					auto total=emit(BindingRule.trans,t.id,next.id,proof,step);
					if(mask){
						// The coercion now sits on the masked value, which may itself be masked.
						auto inner=exposeSumMasks(right);
						if(inner.output!=right.id){
							auto deeper=primitive(op2,[left,at(inner.output)]);
							auto lift=emit(BindingRule.congr,next.id,deeper.id,emit(BindingRule.refl,left.id,left.id),inner.proof);
							return Result(deeper.id,emit(BindingRule.trans,t.id,deeper.id,total,lift));
						}
					}
					return Result(next.id,total);
				}
			}
			return Result(out_.id,proof);
		}
		BoundTerm solveFinite(BoundTerm t,out uint extra,bool infinite=false,bool abelOnly=false){
			auto n=node(t),fn=nodes[n.a]; if(fn.op!=BoundOp.lambda||pool.view(type(at(n.a))).fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
			auto sort=elementSort(types[n.type]); if(sort!=Sort.rational&&sort!=Sort.real_&&sort!=Sort.complex) return BoundTerm.init;
			uint index; foreach(id;0..arena.length){ auto v=arena.node(arena.at(cast(uint)id)); if(v.op==Op.variable&&v.value>=index) index=cast(uint)v.value+1; }
			auto variable=arena.variable(Sort.natural,index),body=scalarBody(at(fn.a),variable); if(body==Term.init) return BoundTerm.init;
			// Candidate normalization is untrusted; identities below are still
			// checked against the original summand, including its domain.
			auto search=Options(DensityMode.preserve,false); search.expandScalarEmbeddings=true;
			search.maxRewrites=512; search.maxAlgebraWork=16384;
			SumPrimitive[] tail;
			// Keep elementary ratios opaque during candidate algebra. Scalar
			// rewrites otherwise turn exp(a)^n back into exp(a*n), losing the
			// geometric representation before the identity checker sees it.
			Term geometricCandidate(Term input,out SumPrimitive[] pieces){
				Term[] originals,parameters;
				Term protect(Term x){
					auto v=arena.view(x);
					if(v.op==Op.builtin&&(v.value==Builtin.expR||v.value==Builtin.expC||v.value==Builtin.cisR||v.value==Builtin.expiC||v.value==Builtin.e)){
						bool dependent;foreach(id;arena.viewPostorder(x))if(arena.at(id)==variable){dependent=true;break;}
						if(!dependent){
							foreach(i,t;originals)if(t==x)return parameters[i];
							auto p=arena.variable(arena.sort(x),index+1+cast(uint)originals.length);originals~=x;parameters~=p;return p;
						}
					}
					Term[] args;foreach(i;0..v.arity)args~=protect(arena.viewChild(x,i));return args.length?arena.viewRebuild(x,args,true):x;
				}
				Term restore(Term x){
					foreach(i,p;parameters)if(x==p)return originals[i];
					auto v=arena.view(x);Term[] args;foreach(i;0..v.arity)args~=restore(arena.viewChild(x,i));return args.length?arena.viewRebuild(x,args,true):x;
				}
				auto candidate=sumAntidifference(arena,protect(input),variable,pieces);
				if(candidate==Term.init)return candidate;
				foreach(ref p;pieces){p.coefficient=restore(p.coefficient);p.ratio=restore(p.ratio);}
				return restore(candidate);
			}
			// Use exact polynomial arithmetic for higher-degree finite sums;
			// retain coefficient matching for small sums and infinite tails.
			auto candidate=!infinite&&!abelOnly?polynomialAntidifference(arena,body,variable):Term.init;
			auto exactPolynomial=candidate!=Term.init;
			if(candidate==Term.init&&!abelOnly)candidate=geometricCandidate(body,tail);
			if(candidate==Term.init&&!abelOnly){
				auto normalized=simplify(arena,body,[],search);tail=null;
				if(!normalized.exhausted)candidate=geometricCandidate(arena.castTo(normalized.output,sort),tail);
			}
			bool usedAbel;
			if(candidate==Term.init&&!infinite){ candidate=sumAbelAntidifference(arena,body,variable); usedAbel=true; }
			if(candidate==Term.init)return BoundTerm.init;
			bool symbolicRatio;foreach(p;tail)symbolicRatio|=!arena.isNumber(p.ratio);
			if(!infinite) tail=null;
			auto zero=arena.number(Number(0),sort);
			if(infinite){
				if(pool.view(type(at(n.a))).fields[0]!=scalarType(Sort.natural)||!tail.length) return BoundTerm.init;
				candidate=zero;
				auto power=sort==Sort.rational?Builtin.powQN:sort==Sort.real_?Builtin.powRN:Builtin.powCN;
				foreach_reverse(p;tail){
					if(!arena.isNumber(p.ratio)) return BoundTerm.init;
					auto q=arena.number(p.ratio); if(q.re*q.re+q.im*q.im>=Rational(1)) return BoundTerm.init;
					auto monomial=arena.mul(arena.mul(p.coefficient,arena.call(power,[arena.castTo(variable,sort),arena.natural_(p.degree)]),true),arena.call(power,[p.ratio,variable]),true);
					candidate=arena.add(monomial,candidate,true);
				}
			}
			Term subst(Term t,Term x){ auto v=arena.view(t); if(t==variable) return x; Term[] args; foreach(i;0..v.arity) args~=subst(arena.viewChild(t,i),x); return args.length?arena.viewRebuild(t,args,true):t; }
			auto initial=subst(candidate,arena.natural_(0));
			auto step=arena.add(subst(candidate,arena.add(variable,arena.natural_(1),true)),arena.mul(arena.number(Number(-1),sort),arena.add(candidate,body,true),true),true);
			auto opts=Options(DensityMode.preserve,true); opts.expandPowers=true; opts.expandScalarEmbeddings=true;
			opts.maxRewrites=2048; opts.maxAlgebraWork=32768;
			ScalarDomain[] checks;
			foreach(rawInput;infinite?[step]:[initial,step]){
				auto input=sort==Sort.rational?arena.castTo(rawInput,Sort.real_):rawInput;
				if(exactPolynomial&&polynomialZero(arena,input)){
					auto check=ScalarDomain.init;check.input=input;check.variable=index;check.sort=Sort.natural;check.polynomial=true;
					checks~=check;continue;
				}
				Term[] cases;
				if(!infinite&&symbolicRatio&&rationalIdentityZero(arena,rawInput,cases)){
					auto check=ScalarDomain.init;check.input=rawInput;check.variable=index;check.sort=Sort.natural;check.rational=true;check.rationalConditions=cases;
					checks~=check;continue;
				}
				auto domain=simplifyDomain(arena,input,[],opts),value=simplify(arena,input,[],opts);
				if(domain.exhausted||value.exhausted||domain.output!=arena.boolean(true)||!arena.isNumber(value.output)||!arena.number(value.output).zero)
					return !infinite&&!usedAbel?solveFinite(t,extra,false,true):BoundTerm.init;
				checks~=ScalarDomain(input,domain,value,index,Sort.natural);
			}
			auto g=inheritHint(at(n.a),lambda(restoreBody(candidate,context(at(fn.a)),variable)));
			auto output=infinite?scalar(context(t),arena.mul(arena.number(Number(-1),sort),initial,true)):apply(g,at(n.b));
			// Preserve application for endpoints whose totality requires a proof.
			// Ordinary beta/scalar rules then justify substitution and normalization.
			if(!infinite&&totalScalar(at(n.b)))output=scalar(context(t),subst(candidate,arena.at(nodes[n.b].data)));
			auto start=cast(uint)scalarDomains.length;
			uint[] totals,convergence;
			if(infinite) foreach(p;tail) foreach(input;[p.coefficient,p.ratio]){
				auto domain=simplifyDomain(arena,input,[],opts);
				if(domain.exhausted||domain.output!=arena.boolean(true)) return BoundTerm.init;
				totals~=start+cast(uint)checks.length; checks~=ScalarDomain(input,domain);
			}
			if(infinite) foreach(p;tail){
				auto norm=sort==Sort.complex?arena.call(Builtin.absC,[p.ratio]):arena.abs(arena.castTo(p.ratio,Sort.real_));
				auto pred=arena.lt(norm,arena.real_(1)),domain=simplifyDomain(arena,pred,[],opts),value=simplify(arena,pred,[],opts);
				if(domain.exhausted||value.exhausted||domain.output!=arena.boolean(true)||value.output!=arena.boolean(true)) return BoundTerm.init;
				convergence~=start+cast(uint)checks.length; checks~=ScalarDomain(pred,domain,value);
			}
			scalarDomains~=checks;
			extra=cast(uint)sums.length; sums~=SummationSolution(t.id,output.id,g.id,index,infinite?uint.max:start,infinite?start:start+1,tail,totals,convergence); return output;
		}
		BoundTerm pointwise(BoundTerm binder,out uint extra){
			auto body=at(node(binder).a),ctx=context(body),param=type(variable(ctx,0)); Sort sort; bool scalarParam;
			foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean])
				if(param==scalarType(s)){ sort=s; scalarParam=true; break; }
			if(!scalarParam) return BoundTerm.init;
			auto index=freshScalarIndex(body.id);
			auto argument=arena.variable(sort,index);
			BoundTerm rewrite(BoundTerm t,uint[] path,bool masksOnly){
				auto n=node(t),mode=n.op==BoundOp.defined||n.op==BoundOp.holds?n.op:BoundOp.scalar;
				if(masksOnly&&primitiveOp(t.id,Op.mask)&&binderNonzero(n.a).length&&depends(at(n.b),0)){
					auto z=arena.number(Number(0),sort),input=scalarBody(at(n.b),z);
					if(input!=Term.init){
						auto opts=Options(DensityMode.preserve,true),value=simplify(arena,input,opts);
						if(!value.exhausted&&arena.isNumber(value.output)&&arena.number(value.output).zero){
							auto domain=simplifyDomain(arena,input,[],opts);
							if(!domain.exhausted&&domain.output==arena.boolean(true)){
								extra=cast(uint)scalarDomains.length;
								scalarDomains~=ScalarDomain(input,domain,value,index,sort,path,BoundOp.primitive);
								return at(n.b);
							}
						}
					}
				}
				auto source=masksOnly?Term.init:scalarBody(mode==BoundOp.scalar?t:at(n.a),argument);
				if(source!=Term.init){
					ScalarResult value; BoundTerm simplified;
					if(mode==BoundOp.scalar){
						if(arena.isNumber(source)) return BoundTerm.init;
						value=simplify(arena,source,Options(DensityMode.preserve,true)); exhausted|=value.exhausted;
						if(arena.castTo(value.output,arena.sort(source))==source) return BoundTerm.init;
						simplified=restoreBody(arena.castTo(value.output,arena.sort(source)),ctx,argument);
						// Re-embedding may change only where closed scalar subtrees
						// are split into binder primitives. Do not cycle on that split.
						if(simplified==t||scalarBody(simplified,argument)==source) return BoundTerm.init;
					}
					auto d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true)); exhausted|=d.exhausted;
					extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d,value,index,sort,path,mode);
					if(mode==BoundOp.defined) return restoreBody(d.output,ctx,argument);
					if(mode==BoundOp.holds) return restoreBody(arena.and_(d.output,source),ctx,argument);
					return d.output==arena.boolean(true)?simplified:guard(restoreBody(d.output,ctx,argument),simplified);
				}
				if(n.op==BoundOp.conditional||n.op==BoundOp.guard||n.op==BoundOp.primitive||n.op==BoundOp.defined||n.op==BoundOp.holds||n.op==BoundOp.vectorCons||n.op==BoundOp.pair||n.op==BoundOp.get||n.op==BoundOp.first||n.op==BoundOp.rest||n.op==BoundOp.tensor){
					BoundTerm[] children=[at(n.a)]; if(n.b!=uint.max) children~=at(n.b); if(n.c!=uint.max) children~=at(n.c);
					foreach(i,child;children){
						auto changed=rewrite(child,path~cast(uint)i,masksOnly);
						if(changed!=BoundTerm.init){ children[i]=changed; return rebuild(t,ctx,children); }
					}
				}
				return BoundTerm.init;
			}
			auto output=rewrite(body,[],false);
			if(output==BoundTerm.init&&sort!=Sort.boolean) output=rewrite(body,[],true);
			return output==BoundTerm.init?output:inheritHint(binder,node(binder).op==BoundOp.lambda?lambda(output):set(output));
		}
		BoundTerm rayCoordinate(BoundTerm fn,out uint orientation,out BindingRule rule){
			auto f=node(fn);
			if(f.op!=BoundOp.lambda||!primitiveOp(f.a,Op.mask)) return BoundTerm.init;
			auto mask=nodes[f.a],test=nodes[mask.a];
			if(test.op!=BoundOp.primitive) return BoundTerm.init;
			auto cmp=arena.view(arena.at(test.data)).op;
			if(cmp!=Op.lt&&cmp!=Op.le) return BoundTerm.init;
			auto x=at(mask.b);
			uint degree=1;
			if(primitiveOp(mask.b,Op.pow)){
				auto power=arena.view(arena.at(node(x).data));
				if(power.value<2) return BoundTerm.init;
				degree=cast(uint)power.value;
				x=at(node(x).a);
			}
			if(node(x).op!=BoundOp.variable||node(x).data!=0) return BoundTerm.init;
			bool left=test.a==x.id;
			auto endpoint=nodes[left?test.b:test.a],zero=arena.real_(0);
			if((left?test.a:test.b)!=x.id||endpoint.op!=BoundOp.scalar||arena.at(endpoint.data)!=zero) return BoundTerm.init;
			orientation=cast(uint)left+2*cast(uint)(cmp==Op.le);
			auto guard=at(mask.a),jac=scalar(context(x),arena.real_(degree));
			if(degree>1){
				auto absX=primitive(arena.abs(zero),[x]);
				auto magnitude=primitive(arena.pow(zero,degree-1),[absX]);
				jac=primitive(scalarOperator(type(x),TensorOp.mul),[jac,magnitude]);
			}else{
				guard=primitive(arena.lt(zero,zero),[at(test.a),at(test.b)]);
			}
			auto weight=inheritHint(fn,lambda(primitive(arena.mask(arena.boolean(true),zero),[guard,jac])));
			auto ctx=context(fn),regular=distribution(ctx,BoundOp.distributionWeight,[weight,distribution(ctx,BoundOp.distributionLebesgue)]);
			if(degree>1){ rule=BindingRule.distributionCoordinateRayPower; return regular; }
			auto isZero=primitive(arena.not_(arena.boolean(true)),[primitive(arena.nonzero(zero),[x])]);
			auto square=primitive(arena.pow(zero,2),[x]);
			auto corner=distribution(ctx,BoundOp.distributionPushforwardOn,[lambda(isZero),lambda(square)]);
			rule=BindingRule.distributionCoordinateRayLinear;
			return distribution(ctx,BoundOp.distributionAdd,[corner,regular]);
		}
		BoundTerm smoothCoordinate(BoundTerm fn,BoundTerm pred=BoundTerm.init){
			auto body=at(node(fn).a),inner=context(body),ctx=context(fn);
			string unused; auto derivative=smoothSlope(body,unused);
			if(derivative==BoundTerm.init) return BoundTerm.init;
			auto zero=arena.real_(0),w=primitive(arena.abs(zero),[derivative]);
			if(pred!=BoundTerm.init){
				uint[] shift; foreach(i;0..contexts[ctx.index].length) shift~=i+1;
				auto guard=apply(rename(pred,inner,shift),body);
				w=primitive(arena.mask(arena.boolean(true),zero),[guard,w]);
			}
			return distribution(ctx,BoundOp.distributionWeight,
				[inheritHint(fn,lambda(w)),distribution(ctx,BoundOp.distributionLebesgue)]);
		}
		BoundTerm gridAtom(Scope ctx,Rational a,Rational height){
			auto d=distribution(ctx,BoundOp.distributionDirac,[scalar(ctx,arena.real_(a))]);
			return height==Rational(1)?d:distribution(ctx,BoundOp.distributionScale,[scalar(ctx,arena.real_(height)),d]);
		}
		// The symbolic domain proposes probes. Only a closed scalar domain proof
		// can establish that a particular point of the traversal is missing.
		bool missingTraversal(uint test,Rational lo,Rational hi,ref CoordinateJoin join){
			auto testNode=nodes[test];
			bool guarded=testNode.op==BoundOp.guard;
			auto id=guarded?testNode.a:test;
			auto axis=arena.variable(Sort.real_,freshScalarIndex(id)),body=scalarBody(at(id),axis);
			if(body==Term.init) return false;
			auto opts=Options(DensityMode.preserve,true);
			opts.maxRewrites=512; opts.maxAlgebraWork=16384;
			auto domain=guarded?simplify(arena,body,[],opts):simplifyDomain(arena,body,[],opts);
			if(domain.output==arena.boolean(true)) return false;
			Rational[] probes=[lo,hi],cuts;
			auto left=lo;
			if(!domain.exhausted&&integralCutPoints(arena,domain.output,axis,cuts)&&cuts.length<=64){
				import std.algorithm.sorting:sort;
				sort(cuts);
				foreach(c;cuts) if(left<c&&c<hi){
					probes~=c; probes~=(left+c)/Rational(2); left=c;
				}
			}
			probes~=(left+hi)/Rational(2);
			foreach(u;probes){
				if(u.words>128) continue;
				auto sample=scalarBody(at(id),arena.real_(u));
				auto check=guarded?simplify(arena,sample,[],opts):simplifyDomain(arena,sample,[],opts);
				if(check.exhausted||check.output!=arena.boolean(false)) continue;
				auto evidence=ScalarDomain(sample,check);
				if(guarded){
					evidence.value=check;
					evidence.result=simplifyDomain(arena,sample,[],opts);
					if(evidence.result.exhausted) continue;
				}
				join.witness=u; join.missingGuard=guarded;
				join.missingDomain=cast(uint)scalarDomains.length;
				scalarDomains~=evidence;
				return true;
			}
			return false;
		}
		BoundTerm partialJumpAtom(Scope ctx,Rational a,Rational l,Rational r,BoundTerm mass){
			auto atom=distribution(ctx,BoundOp.distributionDirac,[scalar(ctx,arena.real_(a))]);
			auto scaled=distribution(ctx,BoundOp.distributionScale,[mass,atom]);
			if((l<r?r-l:l-r)<Rational(1)) return scaled;
			auto zero=arena.real_(0);
			auto gap=primitive(arena.add(zero,zero,true),[mass,scalar(ctx,arena.real_(-1))]);
			auto unit=primitive(arena.not_(arena.boolean(true)),[primitive(arena.nonzero(zero),[gap])]);
			return conditional(unit,atom,scaled);
		}
		BoundTerm sqrtJumpAtom(Scope ctx,Rational a,Rational l,Rational r){
			auto lo=l<r?l:r,hi=l<r?r:l;
			auto delta=hi-lo-Rational(1);
			auto atom=distribution(ctx,BoundOp.distributionDirac,[scalar(ctx,arena.real_(a))]);
			if(delta>=Rational(0)&&delta*delta==Rational(4)*lo) return atom;
			auto zero=arena.real_(0),root=arena.call(Builtin.sqrtR,[zero]);
			BoundTerm image(Rational v){return primitive(root,[scalar(ctx,arena.real_(v))]);}
			auto negative=primitive(arena.mul(zero,zero,true),[scalar(ctx,arena.real_(-1)),image(lo)]);
			auto gap=primitive(arena.add(zero,zero,true),[image(hi),negative]);
			return distribution(ctx,BoundOp.distributionScale,[gap,atom]);
		}
		BoundTerm polynomialCoordinate(BoundTerm fn,out uint index,BoundTerm pred=BoundTerm.init,
			CoordinateGridMode mode=CoordinateGridMode.source){
			bool changed=mode!=CoordinateGridMode.source,requireJump=mode==CoordinateGridMode.jumpChange;
			auto body=at(node(fn).a),inner=context(body),ctx=context(fn),x=variable(inner,0);
			CoordinateGrid cert;
			auto outerBody=body;
			if(changed){
				cert.change=gridChange(body.id);
				if(cert.change==CoordinateChange.none) return BoundTerm.init;
				body=at(node(body).a);
			}
			Rational[] global;
			if(axisPolynomial(body.id,global)) cert.grid.cells~=global;
			else if(!polynomialGrid([body.id],cert.grid,false,requireJump)) return BoundTerm.init;
			auto cuts=cert.grid.cuts;
			if(changed&&!cuts.length) return BoundTerm.init;
			// A global polynomial needs no cuts or region certificates.
			Rational[][] slopes;
			foreach(p;cert.grid.cells) slopes~=derivativeCoefficients(p);
			foreach(i,a;cuts){
				auto l=polynomialAt(cert.grid.cells[i],a),r=polynomialAt(cert.grid.cells[i+1],a);
				auto dl=polynomialAt(slopes[i],a),dr=polynomialAt(slopes[i+1],a),v=cert.grid.points[i];
				if((v!=l&&v!=r)||l.words>128||r.words>128||dl.words>128||dr.words>128) return BoundTerm.init;
				auto j=CoordinateJoin(l!=r?JoinKind.jump:dl!=dr?JoinKind.corner:JoinKind.smooth,l,r,dl);
				if(requireJump&&j.kind!=JoinKind.smooth&&(!admitsTrace(cert.change,l)||!admitsTrace(cert.change,r))) return BoundTerm.init;
				if(changed&&j.kind==JoinKind.jump){
					if(!requireJump) return BoundTerm.init;
					if(!rationalImage(cert.change,l,j.leftImage)||!rationalImage(cert.change,r,j.rightImage)){
						if(cert.change!=CoordinateChange.sqrt||pred!=BoundTerm.init) return BoundTerm.init;
						j.symbolicRoot=true;
					}
					cert.image=true;
				}
				cert.joins~=j;
			}
			if(requireJump&&!cert.image) return BoundTerm.init;
			cert.traceRange=cert.image;
			auto zero=arena.real_(0),mul=arena.mul(zero,zero,true),add=arena.add(zero,zero,true);
			auto lt=arena.lt(zero,zero),le=arena.le(zero,zero),mask=arena.mask(arena.boolean(true),zero);
			BoundTerm originalPred;
			if(changed){
				string proof; if(!gridChangeRange(cert.change,body.id,proof,null,requireJump)) return BoundTerm.init;
				if(pred!=BoundTerm.init){
					cert.outerPredicate=node(pred).a;
					uint[] shift; foreach(i;0..contexts[ctx.index].length) shift~=i+1;
					originalPred=rename(pred,inner,shift);
					pred=lambda(apply(originalPred,primitive(arena.at(node(outerBody).data),[x])));
				}
			}
			if(pred!=BoundTerm.init){
				// Restrict a jump in its traversed coordinate. Only commit the
				// rewrite when every exceptional contribution has a certificate.
				cert.predicate=node(pred).a;
				foreach(ref j;cert.joins){
					if(j.kind==JoinKind.corner){
						// A source restriction is tested after the outer change.
						auto test=cert.image?cert.outerPredicate:cert.predicate;
						auto value=j.left;
						if(cert.image&&!rationalImage(cert.change,j.left,j.leftImage)) continue;
						if(cert.image) value=j.leftImage;
						Term v;
						if(gridNumerical(test)&&gridValue(test,value,v)&&arena.view(v).op==Op.boolLit)
							j.selection=v==arena.boolean(true)?CornerSelection.active:CornerSelection.inactive;
					}
					if(j.kind!=JoinKind.jump) continue;
					auto l=cert.image?j.leftImage:j.left,r=cert.image?j.rightImage:j.right;
					auto lo=l<r?l:r,hi=l<r?r:l;
					auto between=primitive(arena.and_(arena.boolean(true),arena.boolean(true)),[
						primitive(le,[scalar(inner,arena.real_(lo)),x]),primitive(le,[x,scalar(inner,arena.real_(hi))])]);
					auto selected=primitive(mask,[at(cert.image?cert.outerPredicate:cert.predicate),scalar(inner,arena.real_(1))]);
					auto w=primitive(mask,[between,selected]);
					auto d=distribution(ctx,BoundOp.distributionWeight,[lambda(w),distribution(ctx,BoundOp.distributionLebesgue)]);
					auto mass=distribution(ctx,BoundOp.distributionMass,[d]);
					j.clipped=new IntegralSolution;
					if(integratePolynomials(mass,*j.clipped)==BoundTerm.init){
						j.clipped=null;
						if(!missingTraversal(cert.image?cert.outerPredicate:cert.predicate,lo,hi,j)) j.traversal=mass.id;
					}
				}
			}
			BoundTerm weight;
			foreach(i,p;slopes){
				if(!p.length) continue;
				auto derivative=coordinatePolynomial(inner,p);
				auto magnitude=primitive(arena.abs(zero),[derivative]);
				BoundTerm guard;
				if(i) guard=primitive(cert.joins[i-1].kind==JoinKind.smooth?le:lt,[scalar(inner,arena.real_(cuts[i-1])),x]);
				if(i<cuts.length){
					auto upper=primitive(lt,[x,scalar(inner,arena.real_(cuts[i]))]);
					guard=guard==BoundTerm.init?upper:primitive(arena.and_(arena.boolean(true),arena.boolean(true)),[guard,upper]);
				}
				if(guard!=BoundTerm.init) magnitude=primitive(mask,[guard,magnitude]);
				weight=weight==BoundTerm.init?magnitude:primitive(add,[weight,magnitude]);
			}
			if(weight==BoundTerm.init) weight=scalar(inner,zero);
			cert.weight=weight.id;
			if(changed) weight=primitive(mul,[gridChangeJacobian(cert.change,body),weight]);
			BoundTerm localPred;
			if(pred!=BoundTerm.init){
				uint[] shift; foreach(i;0..contexts[ctx.index].length) shift~=i+1;
				localPred=rename(pred,inner,shift);
				auto guard=changed?apply(originalPred,outerBody):apply(localPred,body);
				weight=primitive(mask,[guard,weight]);
			}
			auto result=distribution(ctx,BoundOp.distributionWeight,[inheritHint(fn,lambda(weight)),distribution(ctx,BoundOp.distributionLebesgue)]);
			foreach_reverse(i,a;cuts){
				auto join=cert.joins[i];
				if(join.kind==JoinKind.smooth) continue;
				BoundTerm event;
				if(join.kind==JoinKind.corner){
					auto isZero=primitive(arena.not_(arena.boolean(true)),[primitive(arena.nonzero(zero),[x])]);
					auto square=primitive(arena.pow(zero,2),[x]);
					auto map=primitive(add,[square,scalar(inner,arena.real_(a))]);
					event=distribution(ctx,BoundOp.distributionPushforwardOn,[lambda(isZero),lambda(map)]);
				}else{
					auto k=join.right-join.left; if(k<Rational(0)) k=-k;
					event=gridAtom(ctx,a,k);
				}
				cert.joins[i].event=event.id;
				if(join.symbolicRoot){
					event=sqrtJumpAtom(ctx,a,join.left,join.right);
				}else if(cert.image&&join.kind==JoinKind.jump&&pred==BoundTerm.init){
					auto k=join.rightImage-join.leftImage;
					event=gridAtom(ctx,a,k<Rational(0)?-k:k);
				}
				if(pred!=BoundTerm.init){
					if(join.missingDomain!=uint.max) event=bottom(ctx,type(event));
					else if(join.traversal!=uint.max){
						event=partialJumpAtom(ctx,a,cert.image?join.leftImage:join.left,cert.image?join.rightImage:join.right,at(join.traversal));
					}else if(join.kind==JoinKind.jump) event=gridAtom(ctx,a,join.clipped.value);
					else final switch(join.selection){
						case CornerSelection.active:break;
						case CornerSelection.inactive:
							event=distribution(ctx,BoundOp.distributionWeight,
								[lambda(scalar(inner,zero)),distribution(ctx,BoundOp.distributionLebesgue)]);
							break;
						case CornerSelection.dynamic:
							auto graph=node(event),test=at(nodes[graph.a].a);
							auto active=apply(localPred,scalar(inner,arena.real_(join.left)));
							auto guard=primitive(arena.and_(arena.boolean(true),arena.boolean(true)),[test,active]);
							event=distribution(ctx,BoundOp.distributionPushforwardOn,[lambda(guard),at(graph.b)]);
							break;
					}
				}
				result=distribution(ctx,BoundOp.distributionAdd,[event,result]);
			}
			cert.body=body.id;index=cast(uint)coordinates.length;coordinates~=cert;
			return result;
		}
		BoundTerm singletonCoordinate(BoundTerm fn,out uint index,out BindingRule rule,BoundTerm pred=BoundTerm.init){
			rule=BindingRule.distributionCoordinateGrid;
			auto result=polynomialCoordinate(fn,index,pred);
			if(result!=BoundTerm.init) return result;
			result=smoothCoordinate(fn,pred);
			if(result!=BoundTerm.init){rule=BindingRule.distributionSmoothCoordinate; return result;}
			return polynomialCoordinate(fn,index,pred,CoordinateGridMode.continuousChange);
		}
		BoundTerm jumpCoordinate(BoundTerm fn,JumpRays rays){
			auto x=at(rays.x),ctx=context(fn),inner=context(x),zero=arena.real_(0);
			auto mask=arena.mask(arena.boolean(true),zero);
			auto slope=primitive(scalarOperator(type(x),TensorOp.mul),[scalar(inner,arena.real_(-2)),x]);
			auto left=primitive(mask,[at(rays.leftTest),slope]);
			auto right=primitive(mask,[at(rays.rightTest),scalar(inner,arena.real_(1))]);
			auto weight=inheritHint(fn,lambda(primitive(scalarOperator(type(x),TensorOp.add),[left,right])));
			auto regular=distribution(ctx,BoundOp.distributionWeight,[weight,distribution(ctx,BoundOp.distributionLebesgue)]);
			auto a=scalar(ctx,rays.a),b=scalar(ctx,rays.b);
			auto leftAtom=distribution(ctx,BoundOp.distributionDirac,[a]),rightAtom=distribution(ctx,BoundOp.distributionDirac,[b]);
			if(arena.number(rays.a).re!=Rational(-1))
				leftAtom=distribution(ctx,BoundOp.distributionScale,[primitive(arena.pow(zero,2),[a]),leftAtom]);
			if(arena.number(rays.b).re!=Rational(1))
				rightAtom=distribution(ctx,BoundOp.distributionScale,[b,rightAtom]);
			return distribution(ctx,BoundOp.distributionAdd,[leftAtom,distribution(ctx,BoundOp.distributionAdd,[rightAtom,regular])]);
		}
		bool squareMap(uint id,out bool product){
			if(nodes[id].op!=BoundOp.lambda) return false;
			auto body=nodes[nodes[id].a];
			if(body.op!=BoundOp.primitive||body.a==uint.max||nodes[body.a].op!=BoundOp.variable||nodes[body.a].data!=0) return false;
			auto op=arena.view(arena.at(body.data));
			product=op.op==Op.mul&&body.a==body.b;
			return product||op.op==Op.pow&&op.value==2;
		}
		BoundTerm oddRoot(uint degree,BoundTerm y){
			auto zero=arena.real_(0),ctx=context(y);
			if(degree==3) return primitive(arena.call(Builtin.cbrtR,[zero]),[y]);
			auto sign=primitive(arena.call(Builtin.signR,[zero]),[y]);
			foreach(c;[Builtin.castZQ,Builtin.castQR])
				sign=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[sign]);
			auto exponent=primitive(arena.inv(arena.real_(1)),[scalar(ctx,arena.real_(degree))]);
			auto magnitude=primitive(arena.call(Builtin.powerR,[zero,zero]),[primitive(arena.abs(zero),[y]),exponent]);
			return primitive(scalarOperator(type(y),TensorOp.mul),[sign,magnitude]);
		}
		BoundTerm openUnit(BoundTerm x){
			auto ctx=context(x),zero=scalar(ctx,arena.real_(0)),one=scalar(ctx,arena.real_(1));
			auto lt=arena.lt(arena.real_(0),arena.real_(0));
			return primitive(arena.and_(arena.boolean(true),arena.boolean(true)),
				[primitive(lt,[zero,x]),primitive(lt,[x,one])]);
		}
		BoundTerm openUnitDensity(BoundTerm y){
			auto ctx=context(y),root=primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[y]);
			auto twice=primitive(scalarOperator(type(y),TensorOp.mul),[scalar(ctx,arena.real_(2)),root]);
			return primitive(arena.mask(arena.boolean(false),arena.real_(0)),
				[openUnit(y),primitive(arena.inv(arena.real_(1)),[twice])]);
		}
		bool openUnitPredicate(uint id){
			if(nodes[id].op!=BoundOp.lambda) return false;
			auto body=at(nodes[id].a);
			return body==openUnit(variable(context(body),0));
		}
		Table!(uint,uint) mapDomains;
		uint totalMapDomain(uint body){
			auto known=mapDomains.get(body,uint.max);
			if(known!=uint.max) return known;
			ScalarDomain check;
			if(!totalRowDomain(body,check)) return uint.max;
			auto id=cast(uint)scalarDomains.length;
			scalarDomains~=check;
			mapDomains.set(body,id);
			return id;
		}
		// Match the same affine grammar as the certificate builder. A product
		// needs a syntactically constant side so its numeric proof is closed.
		bool affineMap(uint id,out Rational a,out Rational b){
			if(nodes[id].op!=BoundOp.lambda||type(at(id))!=pool.function_(scalarType(Sort.real_),scalarType(Sort.real_))) return false;
			auto body=at(nodes[id].a);
			bool shape(uint i){
				auto n=nodes[i];
				if(!depends(at(i),0)) return true;
				if(n.op==BoundOp.variable) return n.data==0;
				if(n.op!=BoundOp.primitive) return false;
				auto op=arena.view(arena.at(n.data)).op;
				return (op==Op.add||op==Op.mul&&(!depends(at(n.a),0)||!depends(at(n.b),0)))&&shape(n.a)&&shape(n.b);
			}
			if(!shape(body.id)) return false;
			auto arg=arena.variable(Sort.real_,freshScalarIndex(body.id)),raw=scalarBody(body,arg);
			return raw!=Term.init&&integralAffine(arena,raw,arg,a,b)&&!a.zero;
		}
		// Build the inverse in the source binder's context. It can then be
		// applied to any (possibly partial) target without capturing variables.
		AffineChart affineChart(uint map,Rational slope,Rational offset,bool needInverse,uint predicateDomain=uint.max){
			auto inner=context(at(nodes[map].a)),reciprocal=Rational(1)/slope;
			auto literal=(Rational r)=>scalar(inner,arena.real_(r));
			auto jac=literal(reciprocal<Rational(0)?-reciprocal:reciprocal);
			uint inverse=uint.max;
			if(needInverse){
				auto product=primitive(arena.mul(arena.real_(0),arena.real_(0),true),[literal(reciprocal),variable(inner,0)]);
				inverse=primitive(arena.add(arena.real_(0),arena.real_(0),true),[product,literal(-offset*reciprocal)]).id;
			}
			return AffineChart(nodes[map].a,inverse,jac.id,predicateDomain);
		}
		struct PowerMap{ uint degree; BoundTerm affine; Rational slope,offset; bool product; }
		PowerMap powerMap(uint id,bool square){
			if(nodes[id].op!=BoundOp.lambda) return PowerMap.init;
			auto body=nodes[nodes[id].a];
			if(body.op!=BoundOp.primitive||body.a==uint.max) return PowerMap.init;
			auto power=arena.view(arena.at(body.data));
			bool product=power.op==Op.mul&&body.a==body.b;
			if(square){
				if(!product&&(power.op!=Op.pow||power.value!=2)) return PowerMap.init;
			}else if(power.op!=Op.pow||power.value<3||power.value%2!=1) return PowerMap.init;
			auto degree=square?2:cast(uint)power.value,base=nodes[body.a];
			if(!square&&base.op==BoundOp.variable&&base.data==0) return PowerMap(degree);
			auto inner=lambda(at(body.a)); Rational slope,offset;
			if(!affineMap(inner.id,slope,offset)) return PowerMap.init;
			return PowerMap(degree,inner,slope,offset,product);
		}
		// Scalar simplification can expand a square before the graph rule sees
		// it. Propose its affine root and export the polynomial difference.
		PowerMap factoredSquare(uint map,out ScalarDomain check){
			if(nodes[map].op!=BoundOp.lambda) return PowerMap.init;
			auto node_=nodes[nodes[map].a];
			if(node_.op!=BoundOp.primitive) return PowerMap.init;
			auto operation=arena.view(arena.at(node_.data));
			if(operation.op!=Op.add&&operation.op!=Op.mul&&!(operation.op==Op.pow&&operation.value==2)) return PowerMap.init;
			auto body=at(nodes[map].a),index=freshScalarIndex(body.id),x=arena.variable(Sort.real_,index);
			auto raw=scalarBody(body,x); Rational a,b;
			if(raw==Term.init||!rationalAffineSquare(arena,raw,x,a,b)) return PowerMap.init;
			auto base=arena.mul(arena.real_(a),x,true);
			if(!b.zero) base=arena.add(base,arena.real_(b),true);
			auto diff=arena.add(raw,arena.mul(arena.real_(-1),arena.pow(base,2),true),true);
			if(!polynomialZero(arena,diff)) return PowerMap.init;
			check.input=diff; check.variable=index; check.sort=Sort.real_; check.polynomial=true;
			return PowerMap(2,lambda(restoreBody(base,context(body),x)),a,b,false);
		}
		bool squareBand(uint predicate,out uint lo,out uint hi,out bool strict){
			auto n=nodes[predicate];
			bool op(BoundNode q,Op which){ return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==which; }
			if(!op(n,Op.and_)) return false;
			auto l=nodes[n.a],r=nodes[n.b];
			strict=op(l,Op.lt);
			if((!strict&&!op(l,Op.le))||!op(r,strict?Op.lt:Op.le)||l.b!=r.a||nodes[l.b].op!=BoundOp.variable||nodes[l.b].data!=0) return false;
			lo=l.a; hi=r.b;
			return nodes[lo].op==BoundOp.scalar&&nodes[hi].op==BoundOp.scalar&&
				arena.isNumber(arena.at(nodes[lo].data))&&arena.isNumber(arena.at(nodes[hi].data));
		}
		PowerMap oddMap(uint id){ return powerMap(id,false); }
		bool isTrue(uint id,bool value){
			auto n=nodes[id]; if(n.op!=BoundOp.scalar) return false;
			auto v=arena.view(arena.at(n.data)); return v.op==Op.boolLit&&v.value==value;
		}
		BoundTerm squareFromCover(BoundTerm cover,out CoverStep step){
			auto first=nodes[node(cover).a];
			if(first.op!=BoundOp.vectorCons) return BoundTerm.init;
			auto second=nodes[first.b];
			if(second.op!=BoundOp.vectorCons||nodes[second.b].op!=BoundOp.vectorNil) return BoundTerm.init;
			auto lower=nodes[first.a],upper=nodes[second.a];
			if(lower.op!=BoundOp.lambda||upper.op!=BoundOp.lambda) return BoundTerm.init;
			auto minus=nodes[lower.a],plus=nodes[upper.a];
			bool op(BoundNode n,Op o){ return n.op==BoundOp.primitive&&arena.view(arena.at(n.data)).op==o; }
			auto radiusBody=at(upper.a),centre=arena.real_(0);
			if(op(plus,Op.add)){
				if(!op(minus,Op.add)) return BoundTerm.init;
				step.upperSwap=nodes[plus.a].op!=BoundOp.scalar;
				auto c=step.upperSwap?plus.b:plus.a;
				if(nodes[c].op!=BoundOp.scalar||!arena.isNumber(arena.at(nodes[c].data))) return BoundTerm.init;
				step.lowerSwap=minus.a!=c;
				if(step.lowerSwap&&minus.b!=c) return BoundTerm.init;
				step.centred=true; centre=arena.at(nodes[c].data);
				radiusBody=at(step.upperSwap?plus.a:plus.b); minus=nodes[step.lowerSwap?minus.a:minus.b];
			}
			if(!op(minus,Op.mul)) return BoundTerm.init;
			step.factorSwap=nodes[minus.a].op!=BoundOp.scalar;
			step.coefficient=step.factorSwap?minus.b:minus.a;
			if(nodes[step.coefficient].op!=BoundOp.scalar) return BoundTerm.init;
			auto operand=step.factorSwap?minus.a:minus.b;
			auto radius=hint(lambda(radiusBody),binderHint(at(second.a)).name);
			string form; auto j=sqrtRadiusScale(radius.id,form);
			if(j==Term.init) return BoundTerm.init;
			auto coefficient=arena.at(nodes[step.coefficient].data);
			step.nested=operand==radiusBody.id&&coefficient==arena.real_(-1);
			if(!step.nested){
				auto root=nodes[operand];
				if(root.op!=BoundOp.primitive||arena.view(arena.at(root.data)).op!=Op.builtin||
					arena.view(arena.at(root.data)).value!=Builtin.sqrtR||nodes[root.a].op!=BoundOp.variable||nodes[root.a].data!=0) return BoundTerm.init;
				if(coefficient!=arena.real_(-arena.number(j).re)&&coefficient!=arena.mul(arena.real_(-1),j)) return BoundTerm.init;
			}
			auto ctx=context(cover);
			return distribution(ctx,BoundOp.distributionRadiusImage,[scalar(ctx,centre),radius]);
		}
		bool unitSquarePart(BoundTerm part,out uint lowerBody,out uint upperBody){
			auto first=nodes[node(part).b];
			if(first.op!=BoundOp.vectorCons) return false;
			auto second=nodes[first.b];
			if(second.op!=BoundOp.vectorCons||nodes[second.b].op!=BoundOp.vectorNil) return false;
			auto lower=nodes[first.a],upper=nodes[second.a]; string form;
			if(lower.op!=BoundOp.lambda||sqrtRadiusScale(second.a,form)==Term.init||form!="one") return false;
			auto minus=nodes[lower.a];
			if(minus.op!=BoundOp.primitive||arena.view(arena.at(minus.data)).op!=Op.mul||
				minus.b!=upper.a||nodes[minus.a].op!=BoundOp.scalar||arena.at(nodes[minus.a].data)!=arena.real_(-1))
				return false;
			lowerBody=lower.a; upperBody=upper.a; return true;
		}
		// The two open sqrt sheets have distinct source signs. Retain the
		// joint probe at their common endpoint as a strict zero contribution.
		BoundTerm squarePartPairing(BoundTerm part,BoundTerm test){
			uint lower,upper;
			if(!unitSquarePart(part,lower,upper)) return BoundTerm.init;
			auto pred=at(node(part).a),ctx=context(part),inner=context(at(upper)),y=variable(inner,0);
			auto zero=arena.real_(0),one=arena.real_(1),mul=scalarOperator(type(y),TensorOp.mul);
			uint[] shift; foreach(i;0..contexts[ctx.index].length) shift~=i+1;
			auto localPred=rename(pred,inner,shift);
			if(test==BoundTerm.init){
				auto mask=primitive(arena.mask(arena.boolean(true),one),[apply(localPred,y),scalar(inner,one)]);
				auto source=distribution(ctx,BoundOp.distributionWeight,[hint(lambda(mask),binderHint(pred).name),distribution(ctx,BoundOp.distributionLebesgue)]);
				return sequence(pred,distribution(ctx,BoundOp.distributionMass,[source]));
			}
			auto localTest=rename(test,inner,shift);
			BoundTerm probe(BoundTerm p,BoundTerm t,BoundTerm x,BoundTerm target){
				auto mask=primitive(arena.mask(arena.boolean(true),one),[apply(p,x),scalar(context(x),one)]);
				return primitive(mul,[mask,apply(t,target)]);
			}
			auto den=primitive(mul,[scalar(inner,arena.real_(2)),at(upper)]);
			auto jac=primitive(arena.inv(one),[den]);
			auto positive=primitive(arena.lt(zero,zero),[scalar(inner,zero),y]);
			BoundTerm branch(uint root){
				auto weighted=primitive(mul,[probe(localPred,localTest,at(root),y),jac]);
				auto row=hint(lambda(primitive(arena.mask(arena.boolean(true),one),[positive,weighted])),binderHint(lambda(at(upper))).name);
				return distribution(ctx,BoundOp.distributionMass,[distribution(ctx,BoundOp.distributionWeight,
					[row,distribution(ctx,BoundOp.distributionLebesgue)])]);
			}
			auto z=scalar(ctx,zero),endpoint=sequence(probe(pred,test,z,z),z);
			auto plus=arena.add(zero,zero,true);
			return primitive(plus,[branch(lower),primitive(plus,[branch(upper),endpoint])]);
		}
		BoundTerm inverseSquareChart(BoundTerm graph,out uint evidence){
			auto n=node(graph);
			if(n.op!=BoundOp.distributionPushforwardOn||nodes[n.a].op!=BoundOp.lambda) return BoundTerm.init;
			auto body=nodes[n.a].a;
			uint lo,hi;
			bool strict; bool band=squareBand(body,lo,hi,strict);
			if(!band&&!isTrue(body,true)) return BoundTerm.init;
			ScalarDomain polynomial;
			auto map=powerMap(n.b,true);
			if(!map.degree) map=factoredSquare(n.b,polynomial);
			if(!map.degree) return BoundTerm.init;
			auto centre=-map.offset/map.slope; Rational cap;
			if(band){
				auto l=arena.number(arena.at(nodes[lo].data)).re,h=arena.number(arena.at(nodes[hi].data)).re;
				if(l>h||strict&&l==h||l+h!=Rational(2)*centre) return BoundTerm.init;
				auto edge=map.slope*h+map.offset; cap=edge*edge;
			}
			auto chart=affineChart(map.affine.id,map.slope,map.offset,false);
			auto ctx=context(graph),inner=context(at(chart.map)),y=variable(inner,0);
			auto root=primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[y]);
			auto radius=primitive(scalarOperator(type(y),TensorOp.mul),[at(chart.jacobian),root]);
			auto image=distribution(ctx,BoundOp.distributionRadiusImage,[scalar(ctx,arena.real_(centre)),hint(lambda(radius),"y")]);
			chart.radiusCentre=scalar(inner,arena.real_(centre)).id; chart.squareProduct=map.product;
			if(polynomial.polynomial){chart.polynomialCheck=cast(uint)scalarDomains.length; scalarDomains~=polynomial;}
			if(band){
				auto zero=arena.real_(0),bound=scalar(inner,arena.real_(cap));
				auto pred=primitive(strict?arena.lt(zero,zero):arena.le(zero,zero),[y,bound]);
				auto mask=primitive(arena.mask(arena.boolean(true),arena.real_(1)),[pred,scalar(inner,arena.real_(1))]);
				image=distribution(ctx,BoundOp.distributionWeight,[hint(lambda(mask),"y"),image]);
				chart.bandLo=lo; chart.bandHi=hi; chart.cutoff=bound.id; chart.openBand=strict;
			}
			evidence=cast(uint)affineCharts.length; affineCharts~=chart;
			return image;
		}
		bool hasPowerDensity(uint id){ return oddMap(id).degree||powerMap(id,true).degree; }
		AffineChart sourceChart(PowerMap m){
			if(m.affine==BoundTerm.init) return AffineChart.init;
			auto chart=affineChart(m.affine.id,m.slope,m.offset,true);
			chart.powerDegree=m.degree; chart.squareProduct=m.product;
			auto magnitude=m.slope<Rational(0)?-m.slope:m.slope;
			auto factor=Rational(m.degree)*magnitude,ctx=context(at(chart.map));
			chart.derivativeNumerator=scalar(ctx,arena.real_(Rational(factor.numerator,BigInt(1)))).id;
			chart.derivativeDenominator=scalar(ctx,arena.real_(Rational(factor.denominator,BigInt(1)))).id;
			return chart;
		}
		BoundTerm affineInverseAt(AffineChart chart,BoundTerm y){
			auto inverse=lambda(at(chart.inverse)),ctx=context(y);
			if(context(inverse)!=ctx){
				// A whole chart introduces a fresh target binder.
				uint[] shift;
				foreach(i;0..contexts[context(inverse).index].length) shift~=i+1;
				inverse=rename(inverse,ctx,shift);
			}
			return apply(inverse,y);
		}
		BoundTerm powerJacobian(PowerMap map,AffineChart chart,BoundTerm factor){
			auto ctx=context(factor),mul=scalarOperator(type(factor),TensorOp.mul);
			auto num=map.affine==BoundTerm.init?arena.real_(map.degree):arena.at(nodes[chart.derivativeNumerator].data);
			auto w=primitive(arena.inv(arena.real_(1)),[primitive(mul,[scalar(ctx,num),factor])]);
			if(map.affine!=BoundTerm.init){
				auto den=arena.at(nodes[chart.derivativeDenominator].data);
				if(!arena.number(den).re.one) w=primitive(mul,[scalar(ctx,den),w]);
			}
			return w;
		}
		void oddCoordinates(PowerMap m,AffineChart chart,BoundTerm y,out BoundTerm point,out BoundTerm weight){
			auto root=oddRoot(m.degree,y);
			point=m.affine==BoundTerm.init?root:affineInverseAt(chart,root);
			weight=powerJacobian(m,chart,primitive(arena.pow(arena.real_(1),m.degree-1),[root]));
		}
		void squareCoordinates(PowerMap map,AffineChart chart,BoundTerm y,out BoundTerm lo,out BoundTerm hi,out BoundTerm w){
			auto root=primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[y]);
			auto minus=primitive(scalarOperator(type(y),TensorOp.mul),[scalar(context(y),arena.real_(-1)),root]);
			// The model stores the two atoms in increasing source order.
			lo=affineInverseAt(chart,map.slope>Rational(0)?minus:root);
			hi=affineInverseAt(chart,map.slope>Rational(0)?root:minus);
			w=powerJacobian(map,chart,root);
		}
		BoundTerm maskedInverseRoot(BoundTerm y,Term scale){
			auto ctx=context(y),zero=scalar(ctx,arena.real_(0));
			if(node(y).op==BoundOp.bottom||y==zero) return bottom(ctx,type(y));
			auto nonnegative=primitive(arena.le(arena.real_(0),arena.real_(0)),[zero,y]);
			auto root=primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[y]);
			auto inv=primitive(arena.inv(arena.real_(1)),[root]);
			auto jac=scalar(ctx,scale);
			auto weight=primitive(scalarOperator(type(y),TensorOp.mul),[inv,jac]);
			return primitive(arena.mask(arena.boolean(true),arena.real_(1)),[nonnegative,weight]);
		}
		BoundTerm closedSquareDensity(PowerMap map,BoundTerm y,out uint evidence){
			auto chart=sourceChart(map);
			evidence=cast(uint)affineCharts.length; affineCharts~=chart;
			return maskedInverseRoot(y,arena.at(nodes[chart.jacobian].data));
		}
		BoundTerm squareObservation(PowerMap map,BoundTerm y,BoundTerm predicate,bool scalarResult,out uint evidence){
			auto chart=sourceChart(map),ctx=context(y);
			evidence=cast(uint)affineCharts.length; affineCharts~=chart;
			auto zero=scalar(ctx,arena.real_(0)),lt=arena.lt(arena.real_(0),arena.real_(0));
			BoundTerm lo,hi,w;
			squareCoordinates(map,chart,y,lo,hi,w);
			BoundTerm atom(BoundTerm point,BoundTerm weight){
				if(scalarResult) return weight;
				return distribution(ctx,BoundOp.distributionScale,[weight,distribution(ctx,BoundOp.distributionDirac,[point])]);
			}
			BoundTerm branch(BoundTerm point){
				auto weight=predicate==BoundTerm.init?w:
					primitive(arena.mask(arena.boolean(true),arena.real_(1)),[apply(predicate,point),w]);
				return atom(point,weight);
			}
			auto left=branch(lo),right=branch(hi);
			auto pair=scalarResult?primitive(arena.add(arena.real_(0),arena.real_(0),true),[left,right]):
				distribution(ctx,BoundOp.distributionAdd,[left,right]);
			auto empty=scalarResult?zero:distribution(ctx,BoundOp.distributionZero,[],type(y));
			auto crit=bottom(ctx,type(empty));
			if(predicate!=BoundTerm.init){
				auto centre=affineInverseAt(chart,zero);
				crit=conditional(apply(predicate,centre),crit,atom(centre,zero));
			}
			auto result=node(y).op==BoundOp.bottom?bottom(ctx,type(empty)):
				conditional(primitive(lt,[zero,y]),pair,conditional(primitive(lt,[y,zero]),empty,crit));
			return predicate==BoundTerm.init?result:sequence(predicate,result);
		}
		uint oddEvidence(PowerMap m,AffineChart chart,ref BindingRule rule){
			if(m.affine==BoundTerm.init) return (m.degree-3)/2;
			rule=BindingRule.distributionAffineOdd;
			auto id=cast(uint)affineCharts.length;
			affineCharts~=chart;
			return id;
		}
		BoundTerm atomRowsGraph(BoundTerm t,out uint domainPair,bool directDensity=false){
			domainPair=uint.max;
			uint weight,point;
			if(!realAtomRow(t,weight,point)) return BoundTerm.init;
			if(weight==uint.max){
				if(directDensity&&!hasPowerDensity(lambda(at(point)).id)) return BoundTerm.init;
				domainPair=totalMapDomain(point);
				if(domainPair==uint.max) return BoundTerm.init;
				auto pred=lambda(scalar(context(at(point)),arena.boolean(true)));
				return distribution(context(t),BoundOp.distributionPushforwardOn,[pred,lambda(at(point))]);
			}
			auto mask=nodes[weight];
			if(mask.op!=BoundOp.primitive||arena.view(arena.at(mask.data)).op!=Op.mask||
				nodes[mask.b].op!=BoundOp.scalar||arena.at(nodes[mask.b].data)!=arena.real_(1)) return BoundTerm.init;
			auto pred=lambda(at(mask.a)),map=lambda(at(point));
			if(directDensity&&!hasPowerDensity(map.id)) return BoundTerm.init;
			// Retain the compact proof for the existing open-unit monomials.
			auto x=variable(context(at(point)),0),body=nodes[point];
			bool monomial=at(point)==x;
			if(body.op==BoundOp.primitive&&body.a==x.id){
				auto op=arena.view(arena.at(body.data)).op;
				monomial=op==Op.pow||(op==Op.mul&&body.b==x.id);
			}
			if(!monomial||!openUnitPredicate(pred.id)){
				ScalarDomain[2] checks;
				if(!totalRowDomain(mask.a,checks[0])||!totalRowDomain(point,checks[1])) return BoundTerm.init;
				domainPair=cast(uint)scalarDomains.length;
				scalarDomains~=checks[];
				mapDomains.set(point,domainPair+1);
			}
			return distribution(context(t),BoundOp.distributionPushforwardOn,[pred,map]);
		}
		// A strict sign comparison proves totality and rules out cancellation
		// separately on each fibre, even if the source changes sign elsewhere.
		bool compatibleSquareWeight(uint weight,out ScalarDomain check){
			auto index=freshScalarIndex(weight),arg=arena.variable(Sort.real_,index);
			auto right=scalarBody(at(weight),arg);
			if(right==Term.init) return false;
			auto left=scalarBody(at(weight),arena.mul(arena.real_(-1),arg,true));
			auto claim=arena.le(arena.real_(0),arena.mul(left,right,true));
			auto opts=Options(DensityMode.preserve,true),value=simplify(arena,claim,[],opts);
			if(value.exhausted||value.output!=arena.boolean(true)) return false;
			auto domain=simplifyDomain(arena,claim,[],opts);
			if(domain.exhausted||domain.output!=arena.boolean(true)) return false;
			check=ScalarDomain(claim,domain,value,index,Sort.real_);
			return true;
		}
		bool absoluteSquareWeight(uint weight){
			auto body=nodes[weight];
			return body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.abs&&
				nodes[body.a].op==BoundOp.variable&&nodes[body.a].data==0;
		}
		BoundTerm regularSquareWeight(BoundTerm w,BoundTerm y){
			auto ctx=context(y),zero=arena.real_(0),mul=scalarOperator(type(y),TensorOp.mul);
			auto root=primitive(arena.call(Builtin.sqrtR,[zero]),[y]);
			auto left=primitive(mul,[scalar(ctx,arena.real_(-1)),root]);
			auto sum=primitive(arena.add(zero,zero,true),[apply(w,left),apply(w,root)]);
			auto twice=primitive(mul,[scalar(ctx,arena.real_(2)),root]);
			return primitive(mul,[sum,primitive(arena.inv(arena.real_(1)),[twice])]);
		}
		BoundTerm weightedSquareTarget(BoundTerm weight,bool absolute){
			auto inner=context(weight),ctx=context(lambda(weight)),y=variable(inner,0),zero=arena.real_(0);
			auto pos=primitive(arena.lt(zero,zero),[scalar(inner,zero),y]);
			auto coefficient=scalar(inner,arena.real_(1));
			if(!absolute){
				uint[] shift;
				foreach(i;0..contexts[ctx.index].length) shift~=i+1;
				coefficient=regularSquareWeight(rename(lambda(weight),inner,shift),y);
			}
			auto mask=primitive(arena.mask(arena.boolean(true),arena.real_(1)),[pos,coefficient]);
			return distribution(ctx,BoundOp.distributionWeight,[hint(lambda(mask),"y"),distribution(ctx,BoundOp.distributionLebesgue)]);
		}

		// Recover the source grid before postcomposition. Each trace must
		// admit the change, even when the source omits that value at the cut.
		bool changedJumpGrid(CoordinateChange change,uint input,out uint index,bool flat){
			if(change==CoordinateChange.none||!gridNumerical(input)) return false;
			Rational[] global; string proof;
			if(axisPolynomial(input,global)||!gridChangeRange(change,input,proof)) return false;
			if(polynomialCoordinate(lambda(at(input)),index)==BoundTerm.init) return false;
			auto c=&coordinates[index]; bool jump;
			foreach(j;c.joins){
				if(j.kind==JoinKind.smooth) continue;
				if(!admitsTrace(change,j.left)||!admitsTrace(change,j.right)){coordinates.length=index; return false;}
				jump|=j.kind==JoinKind.jump;
			}
			if(!jump||flat&&!(nodes[c.weight].op==BoundOp.scalar&&arena.at(nodes[c.weight].data)==arena.real_(0))){
				coordinates.length=index; return false;
			}
			c.change=change; c.traceRange=true;
			return true;
		}
		BoundTerm changedJumpCoordinate(BoundTerm t,out uint index){
			auto n=node(t); bool restricted=n.op==BoundOp.distributionInversePart;
			if(restricted&&nodes[n.a].op!=BoundOp.lambda) return BoundTerm.init;
			auto row=nodes[restricted?n.b:n.a];
			if(row.op!=BoundOp.vectorCons||nodes[row.b].op!=BoundOp.vectorNil||nodes[row.a].op!=BoundOp.lambda) return BoundTerm.init;
			auto id=nodes[row.a].a,change=gridChange(id);
			if(change!=CoordinateChange.reciprocal&&change!=CoordinateChange.sqrt) return BoundTerm.init;
			auto input=nodes[id].a;
			if(!hasMask(input)||!gridNumerical(input,true)) return BoundTerm.init;
			return polynomialCoordinate(at(row.a),index,restricted?at(n.a):BoundTerm.init,CoordinateGridMode.jumpChange);
		}
		BoundTerm flatCoordinateMass(BoundTerm t,out uint index){
			auto cover=nodes[node(t).a];
			if(cover.op!=BoundOp.distributionInverseCover) return BoundTerm.init;
			auto row=nodes[cover.a];
			if(row.op!=BoundOp.vectorCons||nodes[row.b].op!=BoundOp.vectorNil||nodes[row.a].op!=BoundOp.lambda) return BoundTerm.init;
			auto id=nodes[row.a].a,body=nodes[id],change=gridChange(id);
			if(!changedJumpGrid(change,body.a,index,true)) return BoundTerm.init;
			auto c=&coordinates[index]; c.flatMass=true;
			auto ctx=context(t),zero=arena.real_(0),sum=scalar(ctx,zero),minus=scalar(ctx,arena.real_(-1));
			auto add=arena.add(zero,zero,true),mul=arena.mul(zero,zero,true),abs=arena.abs(zero);
			BoundTerm trace(Rational r){return primitive(arena.at(body.data),[scalar(ctx,arena.real_(r))]);}
			foreach_reverse(j;c.joins){
				if(j.kind==JoinKind.smooth) continue;
				auto gap=primitive(add,[trace(j.right),primitive(mul,[minus,trace(j.left)])]);
				sum=primitive(add,[primitive(abs,[gap]),sum]);
			}
			return sum;
		}
		// A rational point asks for one cell or one exceptional event. The model
		// determines the answer directly from the checked grid.
		Result literalGridDensity(BoundTerm t){
			auto n=node(t),cover=nodes[n.a],y=nodes[n.b];
			auto miss=Result(uint.max,uint.max);
			if(y.op!=BoundOp.scalar||!arena.isNumber(arena.at(y.data))) return miss;
			bool restricted=cover.op==BoundOp.distributionInversePart;
			if(!restricted&&cover.op!=BoundOp.distributionInverseCover) return miss;
			auto row=nodes[restricted?cover.b:cover.a];
			if(row.op!=BoundOp.vectorCons||nodes[row.b].op!=BoundOp.vectorNil||nodes[row.a].op!=BoundOp.lambda) return miss;
			auto body=nodes[nodes[row.a].a];
			if(body.op!=BoundOp.primitive) return miss;
			auto op=arena.view(arena.at(body.data)).op;
			auto change=gridChange(nodes[row.a].a);
			bool changed=change!=CoordinateChange.none;
			if(!restricted&&!gridNumerical(changed?body.a:nodes[row.a].a)) return miss;
			if(!changed){
				// Polynomials and elementary rays already have smaller specialized proofs.
				if(op!=Op.abs&&op!=Op.add&&op!=Op.mul) return miss;
				Rational[] global; JumpRays rays;
				if(axisPolynomial(nodes[row.a].a,global)||jumpRays(row.a,rays)) return miss;
			}
			auto sample=arena.number(arena.at(y.data)).re;
			if(sample.words>128) return miss;
			uint index;
			if(restricted){
				auto domainsBefore=scalarDomains.length;
				if(changedJumpCoordinate(at(n.a),index)==BoundTerm.init) return miss;
				foreach(j;coordinates[index].joins){
					if(j.kind==JoinKind.corner&&j.selection==CornerSelection.dynamic||j.kind==JoinKind.jump&&!j.clipped){
						coordinates.length=index; scalarDomains.length=domainsBefore; return miss;
					}
				}
			}else if(polynomialCoordinate(at(row.a),index,BoundTerm.init,changed?CoordinateGridMode.continuousChange:CoordinateGridMode.source)==BoundTerm.init&&
				!changedJumpGrid(change,body.a,index,false)) return miss;
			auto c=&coordinates[index];
			size_t cell;
			while(cell<c.grid.cuts.length&&c.grid.cuts[cell]<sample) ++cell;
			bool seam=cell<c.grid.cuts.length&&c.grid.cuts[cell]==sample;
			auto ctx=context(t); BoundTerm answer;
			bool exceptional=seam&&c.joins[cell].kind!=JoinKind.smooth;
			bool missing=exceptional;
			if(restricted&&exceptional){
				auto j=c.joins[cell];
				missing=j.kind==JoinKind.corner?j.selection==CornerSelection.active:!j.clipped.value.zero;
			}
			if(missing) answer=bottom(ctx,type(t));
			else{
				c.sampledValue=seam?c.grid.points[cell]:polynomialAt(c.grid.cells[cell],sample);
				auto slope=exceptional?Rational(0):polynomialAt(derivativeCoefficients(c.grid.cells[cell]),sample);
				c.sampledWeight=slope<Rational(0)?-slope:slope;
				if(c.sampledValue.words>128||c.sampledWeight.words>128){coordinates.length=index; return miss;}
				answer=scalar(ctx,arena.real_(c.sampledWeight));
				if(changed){
					auto inner=scalar(ctx,arena.real_(c.sampledValue));
					answer=primitive(arena.mul(arena.real_(0),arena.real_(0),true),[gridChangeJacobian(c.change,inner),answer]);
					if(restricted){
						auto guard=apply(at(cover.a),primitive(arena.at(body.data),[inner]));
						answer=primitive(arena.mask(arena.boolean(true),arena.real_(0)),[guard,answer]);
					}
				}
			}
			c.query=n.b;
			return Result(answer.id,emit(BindingRule.distributionCoordinateGrid,t.id,answer.id,uint.max,uint.max,index));
		}
		// Evaluate a smooth coordinate at a literal before normalizing its
		// derivative under a lambda. Each step is an existing binding rule.
		Result literalCoordinateDensity(BoundTerm t){
			auto n=node(t),d=nodes[n.a],y=at(n.b);
			auto miss=Result(uint.max,uint.max);
			if(node(y).op!=BoundOp.scalar||!arena.isNumber(arena.at(node(y).data))) return miss;
			bool restricted=d.op==BoundOp.distributionInversePart;
			if(!restricted&&d.op!=BoundOp.distributionInverseCover) return miss;
			if(restricted&&nodes[d.a].op!=BoundOp.lambda) return miss;
			auto row=nodes[restricted?d.b:d.a];
			if(row.op!=BoundOp.vectorCons||nodes[row.b].op!=BoundOp.vectorNil||nodes[row.a].op!=BoundOp.lambda) return miss;
			auto fn=at(row.a);
			auto body=nodes[node(fn).a];
			if(body.op!=BoundOp.primitive) return miss;
			auto op=arena.view(arena.at(body.data)).op;
			if(op!=Op.builtin&&op!=Op.inv) return miss;
			auto w=smoothCoordinate(fn,restricted?at(d.a):BoundTerm.init);
			if(w==BoundTerm.init) return miss;

			auto density=distribution(context(t),BoundOp.distributionDensityAt,[w,y]);
			auto coordinate=emit(BindingRule.distributionSmoothCoordinate,n.a,w.id);
			auto lifted=emit(BindingRule.congr,t.id,density.id,coordinate,emit(BindingRule.refl,y.id,y.id));
			auto weight=at(node(w).a),app=apply(weight,y);
			auto applyWeight=emit(BindingRule.distributionDensityWeight,density.id,app.id);
			auto exposed=emit(BindingRule.trans,t.id,app.id,lifted,applyWeight);
			auto value=beta(at(node(weight).a),y);
			auto atPoint=emit(BindingRule.trans,t.id,value.id,exposed,emit(BindingRule.beta,app.id,value.id));
			// A closed rational derivative has one calculator proof. This bypasses
			// scalar normalization of every intermediate product and reciprocal.
			Rational q; Term expression;
			auto applied=at(node(value).b);
			if(numericSyntax(applied.id)&&closedRational(applied,q,expression)){
				auto literal=scalar(context(t),arena.real_(q));
				if(applied!=literal){
					auto present=emit(BindingRule.seqScalar,value.id,applied.id);
					auto evaluated=emit(BindingRule.closedRationalValue,applied.id,literal.id,uint.max,uint.max,expression.id);
					auto answer=emit(BindingRule.trans,value.id,literal.id,present,evaluated);
					return Result(literal.id,emit(BindingRule.trans,t.id,literal.id,atPoint,answer));
				}
			}
			return Result(value.id,atPoint);
		}
		struct RewriteFrame { uint original,rebuilt,congruence,step; }
		Result visitOnce(BoundTerm t,uint depth,ref RewriteFrame[] chain){
			enforce(depth<512,"binding normalization depth exceeded");
			auto old=memo.get(t.id,Result(uint.max,uint.max)); if(old.output!=uint.max) return old;
			if(active.get(t.id,false)){ exhausted=true; return Result(t.id,emit(BindingRule.refl,t.id,t.id)); }
			active.set(t.id,true);
			auto n=node(t); Result result;
			// Read the typed source lambda before reducing its body. The Lean
			// certificate relates that same lambda to the model's affine step.
			if(n.op==BoundOp.distributionFixed&&steps<budget&&nodes[n.a].op==BoundOp.lambda){
				RetryParts parts;
				if(retrySource(nodes[n.a].a,parts)){
					auto ctx=context(t); BoundTerm target; BindingRule rule;
					if(parts.seed==uint.max&&!parts.forms.length){
						target=distribution(ctx,BoundOp.distributionZero,[],pool.view(type(t)).fields[0]);
						rule=BindingRule.distributionFixedTail;
					}else{
						BoundTerm[] env=[bottom(ctx,type(t))];
						foreach(i;0..contexts[ctx.index].length) env~=variable(ctx,i);
						BoundTerm base;
						if(parts.forms.length){
							BoundTerm[uint] cache;
							base=affineSeed(parts.tail,ctx,env,parts.forms,cache);
							rule=BindingRule.distributionFixedBody;
						}else{
							base=substitute(at(parts.seed),ctx,env);
							rule=parts.direct?BindingRule.distributionFixedRetry:BindingRule.distributionFixedAffine;
						}
						target=distribution(ctx,BoundOp.distributionRetry,[scalar(ctx,arena.real_(parts.ratio)),base]);
						inheritHint(at(n.a),target);
					}
					++steps; auto proof=emit(rule,t.id,target.id);
					chain~=RewriteFrame(t.id,t.id,emit(BindingRule.refl,t.id,t.id),proof);
					return Result(target.id,uint.max);
				}
			}
			if(n.op==BoundOp.distributionMass&&steps<budget){
				BindingRule rule; auto target=shiftMass(t,rule);
				if(target==BoundTerm.init) target=involutionMass(t,rule);
				if(target==BoundTerm.init){ target=countdownMass(t); rule=BindingRule.distributionMassCountdown; }
				if(target!=BoundTerm.init){
					++steps;
					auto proof=emit(rule,t.id,target.id),tail=visit(target,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
			}
			if((n.op==BoundOp.distributionInverseCover||n.op==BoundOp.distributionInversePart)&&steps<budget){
				uint index; auto image=changedJumpCoordinate(t,index);
				if(image!=BoundTerm.init){
					++steps;
					auto proof=emit(BindingRule.distributionCoordinateGrid,t.id,image.id,uint.max,uint.max,index);
					chain~=RewriteFrame(t.id,t.id,emit(BindingRule.refl,t.id,t.id),proof);
					return Result(image.id,uint.max);
				}
			}
			if(n.op==BoundOp.distributionInverseCover&&steps<budget){
				CoverStep step; auto chart=squareFromCover(t,step);
				if(chart!=BoundTerm.init){
					++steps;
					auto id=cast(uint)covers.length; covers~=step;
					auto proof=emit(BindingRule.distributionCoverRadius,t.id,chart.id,uint.max,uint.max,id);
					auto tail=visit(chart,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
			}
			// Keep the short proof for a factored square and preserve closed
			// endpoints before scalar normalization can change either shape.
			if(n.op==BoundOp.distributionPushforwardOn&&steps<budget){
				uint evidence; auto image=inverseSquareChart(t,evidence);
				if(image!=BoundTerm.init){
					++steps;
					auto proof=emit(BindingRule.distributionRadiusChart,t.id,image.id,uint.max,uint.max,evidence),tail=visit(image,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
			}
			if(n.op==BoundOp.distributionMass&&steps<budget){
				uint index; auto mass=flatCoordinateMass(t,index);
				if(mass!=BoundTerm.init){
					++steps;
					auto step=emit(BindingRule.distributionCoordinateGrid,t.id,mass.id,uint.max,uint.max,index);
					chain~=RewriteFrame(t.id,t.id,emit(BindingRule.refl,t.id,t.id),step);
					return Result(mass.id,uint.max);
				}
			}
			if(n.op==BoundOp.distributionDensityAt&&steps<budget){
				if(budget-steps>=3){
					auto direct=literalCoordinateDensity(t);
					if(direct.output!=uint.max){
						steps+=3;
						chain~=RewriteFrame(t.id,t.id,emit(BindingRule.refl,t.id,t.id),direct.proof);
						return Result(direct.output,uint.max);
					}
				}
				auto grid=literalGridDensity(t);
				if(grid.output!=uint.max){
					++steps;
					chain~=RewriteFrame(t.id,t.id,emit(BindingRule.refl,t.id,t.id),grid.proof);
					return Result(grid.output,uint.max);
				}
				uint weight,point; bool product;
				if(realAtomRow(at(n.a),weight,point)&&weight!=uint.max&&squareMap(lambda(at(point)).id,product)){
					auto body=nodes[weight];
					bool iverson=body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.mask&&
						nodes[body.b].op==BoundOp.scalar&&arena.at(nodes[body.b].data)==arena.real_(1);
					// Both shapes already have a simpler whole-chart normal form.
					auto total=iverson||absoluteSquareWeight(weight)?uint.max:totalMapDomain(weight);
					if(total!=uint.max){
						auto ctx=context(t),y=at(n.b),w=lambda(at(weight)),zero=scalar(ctx,arena.real_(0));
						auto lt=arena.lt(arena.real_(0),arena.real_(0));
						auto atCritical=primitive(arena.nonzero(arena.real_(0)),[apply(w,zero)]);
						auto critical=conditional(atCritical,bottom(ctx,type(t)),zero);
						auto target=node(y).op==BoundOp.bottom?bottom(ctx,type(t)):
							conditional(primitive(lt,[zero,y]),regularSquareWeight(w,y),
							conditional(primitive(lt,[y,zero]),zero,critical));
						++steps;
						auto proof=emit(BindingRule.distributionWeightedSquareDensity,t.id,target.id,uint.max,uint.max,total);
						auto tail=visit(target,depth+1);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
						active.set(t.id,false); memo.set(t.id,result); return result;
					}
				}
			}
			// Preserve the original real Iverson before scalar normalization moves
			// its coercions outside the mask.
			if(steps<budget&&(n.op==BoundOp.distributionBind||n.op==BoundOp.distributionIntegral)){
				uint pair; auto graph=atomRowsGraph(t,pair);
				if(graph!=BoundTerm.init){
					++steps;
					auto proof=emit(BindingRule.distributionAtomRows,t.id,graph.id,uint.max,uint.max,pair),tail=visit(graph,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
				uint weight,point; bool product;
				if(realAtomRow(t,weight,point)&&weight!=uint.max&&squareMap(lambda(at(point)).id,product)){
					bool absolute=absoluteSquareWeight(weight);
					uint signDomain=uint.max,criticalProof=uint.max;
					bool valid=absolute;
					ScalarDomain sign;
					if(!absolute&&borelProof(weight).length&&compatibleSquareWeight(weight,sign)){
						auto atZero=apply(lambda(at(weight)),scalar(context(t),arena.real_(0)));
						auto critical=visit(primitive(arena.nonzero(arena.real_(0)),[atZero]),depth+1);
						if(isTrue(critical.output,false)){
							valid=true; criticalProof=critical.proof; signDomain=cast(uint)scalarDomains.length; scalarDomains~=sign;
						}
					}
					if(valid){
						++steps;
						auto target=weightedSquareTarget(at(weight),absolute);
						auto proof=emit(BindingRule.distributionWeightedSquare,t.id,target.id,signDomain,criticalProof);
						auto tail=visit(target,depth+1);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
						active.set(t.id,false); memo.set(t.id,result); return result;
					}
				}
			}
			if(steps<budget&&n.op==BoundOp.distributionWeight&&nodes[n.a].op==BoundOp.lambda&&nodes[n.b].op==BoundOp.distributionWeight){
				auto inner=nodes[n.b];
				if(nodes[inner.b].op==BoundOp.distributionLebesgue&&nodes[inner.a].op==BoundOp.lambda){
					auto mask=nodes[nodes[n.a].a],base=nodes[nodes[inner.a].a];
					bool isOp(BoundNode n,Op op){ return n.op==BoundOp.primitive&&arena.view(arena.at(n.data)).op==op; }
					if(isOp(mask,Op.mask)&&isOp(base,Op.mask)&&isOp(nodes[mask.a],Op.and_)&&
						nodes[mask.a].a==base.a&&nodes[base.b].op==BoundOp.scalar&&arena.at(nodes[base.b].data)==arena.real_(1)){
						auto next=distribution(context(t),BoundOp.distributionWeight,[at(n.a),at(inner.b)]);
						++steps;
						auto proof=emit(BindingRule.distributionMaskAbsorb,t.id,next.id),tail=visit(next,depth+1);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
						active.set(t.id,false); memo.set(t.id,result); return result;
					}
				}
			}
			// Applying the mass observer is strict in its distribution argument.
			// Expose the observer before expanding a symbolic graph fibre.
			if(steps<budget&&n.op==BoundOp.apply&&nodes[n.a].op==BoundOp.lambda){
				auto body=nodes[nodes[n.a].a];
				if(body.op==BoundOp.distributionMass&&nodes[body.a].op==BoundOp.variable&&nodes[body.a].data==0){
					auto mass=distribution(context(t),BoundOp.distributionMass,[at(n.b)]);
					++steps;
					auto proof=emit(BindingRule.fold,t.id,mass.id),tail=visit(mass,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
			}
			// A test of one atom has a direct observer. Use it before the atom's
			// weight is evaluated as a coefficient by the mixture laws below.
			if(n.op==BoundOp.distributionMass&&nodes[n.a].op==BoundOp.distributionWeight&&nodes[nodes[n.a].b].op==BoundOp.distributionDirac&&steps<budget){
				auto d=nodes[n.a],next=apply(at(d.a),at(nodes[d.b].a)); ++steps;
				auto proof=emit(BindingRule.distributionMassWeightedDirac,t.id,next.id),tail=visit(next,depth+1);
				result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
				active.set(t.id,false); memo.set(t.id,result); return result;
			}
			// Split a bind over the sum or scaling of its source before the
			// summands are normalized: a chart is recognized from its original mask.
			if(n.op==BoundOp.distributionBind&&(nodes[n.a].op==BoundOp.distributionAdd||nodes[n.a].op==BoundOp.distributionScale)&&steps<budget){
				auto d=nodes[n.a],k=at(n.b),scope_=context(t); bool sum=d.op==BoundOp.distributionAdd;
				auto next=sum?distribution(scope_,BoundOp.distributionAdd,[distribution(scope_,BoundOp.distributionBind,[at(d.a),k]),distribution(scope_,BoundOp.distributionBind,[at(d.b),k])])
					:distribution(scope_,BoundOp.distributionScale,[at(d.a),distribution(scope_,BoundOp.distributionBind,[at(d.b),k])]);
				++steps;
				auto proof=emit(sum?BindingRule.distributionBindAdd:BindingRule.distributionBindScale,t.id,next.id),tail=visit(next,depth+1);
				result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
				active.set(t.id,false); memo.set(t.id,result); return result;
			}
			if(n.op==BoundOp.distributionMass&&nodes[n.a].op==BoundOp.distributionGraphFibre&&steps<budget){
				auto graph=nodes[n.a],out_=distribution(context(t),BoundOp.distributionGraphMass,[at(graph.a),at(graph.b)]);
				++steps;
				auto proof=emit(BindingRule.distributionGraphMass,t.id,out_.id),tail=visit(out_,depth+1);
				result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
				active.set(t.id,false); memo.set(t.id,result); return result;
			}
			if(domains&&steps<budget&&n.op==BoundOp.defined&&nodes[n.a].op==BoundOp.get){
				auto child=nodes[n.a],index=nodes[child.b],v=pool.view(type(at(child.a)));
				if(v.dimension.constant&&index.op==BoundOp.scalar&&arena.isNumber(arena.at(index.data))){
					auto i=arena.number(arena.at(index.data)).re;
					if(i.small&&i.integer>=0&&cast(ulong)i.integer<v.length){
						auto next=defined(at(child.a)); ++steps;
						auto proof=emit(BindingRule.getDomain,t.id,next.id),tail=visit(next,depth+1);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
						active.set(t.id,false); memo.set(t.id,result); return result;
					}
				}
			}
			if(domains&&steps<budget&&(n.op==BoundOp.defined&&nodes[n.a].op==BoundOp.tensor||n.op==BoundOp.domain&&nodes[n.a].op==BoundOp.lambda)){
				auto child=nodes[n.a]; BoundTerm next; BindingRule rule;
				if(n.op==BoundOp.domain){ next=inheritHint(at(n.a),set(defined(at(child.a)))); rule=BindingRule.domainLam; }
				else{ next=primitive(arena.and_(arena.boolean(true),arena.boolean(true)),[defined(at(child.a)),defined(at(child.b))]); rule=BindingRule.tensorDomain; }
				++steps; auto proof=emit(rule,t.id,next.id),tail=visit(next,depth+1);
				result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
				active.set(t.id,false); memo.set(t.id,result); return result;
			}
			if(domains&&n.op==BoundOp.domain&&nodes[n.a].op==BoundOp.fixed&&steps<budget){
				// Shifted intervals can enumerate every seed during domain inference.
				// Reuse their known function solution; keep ranking for other domains.
				RecurrenceSolution solution; auto solved=solveRecurrence(at(n.a),solution);
				if(solved!=BoundTerm.init&&solution.cutoff&&solution.band==2){
					auto extra=cast(uint)solutions.length; solutions~=solution; ++steps;
					auto proof=emit(BindingRule.fixedRecurrence,n.a,solved.id,uint.max,uint.max,extra),next=domain(solved);
					auto congr=emit(BindingRule.congr,t.id,next.id,proof),tail=visit(next,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,congr,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
				DomainRank rank;
				if(rankDomain(at(n.a),rank)){
					auto extra=cast(uint)ranks.length; ranks~=rank;
					auto predicate=rank.iterations.length?rank.iterations[$-1].output:rank.lower.output!=Term.init?rank.result.output:arena.boolean(true);
					auto next=inheritHint(at(nodes[n.a].a),set(restoreBody(predicate,push(context(t),scalarType(rank.sort)),arena.variable(rank.sort,rank.variable))));
					++steps; auto proof=emit(BindingRule.domainFixedTotal,t.id,next.id,uint.max,uint.max,extra),tail=visit(next,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
			}
			if(domains&&n.op==BoundOp.defined&&nodes[n.a].op==BoundOp.apply&&nodes[nodes[n.a].a].op==BoundOp.fixed&&steps<budget){
				auto call=nodes[n.a],d=visit(domain(at(call.a)),depth+1);
				if(nodes[d.output].op==BoundOp.set&&steps<budget){
					++steps; auto next=holds(member(domain(at(call.a)),at(call.b)));
					auto proof=emit(BindingRule.definedApp,t.id,next.id),tail=visit(next,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
			}
			if(n.a==uint.max) result=Result(t.id,emit(BindingRule.refl,t.id,t.id));
			else{
				Result x=Result(uint.max,uint.max);
				if(domains&&n.op==BoundOp.apply&&nodes[n.a].op==BoundOp.fixed&&steps<budget&&closedFixedArgument(at(n.b))){
					RecurrenceSolution solution; auto function_=at(n.a),solved=solveRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solveAffineRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solveLinearRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solvePrefixRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solveCoupledRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solveIndexedRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solveCFiniteRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solveDivideRecurrence(function_,solution);
					if(solved!=BoundTerm.init){
						auto extra=cast(uint)solutions.length; solutions~=solution; ++steps;
						x=Result(solved.id,emit(BindingRule.fixedRecurrence,n.a,solved.id,uint.max,uint.max,extra));
					}
				}
				// The direct scalar observers have shorter proof terms than first
				// changing the graph coordinates and then observing the result.
				bool product;
				if(n.op==BoundOp.distributionMass||n.op==BoundOp.distributionDensityAt){
					auto graph=nodes[n.a];
					Rational a,b;
					if(graph.op==BoundOp.distributionPushforwardOn&&
						(oddMap(graph.b).degree!=0||n.op==BoundOp.distributionDensityAt&&powerMap(graph.b,true).degree||
						 openUnitPredicate(graph.a)&&squareMap(graph.b,product)||
						 n.op==BoundOp.distributionMass&&nodes[graph.b].op==BoundOp.lambda&&nodes[nodes[graph.b].a].op!=BoundOp.variable&&affineMap(graph.b,a,b)))
						x=Result(n.a,emit(BindingRule.refl,n.a,n.a));
					else if(steps<budget&&(graph.op==BoundOp.distributionBind||graph.op==BoundOp.distributionIntegral)){
						uint pair; auto chart=atomRowsGraph(at(n.a),pair,n.op!=BoundOp.distributionMass);
						if(chart!=BoundTerm.init){
							++steps;
							x=Result(chart.id,emit(BindingRule.distributionAtomRows,n.a,chart.id,uint.max,uint.max,pair));
						}
					}
				}
				// Beta reduction already preserves the argument domain; normalize
				// an applied lambda after substitution, not once on each side of it.
				if(x.output==uint.max) x=n.op==BoundOp.finiteSum||n.op==BoundOp.summation||n.op==BoundOp.limit||n.op==BoundOp.fixed||n.op==BoundOp.apply&&nodes[n.a].op==BoundOp.lambda?Result(n.a,emit(BindingRule.refl,n.a,n.a)):visit(at(n.a),depth+1);
				BoundTerm[] args=[at(x.output)]; uint y=uint.max,z=uint.max;
				if(n.b!=uint.max){
					bool skip; auto left=nodes[x.output];
					if(domains&&left.op==BoundOp.scalar){
						auto v=arena.view(arena.at(left.data));
						if(v.op==Op.boolLit){
							auto op=n.op==BoundOp.primitive?arena.view(arena.at(n.data)).op:Op.variable;
							skip=!v.value&&(n.op==BoundOp.conditional||n.op==BoundOp.guard||op==Op.mask||op==Op.and_)||v.value&&op==Op.or_;
						}
					}
					if(n.op==BoundOp.conditional) skip=left.op==BoundOp.bottom||left.op==BoundOp.scalar&&arena.at(left.data)==arena.boolean(false);
					auto r=skip?Result(n.b,emit(BindingRule.refl,n.b,n.b)):visit(at(n.b),depth+1); args~=at(r.output); y=r.proof;
				}
				if(n.c!=uint.max){
					auto left=nodes[x.output];
					bool skip=left.op==BoundOp.bottom||left.op==BoundOp.scalar&&arena.at(left.data)==arena.boolean(true);
					auto r=skip?Result(n.c,emit(BindingRule.refl,n.c,n.c)):visit(at(n.c),depth+1); args~=at(r.output); z=r.proof;
				}
				auto rebuilt=rebuild(t,context(t),args);
				result=Result(rebuilt.id,emit(BindingRule.congr,t.id,rebuilt.id,x.proof,y,z));
			}
			auto current=node(at(result.output)); BoundTerm next; BindingRule rule; uint extra=uint.max;
			uint predicateDomain=uint.max,excludedZero=uint.max;
			auto ctx=context(at(result.output));

			bool constantSet(uint id,bool value){ auto n=nodes[id]; return n.op==BoundOp.set&&isTrue(n.a,value); }
			BoundTerm both(BoundTerm x,BoundTerm y){ return primitive(arena.and_(arena.boolean(true),arena.boolean(true)),[x,y]); }
			bool guardReady(uint id){
				auto g=nodes[id];
				// Let pointwise normalization resolve domain queries first. Lifting
				// them early can combine large scalar domains and exhaust their budget.
				if(g.op==BoundOp.defined||g.op==BoundOp.holds||g.op==BoundOp.domain) return false;
				return (g.a==uint.max||guardReady(g.a))&&(g.b==uint.max||guardReady(g.b))&&(g.c==uint.max||guardReady(g.c));
			}

			if(current.op==BoundOp.distributionInversePart&&nodes[current.a].op==BoundOp.lambda){
				auto first=nodes[current.b];
				if(first.op==BoundOp.vectorCons&&nodes[first.b].op==BoundOp.vectorNil&&nodes[first.a].op==BoundOp.lambda){
					next=singletonCoordinate(at(first.a),extra,rule,at(current.a));
				}
			}
			if(current.op==BoundOp.distributionInverseCover){
				auto first=nodes[current.a]; Rational slope,offset; bool product;
				bool single=first.op==BoundOp.vectorCons&&nodes[first.b].op==BoundOp.vectorNil;
				JumpRays rays;
				auto ray=single?rayCoordinate(at(first.a),extra,rule):BoundTerm.init;
				if(ray!=BoundTerm.init){
					next=ray;
				}else if(single&&jumpRays(first.a,rays)){
					next=jumpCoordinate(at(first.a),rays); rule=BindingRule.distributionCoordinateTwoJumps;
				}else if(single&&squareMap(first.a,product)){
					auto x=at(nodes[nodes[first.a].a].a),zero=arena.real_(0);
					auto magnitude=primitive(arena.abs(zero),[x]);
					auto jac=primitive(scalarOperator(type(x),TensorOp.mul),[scalar(context(x),arena.real_(2)),magnitude]);
					next=distribution(ctx,BoundOp.distributionWeight,[inheritHint(at(first.a),lambda(jac)),distribution(ctx,BoundOp.distributionLebesgue)]);
					extra=product; rule=BindingRule.distributionCoordinateSquare;
				}else if(single&&affineMap(first.a,slope,offset)){
					auto j=slope<Rational(0)?-slope:slope;
					auto inner=context(at(nodes[first.a].a)),coefficient=scalar(inner,arena.real_(j));
					next=distribution(ctx,BoundOp.distributionLebesgue);
					if(j!=Rational(1)) next=distribution(ctx,BoundOp.distributionWeight,[hint(lambda(coefficient),binderHint(at(first.a)).name),next]);
					extra=coefficient.id; rule=BindingRule.distributionCoverAffine;
				}else if(single&&nodes[first.a].op==BoundOp.lambda){
					auto body=nodes[nodes[first.a].a];
					if(body.op==BoundOp.primitive&&nodes[body.a].op==BoundOp.variable&&nodes[body.a].data==0){
						auto op=arena.view(arena.at(body.data));
						if(op.op==Op.builtin&&(op.value==Builtin.sinhR||op.value==Builtin.asinhR)){
							auto y=at(body.a),zero=arena.real_(0); BoundTerm w;
							if(op.value==Builtin.sinhR){
								w=primitive(arena.call(Builtin.coshR,[zero]),[y]);
								rule=BindingRule.distributionCoverSinh;
							}else{
								auto sq=primitive(arena.pow(zero,2),[y]);
								auto sum=primitive(arena.add(zero,zero,true),[scalar(context(y),arena.real_(1)),sq]);
								w=primitive(arena.inv(zero),[primitive(arena.call(Builtin.sqrtR,[zero]),[sum])]);
								rule=BindingRule.distributionCoverAsinh;
							}
							next=distribution(ctx,BoundOp.distributionWeight,[hint(lambda(w),binderHint(at(first.a)).name),
								distribution(ctx,BoundOp.distributionLebesgue)]);
						}
					}
					if(next==BoundTerm.init) next=singletonCoordinate(at(first.a),extra,rule);
				}
			}
			if(current.op==BoundOp.distributionBind||current.op==BoundOp.distributionIntegral){
				next=atomRowsGraph(at(result.output),extra);
				if(next!=BoundTerm.init) rule=BindingRule.distributionAtomRows;
				else{
					// A total weight that is not a unit guard travels through an
					// affine graph as a function: evaluate it at the inverse point.
					uint weight,point; Rational slope,offset; ScalarDomain weightDomain;
					if(realAtomRow(at(result.output),weight,point)&&weight!=uint.max){
						auto map=lambda(at(point));
						if(affineMap(map.id,slope,offset)&&!slope.zero&&totalRowDomain(weight,weightDomain)){
							auto chart=affineChart(map.id,slope,offset,true,cast(uint)scalarDomains.length);
							auto inv=at(chart.inverse),inner=context(inv),jac=at(chart.jacobian);
							uint[] shift;
							foreach(i;0..contexts[ctx.index].length) shift~=i+1;
							auto value=apply(rename(lambda(at(weight)),inner,shift),inv);
							auto density=hint(lambda(primitive(arena.mul(arena.real_(1),arena.real_(1),true),[value,jac])),"y");
							next=distribution(ctx,BoundOp.distributionWeight,[density,distribution(ctx,BoundOp.distributionLebesgue)]);
							extra=cast(uint)affineCharts.length;
							affineCharts~=chart;
							scalarDomains~=weightDomain; rule=BindingRule.distributionWeightedAffine;
						}
					}
				}
			}
			if(domains&&current.op==BoundOp.distributionScale){
				auto weight=at(current.a);
				if(node(weight).op==BoundOp.bottom){
					next=bottom(ctx,types[current.type]); rule=BindingRule.fold;
				}else if(!totalScalar(weight)&&closedScalar(weight)){
					auto source=arena.at(node(weight).data);
					auto domain=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true));
					if(!domain.exhausted&&domain.output==arena.boolean(false)){
						extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,domain);
						next=bottom(ctx,types[current.type]); rule=BindingRule.distributionScaleUndefined;
					}
				}
			}
			if(current.op==BoundOp.distributionMass){
				auto d=nodes[current.a];
				if(d.op==BoundOp.bottom){ next=bottom(ctx,types[current.type]); rule=BindingRule.fold; }
				else if(d.op==BoundOp.distributionZero){ next=scalar(ctx,arena.real_(0)); rule=BindingRule.distributionMassZero; }
				else if(d.op==BoundOp.distributionWeight&&nodes[d.a].op==BoundOp.lambda&&cornerChart(d.b)){
					auto domain=totalMapDomain(nodes[d.a].a);
					if(domain!=uint.max){ next=scalar(ctx,arena.real_(0)); rule=BindingRule.distributionCornerPairing; extra=domain; }
				}
				else if(d.op==BoundOp.distributionInversePart||d.op==BoundOp.distributionWeight&&nodes[d.b].op==BoundOp.distributionInversePart){
					bool bare=d.op==BoundOp.distributionInversePart;
					auto test=bare?BoundTerm.init:at(d.a);
					next=squarePartPairing(at(bare?current.a:d.b),test);
					if(next!=BoundTerm.init) rule=bare?BindingRule.distributionSquarePartMass:BindingRule.distributionSquarePartPairing;
				}
				else if(d.op==BoundOp.distributionWeight&&nodes[d.b].op==BoundOp.distributionRadiusImage){
					auto image=nodes[d.b]; string form; bool casts,strict;
					auto j=sqrtRadiusScale(image.b,form),bound=sublevelBound(d.a,casts,strict);
					if(j!=Term.init&&bound!=BoundTerm.init&&nodes[image.a].op==BoundOp.scalar&&arena.isNumber(arena.at(nodes[image.a].data))){
						auto q=dropIndex(bound);
						if(node(q).op==BoundOp.bottom) next=q;
						else{
							auto zero=scalar(ctx,arena.real_(0)),two=scalar(ctx,arena.real_(2));
							auto le=primitive(arena.le(arena.real_(0),arena.real_(0)),[zero,q]);
							auto mul=scalarOperator(type(q),TensorOp.mul),width=primitive(mul,[two,scalar(ctx,j)]);
							auto root=primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[q]);
							next=primitive(arena.mask(arena.boolean(true),arena.real_(1)),[le,primitive(mul,[width,root])]);
						}
						rule=BindingRule.distributionRadiusSublevel; extra=q.id;
					}else if(j!=Term.init&&nodes[image.a].op==BoundOp.scalar&&arena.isNumber(arena.at(nodes[image.a].data))){
						auto test=at(d.a),inner=push(ctx,scalarType(Sort.real_)),y=variable(inner,0);
						uint[] shift; foreach(i;0..contexts[ctx.index].length) shift~=i+1;
						auto zero=arena.real_(0),mul=scalarOperator(type(y),TensorOp.mul);
						auto pos=primitive(arena.lt(zero,zero),[scalar(inner,zero),y]);
						auto root=primitive(arena.call(Builtin.sqrtR,[zero]),[y]);
						auto jac=primitive(mul,[primitive(arena.inv(zero),[root]),scalar(inner,j)]);
						auto value=primitive(mul,[apply(rename(test,inner,shift),y),jac]);
						auto weight=hint(lambda(primitive(arena.mask(arena.boolean(true),arena.real_(1)),[pos,value])),binderHint(at(image.b)).name);
						auto source=distribution(ctx,BoundOp.distributionWeight,[weight,distribution(ctx,BoundOp.distributionLebesgue)]);
						next=sequence(apply(test,scalar(ctx,zero)),distribution(ctx,BoundOp.distributionMass,[source]));
						rule=BindingRule.distributionRadiusPairing;
					}
				}
				else if(d.op==BoundOp.distributionPushforwardOn&&nodes[d.a].op==BoundOp.lambda){
					bool product;
					bool square=squareMap(d.b,product);
					uint mapProof=uint.max;
					if(!square&&nodes[d.b].op==BoundOp.lambda&&type(at(current.a))==pool.distribution(scalarType(Sort.real_)))
						mapProof=totalMapDomain(nodes[d.b].a);
					if(square||mapProof!=uint.max){
						auto pred=at(nodes[d.a].a),one=scalar(context(pred),arena.real_(1));
						auto weight=lambda(primitive(arena.mask(arena.boolean(false),arena.real_(0)),[pred,one]));
						auto source=distribution(ctx,BoundOp.distributionWeight,[weight,distribution(ctx,BoundOp.distributionLebesgue)]);
						next=distribution(ctx,BoundOp.distributionMass,[source]);
						rule=square?BindingRule.distributionPushforwardMass:BindingRule.distributionTotalGraphMass;
						extra=square?cast(uint)product:mapProof;
					}
				}
				else if(d.op==BoundOp.distributionAdd){
					next=primitive(arena.add(arena.real_(0),arena.real_(0),true),[distribution(ctx,BoundOp.distributionMass,[at(d.a)]),distribution(ctx,BoundOp.distributionMass,[at(d.b)])]); rule=BindingRule.distributionMassAdd;
				}else if(d.op==BoundOp.distributionScale){
					next=primitive(arena.mul(arena.real_(1),arena.real_(1),true),[at(d.a),distribution(ctx,BoundOp.distributionMass,[at(d.b)])]); rule=BindingRule.distributionMassScale;
				}else if(d.op==BoundOp.distributionIntegral&&nodes[d.a].op==BoundOp.lambda){
					auto body=at(nodes[d.a].a),row=distribution(context(body),BoundOp.distributionMass,[body]);
					auto weighted=distribution(ctx,BoundOp.distributionWeight,[lambda(row),distribution(ctx,BoundOp.distributionLebesgue)]);
					next=distribution(ctx,BoundOp.distributionMass,[weighted]); rule=BindingRule.distributionMassIntegral;
				}else if(d.op==BoundOp.distributionBind&&nodes[d.b].op==BoundOp.lambda){
					IntegralSolution source;
					if(densityBodies(d.a,source.from)){
						auto body=at(nodes[d.b].a),row=distribution(context(body),BoundOp.distributionMass,[body]);
						auto weighted=distribution(ctx,BoundOp.distributionWeight,[lambda(row),at(d.a)]);
						next=distribution(ctx,BoundOp.distributionMass,[weighted]); rule=BindingRule.distributionMassBind;
						extra=cast(uint)integrals.length; integrals~=source;
					}
				}
			}
			if(current.op==BoundOp.distributionMass){
				IntegralSolution solution; auto evaluated=integrateSteps(at(result.output),solution);
				if(evaluated==BoundTerm.init){ solution=IntegralSolution.init; evaluated=integratePolynomials(at(result.output),solution); }
				if(evaluated==BoundTerm.init){ solution=IntegralSolution.init; evaluated=integrateInterval(at(result.output),solution); }
				if(evaluated==BoundTerm.init){ solution=IntegralSolution.init; evaluated=integrateGaussian(at(result.output),solution); }
				if(evaluated==BoundTerm.init){ solution=IntegralSolution.init; evaluated=integratePieces(at(result.output),solution); }
				if(evaluated==BoundTerm.init){
					auto strict=unguardMass(at(result.output)),unguarded=strict==BoundTerm.init?massGuard(at(result.output),0):BoundTerm.init;
					IntegralSolution sum; auto spread=strict==BoundTerm.init&&unguarded==BoundTerm.init?distributeMass(at(result.output),sum,true):BoundTerm.init;
					if(strict!=BoundTerm.init){ next=strict; rule=BindingRule.distributionMassStrictGuard; }
					else if(spread!=BoundTerm.init){ next=spread; rule=BindingRule.distributionMassSpread; extra=cast(uint)integrals.length; integrals~=sum; }
					else if(unguarded!=BoundTerm.init){ next=unguarded; rule=BindingRule.distributionMassGuard; }
					else{ solution=IntegralSolution.init; evaluated=normalizeNullEdits(at(result.output),solution); }
				}
				if(evaluated!=BoundTerm.init){ next=evaluated; extra=cast(uint)integrals.length; integrals~=solution; rule=solution.ae?BindingRule.distributionIntegralAE:BindingRule.distributionInterval; }
			}
			if(current.op==BoundOp.distributionMass&&nodes[current.a].op==BoundOp.distributionDirac){
				next=sequence(at(nodes[current.a].a),scalar(ctx,arena.real_(1))); rule=BindingRule.distributionMassDirac;
			}

			if(current.op==BoundOp.distributionMass&&nodes[current.a].op==BoundOp.distributionWeight&&nodes[nodes[current.a].b].op==BoundOp.distributionDirac){
				auto d=nodes[current.a]; next=apply(at(d.a),at(nodes[d.b].a)); rule=BindingRule.distributionMassWeightedDirac;
			}
			// A missing distribution operand makes these constructors missing.
			if(next==BoundTerm.init&&(current.op==BoundOp.distributionAdd||current.op==BoundOp.distributionScale||current.op==BoundOp.distributionWeight||
				current.op==BoundOp.distributionBind||current.op==BoundOp.distributionDensityAt)){
				bool left=nodes[current.a].op==BoundOp.bottom,right=nodes[current.b].op==BoundOp.bottom;
				bool either=current.op==BoundOp.distributionAdd||current.op==BoundOp.distributionDensityAt;
				bool source=current.op==BoundOp.distributionBind;
				if(left&&(either||source)||right&&!source){ next=bottom(ctx,types[current.type]); rule=BindingRule.distributionStrict; }
			}
			// A sum of presentations over ℤ. Its mass is the scalar sum of the masses
			// of its terms; weighting and composition act on the terms. The weight or
			// kernel is copied below the index binder and is still evaluated once
			// outside, so that a missing one makes the result missing.
			if(next==BoundTerm.init&&current.op==BoundOp.distributionMass&&nodes[current.a].op==BoundOp.distributionSum&&nodes[nodes[current.a].a].op==BoundOp.lambda){
				auto term=at(nodes[nodes[current.a].a].a);
				next=summation(lambda(distribution(context(term),BoundOp.distributionMass,[term]))); rule=BindingRule.distributionMassSum;
			}
			if(next==BoundTerm.init&&(current.op==BoundOp.distributionWeight||current.op==BoundOp.distributionBind)){
				bool weight=current.op==BoundOp.distributionWeight;
				auto source=nodes[weight?current.b:current.a],other=at(weight?current.a:current.b);
				if(source.op==BoundOp.distributionSum&&nodes[source.a].op==BoundOp.lambda){
					auto term=at(nodes[source.a].a),inner=context(term);
					uint[] shift; foreach(i;0..contexts[ctx.index].length) shift~=i+1;
					auto copy=rename(other,inner,shift);
					auto row=weight?distribution(inner,BoundOp.distributionWeight,[copy,term]):distribution(inner,BoundOp.distributionBind,[term,copy]);
					next=sequence(other,distribution(ctx,BoundOp.distributionSum,[lambda(row)]));
					rule=weight?BindingRule.distributionWeightSum:BindingRule.distributionBindSum;
				}
			}
			// Finite mixtures of point masses. Weighting and composition follow the
			// constructors of the source; coefficients and atoms are not merged.
			// The real bind is structural in sums and scalings, so a parameter chart
			// below them keeps its row interpreter.
			if(next==BoundTerm.init&&current.op==BoundOp.distributionWeight){
				auto f=at(current.a),d=nodes[current.b];
				if(d.op==BoundOp.distributionDirac){
					next=distribution(ctx,BoundOp.distributionScale,[apply(f,at(d.a)),at(current.b)]); rule=BindingRule.distributionWeightDirac;
				}else if(d.op==BoundOp.distributionZero){
					next=sequence(f,at(current.b)); rule=BindingRule.distributionWeightZero;
				}else if(d.op==BoundOp.distributionWeight&&(nodes[d.b].op==BoundOp.distributionLebesgue||cornerChart(d.b))&&
					node(f).op==BoundOp.lambda&&nodes[d.a].op==BoundOp.lambda&&depends(at(nodes[d.a].a),0)){
					// Combine a varying density with its test. Constant parameter factors
					// are already handled separately by the scalar integral rules.
					auto g=at(nodes[d.a].a),outer=at(node(f).a);
					auto bothWeights=primitive(scalarOperator(type(g),TensorOp.mul),[g,outer]);
					next=distribution(ctx,BoundOp.distributionWeight,[inheritHint(at(d.a),lambda(bothWeights)),at(d.b)]);
					rule=nodes[d.b].op==BoundOp.distributionLebesgue?BindingRule.distributionWeightWeightLebesgue:BindingRule.distributionWeightWeightChart;
				}else if(d.op==BoundOp.distributionAdd){
					next=distribution(ctx,BoundOp.distributionAdd,[distribution(ctx,BoundOp.distributionWeight,[f,at(d.a)]),distribution(ctx,BoundOp.distributionWeight,[f,at(d.b)])]);
					rule=BindingRule.distributionWeightAdd;
				}else if(d.op==BoundOp.distributionScale){
					next=distribution(ctx,BoundOp.distributionScale,[at(d.a),distribution(ctx,BoundOp.distributionWeight,[f,at(d.b)])]); rule=BindingRule.distributionWeightScale;
				}
			}
			if(next==BoundTerm.init&&current.op==BoundOp.distributionBind){
				auto d=nodes[current.a],k=at(current.b);
				if(d.op==BoundOp.distributionDirac){ next=apply(k,at(d.a)); rule=BindingRule.distributionBindDirac; }
				else if(d.op==BoundOp.distributionAdd){
					next=distribution(ctx,BoundOp.distributionAdd,[distribution(ctx,BoundOp.distributionBind,[at(d.a),k]),distribution(ctx,BoundOp.distributionBind,[at(d.b),k])]);
					rule=BindingRule.distributionBindAdd;
				}else if(d.op==BoundOp.distributionScale){
					next=distribution(ctx,BoundOp.distributionScale,[at(d.a),distribution(ctx,BoundOp.distributionBind,[at(d.b),k])]); rule=BindingRule.distributionBindScale;
				}else if(d.op==BoundOp.distributionZero){
					next=sequence(k,distribution(ctx,BoundOp.distributionZero,[],pool.view(types[current.type]).fields[0])); rule=BindingRule.distributionBindZero;
				}
			}
			bool squareProduct;
			if(current.op==BoundOp.distributionPushforwardOn&&nodes[current.a].op==BoundOp.lambda&&nodes[current.b].op==BoundOp.lambda){
				auto map=nodes[nodes[current.b].a];
				if(map.op==BoundOp.variable&&map.data==0){
					auto pred=at(nodes[current.a].a),one=scalar(context(pred),arena.real_(1));
					auto weight=lambda(primitive(arena.mask(arena.boolean(false),arena.real_(0)),[pred,one]));
					next=distribution(ctx,BoundOp.distributionWeight,[weight,distribution(ctx,BoundOp.distributionLebesgue)]);
					rule=BindingRule.distributionIdentityChart;
				}else{
					Rational slope,offset; ScalarDomain predDomain;
					if(affineMap(current.b,slope,offset)&&totalRowDomain(nodes[current.a].a,predDomain)){
						auto chart=affineChart(current.b,slope,offset,true,cast(uint)scalarDomains.length);
						auto inv=at(chart.inverse),inner=context(inv),jac=at(chart.jacobian);
						uint[] shift;
						foreach(i;0..contexts[ctx.index].length) shift~=i+1;
						auto guard=apply(rename(at(current.a),inner,shift),inv);
						auto weight=hint(lambda(primitive(arena.mask(arena.boolean(true),arena.real_(1)),[guard,jac])),"y");
						next=distribution(ctx,BoundOp.distributionWeight,[weight,distribution(ctx,BoundOp.distributionLebesgue)]);
						extra=cast(uint)affineCharts.length;
						affineCharts~=chart;
						scalarDomains~=predDomain; rule=BindingRule.distributionAffineChart;
					}
				}
			}
			if(current.op==BoundOp.distributionPushforwardOn&&openUnitPredicate(current.a)&&squareMap(current.b,squareProduct)){
				auto y=variable(push(ctx,scalarType(Sort.real_)),0);
				auto weight=hint(lambda(openUnitDensity(y)),"y");
				next=distribution(ctx,BoundOp.distributionWeight,[weight,distribution(ctx,BoundOp.distributionLebesgue)]);
				rule=BindingRule.distributionSquareChart; extra=squareProduct;
			}else if(current.op==BoundOp.distributionPushforwardOn&&nodes[current.a].op==BoundOp.lambda){
				auto branch=oddMap(current.b);
				if(!branch.degree) branch=powerMap(current.b,true);
				auto body=nodes[current.a].a;
				if(result.output!=t.id){
					auto image=inverseSquareChart(at(result.output),extra);
					if(image!=BoundTerm.init){ next=image; rule=BindingRule.distributionRadiusChart; }
				}
				uint puncture=uint.max;
				if(branch.degree==2&&nodes[body].op==BoundOp.primitive&&arena.view(arena.at(nodes[body].data)).op==Op.nonzero){
					Rational slope,offset;
					if(affineMap(lambda(at(nodes[body].a)).id,slope,offset)) puncture=nodes[body].a;
				}
				ScalarDomain total;
				if(branch.degree&&steps<budget&&!isTrue(body,true)&&(puncture!=uint.max||
					(branch.degree!=2||borelProof(body).length)&&totalRowDomain(body,total))){
					auto predicate=at(current.a);
					auto chart=sourceChart(branch),zero=scalar(ctx,arena.real_(0));
					auto source=branch.affine==BoundTerm.init?zero:affineInverseAt(chart,zero);
					auto critical=visit(apply(predicate,source),depth+1);
					if(isTrue(critical.output,false)){
						auto inner=push(ctx,scalarType(Sort.real_)),y=variable(inner,0);
						uint[] shift;
						foreach(i;0..contexts[ctx.index].length) shift~=i+1;
						auto pred=rename(predicate,inner,shift),maskOp=arena.mask(arena.boolean(true),arena.real_(1));
						BoundTerm masked(BoundTerm point,BoundTerm w){return primitive(maskOp,[apply(pred,point),w]);}
						BoundTerm mask;
						if(branch.degree==2){
							BoundTerm coefficient;
							if(puncture!=uint.max){
								auto root=primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[y]);
								auto inv=primitive(arena.inv(arena.real_(1)),[root]);
								coefficient=primitive(scalarOperator(type(y),TensorOp.mul),[inv,at(chart.jacobian)]);
								chart.punctureBody=puncture;
							}else{
								BoundTerm lo,hi,w;
								squareCoordinates(branch,chart,y,lo,hi,w);
								coefficient=primitive(arena.add(arena.real_(0),arena.real_(0),true),[masked(lo,w),masked(hi,w)]);
								chart.borelPredicate=body;
							}
							auto pos=primitive(arena.lt(arena.real_(0),arena.real_(0)),[scalar(inner,arena.real_(0)),y]);
							mask=primitive(maskOp,[pos,coefficient]);
							extra=cast(uint)affineCharts.length; affineCharts~=chart; rule=BindingRule.distributionAffineSquare;
						}else{
							BoundTerm point,w;
							oddCoordinates(branch,chart,y,point,w);
							mask=masked(point,w); rule=BindingRule.distributionOddChart;
							extra=oddEvidence(branch,chart,rule);
						}
						next=distribution(ctx,BoundOp.distributionWeight,[hint(lambda(mask),"y"),distribution(ctx,BoundOp.distributionLebesgue)]);
						if(puncture==uint.max){ predicateDomain=cast(uint)scalarDomains.length; scalarDomains~=total; }
						excludedZero=critical.proof;
					}
				}
			}
			if(next==BoundTerm.init&&current.op==BoundOp.distributionMass){
				auto d=nodes[current.a];
				if(d.op==BoundOp.distributionWeight&&nodes[d.b].op==BoundOp.distributionLebesgue&&nodes[d.a].op==BoundOp.lambda){
					auto body=nodes[nodes[d.a].a];
					if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.mask&&
						at(body.a)==openUnit(variable(context(at(body.a)),0))){
						auto canonical=visit(lambda(openUnitDensity(variable(context(at(body.a)),0))),depth+1);
						if(canonical.output==d.a){
							extra=canonical.proof; next=scalar(ctx,arena.real_(1)); rule=BindingRule.distributionChartMass;
						}
					}
				}
			}
			bool maskedGraph=current.op==BoundOp.apply&&nodes[current.a].op==BoundOp.distributionMaskedGraph;
			bool graph=maskedGraph||current.op==BoundOp.distributionGraphFibre||current.op==BoundOp.distributionGraphMass;
			auto graphMap=maskedGraph?nodes[current.a].b:current.a;
			auto oddGraph=graph?oddMap(graphMap):PowerMap.init; PowerMap squareBranch;
			if(oddGraph.degree){
				auto chart=sourceChart(oddGraph); BoundTerm point,weight;
				oddCoordinates(oddGraph,chart,at(current.b),point,weight);
				if(current.op==BoundOp.distributionGraphMass){
					next=weight; rule=BindingRule.distributionOddMass;
				}else{
					if(maskedGraph){
						auto active=apply(at(nodes[current.a].a),point);
						weight=primitive(arena.mask(arena.boolean(true),arena.real_(1)),[active,weight]);
					}
					next=distribution(ctx,BoundOp.distributionScale,[weight,distribution(ctx,BoundOp.distributionDirac,[point])]);
					rule=maskedGraph?BindingRule.distributionMaskedOdd:BindingRule.distributionOddFibre;
				}
				extra=oddEvidence(oddGraph,chart,rule);
			}else if(graph&&squareMap(graphMap,squareProduct)){
				auto query=at(current.b),zero=scalar(ctx,arena.real_(0));
				auto root=primitive(arena.call(Builtin.sqrtR,[arena.real_(0)]),[query]);
				auto lt=arena.lt(arena.real_(0),arena.real_(0));
				extra=squareProduct;
				if(current.op==BoundOp.distributionGraphMass){
					auto positive=primitive(arena.inv(arena.real_(1)),[root]);
					next=primitive(arena.mask(arena.boolean(false),arena.real_(0)),
						[primitive(arena.le(arena.real_(0),arena.real_(0)),[zero,query]),positive]);
					rule=BindingRule.distributionSquareMass;
				}else{
					auto mul=scalarOperator(type(query),TensorOp.mul);
					auto negative=primitive(mul,[scalar(ctx,arena.real_(-1)),root]);
					auto twice=primitive(mul,[scalar(ctx,arena.real_(2)),root]);
					auto weight=primitive(arena.inv(arena.real_(1)),[twice]);
					BoundTerm branch(BoundTerm x){
						auto w=weight;
						if(maskedGraph){
							auto active=apply(at(nodes[current.a].a),x);
							w=primitive(arena.mask(arena.boolean(true),arena.real_(1)),[active,weight]);
						}
						return distribution(ctx,BoundOp.distributionScale,[w,distribution(ctx,BoundOp.distributionDirac,[x])]);
					}
					auto pair=distribution(ctx,BoundOp.distributionAdd,[branch(negative),branch(root)]);
					auto empty=distribution(ctx,BoundOp.distributionZero,[],type(query));
					auto critical=bottom(ctx,type(empty));
					if(maskedGraph){
						auto excluded=distribution(ctx,BoundOp.distributionScale,[zero,distribution(ctx,BoundOp.distributionDirac,[zero])]);
						critical=conditional(apply(at(nodes[current.a].a),zero),critical,excluded);
					}
					next=conditional(primitive(lt,[zero,query]),pair,conditional(primitive(lt,[query,zero]),empty,critical));
					if(maskedGraph) next=sequence(at(nodes[current.a].a),next);
					rule=maskedGraph?BindingRule.distributionMaskedSquare:BindingRule.distributionSquareGraph;
				}
			}else if(graph&&(squareBranch=powerMap(graphMap,true)).degree){
				if(current.op==BoundOp.distributionGraphMass){
					next=closedSquareDensity(squareBranch,at(current.b),extra);
					rule=BindingRule.distributionClosedSquare;
				}else{
					next=squareObservation(squareBranch,at(current.b),maskedGraph?at(nodes[current.a].a):BoundTerm.init,false,extra);
					rule=BindingRule.distributionAffineSquare;
				}
			}else if(graph){
				Rational slope,offset;
				if(affineMap(graphMap,slope,offset)){
					bool fibre=current.op!=BoundOp.distributionGraphMass;
					auto chart=affineChart(graphMap,slope,offset,fibre);
					auto jac=scalar(ctx,arena.at(nodes[chart.jacobian].data)),query=at(current.b);
					if(fibre){
						auto point=apply(lambda(at(chart.inverse)),query),weight=jac;
						if(maskedGraph){
							auto active=apply(at(nodes[current.a].a),point);
							weight=primitive(arena.mask(arena.boolean(true),arena.real_(1)),[active,jac]);
						}
						next=distribution(ctx,BoundOp.distributionScale,[weight,distribution(ctx,BoundOp.distributionDirac,[point])]);
						rule=maskedGraph?BindingRule.distributionMaskedAffine:BindingRule.distributionAffineFibre;
					}else{
						next=sequence(query,jac);
						rule=BindingRule.distributionAffineMass;
					}
					extra=cast(uint)affineCharts.length;
					affineCharts~=chart;
				}
			}
			if(current.op==BoundOp.distributionDensityAt){
				auto d=nodes[current.a],query=at(current.b);
				auto densityBranch=d.op==BoundOp.distributionPushforwardOn?oddMap(d.b):PowerMap.init;
				if(d.op==BoundOp.distributionLebesgue){ next=sequence(query,scalar(ctx,arena.real_(1))); rule=BindingRule.distributionDensityLebesgue; }
				else if(d.op==BoundOp.distributionInversePart){
					uint lower,upper;
					if(unitSquarePart(at(current.a),lower,upper)){
						auto inner=context(at(upper)),x=variable(inner,0);
						auto square=lambda(primitive(arena.pow(arena.real_(0),2),[x]));
						auto graphD=distribution(ctx,BoundOp.distributionPushforwardOn,[at(d.a),square]);
						next=distribution(ctx,BoundOp.distributionDensityAt,[graphD,query]);
						rule=BindingRule.distributionSquarePartDensity;
					}
				}
				else if(d.op==BoundOp.distributionRadiusImage&&nodes[d.a].op==BoundOp.scalar&&arena.isNumber(arena.at(nodes[d.a].data))){
					string form; auto j=sqrtRadiusScale(d.b,form);
					if(j!=Term.init){next=maskedInverseRoot(query,j); rule=BindingRule.distributionRadiusDensity;}
				}
				else if(d.op==BoundOp.distributionWeight&&nodes[d.b].op==BoundOp.distributionRadiusImage){
					auto chart=nodes[d.b]; bool casts,strict; string form;
					auto bound=sublevelBound(d.a,casts,strict),j=sqrtRadiusScale(chart.b,form);
					if(bound!=BoundTerm.init&&node(bound).op==BoundOp.scalar&&arena.isNumber(arena.at(node(bound).data))&&
						j!=Term.init&&nodes[chart.a].op==BoundOp.scalar&&arena.isNumber(arena.at(nodes[chart.a].data))){
						auto q=dropIndex(bound),zero=arena.real_(0);
						auto test=primitive(strict?arena.lt(zero,zero):arena.le(zero,zero),[query,q]);
						next=primitive(arena.mask(arena.boolean(true),arena.real_(1)),[test,maskedInverseRoot(query,j)]);
						rule=BindingRule.distributionCutoffDensity; extra=q.id;
					}
				}
				else if(d.op==BoundOp.distributionWeight&&nodes[d.b].op==BoundOp.distributionLebesgue){ next=apply(at(d.a),query); rule=BindingRule.distributionDensityWeight; }
				else if(densityBranch.degree){
					auto chart=sourceChart(densityBranch); BoundTerm point,weight;
					oddCoordinates(densityBranch,chart,query,point,weight);
					next=primitive(arena.mask(arena.boolean(true),arena.real_(1)),[apply(at(d.a),point),weight]);
					rule=BindingRule.distributionOddDensity; extra=oddEvidence(densityBranch,chart,rule);
				}else if(d.op==BoundOp.distributionPushforwardOn&&openUnitPredicate(d.a)&&squareMap(d.b,squareProduct)){
					next=openUnitDensity(query);
					if(node(query).op==BoundOp.bottom) next=bottom(ctx,type(query));
					rule=BindingRule.distributionRestrictedSquare; extra=squareProduct;
				}else if(d.op==BoundOp.distributionPushforwardOn&&(squareBranch=powerMap(d.b,true)).degree){
					if(nodes[d.a].op==BoundOp.lambda&&isTrue(nodes[d.a].a,true)){
						next=closedSquareDensity(squareBranch,query,extra);
						rule=BindingRule.distributionClosedSquare;
					}else{
						next=squareObservation(squareBranch,query,at(d.a),true,extra);
						rule=BindingRule.distributionAffineSquare;
					}
				}else if(d.op==BoundOp.distributionSum&&nodes[d.a].op==BoundOp.lambda){
					auto body=at(nodes[d.a].a),row=node(body);
					if(!naturalIndex(d.a)&&row.op==BoundOp.distributionDirac&&!depends(at(row.a),0)){
						auto atom=distribution(ctx,BoundOp.distributionDirac,[dropIndex(at(row.a))]);
						next=distribution(ctx,BoundOp.distributionDensityAt,[atom,query]);
						rule=BindingRule.distributionDensityInfiniteSeries;
					}else if(row.op==BoundOp.distributionDirac&&row.a==realIndex(variable(context(body),0)).id){
						auto point=realIndex(indexBuiltin(naturalIndex(d.a)?Builtin.floorN:Builtin.floorR,query));
						next=guard(awayFromAtom(point.id,query),scalar(ctx,arena.real_(0)));
						rule=BindingRule.distributionCountingDensity;
					}else{
						uint[] shift; foreach(i;0..this.depth(ctx)) shift~=i+1;
						FibreStep[] witness;
						if(extractFibre(body.id,rename(query,context(body),shift),witness)!=BoundTerm.init){
							auto root=witness[$-1];
							auto charge=summation(lambda(at(root.charge))),regular=summation(lambda(at(root.regular)));
							auto nonzero=primitive(arena.nonzero(arena.real_(0)),[charge]);
							next=guard(primitive(arena.not_(arena.boolean(false)),[nonzero]),regular);
							rule=BindingRule.distributionDensitySum;
							extra=cast(uint)fibres.length; fibres~=witness;
						}
					}
				}else if(d.op==BoundOp.distributionDirac){
					next=guard(awayFromAtom(d.a,query),scalar(ctx,arena.real_(0)));
					rule=BindingRule.distributionDensityDirac;
				}else if(d.op==BoundOp.distributionAdd){
					bool atomFirst=nodes[d.a].op==BoundOp.distributionDirac;
					auto atom=nodes[atomFirst?d.a:d.b],branch=atomFirst?d.b:d.a;
					IntegralSolution source;
					if(atom.op==BoundOp.distributionDirac&&densityBodies(branch,source.from)){
						next=guard(awayFromAtom(atom.a,query),retainedWeight(source.from,query));
						rule=BindingRule.distributionDensityAtomAdd;
						extra=cast(uint)integrals.length; integrals~=source;
					}
				}
				if(next==BoundTerm.init){
					FibreStep[] witness;
					next=extractFibre(current.a,query,witness);
					if(next!=BoundTerm.init){
						rule=BindingRule.distributionDensityFibre;
						extra=cast(uint)fibres.length; fibres~=witness;
					}
				}
				if(next==BoundTerm.init&&d.op==BoundOp.distributionAdd&&nodes[d.b].op==BoundOp.distributionWeight){
					auto weight=nodes[d.b];
					if(nodes[weight.a].op==BoundOp.lambda&&nodes[weight.b].op==BoundOp.distributionLebesgue){
						auto left=distribution(ctx,BoundOp.distributionDensityAt,[at(d.a),query]);
						next=primitive(scalarOperator(type(query),TensorOp.add),[left,apply(at(weight.a),query)]);
						rule=BindingRule.distributionDensityAddWeight;
					}
				}
			}
			if(current.op==BoundOp.conditional){
				bool missingPredicate(uint id){
					auto input=scalarBody(at(id),Term.init);
					if(input==Term.init||arena.view(input).op==Op.boolLit) return false;
					auto d=simplifyDomain(arena,input,[],Options(DensityMode.preserve,true));
					if(d.exhausted||d.output!=arena.boolean(false)) return false;
					extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(input,d); return true;
				}
				if(isTrue(current.a,true)){ next=at(current.b); rule=BindingRule.conditionalTrue; }
				else if(isTrue(current.a,false)){ next=at(current.c); rule=BindingRule.conditionalFalse; }
				else if(nodes[current.a].op==BoundOp.bottom){ next=bottom(ctx,type(at(result.output))); rule=BindingRule.conditionalBottom; }
				else if(steps<budget&&missingPredicate(current.a)){ next=bottom(ctx,type(at(result.output))); rule=BindingRule.conditionalUndefined; }
				else if(current.b==current.c){ next=sequence(at(current.a),at(current.b)); rule=BindingRule.conditionalSame; }
				else if(types[current.type]==scalarType(Sort.boolean)){
					auto predicate=at(current.a),neg=primitive(arena.not_(arena.boolean(false)),[predicate]);
					next=primitive(arena.or_(arena.boolean(false),arena.boolean(false)),[both(predicate,at(current.b)),both(neg,at(current.c))]); rule=BindingRule.conditionalBool;
				}else{
					Sort sort; bool numeric;
					foreach(candidate;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex])
						if(types[current.type]==scalarType(candidate)){ sort=candidate; numeric=true; break; }
					if(numeric){
						auto predicate=at(current.a),neg=primitive(arena.not_(arena.boolean(false)),[predicate]);
						auto zero=arena.number(Number(0),sort),mask=arena.mask(arena.boolean(false),zero);
						next=primitive(arena.add(zero,zero,true),[primitive(mask,[predicate,at(current.b)]),primitive(mask,[neg,at(current.c)])]);
						rule=BindingRule.conditionalNumeric;
					}
				}
			}
			if(next==BoundTerm.init&&current.op==BoundOp.limit&&nodes[current.a].op==BoundOp.lambda&&steps<budget){
				auto body=nodes[current.a].a; bool bottom=current.data!=0;
				if(limitTerms(body,bottom,false)!=BoundTerm.init){
					next=limitTerms(body,bottom); rule=BindingRule.limitTerms;
					extra=cast(uint)limits.length; limits~=LimitSolution(body,next.id,bottom);
				}
			}
			if(steps<budget&&current.op==BoundOp.summation&&nodes[current.a].op==BoundOp.lambda){
				bool swap;
				next=selectRealIndex(at(current.a),swap);
				if(next!=BoundTerm.init){ rule=BindingRule.sumRealIndex; extra=swap; }
			}
			if(next==BoundTerm.init&&(current.op==BoundOp.summation||current.op==BoundOp.finiteSum)){
				auto witness=missingGuardWitness(at(result.output));
				if(witness!=BoundTerm.init){
					next=bottom(ctx,types[current.type]);rule=BindingRule.sumMissingGuard;extra=witness.id;
				}
			}
			if(next==BoundTerm.init&&current.op==BoundOp.summation&&nodes[current.a].op==BoundOp.lambda){
				auto body=nodes[nodes[current.a].a],ty=types[current.type];
				if(steps<budget){
					auto rounded=roundSumBounds(at(nodes[current.a].a));
					if(rounded.output!=nodes[current.a].a){
						auto fn=inheritHint(at(current.a),lambda(at(rounded.output))),out_=summation(fn);
						auto fp=emit(BindingRule.congr,current.a,fn.id,rounded.proof);
						auto sp=emit(BindingRule.congr,result.output,out_.id,fp); ++steps;
						auto tail=visit(out_,depth+1),rest=emit(BindingRule.trans,result.output,tail.output,sp,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false);memo.set(t.id,result);return result;
					}
				}
				if(steps<budget){
					auto exposed=exposeSumMasks(at(nodes[current.a].a)),b=nodes[exposed.output];
					bool useful=boundedMask(b)||zeroSelector(b)||additive(b)&&boundedMask(nodes[b.a])&&boundedMask(nodes[b.b]);
					if(exposed.output!=nodes[current.a].a&&!useful&&additive(b)&&elementSort(ty)!=Sort.natural){
						foreach(id;[b.a,b.b]){
							auto piece=summation(inheritHint(at(current.a),lambda(at(id))));
							if(sumDefined(piece,depth+1).output!=uint.max){useful=true;break;}
						}
					}
					// A mask below a coercion is not read by the tail and interval rules:
					// (∑(x:ℤ). [0≤x]·(1/2)^x:ℝ) must sum like its rational summand.
					if(exposed.output!=nodes[current.a].a&&!useful&&b.op==BoundOp.primitive&&arena.view(arena.at(b.data)).op==Op.mask) useful=true;
					if(exposed.output!=nodes[current.a].a&&useful){
						auto fn=inheritHint(at(current.a),lambda(at(exposed.output))),out_=summation(fn);
						auto fp=emit(BindingRule.congr,current.a,fn.id,exposed.proof),sp=emit(BindingRule.congr,result.output,out_.id,fp);++steps;
						auto tail=visit(out_,depth+1),rest=emit(BindingRule.trans,result.output,tail.output,sp,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false);memo.set(t.id,result);return result;
					}
				}
				// Distribute finite-support summands without assuming arbitrary infinite linearity.
				if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==arena.view(scalarOperator(ty,TensorOp.add)).op&&arena.view(arena.at(body.data)).value==arena.view(scalarOperator(ty,TensorOp.add)).value&&type(variable(context(at(nodes[current.a].a)),0))==scalarType(Sort.natural)){
					auto left=nodes[body.a],right=nodes[body.b];

					if(boundedMask(left)&&boundedMask(right)){
						auto lp=nodes[left.a],rp=nodes[right.a],lo=dropIndex(at(lp.b)),hi=dropIndex(at(rp.b));
						bool li=arena.view(arena.at(lp.data)).value==Builtin.leN,ri=arena.view(arena.at(rp.data)).value==Builtin.leN;
						BoundTerm upper(BoundTerm n,bool inclusive){return inclusive?primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[n,scalar(ctx,arena.natural_(1))]):n;}
						next=primitive(arena.at(body.data),[finiteSum(inheritHint(at(current.a),lambda(at(left.b))),upper(lo,li)),finiteSum(inheritHint(at(current.a),lambda(at(right.b))),upper(hi,ri))]);
						extra=tuple(ctx,[lo,hi,scalar(ctx,arena.natural_((li?1:0)|(ri?2:0)))]).id;rule=BindingRule.sumBoundedAdd;
					}
				}
				if(next!=BoundTerm.init){}
				else if(body.op==BoundOp.bottom){
					next=bottom(ctx,ty);rule=BindingRule.sumMissingConstant;
				}else if(body.op==BoundOp.scalar&&arena.isNumber(arena.at(body.data))&&arena.number(arena.at(body.data)).zero){
					next=scalar(ctx,arena.number(Number(0),elementSort(ty))); rule=BindingRule.sumZero;
				}else if(!depends(at(nodes[current.a].a),0)){
					auto c=dropIndex(at(nodes[current.a].a)),sort=elementSort(ty),placeholder=arena.number(Number(0),sort);
					auto pred=primitive(arena.not_(arena.boolean(false)),[primitive(arena.nonzero(placeholder),[c])]);
					next=guard(pred,scalar(ctx,placeholder)); rule=BindingRule.sumConstant; extra=c.id;
				}else if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.builtin&&arena.view(arena.at(body.data)).value>=Builtin.powQN&&arena.view(arena.at(body.data)).value<=Builtin.powCN&&nodes[body.b].op==BoundOp.variable&&nodes[body.b].data==0&&!depends(at(body.a),0)){
					auto q=dropIndex(at(body.a)),sort=elementSort(ty),placeholder=arena.number(Number(0),sort);
					auto abs=sort==Sort.complex?primitive(arena.call(Builtin.absC,[placeholder]),[q]):primitive(arena.abs(arena.real_(0)),[sort==Sort.rational?primitive(arena.call(Builtin.castQR,[placeholder]),[q]):q]);
					auto pred=primitive(arena.lt(arena.real_(0),arena.real_(1)),[abs,scalar(ctx,arena.real_(1))]);
					auto neg=primitive(arena.mul(placeholder,placeholder,true),[scalar(ctx,arena.number(Number(-1),sort)),q]);
					auto den=primitive(arena.add(placeholder,placeholder,true),[scalar(ctx,arena.number(Number(1),sort)),neg]);
					next=guard(pred,primitive(arena.inv(placeholder),[den])); rule=BindingRule.sumGeometric; extra=q.id;
				}else if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.builtin&&arena.view(arena.at(body.data)).value>=Builtin.powQN&&arena.view(arena.at(body.data)).value<=Builtin.powCN&&!depends(at(body.a),0)){
					auto exponent=nodes[body.b];
					if(exponent.op==BoundOp.primitive&&arena.view(arena.at(exponent.data)).op==Op.builtin&&arena.view(arena.at(exponent.data)).value==Builtin.addN&&nodes[exponent.a].op==BoundOp.variable&&nodes[exponent.a].data==0&&!depends(at(exponent.b),0)){
						auto q=dropIndex(at(body.a)),offset=dropIndex(at(exponent.b)),power=arena.at(body.data),sort=elementSort(ty),placeholder=arena.number(Number(0),sort);
						auto abs=sort==Sort.complex?primitive(arena.call(Builtin.absC,[placeholder]),[q]):primitive(arena.abs(arena.real_(0)),[sort==Sort.rational?primitive(arena.call(Builtin.castQR,[placeholder]),[q]):q]);
						auto pred=primitive(arena.lt(arena.real_(0),arena.real_(1)),[abs,scalar(ctx,arena.real_(1))]);
						auto neg=primitive(arena.mul(placeholder,placeholder,true),[scalar(ctx,arena.number(Number(-1),sort)),q]);
						auto den=primitive(arena.add(placeholder,placeholder,true),[scalar(ctx,arena.number(Number(1),sort)),neg]);
						next=guard(pred,primitive(scalarOperator(ty,TensorOp.mul),[primitive(power,[q,offset]),primitive(arena.inv(placeholder),[den])])); rule=BindingRule.sumShiftGeometric; extra=tuple(ctx,[q,offset]).id;
					}
				}else if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.mask){
					auto pred=nodes[body.a];
					if(pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.builtin&&(arena.view(arena.at(pred.data)).value==Builtin.ltN||arena.view(arena.at(pred.data)).value==Builtin.leN)&&nodes[pred.a].op==BoundOp.variable&&nodes[pred.a].data==0&&!depends(at(pred.b),0)){
						auto bound=dropIndex(at(pred.b)); extra=bound.id;
						bool inclusive=arena.view(arena.at(pred.data)).value==Builtin.leN;
						auto end=inclusive?primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[bound,scalar(ctx,arena.natural_(1))]):bound;
						next=finiteSum(inheritHint(at(current.a),lambda(at(body.b))),end); rule=inclusive?BindingRule.sumRangeLe:BindingRule.sumRange;
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.builtin&&(arena.view(arena.at(pred.data)).value==Builtin.leN||arena.view(arena.at(pred.data)).value==Builtin.ltN)&&nodes[pred.b].op==BoundOp.variable&&nodes[pred.b].data==0&&!depends(at(pred.a),0)){
						auto bound=dropIndex(at(pred.a)),inner=context(at(body.b)); extra=bound.id;
						bool strict=arena.view(arena.at(pred.data)).value==Builtin.ltN;
						auto lo=strict?primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[at(pred.a),scalar(inner,arena.natural_(1))]):at(pred.a);
						BoundTerm[] values=[primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(inner,0),lo])];
						foreach(i;0..this.depth(ctx)) values~=variable(inner,i+1);
						auto shifted=substitute(at(body.b),inner,values);
						next=sequence(bound,summation(inheritHint(at(current.a),lambda(shifted)))); rule=strict?BindingRule.sumTailStrict:BindingRule.sumTailNatural;
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.and_){
						auto lower=nodes[pred.a],upper=nodes[pred.b],indexType=type(variable(context(at(body.a)),0));
						auto ns=indexType==scalarType(Sort.natural),le=ns?Builtin.leN:Builtin.leZ,lt=ns?Builtin.ltN:Builtin.ltZ;
						bool comparison(BoundNode x,Builtin op){ return x.op==BoundOp.primitive&&arena.view(arena.at(x.data)).op==Op.builtin&&arena.view(arena.at(x.data)).value==op; }
						if((comparison(lower,le)||comparison(lower,lt))&&(comparison(upper,lt)||comparison(upper,le))&&nodes[lower.b].op==BoundOp.variable&&nodes[lower.b].data==0&&nodes[upper.a].op==BoundOp.variable&&nodes[upper.a].data==0&&!depends(at(lower.a),0)&&!depends(at(upper.b),0)){
							bool strict=comparison(lower,lt),inclusive=comparison(upper,le);
							if(strict||inclusive){
								extra=tuple(ctx,[dropIndex(at(lower.a)),dropIndex(at(upper.b)),scalar(ctx,arena.natural_(cast(uint)strict+2*cast(uint)inclusive))]).id;
								auto inner=context(at(body.a)),zero=arena.number(Number(0),ns?Sort.natural:Sort.integer),one=scalar(inner,arena.number(Number(1),ns?Sort.natural:Sort.integer));
								auto l=strict?primitive(arena.add(zero,zero,true),[at(lower.a),one]):at(lower.a),u=inclusive?primitive(arena.add(zero,zero,true),[at(upper.b),one]):at(upper.b);
								auto lp=primitive(arena.call(le,[zero,zero]),[l,variable(inner,0)]),up=primitive(arena.call(lt,[zero,zero]),[variable(inner,0),u]);
								auto predicate=primitive(arena.and_(arena.boolean(false),arena.boolean(false)),[lp,up]);
								next=summation(inheritHint(at(current.a),lambda(primitive(arena.mask(arena.boolean(false),arena.number(Number(0),elementSort(ty))),[predicate,at(body.b)])))); rule=BindingRule.sumBounds;
							}else{
							auto lo=dropIndex(at(lower.a)),hi=dropIndex(at(upper.b));
							extra=tuple(ctx,[lo,hi]).id;
							BoundTerm unary(Builtin op,BoundTerm x){ return primitive(arena.call(op,[arena.number(Number(0),builtinInfo(op).args[0])]),[x]); }
							auto lz=ns?unary(Builtin.castNZ,lo):lo,uz=ns?unary(Builtin.castNZ,hi):hi;
							auto minus=scalar(ctx,arena.integer(-1)),neg=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[minus,lz]);
							auto difference=primitive(arena.add(arena.integer(0),arena.integer(0),true),[uz,neg]);
							auto count=unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,difference)));
							auto inner=push(ctx,scalarType(Sort.natural)),iv=variable(inner,0);
							BoundTerm[] values=[scalar(inner,arena.number(Number(0),ns?Sort.natural:Sort.integer))];
							foreach(i;0..this.depth(ctx)) values~=variable(inner,i+1);
							auto newlo=substitute(at(lower.a),inner,values);
							values[0]=primitive(arena.add(arena.number(Number(0),ns?Sort.natural:Sort.integer),arena.number(Number(0),ns?Sort.natural:Sort.integer),true),[ns?iv:unary(Builtin.castNZ,iv),newlo]);
							auto shifted=substitute(at(body.b),inner,values);
							next=finiteSum(inheritHint(at(current.a),lambda(shifted)),count); rule=BindingRule.sumInterval;
							}
						}
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive){
						auto indexType=type(variable(context(at(body.a)),0)),ns=indexType==scalarType(Sort.natural);
						auto pop=arena.view(arena.at(pred.data));
						bool inclusive=!ns&&pop.op==Op.builtin&&pop.value==Builtin.leZ&&nodes[pred.a].op==BoundOp.variable&&nodes[pred.a].data==0;
						bool lower=!inclusive&&pop.op==Op.builtin&&pop.value==(ns?Builtin.leN:Builtin.leZ),upper=!ns&&pop.op==Op.builtin&&(pop.value==Builtin.ltZ||inclusive);
						auto iv=lower?pred.b:pred.a,k=lower?pred.a:pred.b;
						if((lower||upper)&&nodes[iv].op==BoundOp.variable&&nodes[iv].data==0&&!depends(at(k),0)){
							auto endpoint=dropIndex(at(k)); extra=endpoint.id;
							auto inner=push(ctx,scalarType(Sort.natural)),j=variable(inner,0);
							BoundTerm unary(Builtin op,BoundTerm x){return primitive(arena.call(op,[arena.number(Number(0),builtinInfo(op).args[0])]),[x]);}
							auto zero=arena.number(Number(0),ns?Sort.natural:Sort.integer);
							BoundTerm add(BoundTerm a,BoundTerm b){return primitive(arena.add(zero,zero,true),[a,b]);}
							BoundTerm[] values=[scalar(inner,zero)];foreach(i;0..this.depth(ctx))values~=variable(inner,i+1);
							auto shiftedK=substitute(at(k),inner,values);
							if(ns) values[0]=add(j,shiftedK);
							else if(lower) values[0]=add(unary(Builtin.castNZ,j),shiftedK);
							else values[0]=add(inclusive?shiftedK:add(shiftedK,scalar(inner,arena.integer(-1))),primitive(arena.mul(zero,zero,true),[scalar(inner,arena.integer(-1)),unary(Builtin.castNZ,j)]));
							next=sequence(endpoint,summation(inheritHint(at(current.a),lambda(substitute(at(body.b),inner,values)))));rule=inclusive?BindingRule.sumTailInclusive:BindingRule.sumTail;
						}
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.builtin&&arena.view(arena.at(pred.data)).value==Builtin.nonzeroZ){
						auto cast_=nodes[pred.a];
						if(cast_.op==BoundOp.primitive&&arena.view(arena.at(cast_.data)).op==Op.builtin&&arena.view(arena.at(cast_.data)).value==Builtin.castNZ&&nodes[cast_.a].op==BoundOp.variable&&nodes[cast_.a].data==0){
							auto inner=context(at(body.b)),shift=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(inner,0),scalar(inner,arena.natural_(1))]);
							BoundTerm[] values=[shift];foreach(i;0..this.depth(ctx))values~=variable(inner,i+1);
							next=summation(inheritHint(at(current.a),lambda(substitute(at(body.b),inner,values))));rule=BindingRule.sumExcludeZero;
						}
					}
					if(next==BoundTerm.init&&elementSort(ty)!=Sort.natural&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.builtin&&arena.view(arena.at(pred.data)).value==Builtin.nonzeroZ){
						auto diff=nodes[pred.a];
						if(diff.op==BoundOp.primitive&&arena.view(arena.at(diff.data)).op==Op.builtin&&arena.view(arena.at(diff.data)).value==Builtin.addZ){
							auto cast_=nodes[diff.a];
							if(cast_.op==BoundOp.primitive&&arena.view(arena.at(cast_.data)).op==Op.builtin&&arena.view(arena.at(cast_.data)).value==Builtin.castNZ&&nodes[cast_.a].op==BoundOp.variable&&nodes[cast_.a].data==0&&!depends(at(diff.b),0)){
								auto c=dropIndex(at(diff.b));extra=c.id;
								BoundTerm unary(Builtin op,BoundTerm x){return primitive(arena.call(op,[arena.number(Number(0),builtinInfo(op).args[0])]),[x]);}
								auto negative=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[scalar(ctx,arena.integer(-1)),c]);
								auto plus=primitive(arena.add(arena.integer(0),arena.integer(0),true),[negative,scalar(ctx,arena.integer(1))]);
								BoundTerm count(BoundTerm x){return unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,x)));}
								auto lo=count(negative),hi=count(plus),inner=context(at(body.b));
								uint[] indices;foreach(i;0..this.depth(ctx))indices~=i+1;
								auto shift=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(inner,0),rename(hi,inner,indices)]);
								BoundTerm[] values=[shift];foreach(i;0..this.depth(ctx))values~=variable(inner,i+1);
								auto f=inheritHint(at(current.a),lambda(at(body.b))),g=inheritHint(at(current.a),lambda(substitute(at(body.b),inner,values)));
								next=primitive(scalarOperator(ty,TensorOp.add),[finiteSum(f,lo),summation(g)]);rule=BindingRule.sumExcludeOffset;
							}
						}
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.not_){
						auto nz=nodes[pred.a],indexType=type(variable(context(at(body.a)),0));
						if(nz.op==BoundOp.primitive&&arena.view(arena.at(nz.data)).op==Op.builtin&&(arena.view(arena.at(nz.data)).value==Builtin.nonzeroZ||arena.view(arena.at(nz.data)).value==Builtin.nonzeroN)){
							auto iv=nodes[nz.a];
							if(indexType==scalarType(Sort.natural)&&iv.op==BoundOp.primitive&&arena.view(arena.at(iv.data)).op==Op.builtin&&arena.view(arena.at(iv.data)).value==Builtin.castNZ) iv=nodes[iv.a];
							if(iv.op==BoundOp.variable&&iv.data==0){
								next=apply(inheritHint(at(current.a),lambda(at(body.b))),scalar(ctx,arena.number(Number(0),elementSort(indexType))));rule=BindingRule.sumDeltaZero;extra=arena.view(arena.at(nz.data)).value==Builtin.nonzeroN?1:0;
							}
						}
					}
					if(next==BoundTerm.init&&type(variable(context(at(body.a)),0))==scalarType(Sort.integer)&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.not_){
						auto nz=nodes[pred.a];
						if(nz.op==BoundOp.primitive&&arena.view(arena.at(nz.data)).op==Op.builtin&&arena.view(arena.at(nz.data)).value==Builtin.nonzeroZ){
							auto diff=nodes[nz.a];
							if(diff.op==BoundOp.primitive&&arena.view(arena.at(diff.data)).op==Op.builtin&&arena.view(arena.at(diff.data)).value==Builtin.addZ&&nodes[diff.a].op==BoundOp.variable&&nodes[diff.a].data==0&&!depends(at(diff.b),0)){
								auto c=dropIndex(at(diff.b)); extra=c.id;
								auto bound=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[scalar(ctx,arena.integer(-1)),c]);
								next=apply(inheritHint(at(current.a),lambda(at(body.b))),bound); rule=BindingRule.sumDeltaOffset;
							}
						}
					}
					if(next==BoundTerm.init){
						auto indexType=type(variable(context(at(body.a)),0)),indexSort=elementSort(indexType);
						auto idx=arena.variable(indexSort,cast(uint)arena.length),predicate=scalarBody(at(body.a),idx);
						BoundTerm find(uint id){
							auto t=at(id),v=node(t);
							if(type(t)==indexType&&!depends(t,0)){
								auto k=scalarBody(t,idx);
								if(k!=Term.init&&predicate==arena.equal(idx,k)) return t;
							}
							if(v.op==BoundOp.scalar) foreach(scalarId;arena.viewPostorder(arena.at(v.data))){
								auto k=arena.at(scalarId);
								if(arena.sort(k)==indexSort&&predicate==arena.equal(idx,k)) return scalar(context(t),k);

							}
							if(v.a!=uint.max){ auto r=find(v.a); if(r!=BoundTerm.init) return r; }
							return v.b!=uint.max?find(v.b):BoundTerm.init;
						}
						auto bound=predicate==Term.init?BoundTerm.init:find(body.a);
						if(bound!=BoundTerm.init){ next=apply(inheritHint(at(current.a),lambda(at(body.b))),dropIndex(bound)); rule=BindingRule.sumDelta; }
					}
				}
				// One known absolutely convergent side suffices for exact linearity,
				// including the domain of the still-opaque other side.
				if(next==BoundTerm.init&&additive(body)&&elementSort(ty)!=Sort.natural&&steps<budget){
					auto left=summation(inheritHint(at(current.a),lambda(at(body.a)))),right=summation(inheritHint(at(current.a),lambda(at(body.b))));
					foreach(side;0..2){
						auto known=sumDefined(side?right:left,depth+1);
						if(known.output==uint.max)continue;
						auto out_=primitive(arena.at(body.data),[left,right]);++steps;
						auto sp=emit(side?BindingRule.sumAddRight:BindingRule.sumAddLeft,result.output,out_.id,uint.max,uint.max,known.proof),tail=visit(out_,depth+1);
						auto rest=emit(BindingRule.trans,result.output,tail.output,sp,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false);memo.set(t.id,result);return result;
					}
				}
				if(next==BoundTerm.init){ next=solveFinite(at(result.output),extra,true); rule=BindingRule.rangeSolution; }
			}else if(next==BoundTerm.init&&current.op==BoundOp.finiteSum&&nodes[current.a].op==BoundOp.lambda){
				// Reduce applications introduced by recurrence solutions before
				// lifting the summand to another numeric type.
				Table!(uint,bool) inspected;
				bool betaRedex(uint id){
					if(inspected.get(id,false))return false;inspected.set(id,true);auto q=nodes[id];
					return q.op==BoundOp.apply&&nodes[q.a].op==BoundOp.lambda||q.a!=uint.max&&betaRedex(q.a)||q.b!=uint.max&&betaRedex(q.b)||q.c!=uint.max&&betaRedex(q.c);
				}
				if(steps<budget&&betaRedex(nodes[current.a].a)){
					auto f=visit(at(current.a),depth+1);
					if(f.output!=current.a){
						auto out_=finiteSum(at(f.output),at(current.b));++steps;
						auto proof=emit(BindingRule.congr,result.output,out_.id,f.proof,emit(BindingRule.refl,current.b,current.b));
						auto tail=visit(out_,depth+1),rest=emit(BindingRule.trans,result.output,tail.output,proof,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false);memo.set(t.id,result);return result;
					}
				}
				if(steps<budget){
					auto exposed=exposeSumMasks(at(nodes[current.a].a)),b=nodes[exposed.output];
					if(exposed.output!=nodes[current.a].a&&(boundedMask(b)||additive(b))){
						auto fn=inheritHint(at(current.a),lambda(at(exposed.output))),out_=finiteSum(fn,at(current.b));
						auto fp=emit(BindingRule.congr,current.a,fn.id,exposed.proof);
						auto sp=emit(BindingRule.congr,result.output,out_.id,fp,emit(BindingRule.refl,current.b,current.b));++steps;
						auto tail=visit(out_,depth+1),rest=emit(BindingRule.trans,result.output,tail.output,sp,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false);memo.set(t.id,result);return result;
					}
				}
				auto summand=nodes[nodes[current.a].a];
				if(steps<budget){
					auto rounded=roundSumBounds(at(nodes[current.a].a),true);
					if(rounded.output!=nodes[current.a].a){
						auto fn=inheritHint(at(current.a),lambda(at(rounded.output))),out_=finiteSum(fn,at(current.b));
						auto fp=emit(BindingRule.congr,current.a,fn.id,rounded.proof);
						auto bp=emit(BindingRule.refl,current.b,current.b);
						auto sp=emit(BindingRule.congr,result.output,out_.id,fp,bp);++steps;
						auto tail=visit(out_,depth+1),rest=emit(BindingRule.trans,result.output,tail.output,sp,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false);memo.set(t.id,result);return result;
					}
				}
				auto bound=nodes[current.b],sort=elementSort(types[current.type]);
				auto bop=summand.op==BoundOp.primitive?arena.view(arena.at(summand.data)):Node.init;
				bool elementary(uint id){
					auto q=nodes[id];
					bool leaf(Term t){foreach(i;arena.viewPostorder(t)){auto v=arena.view(arena.at(i));if(v.op==Op.builtin&&(v.value==Builtin.expR||v.value==Builtin.expC||v.value==Builtin.cisR||v.value==Builtin.expiC||v.value==Builtin.e))return true;}return false;}
					if((q.op==BoundOp.scalar||q.op==BoundOp.primitive)&&leaf(arena.at(q.data)))return true;
					return q.a!=uint.max&&elementary(q.a)||q.b!=uint.max&&elementary(q.b);
				}
				bool totalCoefficient(BoundTerm t){
					auto raw=scalarBody(t,arena.natural_(0));if(raw==Term.init)return false;
					foreach(i;arena.viewPostorder(raw)){
						auto v=arena.at(i),q=arena.view(v);
						if(arena.isNumber(v)||q.op==Op.variable||q.op==Op.add||q.op==Op.mul||q.op==Op.pow||q.op==Op.conj||q.op==Op.abs)continue;
						if(q.op==Op.builtin&&builtinInfo(cast(Builtin)q.value).total)continue;
						return false;
					}return true;
				}

				// Empty sums do not evaluate even an undefined guard condition.
				if(summand.op==BoundOp.guard&&!depends(at(summand.a),0)){
					auto condition=dropIndex(at(summand.a)),fn=inheritHint(at(current.a),lambda(at(summand.b)));
					auto nz=primitive(arena.nonzero(arena.natural_(0)),[at(current.b)]);
					auto empty=primitive(arena.not_(arena.boolean(false)),[nz]);
					auto allowed=primitive(arena.or_(arena.boolean(false),arena.boolean(false)),[empty,condition]);
					next=guard(allowed,finiteSum(fn,at(current.b)));rule=BindingRule.rangeGuard;extra=condition.id;
				}else if(summand.op==BoundOp.primitive&&(bop.op==Op.add||bop.op==Op.builtin&&(bop.value==Builtin.addN||bop.value==Builtin.addZ||bop.value==Builtin.addQ))&&
					(hasMask(nodes[current.a].a)||elementary(nodes[current.a].a)||
					 needsBindingScalar(nodes[current.a].a)&&(!depends(at(summand.a),0)||!depends(at(summand.b),0)))){
					auto f=inheritHint(at(current.a),lambda(at(summand.a))),g=inheritHint(at(current.a),lambda(at(summand.b)));
					next=primitive(arena.at(summand.data),[finiteSum(f,at(current.b)),finiteSum(g,at(current.b))]);rule=BindingRule.rangeAdd;
				}else if(summand.op==BoundOp.primitive&&bop.op==Op.mask){
					auto pred=nodes[summand.a];
					auto pop=pred.op==BoundOp.primitive?arena.view(arena.at(pred.data)):Node.init;
					bool lt=pop.op==Op.builtin&&pop.value==Builtin.ltN,ge=pop.op==Op.builtin&&pop.value==Builtin.leN;
					auto index=lt?pred.a:pred.b,k=lt?pred.b:pred.a;
					if((lt||ge)&&nodes[index].op==BoundOp.variable&&nodes[index].data==0&&!depends(at(k),0)){
						auto endpoint=dropIndex(at(k));extra=endpoint.id;
						BoundTerm unary(Builtin f,BoundTerm x){return primitive(arena.call(f,[arena.number(Number(0),builtinInfo(f).args[0])]),[x]);}
						BoundTerm realN(BoundTerm x){return unary(Builtin.castQR,unary(Builtin.castZQ,unary(Builtin.castNZ,x)));}
						auto nz=unary(Builtin.nonzeroZ,unary(Builtin.castNZ,at(current.b)));
						BoundTerm count,fn;
						if(lt){
							count=unary(Builtin.floorN,primitive(arena.call(Builtin.minR,[arena.real_(0),arena.real_(0)]),[realN(at(current.b)),realN(endpoint)]));
							fn=inheritHint(at(current.a),lambda(at(summand.b)));rule=BindingRule.rangeMaskLt;
						}else{
							auto negative=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[scalar(ctx,arena.integer(-1)),unary(Builtin.castNZ,endpoint)]);
							auto delta=primitive(arena.add(arena.integer(0),arena.integer(0),true),[unary(Builtin.castNZ,at(current.b)),negative]);
							count=unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,delta)));
							auto inner=context(at(summand.b)),shift=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(inner,0),at(k)]);
							BoundTerm[] values=[shift];foreach(i;1..this.depth(inner))values~=variable(inner,i);
							fn=inheritHint(at(current.a),lambda(substitute(at(summand.b),inner,values)));rule=BindingRule.rangeMaskGe;
						}
						next=primitive(arena.mask(arena.boolean(false),arena.number(Number(0),sort)),[nz,finiteSum(fn,count)]);
					}
				}
				if(next==BoundTerm.init&&bound.op==BoundOp.scalar&&!arena.isNumber(arena.at(bound.data))){
					auto source=arena.at(bound.data),domain=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true));
					if(!domain.exhausted&&domain.output==arena.boolean(false)){
						extra=cast(uint)scalarDomains.length;scalarDomains~=ScalarDomain(source,domain);
						next=bottom(ctx,types[current.type]);rule=BindingRule.rangeUndefinedBound;
					}
				}
				if(next==BoundTerm.init&&bound.op==BoundOp.bottom){ next=bottom(ctx,types[current.type]); rule=BindingRule.shortCircuit; }
				else if(next==BoundTerm.init&&bound.op==BoundOp.scalar&&arena.isNumber(arena.at(bound.data))&&arena.number(arena.at(bound.data)).re.small){
					auto count=arena.number(arena.at(bound.data)).re.integer;
					if(count==0){ next=scalar(ctx,arena.number(Number(0),sort)); rule=BindingRule.rangeZero; }
					else if(count<=64){
						auto prev=scalar(ctx,arena.natural_(cast(ulong)(count-1))),term=apply(at(current.a),prev),prefix=finiteSum(at(current.a),prev);
						next=primitive(scalarOperator(types[current.type],TensorOp.add),[prefix,term]); rule=BindingRule.rangeStep;
					}
				}
				if(next==BoundTerm.init&&!depends(at(nodes[current.a].a),0)&&!totalCoefficient(at(nodes[current.a].a))){
					// A zero-length sum does not evaluate its coefficient.
					auto coefficient=dropIndex(at(nodes[current.a].a)),count=at(current.b),z=arena.number(Number(0),sort);
					foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR,Builtin.castRC]) if(type(count)!=scalarType(sort))count=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[count]);
					auto nz=primitive(arena.nonzero(arena.natural_(0)),[at(current.b)]);
					auto product=primitive(scalarOperator(types[current.type],TensorOp.mul),[count,coefficient]);
					next=primitive(arena.mask(arena.boolean(false),z),[nz,product]);rule=BindingRule.rangeConstant;extra=coefficient.id;
				}
				// Do not restructure unresolved recurrence-domain sums merely
				// because their summand happens to have a constant factor.
				if(next==BoundTerm.init&&elementary(nodes[current.a].a)&&summand.op==BoundOp.primitive&&(bop.op==Op.mul||bop.op==Op.builtin&&(bop.value==Builtin.mulN||bop.value==Builtin.mulZ||bop.value==Builtin.mulQ))){
					foreach(reverse;0..2){
						auto c=at(reverse?summand.b:summand.a),term=at(reverse?summand.a:summand.b);if(depends(c,0))continue;
						auto coefficient=dropIndex(c),fn=inheritHint(at(current.a),lambda(term)),sum=finiteSum(fn,at(current.b));
						auto product=primitive(arena.at(summand.data),[coefficient,sum]),nz=primitive(arena.nonzero(arena.natural_(0)),[at(current.b)]);
						next=primitive(arena.mask(arena.boolean(false),arena.number(Number(0),sort)),[nz,product]);rule=BindingRule.rangeScale;extra=tuple(ctx,[coefficient,fn,scalar(ctx,arena.natural_(reverse))]).id;break;
					}
				}
				bool elementaryGeometric=summand.op==BoundOp.primitive&&bop.op==Op.builtin&&bop.value>=Builtin.powQN&&bop.value<=Builtin.powCN&&nodes[summand.b].op==BoundOp.variable&&nodes[summand.b].data==0&&!depends(at(summand.a),0)&&elementary(summand.a);
				if(next==BoundTerm.init&&elementaryGeometric&&sort==Sort.complex){
					auto q=dropIndex(at(summand.a)),count=at(current.b);
					uint fresh;foreach(id;0..arena.length){auto v=arena.view(arena.at(cast(uint)id));if(v.op==Op.variable&&v.value>=fresh){enforce(v.value<uint.max-1,"scalar variable limit exceeded");fresh=cast(uint)v.value+1;}}
					auto marker=arena.variable(Sort.natural,fresh),raw=scalarBody(q,marker),rawCount=scalarBody(count,marker);
					// Structural recognition is only a candidate search. The exported
					// theorem checks the actual ratio and count, including undefined n.
					Term unpack(Term t){auto v=arena.view(t);Term[] cs;foreach(i;0..v.arity)cs~=unpack(arena.viewChild(t,i));return cs.length?arena.viewRebuild(t,cs,true):t;}
					if(raw!=Term.init&&rawCount!=Term.init){
						auto ids=arena.viewPostorder(raw);bool phase;foreach(id;ids){auto v=arena.view(arena.at(id));if(v.op==Op.builtin&&v.value==Builtin.pi)phase=true;}
						auto v=arena.view(raw);
						if(phase&&ids.length<=128&&v.op==Op.builtin&&(v.value==Builtin.cisR||v.value==Builtin.expC)){
							raw=unpack(raw);
							bool exponential=v.value==Builtin.expC;
							foreach(rational;[true,false]){
								auto inv=rational?arena.castTo(arena.inv(arena.castTo(rawCount,Sort.rational)),Sort.real_):arena.inv(arena.castTo(rawCount,Sort.real_));
								auto target=exponential?Sort.complex:Sort.real_;
								Term[3] factors=[arena.castTo(inv,target),exponential?arena.complex(0,2):arena.real_(2),arena.castTo(arena.call(Builtin.pi,[]),target)];
								uint[3][6] orders=[[0u,1,2],[0u,2,1],[1u,0,2],[1u,2,0],[2u,0,1],[2u,1,0]];
								foreach(order,perm;orders)foreach(left;[false,true]){
									auto x=factors[perm[0]],y=factors[perm[1]],z=factors[perm[2]];
									auto angle=left?arena.mul(arena.mul(x,y,true),z,true):arena.mul(x,arena.mul(y,z,true),true);
									if(unpack(arena.call(cast(Builtin)v.value,[angle]))!=raw)continue;
									auto integer=primitive(arena.call(Builtin.castNZ,[arena.natural_(0)]),[count]);
									auto delta=primitive(arena.call(Builtin.addZ,[arena.integer(0),arena.integer(0)]),[integer,scalar(ctx,arena.integer(-1))]);
									auto pred=primitive(arena.not_(arena.boolean(false)),[primitive(arena.nonzero(arena.integer(0)),[delta])]);
									next=primitive(arena.mask(arena.boolean(false),arena.complex(1)),[pred,scalar(ctx,arena.complex(1))]);
									extra=cast(uint)(order*8+(rational?4:0)+(exponential?2:0)+(left?1:0));rule=BindingRule.rangeRootsUnity;break;
								}
								if(next!=BoundTerm.init)break;
							}
						}
					}
				}
				if(next==BoundTerm.init&&!elementaryGeometric&&(sort==Sort.rational||sort==Sort.real_||sort==Sort.complex)){ next=solveFinite(at(result.output),extra); rule=BindingRule.rangeSolution; }
				if(next==BoundTerm.init&&(sort==Sort.rational||sort==Sort.real_||sort==Sort.complex)){
					auto body=nodes[nodes[current.a].a];
					if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.builtin&&arena.view(arena.at(body.data)).value>=Builtin.powQN&&arena.view(arena.at(body.data)).value<=Builtin.powCN&&nodes[body.b].op==BoundOp.variable&&nodes[body.b].data==0&&!depends(at(body.a),0)){
						auto q=dropIndex(at(body.a)),countBound=at(current.b),zero=arena.number(Number(0),sort);
						BoundTerm unary(Term op,BoundTerm x){ return primitive(op,[x]); }
						BoundTerm add(BoundTerm x,BoundTerm y){ return primitive(arena.add(zero,zero,true),[x,y]); }
						BoundTerm mask(BoundTerm p,BoundTerm x){ return primitive(arena.mask(arena.boolean(false),zero),[p,x]); }
						BoundTerm not_(BoundTerm p){ return unary(arena.not_(arena.boolean(false)),p); }
						auto nz=unary(arena.nonzero(arena.natural_(0)),countBound),z=scalar(ctx,zero),minus=scalar(ctx,arena.number(Number(-1),sort));
						auto diff=add(q,minus),neq=unary(arena.nonzero(zero),diff),count=countBound;
						foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR,Builtin.castRC]) if(type(count)!=scalarType(sort)) count=unary(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),count);
						auto power=primitive(arena.call(cast(Builtin)arena.view(arena.at(body.data)).value,[zero,arena.natural_(0)]),[q,countBound]);
						auto formula=primitive(arena.mul(zero,zero,true),[add(power,minus),unary(arena.inv(zero),diff)]);
						next=add(mask(not_(nz),z),mask(nz,add(mask(not_(neq),count),mask(neq,formula)))); rule=BindingRule.rangeGeometric; extra=q.id;
					}
				}
				if(next==BoundTerm.init&&summand.op==BoundOp.primitive&&bop.op==Op.builtin&&(bop.value==Builtin.reC||bop.value==Builtin.imC)){
					auto fn=inheritHint(at(current.a),lambda(at(summand.a))),sum=finiteSum(fn,at(current.b));
					next=primitive(arena.at(summand.data),[sum]);rule=BindingRule.rangeProjection;
				}
				if(next==BoundTerm.init&&(sort==Sort.natural||sort==Sort.integer)){
					auto body=at(nodes[current.a].a),lift=body;
					foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR]){
						if(type(lift)==scalarType(builtinInfo(c).args[0])) lift=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[lift]);
					}
					auto lifted=finiteSum(inheritHint(at(current.a),lambda(lift)),at(current.b));
					next=primitive(arena.call(sort==Sort.natural?Builtin.floorN:Builtin.floorR,[arena.real_(0)]),[lifted]); rule=BindingRule.rangeLift;
				}
			}else if(domains&&current.op==BoundOp.apply&&nodes[current.a].op==BoundOp.bottom){
				next=bottom(ctx,type(at(result.output))); rule=BindingRule.fold;
			}else if(domains&&current.op==BoundOp.apply&&nodes[current.b].op==BoundOp.bottom){
				next=bottom(ctx,type(at(result.output))); rule=BindingRule.appBottom;
			}else if(current.op==BoundOp.apply&&nodes[current.a].op==BoundOp.lambda){
				if(steps<budget){ next=beta(at(nodes[current.a].a),at(current.b)); rule=BindingRule.beta; }
				else exhausted=true;
			}else if(domains&&current.op==BoundOp.apply&&nodes[current.a].op==BoundOp.fixed&&closedFixedArgument(at(current.b))){
				if(nodes[current.b].op==BoundOp.scalar){
					auto source=arena.at(nodes[current.b].data),d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true)); exhausted|=d.exhausted;
					if(d.output==arena.boolean(false)){
						extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d);
						next=bottom(ctx,type(at(result.output))); rule=BindingRule.appScalarUndefined;
					}
				}
				if(next==BoundTerm.init){
					if(steps<budget&&depth<128&&fixedSteps<64){
						// Substitute self and the argument before visiting the body.
						// Normalizing the intermediate lambda can unfold a recursive
						// call even when its enclosing branch will never be taken.
						auto f=at(current.a); BoundTerm[] env=[f];
						foreach(i;0..contexts[ctx.index].length) env~=variable(ctx,i);
						auto fn=substitute(at(node(f).a),ctx,env);
						++fixedSteps; next=beta(at(node(fn).a),at(current.b)); rule=BindingRule.fixedApp;
					}else exhausted=true;
				}
			}else if(current.op==BoundOp.sequence){
				if(domains&&nodes[current.a].op==BoundOp.bottom){ next=bottom(ctx,type(at(current.b))); rule=BindingRule.shortCircuit; }
				else if(current.a==current.b){ next=at(current.b); rule=BindingRule.seqSelf; }
				else if(totalScalar(at(current.a))){ next=at(current.b); rule=BindingRule.seqScalar; }
				else if(nodes[current.a].op==BoundOp.lambda){ next=at(current.b); rule=BindingRule.seqLam; }
				else if(domains){
					auto op=nodes[current.a].op;
					if(op==BoundOp.typeValue||op==BoundOp.set||op==BoundOp.global||op==BoundOp.domain||op==BoundOp.defined||op==BoundOp.holds){ next=at(current.b); rule=BindingRule.seqTotal; }
					else{ next=guard(defined(at(current.a)),at(current.b)); rule=BindingRule.seqGuard; }
				}
				if(next!=BoundTerm.init&&steps>=budget){ next=BoundTerm.init; exhausted=true; }
			}
			if(next==BoundTerm.init&&current.a!=uint.max&&conditionalStrict(current)){
				auto left=nodes[current.a];
				if(left.op==BoundOp.conditional){
					auto yes=rebuild(at(result.output),ctx,current.b==uint.max?[at(left.b)]:[at(left.b),at(current.b)]);
					auto no=rebuild(at(result.output),ctx,current.b==uint.max?[at(left.c)]:[at(left.c),at(current.b)]);
					next=conditional(at(left.a),yes,no); rule=current.b==uint.max?BindingRule.conditionalMap:BindingRule.conditionalLeft;
				}else if(current.b!=uint.max&&conditionalStrict(current,true)&&nodes[current.b].op==BoundOp.conditional){
					auto right=nodes[current.b];
					next=conditional(at(right.a),rebuild(at(result.output),ctx,[at(current.a),at(right.b)]),rebuild(at(result.output),ctx,[at(current.a),at(right.c)]));
					rule=BindingRule.conditionalRight;
				}
			}
			if(next==BoundTerm.init&&(additive(current)||multiplicative(current))&&
				(nodes[current.a].op==BoundOp.bottom||nodes[current.b].op==BoundOp.bottom)){
				next=bottom(ctx,types[current.type]);rule=additive(current)?BindingRule.addBottom:BindingRule.mulBottom;
			}
			// Lift guards through strict tuple constructors and projections so a
			// lambda can display the restriction once, on its parameter.
			if(domains&&next==BoundTerm.init&&(current.op==BoundOp.vectorCons||current.op==BoundOp.pair||current.op==BoundOp.get)){
				if(nodes[current.a].op==BoundOp.guard&&guardReady(nodes[current.a].a)){
					auto g=nodes[current.a]; next=guard(at(g.a),rebuild(at(result.output),ctx,[at(g.b),at(current.b)])); rule=BindingRule.guardLeft;
				}else if(nodes[current.b].op==BoundOp.guard&&guardReady(nodes[current.b].a)){
					auto g=nodes[current.b]; next=guard(at(g.a),rebuild(at(result.output),ctx,[at(current.a),at(g.b)])); rule=BindingRule.guardRight;
				}
			}
			if(domains&&next==BoundTerm.init&&(current.op==BoundOp.first||current.op==BoundOp.rest)&&nodes[current.a].op==BoundOp.guard&&guardReady(nodes[current.a].a)){
				auto g=nodes[current.a]; next=guard(at(g.a),rebuild(at(result.output),ctx,[at(g.b)])); rule=BindingRule.guardMap;
			}
			if(next==BoundTerm.init&&current.op==BoundOp.primitive&&type(at(result.output))==scalarType(Sort.real_)){
				auto op=arena.view(arena.at(current.data)).op;
				if(op==Op.add||op==Op.mul) foreach(left;[true,false]){
					auto lit=nodes[left?current.a:current.b],other=left?current.b:current.a;
					Number v;
					if(lit.op==BoundOp.scalar&&literalNumber(arena.at(lit.data),v)&&(op==Op.add?v.zero:v.one)&&needsBindingScalar(other)){
						next=at(other); rule=BindingRule.scalarNeutral; break;
					}
				}
			}
			if(domains&&next==BoundTerm.init&&(current.op==BoundOp.primitive||current.op==BoundOp.guard)&&current.a!=uint.max&&nodes[current.a].op==BoundOp.bottom){ next=bottom(ctx,type(at(result.output))); rule=BindingRule.shortCircuit; }
			if(domains&&next==BoundTerm.init){
				if(current.op==BoundOp.get&&nodes[current.b].op==BoundOp.scalar&&!totalScalar(at(current.b))){
					auto source=arena.at(nodes[current.b].data),d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true)); exhausted|=d.exhausted;
					if(d.output==arena.boolean(false)){
						extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d);
						next=bottom(ctx,type(at(result.output))); rule=BindingRule.getScalarUndefined;
					}
				}
				if(next==BoundTerm.init&&current.op==BoundOp.get&&nodes[current.a].op==BoundOp.vectorCons&&nodes[current.b].op==BoundOp.scalar&&arena.isNumber(arena.at(nodes[current.b].data))){
					auto index=arena.number(arena.at(nodes[current.b].data)).re,cons=nodes[current.a];
					if(index.small){
						next=index.integer?sequence(at(cons.a),get(at(cons.b),scalar(ctx,arena.natural_(cast(ulong)index.integer-1)))):sequence(at(cons.b),at(cons.a));
						rule=BindingRule.getCons;
					}
				}
				if(current.op==BoundOp.get&&(nodes[current.a].op==BoundOp.bottom||nodes[current.b].op==BoundOp.bottom)){
					next=bottom(ctx,type(at(result.output))); rule=BindingRule.getBottom;
				}else if(next==BoundTerm.init&&(current.op==BoundOp.tensor||current.op==BoundOp.get||current.op==BoundOp.first||current.op==BoundOp.rest)){
					SpectralSolution spectrum; next=spectral(at(result.output),spectrum);
					if(next!=BoundTerm.init){ extra=cast(uint)spectra.length; spectra~=spectrum; rule=BindingRule.tensorSpectral; }
					else{
						next=liftSpectrum(at(result.output),extra);
						if(next!=BoundTerm.init) rule=BindingRule.tensorSpectrumCast;
						else{ next=tensorEval(at(result.output)); if(next!=BoundTerm.init) rule=current.op==BoundOp.tensor&&current.data==TensorOp.power&&node(next).op==BoundOp.tensor?BindingRule.tensorPower:BindingRule.tensorEval; }
					}
				}
				if(next==BoundTerm.init&&current.op==BoundOp.fixed){
					auto body=at(current.a),v=pool.view(type(body)),inner=push(ctx,v.fields[0]);
					if(!depends(body,0)){
						BoundTerm[] values=[lambda(bottom(inner,v.fields[1]))];
						foreach(i;0..this.depth(ctx)) values~=variable(ctx,i);
						next=substitute(body,ctx,values); rule=BindingRule.fixedConstant;
					}else{
						auto b=node(at(node(body).a));
						if(b.op==BoundOp.apply&&nodes[b.a].op==BoundOp.variable&&nodes[b.a].data==1&&nodes[b.b].op==BoundOp.variable&&nodes[b.b].data==0){
							next=inheritHint(body,lambda(bottom(inner,v.fields[1]))); rule=BindingRule.fixedIdentity;
						}
					}
					if(next==BoundTerm.init){
						RecurrenceSolution solution; next=solveRecurrence(at(result.output),solution);
						if(next==BoundTerm.init) next=solveAffineRecurrence(at(result.output),solution);
						if(next==BoundTerm.init) next=solveLinearRecurrence(at(result.output),solution);
						if(next==BoundTerm.init) next=solvePrefixRecurrence(at(result.output),solution);
						if(next==BoundTerm.init) next=solveCoupledRecurrence(at(result.output),solution);
						if(next==BoundTerm.init) next=solveIndexedRecurrence(at(result.output),solution);
						if(next==BoundTerm.init) next=solveCFiniteRecurrence(at(result.output),solution);
						if(next==BoundTerm.init) next=solveDivideRecurrence(at(result.output),solution);
						if(next!=BoundTerm.init){ extra=cast(uint)solutions.length; solutions~=solution; rule=BindingRule.fixedRecurrence; }
					}
				}else if(current.op==BoundOp.guard&&isTrue(current.a,false)){
					next=bottom(ctx,type(at(current.b))); rule=BindingRule.shortCircuit;
				}else if(current.op==BoundOp.primitive&&current.b==uint.max&&nodes[current.a].op==BoundOp.bottom){
					auto op=arena.view(arena.at(current.data)).op;
					if(op==Op.not_||op==Op.builtin){ next=bottom(ctx,type(at(result.output))); rule=BindingRule.shortCircuit; }
				}else if(current.op==BoundOp.primitive&&nodes[current.a].op==BoundOp.scalar){
					auto op=arena.view(arena.at(current.data)).op;
					if(isTrue(current.a,false)&&(op==Op.mask||op==Op.and_)){
						auto ty=arena.sort(arena.at(current.data));
						next=scalar(ctx,ty==Sort.boolean?arena.boolean(false):arena.number(Number(0),ty)); rule=BindingRule.shortCircuit;
					}else if(isTrue(current.a,true)&&op==Op.or_){ next=scalar(ctx,arena.boolean(true)); rule=BindingRule.shortCircuit; }
					else if(isTrue(current.a,true)&&(op==Op.mask||op==Op.and_)||isTrue(current.a,false)&&op==Op.or_){ next=at(current.b); rule=BindingRule.shortCircuit; }
				}
				if(next==BoundTerm.init){
					if(current.op==BoundOp.set&&nodes[current.a].op==BoundOp.guard){
						next=set(holds(at(current.a))); rule=BindingRule.setHolds;
					}else if((current.op==BoundOp.lambda||current.op==BoundOp.set)&&steps<budget){
						next=pointwise(at(result.output),extra); rule=BindingRule.pointwise;
					}else if(current.op==BoundOp.scalar&&steps<budget&&!arena.isNumber(arena.at(current.data))){
						auto source=arena.at(current.data),value=simplify(arena,source,Options(DensityMode.preserve,true));
						auto embedded=arena.castTo(value.output,arena.sort(source));
						if(embedded!=source){
							auto d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true));
							auto predicate=arena.view(d.output);
							if(predicate.op==Op.boolLit&&predicate.value){
								extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d,value);
								next=guard(scalar(ctx,d.output),scalar(ctx,embedded)); rule=BindingRule.scalarSimplify;
							}
						}
						exhausted|=value.exhausted;
					}else if(current.op==BoundOp.primitive&&nodes[current.a].op==BoundOp.scalar&&
						(current.b==uint.max||nodes[current.b].op==BoundOp.scalar)){
						Term[] args=[arena.at(nodes[current.a].data)]; if(current.b!=uint.max) args~=arena.at(nodes[current.b].data);
						next=scalar(ctx,arena.viewRebuild(arena.at(current.data),args,true)); rule=BindingRule.fold;
					}else if(current.op==BoundOp.domain&&nodes[current.a].op==BoundOp.fixed){
						DomainRank rank;
						if(rankDomain(at(current.a),rank)){
							extra=cast(uint)ranks.length; ranks~=rank;
							auto predicate=rank.iterations.length?rank.iterations[$-1].output:rank.lower.output!=Term.init?rank.result.output:arena.boolean(true);
							next=inheritHint(at(nodes[current.a].a),set(restoreBody(predicate,push(ctx,scalarType(rank.sort)),arena.variable(rank.sort,rank.variable)))); rule=BindingRule.domainFixedTotal;
						}
					}else if(current.op==BoundOp.domain&&nodes[current.a].op==BoundOp.lambda){
						next=inheritHint(at(current.a),set(defined(at(nodes[current.a].a)))); rule=BindingRule.domainLam;
					}else if(current.op==BoundOp.domain&&nodes[current.a].op==BoundOp.bottom){
						next=set(scalar(push(ctx,pool.view(types[current.type]).fields[0]),arena.boolean(false))); rule=BindingRule.domainBottom;
					}else if(current.op==BoundOp.domain&&nodes[current.a].op==BoundOp.guard&&isTrue(nodes[current.a].a,false)){
						next=set(scalar(push(ctx,pool.view(types[current.type]).fields[0]),arena.boolean(false))); rule=BindingRule.domainGuardFalse;
					}else if(current.op==BoundOp.typeEq){
						if(current.a==current.b){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.typeEqSelf; }
						else if(nodes[current.a].op==BoundOp.typeValue&&nodes[current.b].op==BoundOp.typeValue&&concreteType(typeDenoted(at(current.a)))&&concreteType(typeDenoted(at(current.b)))){
							next=scalar(ctx,arena.boolean(nodes[current.a].data==nodes[current.b].data)); rule=BindingRule.typeEqValues;
						}
					}else if(current.op==BoundOp.equal){
						if(nodes[current.a].op==BoundOp.bottom){ next=bottom(ctx,scalarType(Sort.boolean)); rule=BindingRule.equalBottomLeft; }
						else if(nodes[current.b].op==BoundOp.bottom){ next=bottom(ctx,scalarType(Sort.boolean)); rule=BindingRule.equalBottomRight; }
						else if(current.a==current.b){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.equalSelf; }
						else if(constantSet(current.a,true)&&constantSet(current.b,false)){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.equalUnivEmpty; }
						else if(constantSet(current.a,false)&&constantSet(current.b,true)){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.equalEmptyUniv; }
					}else if(current.op==BoundOp.subset){
						if(current.a==current.b){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.subsetRefl; }
						else if(constantSet(current.a,false)){ next=sequence(at(current.b),scalar(ctx,arena.boolean(true))); rule=BindingRule.subsetEmpty; }
						else if(constantSet(current.b,true)){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.subsetUniv; }
						else if(constantSet(current.a,true)&&constantSet(current.b,false)){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.subsetUnivEmpty; }
					}else if(current.op==BoundOp.member&&nodes[current.a].op==BoundOp.domain&&nodes[nodes[current.a].a].op==BoundOp.fixed&&closedScalar(at(current.b))){
						next=sequence(at(current.b),defined(apply(at(nodes[current.a].a),at(current.b)))); rule=BindingRule.memberDomain;
					}else if(current.op==BoundOp.member&&nodes[current.a].op==BoundOp.set){
						auto reduction=beta(at(nodes[current.a].a),at(current.b));
						next=sequence(at(current.b),holds(at(node(reduction).b))); rule=BindingRule.memberSet;
					}else if(current.op==BoundOp.guard&&isTrue(current.a,true)){
						next=at(current.b); rule=BindingRule.guardTrue;
					}else if(current.op==BoundOp.guard&&nodes[current.b].op==BoundOp.guard){
						next=guard(both(at(current.a),at(nodes[current.b].a)),at(nodes[current.b].b)); rule=BindingRule.guardAnd;
					}else if(current.op==BoundOp.holds&&nodes[current.a].op==BoundOp.guard){
						next=both(holds(at(nodes[current.a].a)),holds(at(nodes[current.a].b))); rule=BindingRule.holdsGuard;
					}else if(current.op==BoundOp.defined){
						auto child=nodes[current.a]; Rational ratio;
						if(child.op==BoundOp.distributionRetry&&nonnegativeReal(child.a,ratio)&&atomicSeed(child.b)){
							next=defined(at(child.b)); rule=BindingRule.distributionDefinedRetry;
						}else if(child.op==BoundOp.distributionDirac){
							next=defined(at(child.a)); rule=BindingRule.distributionDefinedDirac;
						}else if(child.op==BoundOp.distributionAdd||child.op==BoundOp.distributionScale){
							next=both(defined(at(child.a)),defined(at(child.b))); rule=BindingRule.distributionDefinedBinary;
						}else if(child.op==BoundOp.distributionZero||child.op==BoundOp.distributionLebesgue){
							next=scalar(ctx,arena.boolean(true)); rule=BindingRule.seqTotal;
						}else if(child.op==BoundOp.conditional){
							next=holds(conditional(at(child.a),defined(at(child.b)),defined(at(child.c)))); rule=BindingRule.conditionalDefined;
						}else if(child.op==BoundOp.pair||child.op==BoundOp.vectorCons){
							next=both(defined(at(child.a)),defined(at(child.b))); rule=BindingRule.tensorDefined;
						}else if(child.op==BoundOp.unit||child.op==BoundOp.vectorNil){ next=scalar(ctx,arena.boolean(true)); rule=BindingRule.tensorEval; }
						else if(child.op==BoundOp.bottom){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.shortCircuit; }
						else if(child.op==BoundOp.fixed){ next=scalar(ctx,arena.boolean(true)); rule=BindingRule.definedFixed; }
						else if(child.op==BoundOp.typeValue||child.op==BoundOp.lambda||child.op==BoundOp.set||child.op==BoundOp.global||child.op==BoundOp.domain||child.op==BoundOp.defined||child.op==BoundOp.holds){
							next=scalar(ctx,arena.boolean(true)); rule=BindingRule.definedTotal;
						}else if(child.op==BoundOp.guard&&isTrue(child.a,false)){
							next=scalar(ctx,arena.boolean(false)); rule=BindingRule.definedGuardFalse;
						}else if(child.op==BoundOp.guard){
							next=both(holds(at(child.a)),defined(at(child.b))); rule=BindingRule.definedGuard;
						}else if(child.op==BoundOp.member||child.op==BoundOp.subset||child.op==BoundOp.equal){
							next=both(defined(at(child.a)),defined(at(child.b))); rule=child.op==BoundOp.member?BindingRule.definedMember:child.op==BoundOp.subset?BindingRule.definedSubset:BindingRule.definedEqual;
						}else if(child.op==BoundOp.primitive&&arena.view(arena.at(child.data)).op==Op.not_){
							next=defined(at(child.a)); rule=BindingRule.definedNot;
						}else if(child.op==BoundOp.apply){
							next=holds(member(domain(at(child.a)),at(child.b))); rule=BindingRule.definedApp;
						}
					}
				}
				if(current.op==BoundOp.holds&&nodes[current.a].op==BoundOp.bottom){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.shortCircuit; }
				if((current.op==BoundOp.defined||current.op==BoundOp.holds)&&nodes[current.a].op==BoundOp.scalar&&steps<budget){
					auto source=arena.at(nodes[current.a].data),r=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true));
					exhausted|=r.exhausted;
					extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,r);
					next=scalar(ctx,current.op==BoundOp.defined?r.output:arena.and_(r.output,source));
					rule=current.op==BoundOp.defined?BindingRule.scalarDomain:BindingRule.scalarHolds;
				}
				if(steps>=budget){
					if(next!=BoundTerm.init){
						if(rule==BindingRule.fixedRecurrence) --solutions.length;
						if(rule==BindingRule.tensorSpectral) --spectra.length;
						next=BoundTerm.init; exhausted=true;
					}
					if(current.op==BoundOp.scalar&&!totalScalar(at(result.output))||
						(current.op==BoundOp.defined||current.op==BoundOp.holds)&&nodes[current.a].op==BoundOp.scalar) exhausted=true;
				}
			}
			// Try the original binder first: scalar narrowing can hide a geometric
			// power behind casts, and normalizing masks can obscure their bounds.
			if(next==BoundTerm.init&&(current.op==BoundOp.summation||current.op==BoundOp.finiteSum||current.op==BoundOp.limit)&&steps<budget){
				auto function_=visit(at(current.a),depth+1);
				if(function_.output!=current.a){
					auto normalized=current.op==BoundOp.summation?summation(at(function_.output)):
						current.op==BoundOp.limit?limit(at(function_.output),current.data!=0):finiteSum(at(function_.output),at(current.b)); ++steps;
					auto bp=current.op==BoundOp.finiteSum?emit(BindingRule.refl,current.b,current.b):uint.max;
					auto step=emit(BindingRule.congr,result.output,normalized.id,function_.proof,bp),tail=visit(normalized,depth+1);
					auto rest=emit(BindingRule.trans,result.output,tail.output,step,tail.proof);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
			}
			// A scalar under a guard is simplified there: its own domain joins
			// the guard, so both sides are defined together. A total scalar was
			// simplified as a leaf; this one is partial.
			if(next==BoundTerm.init&&current.op==BoundOp.guard&&nodes[current.b].op==BoundOp.scalar&&steps<budget&&!arena.isNumber(arena.at(nodes[current.b].data))){
				auto source=arena.at(nodes[current.b].data),value=simplify(arena,source,Options(DensityMode.preserve,true));
				auto embedded=arena.castTo(value.output,arena.sort(source));
				exhausted|=value.exhausted;
				if(embedded!=source&&!value.exhausted){
					auto d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true));
					if(!d.exhausted){
						auto inner=guard(scalar(ctx,d.output),scalar(ctx,embedded)),guarded=guard(at(current.a),inner);
						auto index=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d,value); ++steps;
						auto simplified=emit(BindingRule.scalarSimplify,current.b,inner.id,uint.max,uint.max,index);
						auto step=emit(BindingRule.congr,result.output,guarded.id,emit(BindingRule.refl,current.a,current.a),simplified),tail=visit(guarded,depth+1);
						auto rest=emit(BindingRule.trans,result.output,tail.output,step,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false); memo.set(t.id,result); return result;
					}
				}
			}
			if(next==BoundTerm.init&&current.op==BoundOp.distributionRetry){
				Rational r;
				if(nodes[current.b].op==BoundOp.bottom){
					next=at(current.b);rule=BindingRule.distributionRetryMissing;
				}else if(nonnegativeReal(current.a,r)){
					AtomicVisits[uint] shapes;
					auto v=atomicVisits(current.b,shapes);
					if(v.kind==VisitKind.empty){
						next=distribution(ctx,BoundOp.distributionZero,[],pool.view(type(t)).fields[0]);
						rule=nodes[current.b].op==BoundOp.distributionZero?BindingRule.distributionRetryZero:BindingRule.distributionRetryEmpty;
					}else if(v.kind==VisitKind.one&&(r<Rational(1)||v.weight==Rational(0))){
						bool contracts=r<Rational(1);
						auto z=contracts?v.weight/(Rational(1)-r):Rational(0);
						next=distribution(ctx,BoundOp.distributionDirac,[at(v.point)]);
						if(z!=Rational(1)) next=distribution(ctx,BoundOp.distributionScale,[scalar(ctx,arena.real_(z)),next]);
						rule=contracts?BindingRule.distributionRetryPoint:BindingRule.distributionRetryZeroPoint;
					}else if(v.kind==VisitKind.one){
						auto point=at(v.point),inner=push(ctx,scalarType(Sort.integer));
						uint[] shift; foreach(i;0..contexts[ctx.index].length) shift~=i+1;
						auto atom=distribution(inner,BoundOp.distributionDirac,[rename(point,inner,shift)]);
						auto series=distribution(ctx,BoundOp.distributionSum,[hint(lambda(atom),"i")]);
						next=sequence(point,series); rule=BindingRule.distributionRetryInfinitePoint;
					}
				}
			}
			if(next==BoundTerm.init&&(current.op==BoundOp.distributionMass||current.op==BoundOp.distributionDensityAt)){
				bool mass=current.op==BoundOp.distributionMass;
				uint[] operations;
				auto loop=nodes[mass?observationInput(current.a,operations):current.a]; Rational r;
				if(loop.op==BoundOp.distributionRetry&&nonnegativeReal(loop.a,r)&&atomicSeed(loop.b)){
					if(mass){
						bool unbounded=r>=Rational(1);
						auto d=at(loop.b);
						if(!unbounded){
							auto gain=scalar(ctx,arena.real_(Rational(1)/(Rational(1)-r)));
							d=distribution(ctx,BoundOp.distributionScale,[gain,d]);
						}
						next=observedMass(d,operations);
						if(unbounded){
							auto zero=arena.real_(0);
							auto nonzero=primitive(arena.nonzero(zero),[next]);
							next=guard(primitive(arena.not_(arena.boolean(false)),[nonzero]),scalar(ctx,zero));
							rule=BindingRule.distributionRetryUnbounded;
						}else rule=operations.length?BindingRule.distributionRetryObservation:BindingRule.distributionRetryMass;
					}else{
						next=distribution(ctx,current.op,[at(loop.b),at(current.b)]); rule=BindingRule.distributionRetryDensity;
					}
				}
			}
			if(next!=BoundTerm.init&&steps>=budget){ next=BoundTerm.init; exhausted=true; }
			if(next!=BoundTerm.init){
				if(node(next).op==current.op&&(current.op==BoundOp.lambda||current.op==BoundOp.set||current.op==BoundOp.fixed)) inheritHint(at(result.output),next);
				++steps; auto step=emit(rule,result.output,next.id,predicateDomain,excludedZero,extra);
				chain~=RewriteFrame(t.id,result.output,result.proof,step);
				return Result(next.id,uint.max);
			}
			active.set(t.id,false); memo.set(t.id,result); return result;
		}
		// Follow successive rewrites in a loop. Child visits still use depth
		// first traversal. Rebuild exactly the same transitivity proofs and
		// memo entries once the last term in this chain has a result.
		Result normalizeChain(BoundTerm t,uint depth){
			RewriteFrame[] chain;
			auto result=visitOnce(t,depth,chain);
			while(result.proof==uint.max) result=visitOnce(at(result.output),++depth,chain);
			foreach_reverse(frame;chain){
				auto rest=emit(BindingRule.trans,frame.rebuilt,result.output,frame.step,result.proof);
				result.proof=emit(BindingRule.trans,frame.original,result.output,frame.congruence,rest);
				active.set(frame.original,false); memo.set(frame.original,result);
			}
			return result;
		}
		visit=&normalizeChain;
		auto result=visit(term,0); return BindingResult(term,at(result.output),exhausted,steps,proofs,result.proof,scalarDomains,solutions,ranks,spectra,sums,integrals,fibres,affineCharts,covers,limits,coordinates);
	}

	/// A scalar refinement can fill a hole in a pointwise observation. If its
	/// definedness changes, keep the source domain as a checked binding guard.
	bool protectObservationDomain(ref BindingResult r,Term source,ScalarResult candidate,Options options){
		auto ty=arena.sort(source),embedded=arena.castTo(candidate.output,ty);
		if(embedded==source) return false;
		bool pointwise;
		foreach(step;r.proofs){
			auto op=nodes[step.from].op;
			if(op==BoundOp.distributionDensityAt||op==BoundOp.distributionGraphMass||
				op==BoundOp.distributionGraphFibre||op==BoundOp.distributionMaskedGraph){ pointwise=true; break; }
		}
		if(!pointwise) return false;
		auto opts=Options(DensityMode.preserve,true);
		auto domain=simplifyDomain(arena,source,[],opts);
		if(domain.output==arena.boolean(true)) return false;
		auto targetDomain=simplifyDomain(arena,embedded,[],Options.init);
		if(domain.output==targetDomain.output) return false;

		// Binding reductions are unconditional, including in a REPL session
		// with assumptions. Only an unconditional value proof can go here.
		options.trace=true;
		auto value=candidate.traced&&!candidate.assumptions.length?candidate:simplify(arena,source,[],options);
		auto ctx=context(r.output),index=cast(uint)r.domains.length;
		r.domains~=ScalarDomain(source,domain,value);
		void extend(BindingRule rule,BoundTerm to,uint extra=uint.max){
			auto proofIndex=cast(uint)r.proofs.length;
			r.proofs~=BindingStep(rule,r.output.id,to.id,uint.max,uint.max,extra);
			r.proofs~=BindingStep(BindingRule.trans,r.input.id,to.id,r.proof,proofIndex);
			r.proof=proofIndex+1; r.output=to; ++r.steps;
		}
		auto leaf=scalar(ctx,source);
		if(r.output!=leaf) extend(BindingRule.fold,leaf);
		auto output=scalar(ctx,arena.castTo(value.output,ty));
		extend(BindingRule.scalarSimplify,guard(scalar(ctx,domain.output),output),index);
		if(domain.output==arena.boolean(false)) extend(BindingRule.shortCircuit,bottom(ctx,type(output)));
		return true;
	}

	Term lower(BoundTerm term){
		enforce(context(term)==empty(),"cannot lower an open binding");
		Table!(uint,uint) memo;
		Term visit(BoundTerm t){
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return arena.at(old);
			auto n=node(t); Term result;
			if(n.op==BoundOp.scalar) result=arena.at(n.data);
			else{
				enforce(n.op==BoundOp.primitive,"residual function or argument domain");
				Term[] args=[visit(at(n.a))]; if(n.b!=uint.max) args~=visit(at(n.b));
				result=arena.viewRebuild(arena.at(n.data),args,true);
			}
			memo.set(t.id,result.id); return result;
		}
		return visit(term);
	}
	private string massObserver(uint[] operations,bool countable){
		auto prefix="Distribution.Atomic."~(countable?"CountableObservation.":"Observation.");
		string observer=prefix~"mass";
		foreach(id;operations){
			auto op=nodes[id]; bool weight=op.op==BoundOp.distributionWeight;
			auto theorem=weight?"weight":types[op.type]==pool.distribution(scalarType(Sort.real_))?"realBind":"bind";
			observer="("~prefix~theorem~" "~observer~" ("~name(weight?op.a:op.b)~".eval ξ ρ))";
		}
		return observer;
	}
	private string name(uint id){ return "(t"~to!string(id)~(dependent_?" δ":"")~" γ)"; }
	private string ctxName(uint id){ auto s="c"~to!string(id); return dependent_?"("~s~" δ)":s; }
	private Term scalarOperator(TypeId t,TensorOp op){
		auto x=arena.variable(elementSort(t),0); return op==TensorOp.add?arena.add(x,x,true):arena.mul(x,x,true);
	}
	private string tensorOperation(TypeId t,TensorOp op){
		auto v=pool.view(t);
		if(v.kind==TypeKind.vector) return "(Tensor.zipValue "~tensorOperation(v.fields[0],op)~" "~v.dimension.lean~")";
		return leanValueOperation(arena,scalarOperator(t,op));
	}
	private string tensorDomainOperation(TypeId t,TensorOp op){
		auto v=pool.view(t);
		if(v.kind==TypeKind.vector) return "(TensorDomains.zip "~tensorOperation(v.fields[0],op)~" "~tensorDomainOperation(v.fields[0],op)~" "~v.dimension.lean~")";
		auto n=arena.view(scalarOperator(t,op));
		if(n.op==Op.builtin) return "(TensorDomains.builtin2 Functions."~builtinInfo(cast(Builtin)n.value).code~" (fun _ _ => True.intro))";
		return op==TensorOp.add?"TensorDomains.add":"TensorDomains.mul";
	}
	private string tensorDomainProof(BoundNode n){
		auto op=cast(TensorOp)n.data,ty=type(at(n.a)),v=pool.view(ty);
		if(op==TensorOp.add||op==TensorOp.mul) return tensorDomainOperation(ty,op);
		auto element=typeLeaf(ty),add=tensorOperation(element,TensorOp.add),mul=tensorOperation(element,TensorOp.mul);
		auto proofs=" "~tensorDomainOperation(element,TensorOp.add)~" "~tensorDomainOperation(element,TensorOp.mul),zero=tensorLiteral(element,0);
		if(op==TensorOp.dot) return "(TensorDomains.dot "~add~" "~mul~" "~(element==scalarType(Sort.complex)?"Value.conj":"id")~proofs~" "~(element==scalarType(Sort.complex)?"TensorDomains.conjugate":"TensorDomains.identity")~" "~zero~" "~v.dimension.lean~")";
		if(op==TensorOp.power) return "(TensorDomains.power "~add~" "~mul~proofs~" "~zero~" "~tensorLiteral(element,1)~" "~v.dimension.lean~")";
		auto dimensions=v.dimension.lean~" "~pool.view(v.fields[0]).dimension.lean;
		if(op==TensorOp.matmul) dimensions~=" "~pool.view(pool.view(type(at(n.b))).fields[0]).dimension.lean;
		return "(TensorDomains."~(op==TensorOp.matmul?"matmul":"matvec")~" "~add~" "~mul~proofs~" "~zero~" "~dimensions~")";
	}
	private string tensorLiteral(TypeId t,uint n){
		auto s=to!string(n),sort=elementSort(t);
		if(sort==Sort.rational) return "("~s~" / 1 : ℚ)";
		if(sort==Sort.real_) return "(("~s~" : ℤ) : ℝ)";
		if(sort==Sort.complex) return "((("~s~" : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I)";
		return s;
	}
	// A sum of presentations over ℕ is, in the model, the sum over ℤ whose terms
	// at negative indices are zero; its laws are stated separately.
	private bool naturalIndex(uint function_){ return pool.view(type(at(function_))).fields[0]==scalarType(Sort.natural); }
	private string valueOperation(BoundNode n){
		final switch(n.op){
			case BoundOp.distributionInverseCover:return "Distribution.GraphFibre.Coordinates.value";
			case BoundOp.distributionInversePart:return "Distribution.GraphFibre.Coordinates.restricted";
			case BoundOp.distributionRadiusImage:return "Distribution.GraphFibre.radiusImageValue";
			case BoundOp.distributionMaskedGraph:return "Distribution.GraphFibre.maskedKernel";
			case BoundOp.distributionGraphFibre:return "Distribution.GraphFibre.value";
			case BoundOp.distributionGraphMass:return "Distribution.GraphFibre.marginal";
			case BoundOp.distributionBind:return pool.view(type(at(n.b))).fields[1]==pool.distribution(scalarType(Sort.real_))?
				"Distribution.GraphFibre.realBindValue":"Distribution.bindValue";
			case BoundOp.distributionPushforwardOn:
				return pool.view(type(at(n.b))).fields[1]==scalarType(Sort.real_)?
					"Distribution.GraphFibre.realPushforwardOnValue":"Distribution.pushforwardOnValue";
			case BoundOp.distributionDirac:return "Distribution.diracValue";
			case BoundOp.distributionAdd:return "Distribution.addValue";
			case BoundOp.distributionFixed:return "Distribution.Atomic.fixedValue";
			case BoundOp.distributionRetry:return "Distribution.Atomic.retryValue";
			case BoundOp.distributionScale:return "Distribution.scaleValue";
			case BoundOp.distributionWeight:return "Distribution.weightValue";
			case BoundOp.distributionIntegral:return pool.view(type(at(n.a))).fields[1]==pool.distribution(scalarType(Sort.real_))?
				"Distribution.GraphFibre.realIntegralValue":"Distribution.integralValue";
			case BoundOp.distributionSum:return naturalIndex(n.a)?"Distribution.sumNatValue":"Distribution.sumValue";
			case BoundOp.distributionMass:return "Distribution.massValue";
			case BoundOp.distributionDensityAt:return "Distribution.densityAtValue";
			case BoundOp.distributionZero,BoundOp.distributionLebesgue:assert(0);
			case BoundOp.conditional:return "Binding.conditionalValue";
			case BoundOp.pair:return "Tensor.pairValue";
			case BoundOp.vectorCons:return "Tensor.consValue";
			case BoundOp.first:return "(fun x => x.map Prod.fst)";
			case BoundOp.rest:return "(fun x => x.map Prod.snd)";
			case BoundOp.get:return "Tensor.getValue";
			case BoundOp.tensor:
				auto op=cast(TensorOp)n.data,ty=types[nodes[n.a].type],v=pool.view(ty);
				if(op==TensorOp.add||op==TensorOp.mul) return tensorOperation(ty,op);
				auto element=typeLeaf(ty),add=tensorOperation(element,TensorOp.add),mul=tensorOperation(element,TensorOp.mul),zero=tensorLiteral(element,0);
				if(op==TensorOp.dot) return "(Tensor.dotValue "~add~" "~mul~" "~(element==scalarType(Sort.complex)?"Value.conj":"id")~" "~zero~" "~v.dimension.lean~")";
				auto row=pool.view(v.fields[0]);
				if(op==TensorOp.power) return "(Tensor.matrixPowerValue "~add~" "~mul~" "~zero~" "~tensorLiteral(element,1)~" "~v.dimension.lean~")";
				auto dimensions=v.dimension.lean~" "~row.dimension.lean;
				if(op==TensorOp.matmul) dimensions~=" "~pool.view(pool.view(types[nodes[n.b].type]).fields[0]).dimension.lean;
				return "(Tensor."~(op==TensorOp.matmul?"matmulValue":"matvecValue")~" "~add~" "~mul~" "~zero~" "~dimensions~")";
			case BoundOp.primitive:return leanValueOperation(arena,arena.at(n.data));
			case BoundOp.member:return "Binding.memberValue";
			case BoundOp.subset:return "Binding.subsetValue";
			case BoundOp.typeEq:return "Binding.typeEqValue";
			case BoundOp.equal:return "Binding.equalValue";
			case BoundOp.finiteSum:return "Summation.rangeValue";
			case BoundOp.summation:
				auto sort=elementSort(types[n.type]);
				return "(Summation.value "~(sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm")~")";
			case BoundOp.limit:return "(Limit.value Filter."~(n.data?"atBot":"atTop")~")";
			case BoundOp.domain:return "Binding.inputDomain";
			case BoundOp.defined:return "Binding.definedValue";
			case BoundOp.holds:return "Binding.holdsValue";
			case BoundOp.guard:return "Binding.guardValue";
			case BoundOp.scalar,BoundOp.variable,BoundOp.lambda,BoundOp.apply,BoundOp.sequence,BoundOp.global,BoundOp.set,BoundOp.typeValue,BoundOp.bottom,BoundOp.fixed,BoundOp.unit,BoundOp.vectorNil:assert(0);
		}
	}
	private string leanType(TypeId t){
		auto v=pool.view(t);
		if(v.kind==TypeKind.distribution) return "(.distribution "~leanType(v.fields[0])~")";
		if(v.kind==TypeKind.unit) return ".unit";
		if(v.kind==TypeKind.vector) return "(.vector "~leanType(v.fields[0])~" "~v.dimension.lean~")";
		if(v.kind==TypeKind.tuple) return "(.pair "~leanType(v.fields[0])~" "~leanType(pool.tuple(v.fields[1..$]))~")";
		if(v.kind==TypeKind.set) return "(.set "~leanType(v.fields[0])~")";
		if(v.kind==TypeKind.function_) return "(.arrow "~leanType(v.fields[0])~" "~leanType(v.fields[1])~")";
		if(v.kind==TypeKind.type_) return ".type";
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean])
			if(t==scalarType(s)) return "(.scalar ."~leanSort(s)~")";
		throw new Exception("unsupported binding type");
	}
	private string leanWitness(TypeId t){
		auto v=pool.view(t);
		if(v.kind==TypeKind.distribution) return "Distribution.Presentation.zero";
		if(v.kind==TypeKind.unit) return "()";
		if(v.kind==TypeKind.vector) return "(fun _ => "~leanWitness(v.fields[0])~")";
		if(v.kind==TypeKind.tuple) return "("~leanWitness(v.fields[0])~", "~leanWitness(pool.tuple(v.fields[1..$]))~")";
		return v.kind==TypeKind.type_?"Binding.Ty.type":v.kind==TypeKind.function_?"(fun _ => none)":v.kind==TypeKind.set?"∅":v.kind==TypeKind.boolean?"false":"0";
	}
	private string tensorEvaluationProof(uint from,uint target){
		uint[] leaves; Table!(uint,bool) seen;
		void collect(uint id){
			if(seen.get(id,false)) return; seen.set(id,true); auto n=nodes[id];
			if(n.op==BoundOp.scalar&&arena.view(arena.at(n.data)).arity&&literalData(at(id))) leaves~=id;
			if(n.a!=uint.max) collect(n.a); if(n.b!=uint.max) collect(n.b); if(n.c!=uint.max) collect(n.c);
		}
		collect(from);
		struct Total{ string value,proof; }
		Total total(Term t){
			auto n=arena.view(t);
			auto source="n"~to!string(t.id)~".eval ξ";
			if(!n.arity){
				auto v="(("~source~").getD "~(n.sort==Sort.boolean?"false":"0")~")";
				return Total(v,"(show "~source~" = some "~v~" from rfl)");
			}
			enforce(n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castRC,"unsupported total tensor scalar");
			auto child=total(arena.viewChild(t,0)),f="Functions."~builtinInfo(cast(Builtin)n.value).code;
			auto v="("~f~".value "~child.value~")";
			return Total(v,"(show "~source~" = some "~v~" from Eq.trans (congrArg "~f~".apply "~child.proof~") (Tensor.apply_some "~f~" "~child.value~" True.intro))");
		}
		string[] values; foreach(id;leaves) values~="("~name(id)~".eval ξ ρ)";
		string value(uint id){
			foreach(i,leaf;leaves) if(id==leaf) return values[i]; auto n=nodes[id];
			if(n.a==uint.max) return "("~name(id)~".eval ξ ρ)";
			return "("~valueOperation(n)~" "~value(n.a)~(n.b==uint.max?"":" "~value(n.b))~(n.c==uint.max?"":" "~value(n.c))~")";
		}
		string prove(size_t i){
			if(i==leaves.length) return "rfl";
			auto id=leaves[i],v=total(arena.at(nodes[id].data)); values[i]="w"~to!string(i);
			auto predicate="(fun "~values[i]~" : Option ("~leanType(type(at(id)))~" : Binding.Ty).denote => "~value(from)~" = "~value(target)~")";
			values[i]="(some "~v.value~")"; return "(Eq.mpr (congrArg "~predicate~" "~v.proof~") "~prove(i+1)~")";
		}
		return ".ofEq (fun ξ ρ => "~prove(0)~")";
	}
	private string exportDependent(BindingResult result){
		enforce(depth(context(result.input))==0,"dependent certificates require a closed context");
		string code="import QSym\nnamespace QSym.DependentCertificate\n";
		Table!(uint,bool) scalarNeeded,visited;
		void collect(BoundTerm t){
			if(visited.get(t.id,false)) return; visited.set(t.id,true); auto n=node(t);
			if(n.op==BoundOp.scalar||n.op==BoundOp.primitive) foreach(id;arena.viewPostorder(arena.at(n.data))) scalarNeeded.set(id,true);
			if(n.a!=uint.max) collect(at(n.a)); if(n.b!=uint.max) collect(at(n.b)); if(n.c!=uint.max) collect(at(n.c));
		}
		collect(result.input); collect(result.output);
		foreach(i;0..arena.length) if(scalarNeeded.get(cast(uint)i,false)) code~=leanSyntaxCode(arena,arena.at(cast(uint)i));
		string dim(Dimension d,string[] vars){
			if(d.index!=uint.max){ enforce(d.index<vars.length,"unbound exported dimension"); return vars[d.index]; }
			if(d.op.length) return "("~dim(d.left,vars)~d.op~dim(d.right,vars)~")";
			return replace(d.lean,"δ","ξ.natural");
		}
		string quotedDim(Dimension d,string[] vars,uint depth){
			bool bound; d.map((uint i){ bound|=i<depth; return Dimension.bound(i); });
			if(!bound){ auto closed=d.map((uint i)=>Dimension.bound(i-depth)); return "(.literal "~dim(closed,vars)~")"; }
			if(d.index!=uint.max) return "(.bound "~to!string(d.index)~")";
			return "(."~(d.op=="+"?"add":d.op=="*"?"mul":"pow")~" "~quotedDim(d.left,vars,depth)~" "~quotedDim(d.right,vars,depth)~")";
		}
		string quotedType(TypeId t,string[] vars,uint depth=0){
			auto v=pool.view(t);
			if(v.kind==TypeKind.unit) return ".unit";
			if(v.kind==TypeKind.type_) return ".type";
			if(v.kind==TypeKind.vector) return "(.vector "~quotedType(v.fields[0],vars,depth)~" "~(depth?quotedDim(v.dimension,vars,depth):dim(v.dimension,vars))~")";
			if(v.kind==TypeKind.tuple) return "(.pair "~quotedType(v.fields[0],vars,depth)~" "~quotedType(pool.tuple(v.fields[1..$]),vars,depth)~")";
			if(v.kind==TypeKind.set) return "(.set "~quotedType(v.fields[0],vars,depth)~")";
			if(v.kind==TypeKind.distribution) return "(.distribution "~quotedType(v.fields[0],vars,depth)~")";
			if(v.kind==TypeKind.pi) return "(.piNat "~quotedType(v.fields[1],vars,depth+1)~")";
			if(v.kind==TypeKind.function_) return "(.arrow "~quotedType(v.fields[0],vars,depth)~" "~quotedType(v.fields[1],vars,depth)~")";
			foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean]) if(t==scalarType(s)) return "(.scalar ."~leanSort(s)~")";
			throw new Exception("unsupported dependent type");
		}
		string ty(TypeId t,string[] vars){ return "("~quotedType(t,vars)~" : Binding.Ty).denote"; }
		string tensorOp(TypeId t,TensorOp op,string[] vars){
			auto v=pool.view(t);
			return v.kind==TypeKind.vector?"(Tensor.zipValue "~tensorOp(v.fields[0],op,vars)~" "~dim(v.dimension,vars)~")":leanValueOperation(arena,scalarOperator(t,op));
		}
		string term(BoundTerm t,string[] vars) @safe{
			auto n=node(t);
			string child(uint id){ return term(at(id),vars); }
			switch(n.op){
				case BoundOp.distributionZero:return "Distribution.zeroValue";
				case BoundOp.distributionLebesgue:return "Distribution.lebesgueValue";
				case BoundOp.distributionFixed,BoundOp.distributionRetry,BoundOp.distributionDirac,BoundOp.distributionAdd,BoundOp.distributionScale,BoundOp.distributionWeight,BoundOp.distributionIntegral,BoundOp.distributionSum,BoundOp.distributionMass,BoundOp.distributionDensityAt,BoundOp.distributionBind,BoundOp.distributionPushforwardOn,BoundOp.distributionInverseCover,BoundOp.distributionInversePart,BoundOp.distributionRadiusImage,BoundOp.distributionMaskedGraph,BoundOp.distributionGraphFibre,BoundOp.distributionGraphMass:
					return "("~valueOperation(n)~" "~child(n.a)~(n.b==uint.max?"":" "~child(n.b))~")";
				case BoundOp.variable:return "(some "~vars[n.data]~")";
				case BoundOp.scalar:return "(n"~to!string(n.data)~".eval ξ)";
				case BoundOp.global:return "(some (γ ("~ty(type(t),vars)~") "~to!string(n.data)~"))";
				case BoundOp.typeValue:return "(some ("~quotedType(typeDenoted(t),vars)~" : Binding.Ty))";
				case BoundOp.unit:return "(some ())";
				case BoundOp.vectorNil:return "Tensor.nilValue";
				case BoundOp.bottom:return "(none : Option ("~ty(type(t),vars)~"))";
				case BoundOp.lambda,BoundOp.set:
					auto name="x"~to!string(vars.length),param=pool.view(type(t)).fields[0];
					if(n.op==BoundOp.set) return "(some {"~name~" : "~ty(param,vars)~" | "~term(at(n.a),[name]~vars)~" = some true})";
					return "(some (fun "~name~" : "~ty(param,vars)~" => "~term(at(n.a),[name]~vars)~"))";
				case BoundOp.apply:
					if(pool.view(type(at(n.a))).kind==TypeKind.pi) return "(Dependent.apply "~child(n.a)~" "~dim(dimension(at(n.b)),vars)~")";
					return "("~child(n.a)~".bind (fun f => "~child(n.b)~".bind f))";
				case BoundOp.sequence:return "("~child(n.a)~".bind (fun _ => "~child(n.b)~"))";
				case BoundOp.typeEq:return "(Binding.typeEqValue "~child(n.a)~" "~child(n.b)~")";
				case BoundOp.domain:
					return "("~(pool.view(type(at(n.a))).kind==TypeKind.pi?"Dependent.inputDomain":"Binding.inputDomain")~" "~child(n.a)~")";
				case BoundOp.tensor:
					auto op=cast(TensorOp)n.data,v=pool.view(type(at(n.a))),element=typeLeaf(type(at(n.a))); string operation;
					if(op==TensorOp.add||op==TensorOp.mul) operation=tensorOp(type(t),op,vars);
					else{
						auto add=tensorOp(element,TensorOp.add,vars),mul=tensorOp(element,TensorOp.mul,vars),zero=tensorLiteral(element,0),size=dim(v.dimension,vars);
						if(op==TensorOp.dot) operation="(Tensor.dotValue "~add~" "~mul~" "~(element==scalarType(Sort.complex)?"Value.conj":"id")~" "~zero~" "~size~")";
						else if(op==TensorOp.power) operation="(Tensor.matrixPowerValue "~add~" "~mul~" "~zero~" "~tensorLiteral(element,1)~" "~size~")";
						else{ auto row=pool.view(v.fields[0]); size~=" "~dim(row.dimension,vars);
							if(op==TensorOp.matmul) size~=" "~dim(pool.view(pool.view(type(at(n.b))).fields[0]).dimension,vars);
							operation="(Tensor."~(op==TensorOp.matmul?"matmulValue":"matvecValue")~" "~add~" "~mul~" "~zero~" "~size~")";
						}
					}
					return "("~operation~" "~child(n.a)~" "~child(n.b)~")";
				case BoundOp.fixed:throw new Exception("dependent fixed-point certificates are not supported yet");
				default:return "("~valueOperation(n)~" "~child(n.a)~(n.b==uint.max?"":" "~child(n.b))~(n.c==uint.max?"":" "~child(n.c))~")";
			}
		}
		auto parameters=" (γ : Dependent.Globals) (ξ : Env)",outputType=ty(type(result.input),[]);
		code~="noncomputable def input"~parameters~" : Option ("~outputType~") := "~term(result.input,[])~"\n";
		code~="noncomputable def output"~parameters~" : Option ("~outputType~") := "~term(result.output,[])~"\n";
		code~="theorem sound"~parameters~" : input γ ξ = output γ ξ := rfl\n";
		code~="theorem domain"~parameters~" : Value.Defined (input γ ξ) ↔ Value.Defined (output γ ξ) := Iff.of_eq (congrArg Value.Defined (sound γ ξ))\n";
		return code~"#qsym_check_axioms sound\n#qsym_check_axioms domain\nend QSym.DependentCertificate\n";
	}
	// The native compiler assembles lemma applications; exported terms run no tactics.
	private final class SourceCertificates{
		@safe:
		string prefix,declarations;
		Term[] numericTerms;
		uint parent;
		this(string prefix,uint body){this.prefix=prefix;parent=contexts[nodes[body].context].parent;}
		static string q(Rational v){return v.denominator==1?"("~to!string(v.numerator)~" : ℚ)":"(("~to!string(v.numerator)~") / ("~to!string(v.denominator)~") : ℚ)";}
		string app(string lemma,string args){return "(Distribution.StepSource."~lemma~" "~args~")";}
		string atPoint(uint id,Rational point){return "("~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some ("~q(point)~" : ℝ)) ρ))";}
		uint serial;Table!(string,string) proofCache;
		string functionAt(uint id){return "(fun x : ℝ => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))";}
		string save(string claim,string proof){
			auto old=proofCache.get(claim,"");if(old.length)return old;
			auto id=prefix~to!string(serial++),dims=dependent_?" (δ : ℕ → ℕ)":"",args=dependent_?" δ":"";
			declarations~="theorem "~id~dims~" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctxName(parent)~") : "~claim~" := "~proof~"\n";
			auto ref_="("~id~args~" γ ξ ρ)";proofCache.set(claim,ref_);return ref_;
		}
		string numericProof(uint id,Rational point,string value){
			auto term=scalarBody(at(id),arena.real_(point));enforce(term!=Term.init,"missing step numeric witness");
			numericTerms~=term;return save(atPoint(id,point)~" = some (Numeric.denote (s := ."~leanSort(arena.sort(term))~") "~value~")", "(Numeric.calculate_sound ξ n"~to!string(term.id)~" "~value~" rfl)");
		}
		struct Linear{Rational slope,offset;string proof;}
		Linear seal(Linear r,uint id){
			r.proof=save("Distribution.StepSource.Affine "~functionAt(id)~" "~q(r.slope)~" "~q(r.offset),r.proof);return r;
		}
		Linear affineProof(uint id){
			auto n=nodes[id];Linear r;
			if(!depends(at(id),0)){
				auto term=scalarBody(at(id),arena.real_(0)),arg=arena.variable(Sort.real_,cast(uint)arena.length+1);
				enforce(term!=Term.init&&integralAffine(arena,term,arg,r.slope,r.offset)&&r.slope.zero,"non-affine step constant");
				r.proof=app("affine_constant",atPoint(id,Rational(0))~" "~q(r.offset)~" "~numericProof(id,Rational(0),q(r.offset)));return seal(r,id);
			}
			if(n.op==BoundOp.variable&&n.data==0){r.slope=Rational(1);r.proof="Distribution.StepSource.affine_variable";return seal(r,id);}
			enforce(n.op==BoundOp.primitive,"non-affine step expression");auto op=arena.view(arena.at(n.data));
			if(op.op==Op.add){
				auto a=affineProof(n.a),b=affineProof(n.b);r.slope=a.slope+b.slope;r.offset=a.offset+b.offset;
				r.proof=app("affine_add","(a := "~q(a.slope)~") (b := "~q(a.offset)~") (c := "~q(b.slope)~") (d := "~q(b.offset)~") "~a.proof~" "~b.proof);return seal(r,id);
			}
			enforce(op.op==Op.mul,"unsupported affine step operation");
			bool left=!depends(at(n.a),0);auto c=affineProof(left?n.a:n.b),f=affineProof(left?n.b:n.a);
			enforce(c.slope.zero,"nonconstant affine multiplier");r.slope=c.offset*f.slope;r.offset=c.offset*f.offset;
			auto hc=numericProof(left?n.a:n.b,Rational(0),q(c.offset));
			r.proof=app("affine_mul_constant_"~(left?"left":"right"),"(a := "~q(f.slope)~") (b := "~q(f.offset)~") "~q(c.offset)~" "~(left?hc~" "~f.proof:f.proof~" "~hc));return seal(r,id);
		}
		// Constancy of a step expression on a region of the axis.
		private string uniformRaw(uint id,string region,Rational sample){
			auto n=nodes[id];
			if(!depends(at(id),0))return app("uniform_const",region~" "~atPoint(id,Rational(0)));
			enforce(n.op==BoundOp.primitive,"unsupported step uniform expression");auto op=arena.view(arena.at(n.data));
			if(op.op==Op.le||op.op==Op.lt||op.op==Op.nonzero){
				auto a=affineProof(n.a);Linear b;if(op.op!=Op.nonzero)b=affineProof(n.b);
				auto value=(a.slope-b.slope)*sample+a.offset-b.offset;
				auto sign=value.zero?"zero":value<Rational(0)?"negative":"positive";
				auto coefficients="(a := "~q(a.slope)~") (b := "~q(a.offset)~") ";
				if(op.op!=Op.nonzero)coefficients~="(c := "~q(b.slope)~") (d := "~q(b.offset)~") ";
				return app("uniform_"~(op.op==Op.le?"le":op.op==Op.lt?"lt":"nonzero"),"(r := "~region~") (s := ."~sign~") "~coefficients~"(of_decide_eq_true rfl) "~a.proof~(op.op==Op.nonzero?"":" "~b.proof)~" rfl");
			}
			auto a=uniform(n.a,region,sample);
			return app("uniform_"~(n.b==uint.max?"unary":"binary"),valueOperation(n)~" "~a~(n.b==uint.max?"":" "~uniform(n.b,region,sample)));
		}
		string uniform(uint id,string region,Rational sample){
			return save("Distribution.StepSource.Uniform "~region~" "~functionAt(id),uniformRaw(id,region,sample));
		}
		// Polynomial evidence on a predicate of the axis: a cell of a grid, or
		// everywhere. Coefficient lists stay symbolic in the claims; Lean
		// computes them where a certificate compares them.
		struct Piece{string proof,poly;}
		enum everywhere="(fun _ : ℝ => True)";
		private Piece pieceRaw(uint id,string set,string region,Rational sample){
			auto n=nodes[id];
			if(!depends(at(id),0)){
				auto term=scalarBody(at(id),arena.real_(Rational(0)));enforce(term!=Term.init,"missing polynomial constant");
				auto v=simplify(arena,term);enforce(!v.exhausted&&arena.isNumber(v.output),"non-numeric polynomial constant");
				auto c=q(arena.number(v.output).re);
				return Piece(app("polynomial_constant",set~" "~atPoint(id,Rational(0))~" "~c~" "~numericProof(id,Rational(0),c)),"["~c~"]");
			}
			if(n.op==BoundOp.variable&&n.data==0)return Piece(app("polynomial_variable",set),"[0, 1]");
			enforce(n.op==BoundOp.primitive,"unsupported polynomial step expression");auto op=arena.view(arena.at(n.data));
			if(op.op==Op.builtin){
				enforce(region.length,"step expression outside a cell");
				auto term=scalarBody(at(id),arena.real_(sample));enforce(term!=Term.init,"missing polynomial step");
				auto v=simplify(arena,term);enforce(!v.exhausted&&arena.isNumber(v.output),"non-numeric polynomial step");
				auto c=q(arena.number(v.output).re);
				return Piece(app("polynomial_uniform",q(sample)~" "~c~" rfl "~uniform(id,region,sample)~" "~numericProof(id,sample,c)),"["~c~"]");
			}
			if(op.op==Op.mask){
				enforce(region.length,"guard outside a cell");
				auto pred=scalarBody(at(n.a),arena.real_(sample));enforce(pred!=Term.init,"missing polynomial guard");
				auto v=simplify(arena,pred);enforce(!v.exhausted&&arena.view(v.output).op==Op.boolLit,"undecided polynomial guard");
				bool truth=v.output==arena.boolean(true);
				auto guard=q(sample)~" rfl "~uniform(n.a,region,sample)~" "~numericProof(n.a,sample,truth?"true":"false");
				if(!truth)return Piece(app("polynomial_mask_false",functionAt(n.b)~" "~guard),"[]");
				auto b=piece(n.b,set,region,sample);
				return Piece(app("polynomial_mask_true",guard~" "~b.proof),b.poly);
			}
			if(op.op==Op.abs){
				enforce(region.length,"absolute value outside a cell");
				auto arg=arena.variable(Sort.real_,freshScalarIndex(n.a));
				Rational slope,offset;
				if(!gridKink(n.a,arg,slope,offset)){
					Rational lead; Rational[] roots;
					enforce(gridFactors(n.a,arg,lead,roots),"missing polynomial factors");
					string[] literals; foreach(a;roots) literals~=q(a);
					auto factors="["~literals.join(", ")~"]";
					auto inside=piece(n.a,set,region,sample);
					return Piece(app("polynomial_abs_factors","(r := "~region~") "~q(lead)~" "~factors~" "~inside.proof~" rfl rfl"),
						"(Distribution.StepSource.absFactors "~region~" "~q(lead)~" "~factors~")");
				}
				auto inside=affineProof(n.a);auto at_=inside.slope*sample+inside.offset;
				auto sign=at_.zero?"zero":at_<Rational(0)?"negative":"positive";
				return Piece(app("polynomial_abs","(r := "~region~") ."~sign~" "~inside.proof~" rfl"),
					"(Distribution.StepSource.absPoly ."~sign~" "~q(inside.slope)~" "~q(inside.offset)~")");
			}
			auto a=piece(n.a,set,region,sample);
			if(op.op==Op.pow)return Piece(app("polynomial_pow",to!string(op.value)~" "~a.proof),"(Distribution.StepSource.polyPow "~a.poly~" "~to!string(op.value)~")");
			enforce(op.op==Op.add||op.op==Op.mul,"unsupported polynomial step operation");
			auto b=piece(n.b,set,region,sample);bool add=op.op==Op.add;
			return Piece(app(add?"polynomial_add":"polynomial_mul",a.proof~" "~b.proof),"(Distribution.StepSource.poly"~(add?"Add":"Mul")~" "~a.poly~" "~b.poly~")");
		}
		Piece piece(uint id,string set,string region,Rational sample){
			auto r=pieceRaw(id,set,region,sample);
			r.proof=save("Distribution.StepSource.PolynomialOn "~set~" "~functionAt(id)~" "~r.poly,r.proof);return r;
		}
		// A polynomial, the exponential of a rational multiple of the axis,
		// or a product of these.
		Piece exponential(uint id){
			Rational[] coefficients;Piece r;string rate;
			if(axisPolynomial(id,coefficients)){
				auto w=piece(id,everywhere,"",Rational(0));
				r=Piece(app("exp_polynomial",w.proof),w.poly);rate="0";
			}else{
				auto n=nodes[id];enforce(n.op==BoundOp.primitive,"unsupported exponential term");
				auto op=arena.view(arena.at(n.data));
				if(op.op==Op.builtin){
					enforce(op.value==Builtin.expR,"unsupported exponential function");
					auto inside=affineProof(n.a);enforce(inside.offset.zero,"shifted exponent");
					r=Piece(app("exp_affine",inside.proof),"[1]");rate=q(inside.slope);
				}else{
					enforce(op.op==Op.mul,"unsupported exponential operation");
					auto a=exponential(n.a),b=exponential(n.b);
					r=Piece(app("exp_mul",a.proof~" "~b.proof),"(Distribution.StepSource.polyMul "~a.poly~" "~b.poly~")");
					return r;
				}
			}
			r.proof=save("Distribution.StepSource.ExpPolynomial "~functionAt(id)~" "~r.poly~" "~rate,r.proof);return r;
		}
		// Along a filter a polynomial times the exponential of a polynomial:
		// the factors are polynomials, exponentials of polynomials, with
		// `pieces` piecewise polynomials beyond their last cut at that end, or
		// free of the variable; these are the scale.
		string exponentialTail(uint id,string filter,bool bottom,bool pieces,out bool scaled,bool offsets=false){
			Rational[] p,exponent; Rational cut;
			final switch(tailFactor(id,bottom,p,exponent,cut,pieces)){
				case TailFactor.polynomial:return "(Limit.EventualExp.polynomial "~piece(id,everywhere,"",Rational(0)).proof~")";
				case TailFactor.exponential:return "(Limit.EventualExp.exp "~piece(nodes[id].a,everywhere,"",Rational(0)).proof~")";
				case TailFactor.piece:
					auto side=bottom?"before":"after",region="(."~side~" "~q(cut)~")";
					auto part=piece(id,"(Distribution.StepSource.Region.contains "~region~")",region,bottom?cut-Rational(1):cut+Rational(1));
					return "(Limit.EventualExp.piece (Limit.tail_"~side~" "~q(cut)~") "~part.proof~")";
				case TailFactor.none:break;
			}
			scaled=true;
			if(!depends(at(id),0)) return "(Limit.EventualScaled.constant "~filter~" ("~name(dropIndex(at(id)).id)~".eval ξ ρ))";
			Rational rate; BoundTerm offset;
			if(pieces&&offsetExponential(id,rate,offset,false)) return "(Limit.EventualScaled.exp_offset "~filter~" "~offsetProof(id,rate)~")";
			if(offsets&&curveOffset(id,exponent,offset,false)){
				// The coefficients above the constant at their rational values:
				// one that is absent is a zero.
				AxisCoefficient[3] c; axisQuadratic(nodes[id].a,c,true);
				string closed(size_t i){ return c[i].present?closedProof(c[i].term,exponent[i]):"Distribution.StepSource.coefValue_absent"; }
				return "(Limit.EventualScaled.exp_curve "~filter~" "~q(exponent[1])~" "~q(exponent[2])~" "~quadratic(nodes[id].a)~" "~closed(1)~" "~closed(2)~")";
			}
			bool left,right; auto product=nodes[id];
			auto a=exponentialTail(product.a,filter,bottom,pieces,left,offsets),b=exponentialTail(product.b,filter,bottom,pieces,right,offsets); scaled=left||right;
			return scaled?"(Limit.EventualScaled."~(left&&right?"mul":left?"times":"after")~" "~a~" "~b~")":"(Limit.EventualExp.mul "~a~" "~b~")";
		}
		// Terms outside the binder that only the proof names: the export
		// keeps them.
		uint[] roots;
		string outside(uint id){auto t=dropIndex(at(id));roots~=t.id;return "("~name(t.id)~".eval ξ ρ)";}
		// A closed term at its rational value, by the numeric calculator.
		string closedProof(BoundTerm t,Rational expected){
			Rational value;Term term;enforce(closedRational(t,value,term)&&value==expected,"coefficient is not the closed rational");
			numericTerms~=term;roots~=t.id;return "(Numeric.calculate_sound ξ n"~to!string(term.id)~" "~q(expected)~" rfl)";
		}
		// A polynomial of degree at most two in the axis whose coefficients do
		// not mention it, by its structure, with the coefficients the rule built.
		string quadratic(uint id){
			if(!depends(at(id),0))return app("Quadratic.constant",outside(id));
			auto n=nodes[id];
			if(n.op==BoundOp.variable){
				auto one=unitCoefficient(id);roots~=one.id;
				return app("Quadratic.variable","(Numeric.calculate_sound ξ n"~to!string(nodes[one.id].data)~" (1 : ℚ) rfl)");
			}
			auto op=arena.view(arena.at(n.data)).op;auto a=quadratic(n.a);
			if(op==Op.pow)return app("Quadratic.square",a);
			auto b=quadratic(n.b);
			if(op==Op.add)return app("Quadratic.add",a~" "~b);
			AxisCoefficient[3] x,y;axisQuadratic(n.a,x,false);axisQuadratic(n.b,y,false);
			return app(!coefficientDegree(x)?"Quadratic.scale":!coefficientDegree(y)?"Quadratic.scaled":"Quadratic.product",a~" "~b);
		}
		// The coefficients the rule built for a polynomial, written out.
		string coefficients(AxisCoefficient[] cs){
			string r="[";
			foreach(i,c;cs){
				if(c.present)roots~=c.term.id;
				r~=(i?", ":"")~(c.present?"some ("~name(c.term.id)~".eval ξ ρ)":"none");
			}
			return r~"]";
		}
		// A polynomial in the axis whose coefficients do not mention it, by its
		// structure. The coefficients the rule built are written out after every
		// sum and product, and for every power on the way to a power: each list
		// is then one step from lists that are written out, and the kernel
		// compares it with them once.
		string symbolic(uint id,out AxisCoefficient[] cs){
			AxisCoefficient c;c.present=true;
			if(!depends(at(id),0)){c.term=dropIndex(at(id));cs=[c];return app("Symbolic.constant",outside(id));}
			auto n=nodes[id];
			if(n.op==BoundOp.variable){
				c.term=unitCoefficient(id);roots~=c.term.id;cs=[AxisCoefficient.init,c];
				return app("Symbolic.variable","(Numeric.calculate_sound ξ n"~to!string(nodes[c.term.id].data)~" (1 : ℚ) rfl)");
			}
			auto op=arena.view(arena.at(n.data));AxisCoefficient[] x,y;auto a=symbolic(n.a,x);
			if(op.op==Op.pow){
				cs=x;auto chain="Distribution.StepSource.Powers.one";
				foreach(i;1..op.value){cs=symbolicProduct(x,cs,true);chain=app("Powers.step",coefficients(cs)~" "~chain~" rfl");}
				return app("Symbolic.pow",a~" "~chain);
			}
			auto b=symbolic(n.b,y);
			cs=op.op==Op.add?symbolicSum(x,y,true):symbolicProduct(x,y,true);
			return app("Symbolic.cast",coefficients(cs)~" "~app(op.op==Op.add?"Symbolic.add":"Symbolic.mul",a~" "~b)~" rfl");
		}
		// The product of two factors with their polynomials of this kind, of
		// which the product is written out where both have one.
		string bellProduct(string a,AxisCoefficient[] x,string b,AxisCoefficient[] y,out AxisCoefficient[] poly){
			auto product=app("bell_mul",a~" "~b);
			if(!x.length||!y.length){poly=x.length?x:y;return product;}
			poly=symbolicProduct(x,y,true);
			return app("Bell.cast",coefficients(poly)~" "~product~" rfl");
		}
		// A factor as scale, polynomials and exponential, the structure of its
		// exponent where it has one, and the coefficients of its polynomial of
		// this kind where it has one.
		string bell(uint id,out string exponent,out AxisCoefficient[] poly){
			Rational[] p;
			final switch(bellFactor(id,p)){
				case BellFactor.none:enforce(0,"unsupported Gaussian factor");assert(0);
				case BellFactor.symbolic:return app("bell_symbolic",symbolic(id,poly));
				case BellFactor.polynomial:return app("bell_polynomial",piece(id,everywhere,"",Rational(0)).proof);
				case BellFactor.exponential:exponent=quadratic(nodes[id].a);return app("bell_exp",functionAt(nodes[id].a));
				case BellFactor.scale:return app("bell_constant",outside(id));
				case BellFactor.product:
					string left,right;AxisCoefficient[] x,y;auto a=bell(nodes[id].a,left,x),b=bell(nodes[id].b,right,y);
					exponent=left.length&&right.length?app("Quadratic.add",left~" "~right):left.length?left:right;
					return bellProduct(a,x,b,y,poly);
			}
		}
		// The exponential of a rational slope with a constant part: the slope,
		// the structure of the exponent, and the slope as a closed term.
		string offsetProof(uint id,Rational slope){
			AxisCoefficient[3] c;axisQuadratic(nodes[id].a,c,true);
			return q(slope)~" "~quadratic(nodes[id].a)~" "~closedProof(c[1].term,slope);
		}
		// Such a product with factors free of the axis: these are its scale,
		// the others multiply.
		string scaledFactor(uint factor,out bool scaled){
			Rational[] coefficients;Rational rate;BoundTerm offset;
			if(axisExponential(factor,coefficients,rate))return exponential(factor).proof;
			scaled=true;
			if(!depends(at(factor),0))return app("scaled_constant","("~name(dropIndex(at(factor)).id)~".eval ξ ρ)");
			if(offsetExponential(factor,rate,offset,false))return app("scaled_exp_offset",offsetProof(factor,rate));
			bool left,right;auto product=nodes[factor];
			auto a=scaledFactor(product.a,left),b=scaledFactor(product.b,right);
			return app(left&&right?"scaled_mul":left?"scaled_times":"scaled_after",a~" "~b);
		}
	}
	// Evidence for a structural limit, case by case as the rule found it.
	private string limitProof(LimitSolution s,SourceCertificates cert){
		auto end=s.bottom?"atBot":"atTop";
		string literal(uint id,string value){ return "(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~value~" rfl)"; }
		// An eventually constant term and its eventual value.
		string eventual(uint id,uint output){
			if(!depends(at(id),0)) return "(Limit.Eventual.const Filter."~end~" ("~name(output)~".eval ξ ρ))";
			auto n=nodes[id],o=nodes[output];
			if(n.op==BoundOp.guard){
				enforce(o.op==BoundOp.guard,"eventual guard mismatch");
				return "(Limit.Eventual.binary Binding.guardValue "~eventual(n.a,o.a)~" "~eventual(n.b,o.b)~")";
			}
			auto op=arena.view(arena.at(n.data)).op;
			bool truth; Rational cut; auto decided=decidedGuard(id,s.bottom,truth,cut);
			if(decided==Decided.cuts){
				auto sample=s.bottom?cut-Rational(1):cut+Rational(1),value=truth?"true":"false";
				auto side=s.bottom?"before":"after",region="(."~side~" "~cert.q(cut)~")";
				return "(Limit.Eventual.step (Limit.tail_"~side~" "~cert.q(cut)~") "~cert.q(sample)~" rfl "~
					cert.uniform(id,region,sample)~" "~cert.numericProof(id,sample,value)~" "~literal(output,value)~")";
			}
			if(decided!=Decided.no){
				enforce(o.op==BoundOp.sequence,"missing limit bound"); bool lower=decided==Decided.lower;
				return "(Limit.Eventual."~(lower?"bound_":"")~(op==Op.le?"le":"lt")~(lower?"":"_bound")~" Limit.above_"~end~" ("~
					name(o.a)~".eval ξ ρ) "~literal(o.b,truth?"true":"false")~")";
			}
			enforce(o.op==BoundOp.primitive&&n.data==o.data,"eventual value mismatch");
			if(op==Op.mask&&(decided=decidedGuard(n.a,s.bottom,truth,cut))!=Decided.no&&!truth){
				auto g=nodes[o.a];
				auto never=decided==Decided.cuts?"(Limit.never_false "~literal(o.a,"false")~")":"(Limit.never_bound ("~name(g.a)~".eval ξ ρ) "~literal(g.b,"false")~")";
				return "(Limit.Eventual.mask_never "~eventual(n.a,o.a)~" "~never~" "~cert.functionAt(n.b)~" ("~name(o.b)~".eval ξ ρ))";
			}
			return "(Limit.Eventual."~(n.b==uint.max?"unary":"binary")~" "~valueOperation(n)~" "~eventual(n.a,o.a)~(n.b==uint.max?"":" "~eventual(n.b,o.b))~")";
		}
		// A quotient of polynomials, by its structure.
		string quotient(uint id){
			Rational[] p;
			if(axisPolynomial(id,p)) return "(Limit.quotient_polynomial "~cert.piece(id,cert.everywhere,"",Rational(0)).proof~")";
			auto n=nodes[id],op=arena.view(arena.at(n.data));
			if(op.op==Op.inv) return "(Limit.quotient_inv "~quotient(n.a)~")";
			if(op.op==Op.pow) return "(Limit.quotient_pow "~to!string(op.value)~" "~quotient(n.a)~")";
			return "(Limit.quotient_mul "~quotient(n.a)~" "~quotient(n.b)~")";
		}
		string visit(uint body,uint output){
			if(!depends(at(body),0)) return "(Limit.Exact.const Filter."~end~" ("~name(output)~".eval ξ ρ))";
			if(eventualTerm(body,s.bottom,false)!=BoundTerm.init) return "(Limit.Exact.of_eventual "~eventual(body,output)~")";
			Rational[] p,exponent; bool scaled;
			if(tailExponential(body,s.bottom,p,exponent,scaled)){
				bool vanishes; Rational rate; size_t order;
				enforce(vanishing(p,exponent,s.bottom,vanishes,rate,order),"limit term does not vanish");
				auto decay=vanishes?"(Limit.vanishes_zero rfl)":"(Limit.decays_"~end~" "~cert.q(rate)~" "~to!string(order)~" rfl)";
				auto zero=scaled?nodes[output].b:output;
				return "(Limit.Exact."~(scaled?"scaled_decay":"decay")~" "~cert.exponentialTail(body,"Filter."~end,s.bottom,true,scaled)~" "~decay~" "~literal(zero,"(0 : ℚ)")~")";
			}
			size_t degree; Rational ratio;
			if(quotientLimit(body,degree,ratio))
				return "(Limit.Exact.quotient Limit.Infinite."~(s.bottom?"bottom":"top")~" "~quotient(body)~" "~to!string(degree)~" "~cert.q(ratio)~" rfl "~literal(output,cert.q(ratio))~")";
			BellParts bell;
			if(gaussianTail(body,bell,true)){
				string quadratic; AxisCoefficient[] poly; auto evidence=cert.bell(body,quadratic,poly); auto zero=output;
				if(bell.c[0].present) zero=nodes[zero].b;
				if(bell.c[1].present) zero=nodes[zero].b;
				if(bell.scaled) zero=nodes[zero].b;
				return "(Limit.Exact.gaussian Limit.Infinite."~(s.bottom?"bottom":"top")~" "~cert.q(bell.c[2].value)~" "~evidence~" "~quadratic~" "~
					cert.closedProof(bell.c[2].term,bell.c[2].value)~" rfl "~literal(zero,"(0 : ℚ)")~")";
			}
			auto n=nodes[body],o=nodes[output];
			if(n.op==BoundOp.guard){
				enforce(o.op==BoundOp.guard,"limit guard mismatch");
				return "(Limit.Exact.guard "~eventual(n.a,o.a)~" "~visit(n.b,o.b)~")";
			}
			enforce(n.op==BoundOp.primitive&&o.op==BoundOp.primitive&&n.data==o.data,"limit structure mismatch");
			auto op=arena.view(arena.at(n.data));
			if(op.op==Op.mask) return "(Limit.Exact.mask "~eventual(n.a,o.a)~" "~visit(n.b,o.b)~")";
			if(op.op==Op.pow) return "(Limit.Exact.pow "~to!string(op.value)~" "~visit(n.a,o.a)~")";
			if(op.op==Op.abs) return "(Limit.Exact.abs "~visit(n.a,o.a)~")";
			if(op.op==Op.builtin&&regularBuiltin(op.value)) return "(Limit.Exact.regular Limit.regular_"~builtinInfo(cast(Builtin)op.value).code~" "~visit(n.a,o.a)~")";
			if(op.op==Op.inv||op.op==Op.builtin){
				Rational q; Term term; enforce(closedRational(at(o.a),q,term),"limit is not a closed number");
				cert.numericTerms~=term;
				auto value=cert.q(q)~" (Numeric.calculate_sound ξ n"~to!string(term.id)~" "~cert.q(q)~" rfl)";
				if(op.op==Op.inv) return "(Limit.Exact.inv "~visit(n.a,o.a)~" (Limit.nonzero_literal "~value~" rfl))";
				return "(Limit.Exact.interior "~visit(n.a,o.a)~" "~value~" (Limit.interior_"~builtinInfo(cast(Builtin)op.value).code~" rfl))";
			}
			enforce(op.op==Op.add||op.op==Op.mul,"unsupported limit operation");
			return "(Limit.Exact."~(op.op==Op.add?"add":"mul")~" "~visit(n.a,o.a)~" "~visit(n.b,o.b)~")";
		}
		return "Limit.Exact.sound "~visit(s.body,s.output);
	}
	private string coordinateGridProof(CoordinateGrid c,SourceCertificates cert){
		alias q=SourceCertificates.q;
		enum grid="Distribution.GraphFibre.Coordinates.Grid.";
		string app(string lemma,string args){ return "("~grid~lemma~" "~args~")"; }
		string numeric(Term t,Rational v){
			cert.numericTerms~=t;
			return "(Numeric.calculate_sound ξ n"~to!string(t.id)~" "~q(v)~" rfl)";
		}
		auto cuts=c.grid.cuts,f=cert.functionAt(c.body),w=cert.functionAt(c.weight);
		string[] sources,cells;
		foreach(i;0..cuts.length+1){
			auto region=!cuts.length?"":!i?"(.before "~q(cuts[0])~")":i==cuts.length?"(.after "~q(cuts[$-1])~")":"(.between "~q(cuts[i-1])~" "~q(cuts[i])~")";
			auto set=cuts.length?"(Distribution.StepSource.Region.contains "~region~")":cert.everywhere;
			auto sample=!cuts.length?Rational(0):!i?cuts[0]-Rational(1):i==cuts.length?cuts[$-1]+Rational(1):(cuts[i-1]+cuts[i])/Rational(2);
			auto src=cert.piece(c.body,set,region,sample);
			sources~=src.proof;
			// The emitted sum has disjoint masks. At most one absolute
			// polynomial contributes on this cell; every sibling certifies zero.
			struct Magnitude{ string proof; bool active; }
			Magnitude magnitude(uint id){
				auto n=nodes[id];
				if(primitiveOp(id,Op.abs))
					return Magnitude(app("magnitude_abs",cert.piece(n.a,set,region,sample).proof),true);
				if(primitiveOp(id,Op.mask)){
					auto predicate=scalarBody(at(n.a),arena.real_(sample));
					if(simplify(arena,predicate).output==arena.boolean(true)){
						auto v=magnitude(n.b);
						return Magnitude(app("magnitude_mask",q(sample)~" rfl "~cert.uniform(n.a,region,sample)~" "~cert.numericProof(n.a,sample,"true")~" "~v.proof),true);
					}
				}
				if(primitiveOp(id,Op.add)){
					auto a=magnitude(n.a),b=magnitude(n.b);
					if(a.active||b.active){
						enforce(!(a.active&&b.active),"overlapping coordinate cells");
						return Magnitude(app(a.active?"magnitude_add_left":"magnitude_add_right",a.proof~" "~b.proof),true);
					}
					return Magnitude(app("zero_add",a.proof~" "~b.proof),false);
				}
				return Magnitude(app("zero_on",cert.piece(id,set,region,sample).proof~" rfl"),false);
			}
			auto weight=magnitude(c.weight);
			auto proof=weight.active?weight.proof:app("magnitude_zero",weight.proof);
			cells~=cert.save(grid~"Cell "~set~" "~f~" "~w~" "~src.poly,app("cell",src.proof~" "~proof~" rfl"));
		}
		bool restricted=c.predicate!=uint.max;
		string pred;
		if(restricted){ cert.roots~=c.weight; pred=cert.functionAt(c.predicate); }
		if(!cuts.length) return restricted?app("polynomialRestricted",pred~" "~cells[0]):app("polynomial",cells[0]);
		bool changed=c.change!=CoordinateChange.none;
		bool probing=c.query!=uint.max&&!restricted,pointProbe=c.query!=uint.max&&restricted,hit;
		Rational sample;
		bool positive=c.change==CoordinateChange.log||c.change==CoordinateChange.sqrt;
		bool checkTraces=c.traceRange&&(positive||c.change==CoordinateChange.reciprocal);
		string probe,continuous,traces,jumps;
		if(c.flatMass) jumps=app("JumpSum.nil",numeric(arena.real_(0),Rational(0)));
		string member(Rational v){
			return checkTraces?app(positive?"CutRange.positive":"CutRange.nonzero",q(v)~" rfl"):"True.intro";
		}
		if(checkTraces) traces=app("CutRange.nil",(positive?"(Set.Ioi (0 : ℝ))":"(fun u : ℝ => u ≠ 0)")~" "~f);
		if(probing||pointProbe){
			sample=arena.number(arena.at(nodes[c.query].data)).re;
			probe=pointProbe?app("PointCuts.nil","_ "~q(sample)):app("Probe.nil",q(sample));
			cert.roots~=c.weight;
		}
		if(changed){
			cert.roots~=c.weight;
			if(restricted) cert.roots~=c.predicate;
			if(!c.traceRange) continuous=app("ContinuousCuts.nil",f);
		}
		string events="([] : List "~grid~"Event)",selected="List.Forall₂.nil";
		auto tail=app("last","(a := "~q(cuts[$-1])~") "~cells[$-1]);
		foreach_reverse(i,a;cuts){
			auto j=c.joins[i],v=c.grid.points[i],lo=i?"(some "~q(cuts[i-1])~")":"none",hi=i+1<cuts.length?"(some "~q(cuts[i+1])~")":"none";
			auto bounds="(lo := "~lo~") (a := "~q(a)~") ";
			auto germs=app("germs",bounds~"(hi := "~hi~") rfl rfl "~sources[i]~" "~sources[i+1]);
			auto point="(v := "~q(v)~") (w := "~w~") ",pv=cert.numericProof(c.body,a,q(v));
			string law;
			if(j.kind==JoinKind.smooth){
				auto k=j.slope<Rational(0)?-j.slope:j.slope;
				auto weight=cert.numericProof(c.weight,a,q(k));
				if(j.slope<Rational(0)) weight=app("magnitudeAt",q(j.slope)~" "~q(k)~" (of_decide_eq_true rfl) "~weight);
				law=app("smooth",point~"(slope := "~q(j.slope)~") "~germs~" "~pv~" rfl rfl rfl rfl "~weight);
			}else{
				auto zero=cert.numericProof(c.weight,a,q(Rational(0)));
				auto av=arena.real_(a),apos=numeric(av,a);
				string eq;
				if(j.kind==JoinKind.corner){
					law=app("corner",point~germs~" "~pv~" rfl rfl (of_decide_eq_true rfl) "~zero);
					eq=app("cornerTerm",q(a)~" "~apos);
					if(changed&&!c.traceRange){
						auto hc=app("continuousJoin",q(v)~" "~germs~" "~pv~" rfl rfl");
						continuous=app("ContinuousCuts.cons","(d := "~name(j.event)~".eval ξ ρ) "~hc~" "~continuous);
					}
				}else{
					auto height=j.right-j.left;if(height<Rational(0))height=-height;
					auto side=v==j.left?"(Or.inl rfl)":"(Or.inr rfl)";
					law=app("jump",point~"(l := "~q(j.left)~") (r := "~q(j.right)~") "~germs~" "~pv~" rfl rfl (of_decide_eq_true rfl) "~side~" "~zero);
					eq=app("atomTerm",q(a)~" "~q(height)~" "~apos~" "~numeric(arena.real_(height),height));
				}
				if(checkTraces){
					auto ends=app("traceEndpoints",q(j.left)~" "~q(j.right)~" "~germs~" rfl rfl");
					traces=app("CutRange.cons","(d := "~name(j.event)~".eval ξ ρ) "~ends~" "~member(j.left)~" "~member(j.right)~" "~traces);
				}
				string trace(Rational v,Rational k){
					return c.change==CoordinateChange.reciprocal?app("reciprocalTrace",q(v)~" "~q(k)~" rfl"):
						app("sqrtTrace",q(v)~" "~q(k)~" (of_decide_eq_true rfl) rfl");
				}
				string ends,op;
				if(c.image||c.flatMass){
					ends=app("traceValues",q(j.left)~" "~q(j.right)~" "~germs~" rfl rfl");
					op=grid~"ScalarChange."~to!string(c.change);
				}
				if(c.image&&!restricted){
					string image;
					if(j.kind==JoinKind.corner){
						image=app("imageCorner",op~" "~q(v)~" "~ends~" "~member(v)~" "~eq);
					}else if(j.symbolicRoot){
						auto lower=j.left<j.right?j.left:j.right,upper=j.left<j.right?j.right:j.left;
						image=app("sqrtImageJump",q(j.left)~" "~q(j.right)~" "~ends~" "~member(j.left)~" "~member(j.right)~
							" (of_decide_eq_true rfl) "~apos~" "~numeric(arena.real_(lower),lower)~" "~numeric(arena.real_(upper),upper)~" "~numeric(arena.real_(-1),Rational(-1)));
					}else{
						auto k=j.rightImage-j.leftImage;
						if(k<Rational(0)) k=-k;
						auto gap=app("imageJump",op~" "~q(j.left)~" "~q(j.right)~" "~q(j.leftImage)~" "~q(j.rightImage)~" "~ends~" "~
							member(j.left)~" "~member(j.right)~" (of_decide_eq_true rfl) "~trace(j.left,j.leftImage)~" "~trace(j.right,j.rightImage));
						image="(Eq.trans "~gap~" "~app("atomTerm",q(a)~" "~q(k)~" "~apos~" "~numeric(arena.real_(k),k))~")";
					}
					selected="(List.Forall₂.cons "~image~" "~selected~")";
				}
				if(c.flatMass){
					jumps=app("JumpSum.cons","(d := "~name(j.event)~".eval ξ ρ) "~op~" "~q(j.left)~" "~q(j.right)~" "~ends~" "~
						member(j.left)~" "~member(j.right)~" "~numeric(arena.real_(j.left),j.left)~" "~numeric(arena.real_(j.right),j.right)~" "~
						numeric(arena.real_(-1),Rational(-1))~" "~jumps);
				}
				if(probing){
					hit|=sample==a;
					probe=app("Probe.cons",q(sample)~" "~q(a)~" ("~name(j.event)~".eval ξ ρ) "~probe);
				}
				if(restricted||probing||c.flatMass||c.image) cert.roots~=j.event;
				if(restricted&&j.kind==JoinKind.corner){
					auto cut=c.image?app("imageRestrictedCorner",op~" "~cert.functionAt(c.outerPredicate)~" "~q(v)~" "~ends~" "~pv~" "~member(v)):
						app("restrictedCorner",pred~" "~q(v)~" "~germs~" "~pv~" rfl rfl");
					string shape;
					final switch(j.selection){
						case CornerSelection.active:
						case CornerSelection.inactive:
							bool active=j.selection==CornerSelection.active;
							auto result=active?"true":"false";
							auto h=c.image?app("imageTest",op~" "~cert.functionAt(c.outerPredicate)~" "~q(v)~" "~q(j.leftImage)~" "~member(v)~
								" "~trace(v,j.leftImage)~" "~cert.numericProof(c.outerPredicate,j.leftImage,result)):
								cert.numericProof(c.predicate,v,result);
							auto tested="(congrArg (Distribution.GraphFibre.Coordinates.VariationChart.corner ("~q(a)~" : ℝ)) "~h~")";
							if(pointProbe){
								hit|=a==sample&&active;
								probe=app("PointCuts.corner",q(sample)~" "~q(a)~" "~result~" (Eq.trans "~cut~" "~tested~") "~probe);
							}else{
								auto term=active?eq:app("cornerInactive",q(a)~" "~numeric(arena.real_(0),Rational(0)));
								shape="(Eq.trans "~tested~" "~term~")";
							}
							break;
						case CornerSelection.dynamic:
							shape=app("cornerGuarded",pred~" "~q(a)~" "~q(v)~" "~apos~" "~numeric(arena.real_(v),v));
							break;
					}
					if(!pointProbe) selected="(List.Forall₂.cons (Eq.trans "~cut~" "~shape~") "~selected~")";
				}else if(restricted){
					auto l=c.image?j.leftImage:j.left,r=c.image?j.rightImage:j.right;
					auto lower=l<r?l:r,upper=l<r?r:l;
					auto prefix=cert.functionAt(c.image?c.outerPredicate:c.predicate)~" "~q(l)~" "~q(r)~" ";
					string limits(){
						return c.image?app("imageTraces",op~" "~q(j.left)~" "~q(j.right)~" "~q(l)~" "~q(r)~" "~ends~" "~
							member(j.left)~" "~member(j.right)~" "~trace(j.left,l)~" "~trace(j.right,r)):
							app("traceValues",q(l)~" "~q(r)~" "~germs~" rfl rfl");
					}
					string boundsProof(){
						return numeric(arena.real_(lower),lower)~" "~numeric(arena.real_(upper),upper)~" "~numeric(arena.real_(1),Rational(1));
					}
					string eventProof;
					if(j.missingDomain!=uint.max){
						auto prefixProof="(QSym.BindingScalar"~to!string(j.missingDomain);
						auto missing=j.missingGuard?app("guardedMissing",prefixProof~".ValueCertificate.refinement ξ)"):
							prefixProof~".DomainCertificate.domain_correct ξ)";
						eventProof=app("restrictedMissingJump",prefix~q(j.witness)~" "~limits()~" (of_decide_eq_true rfl) (of_decide_eq_true rfl) "~missing);
					}else if(j.traversal!=uint.max){
						eventProof=app("restrictedPartialJump",prefix~limits()~" (of_decide_eq_true rfl) "~apos~" "~boundsProof()~" "~numeric(arena.real_(-1),Rational(-1)));
					}else{
						auto mass=*j.clipped;
						cert.roots~=mass.from[0];
						string unused;
						auto hm=stepGridProof(mass,cert,unused);
						auto evidence=c.image?limits():germs~" rfl rfl";
						auto clipped=app(c.image?"restrictedJumpFromLimits":"restrictedJump",prefix~q(mass.value)~" "~evidence~
							" (of_decide_eq_true rfl) "~boundsProof()~" ("~hm~")");
						if(pointProbe){
							hit|=a==sample&&!mass.value.zero;
							probe=app("PointCuts.atom",q(sample)~" "~q(a)~" "~q(mass.value)~" "~clipped~" "~probe);
						}else{
							auto atom=app("atomTerm",q(a)~" "~q(mass.value)~" "~apos~" "~numeric(arena.real_(mass.value),mass.value));
							eventProof="(Eq.trans "~clipped~" "~atom~")";
						}
					}
					if(!pointProbe) selected="(List.Forall₂.cons "~eventProof~" "~selected~")";
				}
				law=app("moveBreak",law~" "~eq);
				events="((("~q(a)~" : ℝ), "~name(j.event)~".eval ξ ρ) :: "~events~")";
			}
			tail=cert.save(grid~"Checked "~f~" "~w~" "~lo~" "~events,app(j.kind==JoinKind.smooth?"pass":"cut",bounds~"rfl "~cells[i]~" "~law~" "~tail));
		}
		string args;
		if(changed){
			string range; enforce(gridChangeRange(c.change,c.body,range,cert,c.image),"missing coordinate range");
			args=grid~"ScalarChange."~to!string(c.change)~" ";
			if(c.traceRange){
				continuous=checkTraces?app("Checked.rangeIn",tail~" "~range~" "~traces):
					"(Distribution.GraphFibre.Coordinates.VariationChart.RangeIn.univ "~app("Checked.chart",tail)~")";
			}else args~=range~" ";
		}
		string sampled(uint id,Rational v){
			return "(Eq.trans "~cert.numericProof(id,sample,q(v))~" (Eq.symm "~numeric(arena.real_(v),v)~"))";
		}
		if(c.image){
			if(restricted) args~=cert.functionAt(c.outerPredicate)~" ";
			if(pointProbe){
				auto answer=hit?"rfl":app("sampleImage",args~sampled(c.body,c.sampledValue)~" "~sampled(c.weight,c.sampledWeight));
				return app("probeImageAt",args~q(sample)~" "~numeric(arena.at(nodes[c.query].data),sample)~" "~tail~" "~continuous~" "~probe~" "~answer);
			}
			return app(restricted?"finishImageRestricted":"finishImage",args~tail~" "~continuous~" "~selected);
		}
		if(c.flatMass) return app("massFlatChange",args~numeric(arena.real_(0),Rational(0))~" "~tail~" "~continuous~" "~jumps);
		if(probing){
			args~=q(sample)~" "~numeric(arena.at(nodes[c.query].data),sample)~" "~tail~" ";
			if(changed) args~=continuous~" ";
			args~=probe;
			if(!hit){
				if(changed) args~=" "~sampled(c.body,c.sampledValue);
				args~=" "~sampled(c.weight,c.sampledWeight);
			}
			return app((c.traceRange?"probeRange":changed?"probeChange":"probe")~(hit?"Cut":"Regular"),args);
		}
		if(changed){
			return restricted?app("finishChangeRestricted",args~cert.functionAt(c.outerPredicate)~" "~tail~" "~continuous~" "~selected):
				app("finishChange",args~tail~" "~continuous);
		}
		return restricted?app("finishRestricted",pred~" "~tail~" "~selected):app("finish",tail);
	}
	private string stepGridProof(IntegralSolution s,SourceCertificates cert,ref string outputProof){
		auto q=&cert.q,app=&cert.app,atPoint=&cert.atPoint,functionAt=&cert.functionAt;
		auto save=&cert.save,numericProof=&cert.numericProof,affineProof=&cert.affineProof;
		alias Linear=SourceCertificates.Linear;
		alias Piece=SourceCertificates.Piece;
		auto uniform=&cert.uniform,piece=&cert.piece,exponential=&cert.exponential;
		// A scale that cannot vanish, by its form.
		string scalarNonzero(Term t){
			enum src="Distribution.StepSource.";
			auto v=arena.view(t);string eval(Term x){return "(n"~to!string(x.id)~".eval ξ)";}
			if(arena.isNumber(t))return "("~src~"Nonvanishing.literal "~q(arena.number(t).re)~" (Numeric.calculate_sound ξ n"~to!string(t.id)~" "~q(arena.number(t).re)~" rfl) rfl)";
			if(v.op==Op.inv)return "("~src~"Nonvanishing.inv "~eval(arena.viewChild(t,0))~")";
			if(v.op==Op.builtin)return "("~src~"Nonvanishing.pi rfl)";
			return "("~src~"Nonvanishing.mul "~scalarNonzero(arena.viewChild(t,0))~" "~scalarNonzero(arena.viewChild(t,1))~")";
		}
		string nonzero(uint id){
			enum src="Distribution.StepSource.";
			auto n=nodes[id];if(n.op==BoundOp.scalar)return scalarNonzero(arena.at(n.data));
			auto v=arena.view(arena.at(n.data));
			if(v.op==Op.inv)return "("~src~"Nonvanishing.inv ("~name(n.a)~".eval ξ ρ))";
			return "("~src~"Nonvanishing.mul "~nonzero(n.a)~" "~nonzero(n.b)~")";
		}
		string densityUniform(string region,Rational sample){
			auto proof=app("uniform_const",region~" (some (1 : ℝ))"),program="Distribution.DensityProgram.lebesgue";
			foreach(id;s.from){
				program="(Distribution.DensityProgram.weight "~functionAt(id)~" "~program~")";
				proof=save("Distribution.StepSource.Uniform "~region~" (Distribution.DensityProgram.density "~program~")",app("uniform_binary","Value.mul "~proof~" "~uniform(id,region,sample)));
			}
			return proof;
		}
		string delegate(uint,Rational) @safe zero;
		string zeroRaw(uint id,Rational point){
			auto n=nodes[id];
			if(!depends(at(id),0)){
				auto term=scalarBody(at(id),arena.real_(point));
				if(term!=Term.init){
					auto v=simplify(arena,term);
					if(!v.exhausted&&arena.isNumber(v.output)&&arena.number(v.output).zero){
						auto sort=arena.sort(term);cert.numericTerms~=term;
						return app("zero_numeric"~(sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":"R"),"ξ n"~to!string(term.id)~" rfl");
					}
				}
			}
			if(n.op!=BoundOp.primitive)return "";auto op=arena.view(arena.at(n.data));
			if(op.op==Op.mask){
				auto pred=scalarBody(at(n.a),arena.real_(point));
				if(pred!=Term.init){auto v=simplify(arena,pred);if(!v.exhausted&&v.output==arena.boolean(false))
					return app("zero_mask_false",atPoint(n.b,point)~" "~numericProof(n.a,point,"false"));}
				auto h=zero(n.b,point);return h.length?app("zero_mask",atPoint(n.a,point)~" "~h):"";
			}
			if(op.op==Op.builtin&&op.value>=Builtin.castNZ&&op.value<=Builtin.castQR){
				auto h=zero(n.a,point);return h.length?app("zero_"~builtinInfo(cast(Builtin)op.value).code,h):"";
			}
			auto a=zero(n.a,point),b=n.b==uint.max?"":zero(n.b,point);
			bool add=op.op==Op.add||op.op==Op.builtin&&(op.value==Builtin.addN||op.value==Builtin.addZ||op.value==Builtin.addQ);
			bool mul=op.op==Op.mul||op.op==Op.builtin&&(op.value==Builtin.mulN||op.value==Builtin.mulZ||op.value==Builtin.mulQ);
			if(add&&a.length&&b.length){
				if(op.op==Op.add)return app("zero_add",a~" "~b);
				return app("zero_binary","Functions."~builtinInfo(cast(Builtin)op.value).code~" (_root_.zero_add 0) "~a~" "~b);
			}
			if(mul&&(a.length||b.length)){
				bool left=a.length!=0;
				if(op.op==Op.mul)return app("zero_mul_"~(left?"left":"right"),"(a := "~atPoint(n.a,point)~") (b := "~atPoint(n.b,point)~") "~(left?a:b));
				return app("zero_binary_"~(left?"left":"right"),"Functions."~builtinInfo(cast(Builtin)op.value).code~" (fun v => _root_."~(left?"zero_mul":"mul_zero")~" v) "~atPoint(left?n.b:n.a,point)~" "~(left?a:b));
			}
			return "";
		}
		zero=(uint id,Rational point) @safe {
			auto proof=zeroRaw(id,point);return proof.length?save("Distribution.StepSource.ZeroOrUndefined "~atPoint(id,point),proof):"";
		};
		string densityZero(Rational point){
			string proof,program="Distribution.DensityProgram.lebesgue";
			foreach(id;s.from){
				auto values="(a := (Distribution.DensityProgram.density "~program~" ("~q(point)~" : ℝ))) (b := "~atPoint(id,point)~") ";
				program="(Distribution.DensityProgram.weight "~functionAt(id)~" "~program~")";
				if(proof.length)proof=app("zero_mul_left",values~proof);
				else{auto h=zero(id,point);if(h.length)proof=app("zero_mul_right",values~h);}
				if(proof.length)proof=save("Distribution.StepSource.ZeroOrUndefined (Distribution.DensityProgram.density "~program~" ("~q(point)~" : ℝ))",proof);
			}
			enforce(proof.length,"missing step tail witness");return proof;
		}
		if(s.gaussian&&s.bell.symbolic){
			// The density is a scale times a polynomial times the exponential of
			// a quadratic, weight by weight; the exponent is a quadratic by its
			// structure, with the coefficients the rule built. The kernel checks
			// the polynomial of the moments and evaluates the curvature.
			auto d=s.bell;enum src="Distribution.StepSource.";
			string literal(uint id,Rational value){return "(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~q(value)~" rfl)";}
			string join(string a,string b){return a.length&&b.length?"("~src~"Quadratic.add "~a~" "~b~")":a.length?a:b;}
			auto program="Distribution.DensityProgram.lebesgue";string exponent;AxisCoefficient[] poly;
			auto evidence="("~src~"bell_polynomial ("~src~"polynomial_one "~SourceCertificates.everywhere~"))";
			foreach(id;s.from){
				string part;AxisCoefficient[] factor,joined;auto w=cert.bell(id,part,factor);
				program="(Distribution.DensityProgram.weight "~functionAt(id)~" "~program~")";
				evidence=cert.bellProduct(evidence,poly,w,factor,joined);poly=joined;exponent=join(exponent,part);
			}
			if(d.zero0!=uint.max)exponent="("~src~"Quadratic.fill0 "~literal(d.zero0,Rational(0))~" "~exponent~")";
			if(d.zero1!=uint.max)exponent="("~src~"Quadratic.fill1 "~literal(d.zero1,Rational(0))~" "~exponent~")";
			// The monomials of a row, of which `count` are there, and the
			// balanced sum of so many terms.
			size_t count;
			string rowProof(Rational[] row,uint[] literals){
				string h=src~"RowTerms.done";
				foreach_reverse(i,c;row){
					if(literals[i]!=uint.max){++count;h="("~src~"RowTerms.term "~q(c)~" "~literal(literals[i],c)~" "~h~")";}
					else h=d.zero1!=uint.max?"("~src~"RowTerms.vanish "~literal(d.zero1,Rational(0))~" "~h~")":"("~src~"RowTerms.zero "~h~")";
				}
				return h;
			}
			string sums(size_t n){return n==1?src~"Sums.one":"("~src~"Sums.add "~sums(n/2)~" "~sums(n-n/2)~")";}
			string list(Rational[] row){string r="[";foreach(i,c;row)r~=(i?", ":"")~q(c);return r~"]";}
			if(d.curved){
				// The rows meet a table that the statement evaluates: which of
				// its rows are zero decides the coefficients. A rational that is
				// not a numeral is elaborated to its end only later, and until
				// then such a row cannot be decided; a monomial that is skipped
				// does not name it again. So the table stands as `(… :)`, which
				// elaborates it to its end first.
				enforce(d.nonzero==uint.max||nonvanishing(d.nonzero),"scale may vanish");
				if(d.tables.length){
					// Each coefficient that is present meets the rows of its table
					// that are not zero, and one of them cannot vanish: a closed
					// rational other than zero, or by its form.
					enforce(poly.length==d.tables.length,"Gaussian coefficients changed");
					string monomials=src~"MomentTerms.done",tables;
					foreach_reverse(j,rows;d.tables){
						string table;
						foreach_reverse(l,row;rows){
							auto present=poly[j].present&&(row.length>1||!row[0].zero);
							monomials="("~src~"MomentTerms."~(present?"present "~rowProof(row,d.tableLiterals[j][l]):"absent "~list(row))~" "~monomials~")";
							table=list(row)~(table.length?", ":"")~table;
						}
						tables="["~table~"]"~(tables.length?", ":"")~tables;
					}
					string witness;
					if(!d.maskPolynomial){
						enforce(d.witness<poly.length&&poly[d.witness].present&&nonvanishingCoefficient(poly[d.witness].term),"coefficient may vanish");
						auto w=poly[d.witness].term;Rational value;Term term;
						witness="("~src~"SomeNonvanishing.here "~(closedRational(w,value,term)?"("~src~"Nonvanishing.literal "~q(value)~" "~cert.closedProof(w,value)~" rfl)":nonzero(w.id))~")";
						foreach(i;0..d.witness)witness="("~src~"SomeNonvanishing.later "~witness~")";
					}
					auto steady=d.nonzero==uint.max?"trivial":nonzero(d.nonzero);
					// The factors that may vanish are under the mask; the others
					// cannot, by their form.
					auto factors=!d.maskScale&&!d.maskPolynomial?steady~" "~witness:
						"("~src~"VanishMask."~(!d.maskPolynomial?"scale "~witness:d.maskScale?"both rfl":"polynomial "~steady~" rfl")~")";
					return "Distribution.DensityProgram.presentation_mass_gaussian_curvature_moments"~(d.maskScale||d.maskPolynomial?"_masked ":" ")~program~" (["~tables~"] :) "~evidence~" "~exponent~" rfl rfl "~
						factors~" "~monomials~" "~sums(count)~" "~literal(d.factor,Rational(-1)/Rational(2))~" "~
						literal(d.exponent,Rational(-1)/Rational(4))~" "~literal(d.scale,Rational(-1))~" rfl";
				}
				// A row that is not zero meets its power of `h`; the first has none.
				string monomials=src~"MomentTerms.done",table;
				foreach_reverse(l,row;d.rows){
					auto present=row.length>1||!row[0].zero;
					monomials="("~src~"MomentTerms."~(!present?"absent "~list(row):(l?"present ":"bare ")~rowProof(row,d.rowLiterals[l]))~" "~monomials~")";
					table=list(row)~(table.length?", ":"")~table;
				}
				return "Distribution.DensityProgram.presentation_mass_gaussian_curvature"~(d.maskScale?"_masked ":" ")~program~" (["~table~"] :) "~evidence~" "~exponent~" rfl "~
					(d.maskScale?"":(d.nonzero==uint.max?"trivial":nonzero(d.nonzero))~" ")~monomials~" "~sums(count)~" "~literal(d.factor,Rational(-1)/Rational(2))~" "~
					literal(d.exponent,Rational(-1)/Rational(4))~" "~literal(d.scale,Rational(-1))~" rfl";
			}
			if(d.rows.length){
				// Each coefficient that is present meets the moments of its power.
				enforce(poly.length==d.rows.length,"Gaussian coefficients changed");
				string monomials=src~"MomentTerms.done",table;
				foreach_reverse(j,row;d.rows){
					monomials="("~src~"MomentTerms."~(poly[j].present?"present "~rowProof(row,d.rowLiterals[j]):"absent "~list(row))~" "~monomials~")";
					table=list(row)~(table.length?", ":"")~table;
				}
				return "Distribution.DensityProgram.presentation_mass_gaussian_moments "~program~" ["~table~"] "~q(d.c2)~" "~q(d.vertex)~" "~q(d.width)~" "~evidence~" "~exponent~
					" "~cert.closedProof(at(d.curvature),d.c2)~" rfl "~monomials~" "~sums(count)~" "~literal(d.exponent,d.vertex)~" "~literal(d.scale,d.width)~" rfl";
			}
			auto monomials=rowProof(d.moments,d.literals);
			return "Distribution.DensityProgram.presentation_mass_gaussian_symbolic "~program~" "~list(d.moments)~" "~q(d.c2)~" "~q(d.vertex)~" "~q(d.width)~" "~evidence~" "~exponent~
				" "~cert.closedProof(at(d.curvature),d.c2)~" rfl "~monomials~" "~sums(count)~" "~literal(d.exponent,d.vertex)~" "~literal(d.scale,d.width)~" rfl";
		}
		if(s.gaussian){
			// The density is a polynomial times the exponential of a quadratic
			// everywhere, weight by weight; the kernel checks the antiderivative.
			auto d=s.bell;enum whole="(⊤ : Filter ℝ)";
			auto program="Distribution.DensityProgram.lebesgue";bool scaled;
			auto evidence="(Limit.EventualExp.polynomial (l := ⊤) (Distribution.StepSource.polynomial_one "~SourceCertificates.everywhere~"))";
			foreach(id;s.from){
				bool part;auto w=cert.exponentialTail(id,whole,false,false,part);
				program="(Distribution.DensityProgram.weight "~functionAt(id)~" "~program~")";
				evidence=part||scaled?"(Limit.EventualScaled."~(part&&scaled?"mul":scaled?"times":"after")~" "~evidence~" "~w~")":"(Limit.EventualExp.mul "~evidence~" "~w~")";
				scaled=scaled||part;
			}
			string literal(uint id,Rational value){return "(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~q(value)~" rfl)";}
			string list="[";foreach(i,c;d.primitive)list~=(i?", ":"")~q(c);list~="]";
			return "Distribution.DensityProgram.presentation_mass_gaussian"~(scaled?"_scaled ":" ")~program~" (R := "~list~") "~q(d.constant)~" "~q(d.c0)~" "~q(d.c1)~" "~q(d.c2)~" "~
				q(d.vertex)~" "~q(d.width)~" "~evidence~" rfl "~literal(d.factor,d.constant)~" "~literal(d.exponent,d.vertex)~" "~literal(d.scale,d.width)~" rfl";
		}
		// A polynomial over a power of the axis, by its structure: a
		// polynomial, the inverse of a monomial, and sums and products of
		// such. The polynomial stays symbolic; Lean computes it where the
		// certificate compares it.
		struct Quotient{string proof,poly;size_t power;}
		// Around a pole that is not zero the value is taken at the axis
		// plus the pole, and its polynomials are moved along.
		string functionAround(uint id,Rational pole){
			return pole.zero?functionAt(id):"(fun y : ℝ => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some (y + (("~cert.q(pole)~" : ℚ) : ℝ))) ρ))";
		}
		// A polynomial, moved along the axis by a pole that is not zero.
		Quotient polynomialAround(uint id,Rational pole){
			enum src="Distribution.StepSource.";
			auto w=cert.piece(id,cert.everywhere,"",Rational(0));
			return pole.zero?Quotient(w.proof,w.poly,0):
				Quotient("("~src~"polynomial_translate "~cert.q(pole)~" "~w.proof~")","("~src~"polyTranslate "~cert.q(pole)~" "~w.poly~")",0);
		}
		Quotient quotient(uint id,Rational pole){
			enum src="Distribution.StepSource.";
			Rational[] p;
			Quotient polynomial(uint id){return polynomialAround(id,pole);}
			if(axisPolynomial(id,p))return polynomial(id);
			auto n=nodes[id];enforce(n.op==BoundOp.primitive,"unsupported quotient");
			auto op=arena.view(arena.at(n.data));Quotient r;
			string monomial(size_t k){return "("~src~"polyMonomial 1 "~to!string(k)~")";}
			if(op.op==Op.inv){
				Rational[] m;enforce(axisPolynomial(n.a,m),"inverse of another expression");
				m=polyTranslate(m,pole);
				while(m.length&&m[$-1].zero)m.length=m.length-1;
				enforce(m.length>=2,"inverse of a constant");
				auto inner=polynomial(n.a);
				r.power=m.length-1;r.poly="[("~cert.q(m[$-1])~")⁻¹]";
				r.proof="("~src~"ratio_inv "~inner.proof~" "~cert.q(m[$-1])~" "~to!string(r.power)~" rfl)";
			}else{
				enforce(op.op==Op.add||op.op==Op.mul,"unsupported quotient operation");
				auto a=quotient(n.a,pole),b=quotient(n.b,pole);bool add=op.op==Op.add,both=a.power&&b.power;
				r.power=add&&!both?(a.power?a.power:b.power):a.power+b.power;
				if(!add)r.poly="("~src~"polyMul "~a.poly~" "~b.poly~")";
				else r.poly="("~src~"polyAdd "~(b.power?"("~src~"polyMul "~a.poly~" "~monomial(b.power)~")":a.poly)~" "~
					(a.power?"("~src~"polyMul "~b.poly~" "~monomial(a.power)~")":b.poly)~")";
				r.proof="("~src~"ratio_"~(add?"add":"mul")~(both?"":a.power?"_right":"_left")~" "~a.proof~" "~b.proof~")";
			}
			r.proof=save(src~"RatioOn "~functionAround(id,pole)~" "~r.poly~" "~to!string(r.power),r.proof);
			return r;
		}
		// Such a quotient in a product with factors that do not mention the
		// axis: each factor of the product is a quotient, a polynomial or
		// such a factor, and the products follow its structure.
		struct Part{string proof,scale,poly;size_t power;bool pole;}
		Part fraction(uint id,Rational pole){
			enum src="Distribution.StepSource.";
			Rational[] p;size_t power;
			if(axisRatio(id,p,power,pole)){
				auto w=quotient(id,pole);
				return Part("("~src~"Fraction."~(power?"ratio ":"polynomial ")~w.proof~")","none",w.poly,w.power,power!=0);
			}
			if(!depends(at(id),0)){
				auto c=cert.outside(id);
				return Part("("~src~"Fraction.scale "~c~")","(some "~c~")","[1]",0,false);
			}
			auto n=nodes[id];enforce(n.op==BoundOp.primitive&&arena.view(arena.at(n.data)).op==Op.mul,"unsupported factor of a quotient");
			auto a=fraction(n.a,pole),b=fraction(n.b,pole);Part r;
			r.poly="("~src~"polyMul "~a.poly~" "~b.poly~")";r.power=a.power+b.power;r.pole=a.pole||b.pole;
			r.scale="("~src~"joinScale "~a.scale~" "~b.scale~")";
			r.proof=save(src~"Fraction "~functionAround(id,pole)~" "~r.scale~" "~r.poly~" "~to!string(r.power)~" "~(r.pole?"true":"false"),
				"("~src~"Fraction.mul "~a.proof~" "~b.proof~")");
			return r;
		}
		// A polynomial times the logarithm of the axis minus a pole, plus a
		// polynomial, by its structure: a polynomial, that logarithm, and
		// sums and products of such in which a logarithm meets polynomials
		// only. The two polynomials stay symbolic.
		struct Logarithm{string proof,p,q;bool found;}
		Logarithm logarithm(uint id,Rational pole){
			enum src="Distribution.StepSource.";
			Rational[] coefficients;
			if(axisPolynomial(id,coefficients)){auto w=polynomialAround(id,pole);return Logarithm(w.proof,"[]",w.poly,false);}
			auto n=nodes[id];enforce(n.op==BoundOp.primitive,"unsupported logarithm");
			auto op=arena.view(arena.at(n.data));Logarithm r;r.found=true;
			if(op.op==Op.builtin){
				Rational at_;uint closedTerm;
				enforce(op.value==Builtin.logR&&logArgument(n.a,at_,closedTerm)&&at_==pole,"logarithm of another argument");
				r.p="[1]";r.q="[]";
				// The closed term may stand on either side of the axis.
				r.proof=pole.zero?src~"log_axis":"("~src~"log_axis_shifted"~(nodes[n.a].a==closedTerm?"' ":" ")~cert.q(pole)~
					" (Numeric.calculate_sound ξ n"~to!string(nodes[closedTerm].data)~" "~cert.q(Rational(0)-pole)~" rfl))";
			}else{
				enforce(op.op==Op.add||op.op==Op.mul,"unsupported operation on a logarithm");
				auto a=logarithm(n.a,pole),b=logarithm(n.b,pole);bool add=op.op==Op.add;
				enforce(a.found||b.found,"polynomial that is not one");
				string poly(string f,string x,string y){return "("~src~"poly"~f~" "~x~" "~y~")";}
				if(add){
					r.p=a.found&&b.found?poly("Add",a.p,b.p):a.found?a.p:b.p;r.q=poly("Add",a.q,b.q);
					r.proof="("~src~"log_add"~(a.found&&b.found?"":a.found?"_right":"_left")~" "~a.proof~" "~b.proof~")";
				}else{
					enforce(!(a.found&&b.found),"product of logarithms");
					r.p=a.found?poly("Mul",a.p,b.q):poly("Mul",a.q,b.p);r.q=poly("Mul",a.q,b.q);
					r.proof="("~src~"log_mul"~(a.found?"_right":"_left")~" "~a.proof~" "~b.proof~")";
				}
			}
			r.proof=save(src~"LogOn "~functionAround(id,pole)~" "~r.p~" "~r.q,r.proof);
			return r;
		}
		// Such a value in a product with factors that do not mention the
		// axis: each factor of the product is such a value, a polynomial or
		// such a factor, and the products follow its structure.
		struct LogPart{string proof,scale,p,q;bool found;}
		LogPart logFraction(uint id,Rational pole){
			enum src="Distribution.StepSource.";
			Rational[] p,q;bool found;
			if(axisLogarithm(id,p,q,pole,found)){
				auto w=logarithm(id,pole);
				return LogPart("("~src~"LogFraction."~(found?"log ":"polynomial ")~w.proof~")","none",found?w.p:"[]",w.q,found);
			}
			if(!depends(at(id),0)){
				auto c=cert.outside(id);
				return LogPart("("~src~"LogFraction.scale "~c~")","(some "~c~")","[]","[1]",false);
			}
			auto n=nodes[id];enforce(n.op==BoundOp.primitive&&arena.view(arena.at(n.data)).op==Op.mul,"unsupported factor of a logarithm");
			auto a=logFraction(n.a,pole),b=logFraction(n.b,pole);LogPart r;
			enforce(!(a.found&&b.found),"product of logarithms");
			string product(string x,string y){return "("~src~"polyMul "~x~" "~y~")";}
			r.found=a.found||b.found;r.scale="("~src~"joinScale "~a.scale~" "~b.scale~")";
			r.p=a.found?product(a.p,b.q):product(a.q,b.p);r.q=product(a.q,b.q);
			r.proof=save(src~"LogFraction "~functionAround(id,pole)~" "~r.scale~" "~r.p~" "~r.q~" "~(r.found?"true":"false"),
				"("~src~"LogFraction.mul_"~(a.found?"right ":"left ")~a.proof~" "~b.proof~")");
			return r;
		}
		// An observation between bounds, above or below one; as a summand in
		// the form that adds, of its weight by itself.
		string between(IntegralSolution q,bool summand){
			auto d=q.bounds;enum everywhere=SourceCertificates.everywhere;
			string ev(uint id){return "("~name(id)~".eval ξ ρ)";}
			string truth(bool b){return b?"true":"false";}
			auto a=ev(d.lower),b=ev(d.upper),m=ev(d.minusOne);
			auto flags=d.below?truth(d.strictUpper)~" "~b:d.half?truth(d.strictLower)~" "~a~" "~m:
				truth(d.swap)~" "~truth(d.strictLower)~" "~truth(d.strictUpper)~" "~a~" "~b~" "~m;
			auto guard=d.below?"(fun x : ℝ => Distribution.StepSource.compare "~truth(d.strictUpper)~" (some x) "~b~")":
				d.half?"(fun x : ℝ => Distribution.StepSource.compare "~truth(d.strictLower)~" "~a~" (some x))":
				"(Distribution.StepSource.intervalGuard "~truth(d.swap)~" "~truth(d.strictLower)~" "~truth(d.strictUpper)~" "~a~" "~b~")";
			auto termsName="Distribution.StepSource."~(d.below?"UpperTerms":d.half?"HalfLineTerms":"IntervalTerms");
			// The first weight is the guard around the value, by evaluation.
			auto body=q.from[0],value=d.unit!=uint.max?"(fun _ : ℝ => some (1 : ℝ))":functionAt(d.value);
			// A value under the strict guard of its domain. Around the mask that
			// guard follows the negations of the comparisons of the mask.
			string under(uint id){return "("~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))";}
			string domain;
			// The guard that the axis is not zero stands there in the same way.
			// The conjunction of the two is the guard of each: of the domain
			// around that of the axis.
			enforce(d.joined?d.domain!=uint.max&&d.axis!=uint.max:d.domain==uint.max||d.axis==uint.max,"two domains of a value");
			auto guarded=d.joined?d.both:d.domain!=uint.max?d.domain:d.axis;
			if(guarded!=uint.max){
				auto inner=value;
				value=d.joined?"(fun x : ℝ => Binding.guardValue "~under(d.domain)~" (Binding.guardValue "~under(d.axis)~" ("~inner~" x)))":
					"(fun x : ℝ => Binding.guardValue "~under(guarded)~" ("~inner~" x))";
				auto regroup="(congrArg (Value.mask _) (Distribution.StepSource.guard_and_"~(d.joined==1?"left":"right")~" _ _ _))";
				if(d.hoisted){
					string comparison(uint id,string rest){
						auto c=nodes[id];
						return app("MaskDomain."~(rest.length?"cons ":"last ")~truth(strictComparison(id))~" "~under(c.a)~" "~under(c.b),rest);
					}
					auto conjunction=nodes[d.guard];
					auto evidence=d.half?comparison(d.guard,""):comparison(conjunction.a,comparison(conjunction.b,""));
					auto around="Distribution.StepSource.MaskDomain.mask (q := "~under(guarded)~") "~evidence~" "~under(d.value);
					domain=d.joined?"(fun x => ("~around~").trans "~regroup~")":"(fun x => "~around~")";
				}else if(d.joined) domain=d.nested?"(fun x => (Distribution.StepSource.mask_mask _ _ _).trans "~regroup~")":"(fun x => "~regroup~")";
			}
			auto shape=save("∀ x : ℝ, "~functionAt(body)~" x = Value.mask ("~guard~" x) ("~value~" x)",
				d.unit!=uint.max?"(fun _ => Distribution.StepSource.bracket_real _ _ "~numericProof(d.unit,Rational(0),"1")~")":
				domain.length?domain:d.nested?"(fun _ => Distribution.StepSource.mask_mask _ _ _)":"(fun _ => rfl)");
			auto program="(Distribution.DensityProgram.weight "~functionAt(body)~" Distribution.DensityProgram.lebesgue)";
			auto masked=summand?save("Distribution.StepSource.Masked "~functionAt(body)~" "~guard~" "~value,"(Distribution.StepSource.Masked.mk "~shape~")"):
				save("Distribution.StepSource.Masked (Distribution.DensityProgram.density "~program~") "~guard~" "~value,app("masked_first",shape));
			string[] factors;
			foreach(id;q.from[1..$]){
				auto w=exponential(id);
				program="(Distribution.DensityProgram.weight "~functionAt(id)~" "~program~")";
				value="(fun x : ℝ => Value.mul ("~value~" x) ("~functionAt(id)~" x))";
				masked=save("Distribution.StepSource.Masked (Distribution.DensityProgram.density "~program~") "~guard~" "~value,app("masked_times",masked~" "~w.proof));
				factors~=w.proof;
			}
			if(d.direct){
				// The value as a scale, a constant and the exponential of a linear
				// exponent by its structure, with the coefficients the rule built:
				// the observation is the integral of its mask, under the strict
				// guard of its domain where it has one.
				enforce(!summand&&d.terms.length==1&&(d.terms[0].rateTerm||d.terms[0].curvatureTerm||d.terms[0].ratioTerm||d.terms[0].logTerm)&&q.from.length==1,"bad direct observation");
				auto r=d.terms[0],g=r.bell;string exponent;AxisCoefficient[] poly;
				string literal(uint id,Rational value){return "(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~cert.q(value)~" rfl)";}
				// A summand that is a term in front of the value `subject`:
				// the observation of the value, plus the term times the
				// distance of the bounds. Under the guard of the domain of the
				// value the term comes out of that guard first.
				string summand_(uint subject,string strictness,string observed){
					if(d.constant==uint.max)return observed;
					enum src="Distribution.StepSource.";
					auto other=d.axis!=uint.max?"(fun x : ℝ => Binding.guardValue "~under(d.axis)~" ("~functionAt(subject)~" x))":functionAt(subject);
					auto split=d.axis!=uint.max?"(fun _ => "~src~"guard_add_first _ _ _)":"(fun _ => "~src~"value_add_comm _ _)";
					return "("~src~"between_add_constant "~strictness~" "~other~" "~cert.outside(d.constant)~" "~literal(d.minusOne,Rational(-1))~" "~split~" "~observed~")";
				}
				if(r.logTerm){
					// The value as a polynomial times the logarithm plus a
					// polynomial, by its structure. The kernel checks the
					// antiderivative against it; at each bound its two
					// polynomials are rows. Around a pole that is not zero all
					// of this is about the value at the axis plus the pole,
					// between the bounds moved by it.
					enum src="Distribution.StepSource.";
					enforce(!d.half,"bad logarithm between bounds");
					// With factors that do not mention the axis the theorem
					// has their product in front.
					bool scaled=r.ratioScale.length!=0;auto pole=r.ratioPole;string proof;
					auto subject=d.inner!=uint.max?d.inner:d.value;
					if(scaled){auto part=logFraction(subject,pole);enforce(part.found,"factor without a logarithm");proof=part.proof;}
					else proof=logarithm(subject,pole).proof;
					if(d.axis!=uint.max){
						enforce(d.axisPositive&&d.axisPoint==pole,"domain of another logarithm");
						auto away="("~src~(pole.zero?"axis_positive ":"shifted_positive "~cert.q(pole)~" ")~literal(d.axisClosed,pole)~")";
						auto test=pole.zero?"fun x : ℝ => "~under(d.axis):
							"fun y : ℝ => "~name(d.axis)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some (y + (("~cert.q(pole)~" : ℚ) : ℝ))) ρ)";
						proof="("~src~(scaled?"LogFraction.guard":"log_guard")~" (g := "~test~") "~proof~" "~away~")";
					}
					string list(Rational[] row){string t="[";foreach(i,c;row)t~=(i?", ":"")~cert.q(c);return t~"]";}
					string sums(size_t n){return n==1?src~"Sums.one":"("~src~"Sums.add "~sums(n/2)~" "~sums(n-n/2)~")";}
					string row(Rational[] coefficients,uint[] literals){
						enforce(literals.length==coefficients.length&&literals[0]!=uint.max,"bad row of a logarithm");
						size_t count;string h=src~"RowTerms.done";
						foreach_reverse(i,c;coefficients){
							if(literals[i]!=uint.max){++count;h="("~src~"RowTerms.term "~cert.q(c)~" "~literal(literals[i],c)~" "~h~")";}
							else h="("~src~"RowTerms.zero "~h~")";
						}
						return h~" "~sums(count);
					}
					string rows;
					foreach(e;0..2){
						enforce(r.ends[e].rows.length==1,"bad literals of a logarithm");
						rows~=" "~row(g.primitive,r.ends[e].primitive)~" "~row(g.moments,r.ends[e].rows[0]);
					}
					auto strictness=truth(d.swap)~" "~truth(d.strictLower)~" "~truth(d.strictUpper);
					auto observed="("~src~"log_between"~(scaled?"_scaled ":" ")~strictness~" "~list(g.primitive)~" "~list(g.moments)~" "~proof~" rfl "~
						literal(r.rateZero,Rational(0))~" "~literal(d.minusOne,Rational(-1))~rows~")";
					if(!pole.zero)observed="("~src~"shift_between "~strictness~" "~cert.q(pole)~" "~literal(r.ratioMove,Rational(0)-pole)~" "~observed~")";
					observed=summand_(subject,strictness,observed);
					// Under the strict guard of a domain that does not mention
					// the axis that guard stays inside the mask of the bounds.
					if(d.domain!=uint.max)observed="("~src~"between_guard_integral "~strictness~" ("~name(dropIndex(at(d.domain)).id)~".eval ξ ρ) "~observed~")";
					return "Distribution.DensityProgram.presentation_mass_direct "~program~" "~masked~" "~observed;
				}
				if(r.ratioTerm){
					// The value as a polynomial over a power of the axis, by its
					// structure. The kernel checks the antiderivative against
					// it; at each bound its two polynomials are rows.
					enum src="Distribution.StepSource.";
					// Under the guard of its domain it is the same quotient.
					// With factors that do not mention the axis the theorem
					// has their product; without its mask it wants to know
					// that no bound is strict, or that the bounds are closed
					// on one side of zero.
					// Around a pole that is not zero all of this is about the
					// value at the axis plus the pole, between the bounds moved
					// by it; the observation is the same.
					bool scaled=r.ratioScale.length!=0;auto pole=r.ratioPole;
					auto subject=d.inner!=uint.max?d.inner:d.value;
					Quotient evidence;
					if(scaled){
						auto part=fraction(subject,pole);enforce(part.pole,"quotient without a pole");
						evidence=Quotient(part.proof,part.poly,part.power);
					}else evidence=quotient(subject,pole);
					if(d.axis!=uint.max){
						enforce(d.axisPoint==pole&&(d.axisClosed==uint.max)==pole.zero,"domain of another pole");
						auto away=pole.zero?src~"axis_nonzero":"("~src~"shifted_nonzero "~cert.q(pole)~" "~literal(d.axisClosed,Rational(0)-pole)~")";
						auto test=pole.zero?"fun x : ℝ => "~under(d.axis):
							"fun y : ℝ => "~name(d.axis)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some (y + (("~cert.q(pole)~" : ℚ) : ℝ))) ρ)";
						evidence.proof="("~src~(scaled?"Fraction.guard":"ratio_guard")~" (q := "~test~") "~evidence.proof~" "~away~")";
					}
					auto kind=scaled?(r.ratioPlain?"_scaled_plain ":"_scaled "):" ";
					string known;
					if(scaled&&r.ratioPlain){
						auto zero=literal(r.rateZero,Rational(0));
						Rational point;Term closed;
						string bound(uint id){enforce(closedRational(at(id),point,closed),"bound is not closed");return cert.closedProof(at(id),point);}
						known=!r.ratioClosed?" (Or.inl rfl)":" (Or.inr ("~src~(d.below?"below_closed "~bound(r.ratioUpper):d.half?"above_closed "~bound(r.ratioLower):
							"side_closed "~bound(r.ratioLower)~" "~bound(r.ratioUpper))~" "~zero~" rfl))";
					}
					string around(string flags,string observed){
						return pole.zero?observed:"("~src~"shift_"~flags~" "~cert.q(pole)~" "~literal(r.ratioMove,Rational(0)-pole)~" "~observed~")";
					}
					string list(Rational[] row){string t="[";foreach(i,c;row)t~=(i?", ":"")~cert.q(c);return t~"]";}
					string sums(size_t n){return n==1?src~"Sums.one":"("~src~"Sums.add "~sums(n/2)~" "~sums(n-n/2)~")";}
					string row(Rational[] coefficients,uint[] literals){
						enforce(literals.length==coefficients.length&&literals[0]!=uint.max,"bad row of a quotient");
						size_t count;string h=src~"RowTerms.done";
						foreach_reverse(i,c;coefficients){
							if(literals[i]!=uint.max){++count;h="("~src~"RowTerms.term "~cert.q(c)~" "~literal(literals[i],c)~" "~h~")";}
							else h="("~src~"RowTerms.zero "~h~")";
						}
						return h~" "~sums(count);
					}
					if(d.half){
						// Beyond one bound: the polynomial over the power of the
						// bound alone, with the opposite sign above it.
						enforce(r.ends[0].rows.length==1,"bad literals of a quotient");
						auto observed="("~src~"ratio_"~(d.below?"below":"above")~kind~
							truth(d.below?d.strictUpper:d.strictLower)~" "~to!string(r.ratioShift)~" "~list(g.moments)~" "~evidence.proof~" rfl "~
							literal(r.rateZero,Rational(0))~(d.below?"":" "~literal(d.minusOne,Rational(-1)))~" "~row(g.moments,r.ends[0].rows[0])~known~")";
						observed=around((d.below?"below ":"above ")~truth(d.below?d.strictUpper:d.strictLower),observed);
						// Under the strict guard of a domain that does not
						// mention the axis: the guard of the observation.
						if(d.domain!=uint.max)observed="("~src~"masked_guard_integral ("~name(dropIndex(at(d.domain)).id)~".eval ξ ρ) ("~src~"compare_"~(d.below?"upper":"lower")~"_cases _ _) "~observed~")";
						return "Distribution.DensityProgram.presentation_mass_direct "~program~" "~masked~" "~observed;
					}
					string rows;
					foreach(e;0..2){
						enforce(r.ends[e].rows.length==1,"bad literals of a quotient");
						rows~=" "~row(g.primitive,r.ends[e].primitive)~" "~row(g.moments,r.ends[e].rows[0]);
					}
					auto observed="("~src~"ratio_between"~kind~truth(d.swap)~" "~truth(d.strictLower)~" "~
						truth(d.strictUpper)~" "~to!string(r.ratioShift)~" "~list(g.primitive)~" "~list(g.moments)~" "~cert.q(g.constant)~" "~evidence.proof~" rfl "~
						literal(r.rateZero,Rational(0))~" "~literal(d.minusOne,Rational(-1))~" "~literal(g.factor,g.constant)~rows~known~")";
					observed=around("between "~truth(d.swap)~" "~truth(d.strictLower)~" "~truth(d.strictUpper),observed);
					observed=summand_(subject,truth(d.swap)~" "~truth(d.strictLower)~" "~truth(d.strictUpper),observed);
					// Between two bounds that guard stays inside their mask.
					if(d.domain!=uint.max)observed="("~src~"between_guard_integral "~truth(d.swap)~" "~truth(d.strictLower)~" "~truth(d.strictUpper)~
						" ("~name(dropIndex(at(d.domain)).id)~".eval ξ ρ) "~observed~")";
					return "Distribution.DensityProgram.presentation_mass_direct "~program~" "~masked~" "~observed;
				}
				auto hv=cert.bell(d.value,exponent,poly);
				if(g.zero0!=uint.max)exponent="(Distribution.StepSource.Quadratic.fill0 "~literal(g.zero0,Rational(0))~" "~exponent~")";
				if(g.zero1!=uint.max)exponent="(Distribution.StepSource.Quadratic.fill1 "~literal(g.zero1,Rational(0))~" "~exponent~")";
				enforce(g.nonzero==uint.max||nonvanishing(g.nonzero),"scale may vanish");
				auto side=d.below?"below":"above",strictness=truth(d.below?d.strictUpper:d.strictLower),steady=g.maskScale?"":(g.nonzero==uint.max?"trivial":nonzero(g.nonzero))~" ";
				string direct;
				if(r.rateTerm){
					// The rows of the antiderivative at the bound: the first is
					// zero, each of the others meets its power of the inverse
					// rate, and a monomial that is skipped has a coefficient
					// that is zero, or the bound is a closed zero. The statement
					// evaluates the table, which is elaborated to its end first.
					enum src="Distribution.StepSource.";
					auto vanish=r.boundZero?cert.closedProof(at(d.below?d.upper:d.lower),Rational(0)):"";
					size_t count;string monomials=src~"MomentTerms.done",table;
					string list(Rational[] row){string t="[";foreach(i,c;row)t~=(i?", ":"")~cert.q(c);return t~"]";}
					string sums(size_t n){return n==1?src~"Sums.one":"("~src~"Sums.add "~sums(n/2)~" "~sums(n-n/2)~")";}
					enforce(g.rows.length>1&&g.rows.length==g.rowLiterals.length,"bad table of a rate");
					foreach_reverse(l,row;g.rows){
						if(l){
							enforce(g.rowLiterals[l].length==row.length&&g.rowLiterals[l][0]!=uint.max,"bad row of a rate");
							string h=src~"RowTerms.done";
							foreach_reverse(i,c;row){
								if(g.rowLiterals[l][i]!=uint.max){++count;h="("~src~"RowTerms.term "~cert.q(c)~" "~literal(g.rowLiterals[l][i],c)~" "~h~")";}
								else h=r.boundZero?"("~src~"RowTerms.vanish "~vanish~" "~h~")":"("~src~"RowTerms.zero "~h~")";
							}
							monomials="("~src~"MomentTerms.present "~h~" "~monomials~")";
						}else monomials="("~src~"MomentTerms.absent "~list(row)~" "~monomials~")";
						table=list(row)~(table.length?", ":"")~table;
					}
					direct="("~src~"rate_"~side~(g.maskScale?"_masked ":" ")~strictness~" (["~table~"] :) "~hv~" "~exponent~" rfl "~
						steady~monomials~" "~sums(count)~" "~literal(r.rateZero,Rational(0))~")";
				}else{
					// The curvature cannot vanish, by its form; the literals are
					// half the constant and those of the vertex.
					enforce(nonvanishing(g.curvature),"curvature may vanish");
					direct="(Distribution.StepSource.curvature_"~side~(g.maskScale?"_masked ":" ")~strictness~" "~cert.q(g.constant)~" "~cert.q(r.half)~" "~hv~" "~exponent~" rfl "~
						steady~nonzero(g.curvature)~" "~literal(g.factor,r.half)~" "~literal(g.exponent,Rational(-1)/Rational(4))~" "~literal(g.scale,Rational(-1))~" "~
						literal(r.side,Rational(d.below?-1:1)/Rational(2))~" rfl)";
				}
				if(d.domain!=uint.max)direct="(Distribution.StepSource.masked_guard_integral ("~name(dropIndex(at(d.domain)).id)~".eval ξ ρ) (Distribution.StepSource.compare_"~(d.below?"upper":"lower")~"_cases _ _) "~direct~")";
				return "Distribution.DensityProgram.presentation_mass_direct "~program~" "~masked~" "~direct;
			}
			size_t next;
			string terms(uint id){
				enforce(next<d.terms.length,"missing interval term");auto r=d.terms[next];
				if(r.value!=id){
					auto sum=nodes[id];enforce(sum.op==BoundOp.primitive&&arena.view(arena.at(sum.data)).op==Op.add,"bad interval sum");
					auto left=terms(sum.a),right=terms(sum.b);
					return "("~termsName~".add "~left~" "~right~")";
				}
				++next;
				if(r.vertex){
					// The term everywhere, the bound at the vertex, the checks of
					// the Gaussian integral there, and the literals of the result.
					enum whole="(⊤ : Filter ℝ)";bool scaled;auto g=r.bell;
					auto hv=cert.exponentialTail(id,whole,false,false,scaled,true);
					string literal(uint id,Rational value){return "(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~cert.q(value)~" rfl)";}
					string list="[";foreach(i,c;g.primitive)list~=(i?", ":"")~cert.q(c);list~="]";
					return "("~termsName~"."~(scaled?"scaledGaussian":"gaussian")~" (R := "~list~") "~cert.q(g.constant)~" "~cert.q(g.c0)~" "~cert.q(g.c1)~" "~cert.q(g.c2)~" "~
						cert.q(g.vertex)~" "~cert.q(g.width)~" "~cert.q(r.point)~" "~cert.q(r.half)~" "~cert.q(r.rest)~" "~hv~" "~cert.closedProof(at(d.below?d.upper:d.lower),r.point)~" rfl "~
						literal(g.factor,r.half)~" "~literal(r.restLiteral,r.rest)~" "~literal(g.exponent,g.vertex)~" "~literal(g.scale,g.width)~" rfl)";
				}
				if(r.rateTerm){
					// The term as a scale, a polynomial and the exponential of a
					// linear exponent by its structure. The kernel checks the
					// rows of the antiderivative and the antiderivative of the
					// polynomial; at each bound the first meet their powers of
					// the inverse rate, and the second is a row of its own.
					enum src="Distribution.StepSource.";
					auto g=r.bell;string exponent;AxisCoefficient[] poly;
					auto hv=cert.bell(id,exponent,poly);
					string literal(uint id,Rational value){return "(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~cert.q(value)~" rfl)";}
					if(g.zero0!=uint.max)exponent="("~src~"Quadratic.fill0 "~literal(g.zero0,Rational(0))~" "~exponent~")";
					string list(Rational[] row){string t="[";foreach(i,c;row)t~=(i?", ":"")~cert.q(c);return t~"]";}
					string sums(size_t n){return n==1?src~"Sums.one":"("~src~"Sums.add "~sums(n/2)~" "~sums(n-n/2)~")";}
					auto symbolic=g.tables.length!=0;
					enforce(symbolic?poly.length==g.tables.length&&r.primitives.length==g.tables.length:g.rows.length>1&&g.primitive.length>1,"bad table of a rate");
					string[2] moments,flat;
					foreach(e;0..2){
						auto end=r.ends[e];
						enforce(symbolic?end.tables.length==g.tables.length&&end.primitives.length==g.tables.length:
							end.rows.length==g.rows.length&&end.primitive.length==g.primitive.length,"bad literals of a rate");
						auto vanish=end.zero?cert.closedProof(at(e?d.lower:d.upper),Rational(0)):"";
						size_t count;
						string rowProof(Rational[] row,uint[] literals){
							enforce(literals.length==row.length&&literals[0]!=uint.max,"bad row of a rate");
							string h=src~"RowTerms.done";
							foreach_reverse(i,c;row){
								if(literals[i]!=uint.max){++count;h="("~src~"RowTerms.term "~cert.q(c)~" "~literal(literals[i],c)~" "~h~")";}
								else h=end.zero?"("~src~"RowTerms.vanish "~vanish~" "~h~")":"("~src~"RowTerms.zero "~h~")";
							}
							return h;
						}
						string meet(bool present,Rational[] row,uint[] literals,string rest){
							return "("~src~"MomentTerms."~(present?"present "~rowProof(row,literals):"absent "~list(row))~" "~rest~")";
						}
						// The first row of a table is zero; a coefficient that is
						// absent meets nothing.
						string monomials=src~"MomentTerms.done";
						if(symbolic)foreach_reverse(j,rows;g.tables)foreach_reverse(l,row;rows)monomials=meet(l&&poly[j].present,row,end.tables[j][l],monomials);
						else foreach_reverse(l,row;g.rows)monomials=meet(l!=0,row,end.rows[l],monomials);
						moments[e]=monomials~" "~sums(count);
						count=0;string rows;
						if(symbolic){
							rows=src~"MomentTerms.done";
							foreach_reverse(j,row;r.primitives)rows=meet(poly[j].present,row,end.primitives[j],rows);
						}else rows=rowProof(g.primitive,end.primitive);
						flat[e]=rows~" "~sums(count);
					}
					// The tables and the antiderivatives are evaluated by the
					// statement, and so elaborated to their end first.
					string tables,primitives;
					if(symbolic){
						foreach_reverse(rows;g.tables){
							string table;foreach_reverse(row;rows)table=list(row)~(table.length?", ":"")~table;
							tables="["~table~"]"~(tables.length?", ":"")~tables;
						}
						foreach_reverse(row;r.primitives)primitives=list(row)~(primitives.length?", ":"")~primitives;
						return "("~termsName~".rateTerms (["~tables~"] :) (["~primitives~"] :) "~hv~" "~exponent~" rfl rfl rfl "~
							moments[0]~" "~moments[1]~" "~flat[0]~" "~flat[1]~")";
					}
					foreach_reverse(row;g.rows)tables=list(row)~(tables.length?", ":"")~tables;
					return "("~termsName~".rate (["~tables~"] :) ("~list(g.primitive)~" :) "~hv~" "~exponent~" rfl rfl "~
						moments[0]~" "~moments[1]~" "~flat[0]~" "~flat[1]~")";
				}
				if(r.erf&&r.symbolic){
					// The term as a scale, a constant and the exponential of a
					// quadratic by its structure, with the coefficients the rule
					// built; the kernel evaluates the curvature and checks the
					// literals of the result.
					auto g=r.bell;string exponent;AxisCoefficient[] poly;
					auto hv=cert.bell(id,exponent,poly);
					string literal(uint id,Rational value){return "(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~cert.q(value)~" rfl)";}
					if(g.zero0!=uint.max)exponent="(Distribution.StepSource.Quadratic.fill0 "~literal(g.zero0,Rational(0))~" "~exponent~")";
					if(g.rows.length){
						// Under a polynomial: the kernel checks the rest and the
						// polynomial of the constant against it. At each bound
						// the rows of the rest meet their powers of the linear
						// coefficient, the first of them none, and the
						// polynomial of the constant is a row of its own. The
						// statement evaluates the table, which is elaborated to
						// its end first.
						enum src="Distribution.StepSource.";
						string list(Rational[] row){string t="[";foreach(i,c;row)t~=(i?", ":"")~cert.q(c);return t~"]";}
						string sums(size_t n){return n==1?src~"Sums.one":"("~src~"Sums.add "~sums(n/2)~" "~sums(n-n/2)~")";}
						size_t count;string vanish;
						string rowProof(Rational[] row,uint[] literals){
							enforce(literals.length==row.length&&literals[0]!=uint.max,"bad row of a rest");
							string h=src~"RowTerms.done";
							foreach_reverse(i,c;row){
								if(literals[i]!=uint.max){++count;h="("~src~"RowTerms.term "~cert.q(c)~" "~literal(literals[i],c)~" "~h~")";}
								else h=vanish.length?"("~src~"RowTerms.vanish "~vanish~" "~h~")":"("~src~"RowTerms.zero "~h~")";
							}
							return h;
						}
						string moments(size_t e){
							auto end=r.ends[e];enforce(end.rows.length==g.rows.length,"bad literals of a rest");
							vanish=end.zero?cert.closedProof(at(e?d.lower:d.upper),Rational(0)):"";count=0;
							string monomials=src~"MomentTerms.done";
							foreach_reverse(i,row;g.rows){
								auto present=row.length>1||!row[0].zero;
								monomials="("~src~"MomentTerms."~(!present?"absent "~list(row):(i?"present ":"bare ")~rowProof(row,end.rows[i]))~" "~monomials~")";
							}
							return monomials~" "~sums(count)~" ";
						}
						string table;foreach_reverse(row;g.rows)table=list(row)~(table.length?", ":"")~table;
						auto above=d.half&&!d.below?"":moments(0),below=d.below?"":moments(1);
						vanish="";count=0;auto constant=rowProof(g.moments,g.literals);
						return "("~termsName~".symbolicErfPolynomial (["~table~"] :) ("~list(g.moments)~" :) "~cert.q(g.c2)~" "~cert.q(g.vertex)~" "~cert.q(g.width)~" "~cert.q(r.point)~" "~
							cert.q(Rational(0)-g.c2)~" "~cert.q(r.offset)~" "~hv~" "~exponent~" "~cert.closedProof(at(g.curvature),g.c2)~" rfl rfl "~above~below~constant~" "~sums(count)~" "~
							(d.half?literal(r.unit,Rational(-1))~" ":"")~literal(g.factor,r.half)~" "~literal(g.exponent,g.vertex)~" "~literal(g.scale,g.width)~" rfl "~
							literal(r.sigma,Rational(0)-g.c2)~" "~literal(r.offsetLiteral,r.offset)~")";
					}
					return "("~termsName~".symbolicErf "~cert.q(g.constant)~" "~cert.q(g.c2)~" "~cert.q(g.vertex)~" "~cert.q(g.width)~" "~cert.q(r.point)~" "~cert.q(r.half)~" "~
						cert.q(Rational(0)-g.c2)~" "~cert.q(r.offset)~" "~hv~" "~exponent~" "~cert.closedProof(at(g.curvature),g.c2)~" rfl "~
						(d.half?literal(r.unit,Rational(-1))~" ":"")~literal(g.factor,r.half)~" "~literal(g.exponent,g.vertex)~" "~literal(g.scale,g.width)~" rfl "~
						literal(r.sigma,Rational(0)-g.c2)~" "~literal(r.offsetLiteral,r.offset)~")";
				}
				if(r.erf){
					// The term and the antiderivative of the rest everywhere, on a
					// half-line strictness in the bound, the checks of the Gaussian
					// integral and of the argument, and the literals of the result.
					enum whole="(⊤ : Filter ℝ)";bool scaled,unused;auto g=r.bell;
					auto hv=cert.exponentialTail(id,whole,false,false,scaled,true),hG=cert.exponentialTail(r.primitive,whole,false,false,unused);
					string literal(uint id,Rational value){return "(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~cert.q(value)~" rfl)";}
					string list="[";foreach(i,c;g.primitive)list~=(i?", ":"")~cert.q(c);list~="]";
					auto rest="(GR := fun o : Option ℝ => "~name(r.primitive)~".eval ξ (Binding.Env.cons (a := .scalar .real) o ρ))";
					return "("~termsName~"."~(scaled?"scaledErf ":"erf ")~rest~" (R := "~list~") "~cert.q(g.constant)~" "~cert.q(g.c0)~" "~cert.q(g.c1)~" "~cert.q(g.c2)~" "~
						cert.q(g.vertex)~" "~cert.q(g.width)~" "~cert.q(r.point)~" "~cert.q(r.half)~" "~cert.q(Rational(0)-g.c2)~" "~cert.q(r.offset)~" "~hv~" "~hG~(d.half?" rfl":"")~" rfl "~
						(d.half?literal(r.unit,Rational(-1))~" ":"")~literal(g.factor,r.half)~" "~literal(g.exponent,g.vertex)~" "~literal(g.scale,g.width)~" rfl "~
						literal(r.sigma,Rational(0)-g.c2)~" "~literal(r.offsetLiteral,r.offset)~")";
				}
				auto primitive_="(G := fun o : Option ℝ => "~name(r.primitive)~".eval ξ (Binding.Env.cons (a := .scalar .real) o ρ)) ";
				if(r.curved){
					// The term and its antiderivative everywhere, the derivative,
					// and on a half-line strictness in the bound and the decay.
					enum whole="(⊤ : Filter ℝ)";bool scaled,unused;
					auto hv=cert.exponentialTail(id,whole,false,false,scaled,true),hG=cert.exponentialTail(r.primitive,whole,false,false,unused);
					return "("~termsName~"."~(scaled?"scaledCurve ":"curve ")~(d.half?cert.q(r.rate)~" "~to!string(r.order)~" ":"")~primitive_~hv~" "~hG~(d.half?" rfl rfl)":" rfl)");
				}
				// On a half-line: strict in the bound, a derivative, and decay.
				auto derivative=" "~exponential(r.primitive).proof~(d.half?" rfl rfl rfl)":" rfl)");
				if(!r.scaled){
					auto hv=id==uint.max?app("exp_polynomial",app("polynomial_unit",everywhere)):exponential(id).proof;
					foreach(w;factors)hv=app("exp_mul",hv~" "~w);
					return "("~termsName~".pure "~primitive_~hv~derivative;
				}
				bool scaled;auto hv=cert.scaledFactor(id,scaled);
				foreach(w;factors)hv=app("scaled_times",hv~" "~w);
				return "("~termsName~".scaled "~primitive_~hv~derivative;
			}
			auto total=terms(d.unit!=uint.max?uint.max:d.value);
			if(d.domain!=uint.max)total="("~termsName~".guard ("~name(dropIndex(at(d.domain)).id)~".eval ξ ρ) "~total~")";
			auto minus="(Numeric.calculate_sound ξ n"~to!string(nodes[d.minusOne].data)~" (-1 : ℚ) rfl)",kind=d.below?"upper":d.half?"halfline":"interval";
			if(summand)return "(Distribution.StepSource."~kind~"_piece "~flags~(d.below?"":" "~minus)~" "~masked~" "~total~")";
			return "Distribution.DensityProgram.presentation_mass_"~kind~" "~program~" "~flags~(d.below?"":" "~minus)~" "~masked~" "~total;
		}
		if(s.pieces.length){
			// The summands in the order of the rule, with the sum around them.
			size_t next;bool guarded;
			string sum(uint id,out string lift){
				enum lifted="Distribution.DensityProgram.GuardedSum.";
				if(next<s.pieces.length&&s.pieces[next].from[0]==id){
					auto piece=s.pieces[next++],domain=piece.bounds.half&&piece.bounds.domain!=uint.max;
					guarded|=domain;lift="("~lifted~(domain?"guard _ _)":"bare _)");
					return between(piece,true);
				}
				auto n=nodes[id];enforce(n.op==BoundOp.primitive&&arena.view(arena.at(n.data)).op==Op.add,"bad sum of observations");
				string la,lb;auto left=sum(n.a,la),right=sum(n.b,lb);
				lift="("~lifted~"add "~la~" "~lb~")";
				return "(Distribution.StepSource.Piece.add "~left~" "~right~")";
			}
			string lift;auto evidence=sum(s.from[0],lift);enforce(next==s.pieces.length,"missing summand");
			auto mass="Distribution.DensityProgram.presentation_mass_pieces (w := "~functionAt(s.from[0])~") "~evidence~" (fun _ => rfl)";
			// The guards of the domains of the summands leave the sum together.
			return guarded?"Eq.trans ("~mass~") (Distribution.DensityProgram.GuardedSum.sound "~lift~")":mass;
		}
		if(s.interval)return between(s,false);
		auto cuts=s.exceptions;enforce(cuts.length,"empty step grid");
		string density(){
			auto p="Distribution.DensityProgram.lebesgue";
			foreach(id;s.from)p="(Distribution.DensityProgram.weight "~functionAt(id)~" "~p~")";
			return "(Distribution.DensityProgram.density "~p~")";
		}
		string constancy(){
			auto left="(.before "~q(cuts[0])~")",right="(.after "~q(cuts[$-1])~")";
			auto tail=app("Tail.nil",q(cuts[$-1])~" "~densityUniform(right,cuts[$-1]+Rational(1)));
			foreach_reverse(i;0..cuts.length-1){
				auto region="(.between "~q(cuts[i])~" "~q(cuts[i+1])~")";
				tail=app("Tail.cons","(a := "~q(cuts[i])~") (b := "~q(cuts[i+1])~") (of_decide_eq_true rfl) "~densityUniform(region,(cuts[i]+cuts[i+1])/Rational(2))~" "~tail);
			}
			return densityUniform(left,cuts[0]-Rational(1))~" "~tail;
		}
		string densityNumeric(Rational point){
			auto p="Distribution.DensityProgram.lebesgue",value=Rational(1);
			auto proof=app("numeric_one","("~q(point)~" : ℝ)");
			foreach(id;s.from){
				auto term=scalarBody(at(id),arena.real_(point));enforce(term!=Term.init,"non-numeric null-edit probe");
				auto result=simplify(arena,term);enforce(!result.exhausted&&arena.isNumber(result.output),"undefined null-edit probe");
				auto head=arena.number(result.output).re,h=numericProof(id,point,q(head));
				proof=app("numeric_mul",q(value)~" "~q(head)~" "~proof~" "~h);value=value*head;
				p="(Distribution.DensityProgram.weight "~functionAt(id)~" "~p~")";
				proof=save("(Distribution.DensityProgram.density "~p~" ("~q(point)~" : ℝ)) = some (Numeric.denote (s := .real) "~q(value)~")",proof);
			}
			return proof;
		}
		string total(){
			Rational[] probes=[cuts[0]-Rational(1)];string[] formulas=["("~q(cuts[0])~" - 1)"];
			foreach(i,c;cuts){
				probes~=c;formulas~=q(c);
				if(i+1<cuts.length){probes~=(c+cuts[i+1])/Rational(2);formulas~="(("~q(c)~" + "~q(cuts[i+1])~") / 2)";}
			}
			probes~=cuts[$-1]+Rational(1);formulas~="("~q(cuts[$-1])~" + 1)";
			auto proof="Distribution.StepSource.ProbeFacts.nil";
			foreach_reverse(i,point;probes){
				auto x="(("~formulas[i]~" : ℚ) : ℝ)";
				auto h="(Eq.trans "~app("rat_argument",density()~" "~formulas[i]~" "~q(point)~" rfl")~" "~densityNumeric(point)~")";
				auto defined=save("Value.Defined ("~density()~" "~x~")","⟨_, "~h~"⟩");
				proof=app("ProbeFacts.cons","(P := fun x => Value.Defined ("~density()~" x)) (x := "~x~") "~defined~" "~proof);
			}
			return proof;
		}

		if(s.polynomial){
			Piece densityPiece(string region,Rational sample){
				auto set="(Distribution.StepSource.Region.contains "~region~")";
				auto program="Distribution.DensityProgram.lebesgue";auto r=Piece(app("polynomial_one",set),"[1]");
				foreach(id;s.from){
					auto b=piece(id,set,region,sample);
					program="(Distribution.DensityProgram.weight "~functionAt(id)~" "~program~")";
					r.poly="(Distribution.StepSource.polyMul "~r.poly~" "~b.poly~")";
					r.proof=save("Distribution.StepSource.PolynomialOn "~set~" (Distribution.DensityProgram.density "~program~") "~r.poly,app("polynomial_mul",r.proof~" "~b.proof));
				}
				return r;
			}
			auto left=densityPiece("(.before "~q(cuts[0])~")",cuts[0]-Rational(1));
			auto tail=app("PolynomialTail.nil",q(cuts[$-1])~" "~densityPiece("(.after "~q(cuts[$-1])~")",cuts[$-1]+Rational(1)).proof~" rfl");
			foreach_reverse(i;0..cuts.length-1){
				auto cell=densityPiece("(.between "~q(cuts[i])~" "~q(cuts[i+1])~")",(cuts[i]+cuts[i+1])/Rational(2));
				tail=app("PolynomialTail.cons","(a := "~q(cuts[i])~") (b := "~q(cuts[i+1])~") (of_decide_eq_true rfl) "~cell.proof~" "~tail);
			}
			auto facts="Distribution.StepSource.ProbeFacts.nil";
			foreach_reverse(c;cuts){
				auto x="("~q(c)~" : ℝ)";
				auto defined=save("Value.Defined ("~density()~" "~x~")","⟨_, "~densityNumeric(c)~"⟩");
				facts=app("ProbeFacts.cons","(P := fun x => Value.Defined ("~density()~" x)) (x := "~x~") "~defined~" "~facts);
			}
			outputProof="(Numeric.calculate_sound ξ n"~to!string(nodes[s.output].data)~" "~q(s.value)~" rfl)";
			string[] rest; foreach(a;cuts[1..$]) rest~=q(a);
			auto program="Distribution.DensityProgram.lebesgue";
			foreach(id;s.from) program="(Distribution.DensityProgram.weight "~functionAt(id)~" "~program~")";
			return "Distribution.DensityProgram.presentation_mass_polynomial "~program~" (a := "~q(cuts[0])~
				") (bs := ["~rest.join(", ")~"]) (v := "~q(s.value)~") "~left.proof~" rfl "~tail~" "~facts~" rfl";
		}
		if(!s.ae){
			auto evidence=constancy()~" "~densityZero(cuts[0]-Rational(1))~" "~densityZero(cuts[$-1]+Rational(1));
			if(s.closed){
				auto known=app("KnownMass.nil","(f := "~density()~") "~q(cuts[$-1])),value=Rational(0);
				foreach_reverse(i,c;s.cells){
					auto formula="(("~q(c.lower)~" + "~q(c.upper)~") / 2)";
					auto h="(Eq.trans "~app("rat_argument",density()~" "~formula~" "~q(c.sample)~" rfl")~" "~densityNumeric(c.sample)~")";
					known=app("KnownMass.cons","(f := "~density()~") (a := "~q(c.lower)~") (b := "~q(c.upper)~") (v := "~q(s.values[i])~") (w := "~q(value)~") "~h~" "~known);
					value=s.values[i]*(c.upper-c.lower)+value;
				}
				outputProof="(Numeric.calculate_sound ξ n"~to!string(nodes[s.output].data)~" "~q(s.value)~" rfl)";
				return evidence~" "~total()~" "~known;
			}
			string ev(uint id){return "("~name(id)~".eval ξ ρ)";}
			string eq(uint id,string value,string proof){return save(ev(id)~" = "~value,proof);}
			string cutTail(size_t start){string v="[";foreach(i;start..cuts.length){if(i!=start)v~=",";v~=q(cuts[i]);}return v~"]";}
			string mass(size_t i){return "(Distribution.StepSource.gridMass "~density()~" "~q(cuts[i])~" "~cutTail(i+1)~")";}
			string literal(uint id,Rational point,string formula){
				enforce(nodes[id].op==BoundOp.scalar,"non-scalar step literal");
				auto h="(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~q(point)~" rfl)";
				auto convert=app("rat_argument","(fun x : ℝ => some x) "~q(point)~" "~formula~" rfl");
				return eq(id,"(some (("~formula~" : ℚ) : ℝ))","(Eq.trans "~h~" "~convert~")");
			}
			string sampled(uint id,uint body,Rational point,string formula){
				auto n=nodes[id];enforce(n.op==BoundOp.apply&&nodes[n.a].a==body,"bad step sample application");
				auto hp=literal(n.b,point,q(point));
				auto h=app("eval_sample",name(body)~" "~name(n.b)~" ξ ρ "~q(point)~" "~hp);
				auto convert=app("rat_argument",functionAt(body)~" "~q(point)~" "~formula~" rfl");
				return eq(id,"("~functionAt(body)~" (("~formula~" : ℚ) : ℝ))","(Eq.trans "~h~" "~convert~")");
			}
			string densityValue(uint id,size_t count,Rational point,string formula){
				auto p="Distribution.DensityProgram.lebesgue";
				foreach(body;s.from[0..count])p="(Distribution.DensityProgram.weight "~functionAt(body)~" "~p~")";
				auto value="(Distribution.DensityProgram.density "~p~" (("~formula~" : ℚ) : ℝ))";
				if(!count)return eq(id,value,"(Numeric.calculate_real_one ξ n"~to!string(nodes[id].data)~" rfl)");
				auto n=nodes[id];
				auto left=densityValue(n.a,count-1,point,formula),right=sampled(n.b,s.from[count-1],point,formula);
				return eq(id,value,"(congrArg₂ Value.mul "~left~" "~right~")");
			}
			string sum(uint id,size_t i){
				if(i+1==cuts.length)return eq(id,mass(i),"(Numeric.calculate_real_zero ξ n"~to!string(nodes[id].data)~" rfl)");
				auto n=nodes[id],m=nodes[n.a];
				auto point=(cuts[i]+cuts[i+1])/Rational(2),formula="(("~q(cuts[i])~" + "~q(cuts[i+1])~") / 2)";
				auto hv=densityValue(m.a,s.from.length,point,formula);
				auto hw=literal(m.b,cuts[i+1]-cuts[i],"("~q(cuts[i+1])~" - "~q(cuts[i])~")");
				return eq(id,mass(i),"(congrArg₂ Value.add (congrArg₂ Value.mul "~hv~" "~hw~") "~sum(n.b,i+1)~")");
			}
			string[] formulas=["("~q(cuts[0])~" - 1)"];
			foreach(i,c;cuts){formulas~=q(c);if(i+1<cuts.length)formulas~="(("~q(c)~" + "~q(cuts[i+1])~") / 2)";}
			formulas~="("~q(cuts[$-1])~" + 1)";
			string probes(size_t i){string v="[";foreach(j;i..formulas.length){if(j!=i)v~=",";v~="(("~formulas[j]~" : ℚ) : ℝ)";}return v~"]";}
			auto program="Distribution.DensityProgram.lebesgue";
			foreach(body;s.from)program="(Distribution.DensityProgram.weight "~functionAt(body)~" "~program~")";
			string run(size_t i){return "(Distribution.DensityProgram.runProbes "~program~" "~probes(i)~" "~mass(0)~")";}
			string sequenceProof(uint id,size_t i){
				if(i==formulas.length)return sum(id,0);
				uint[] seqs;auto cursor=id;
				foreach(body;s.from){seqs~=cursor;enforce(nodes[cursor].op==BoundOp.sequence,"bad step probe sequence");cursor=nodes[cursor].b;}
				auto h=sequenceProof(cursor,i+1),value=run(i+1);
				foreach_reverse(j,body;s.from){
					auto node_=nodes[seqs[j]],hv=sampled(node_.a,body,s.probes[i],formulas[i]);
					value="("~functionAt(body)~" (("~formulas[i]~" : ℚ) : ℝ)).bind (fun _ => "~value~")";
					h=eq(seqs[j],value,app("seq_congr",hv~" "~h));
				}
				return eq(id,run(i),h);
			}
			outputProof=sequenceProof(s.output,0);return evidence;
		}

		auto source=s.from,sourceConst=constancy(),sourceTotal=total(),f=density();
		s.from=s.to;auto targetConst=constancy(),targetTotal=total(),g=density();
		string equal(Rational point){
			s.from=source;auto h=densityNumeric(point);s.from=s.to;
			return "(Eq.trans "~h~" (Eq.symm "~densityNumeric(point)~"))";
		}
		auto same=app("SameSamples.nil","(f := "~f~") (g := "~g~") "~q(cuts[$-1])~" "~equal(cuts[$-1]+Rational(1)));
		foreach_reverse(i;0..cuts.length-1)
			same=app("SameSamples.cons","(f := "~f~") (g := "~g~") (a := "~q(cuts[i])~") (b := "~q(cuts[i+1])~") "~equal((cuts[i]+cuts[i+1])/Rational(2))~" "~same);
		return sourceConst~" "~targetConst~" "~sourceTotal~" "~targetTotal~" "~equal(cuts[0]-Rational(1))~" "~same;
	}

	string exportLean(BindingResult result,bool lowerResult=false){
		if(telescope_) return exportDependent(result);
		check(result.input); check(result.output); enforce(result.proof<result.proofs.length,"missing binding proof");
		auto lowered=lowerResult?lower(result.output):Term.init;
		string code="import QSym\n",dimDecl=dependent_?" (δ : ℕ → ℕ)":"",dimArg=dependent_?" δ":"";
		foreach(i,d;result.domains){
			if(d.rational){
				auto part=replace(exportRationalZeroLean(arena,d.input,d.rationalConditions),"import QSym\n","");
				code~=replace(part,"QSym.RationalCertificate","QSym.BindingScalar"~to!string(i));continue;
			}
			if(d.polynomial){
				auto part=replace(exportPolynomialZeroLean(arena,d.input),"import QSym\n","");
				code~=replace(part,"QSym.PolynomialCertificate","QSym.BindingScalar"~to!string(i));continue;
			}
			auto prefix="QSym.BindingScalar"~to!string(i),part=exportDomainLean(arena,d.input,d.result,ScalarClaims.refinement);
			part=replace(part,"import QSym\n","");
			part=replace(part,"QSym.Certificate",prefix~".Certificate");
			part=replace(part,"QSym.DomainCertificate",prefix~".DomainCertificate"); code~=part;
			if(d.value.traced){
				part=replace(scalarExport(arena,d.value,ScalarClaims.refinement),"import QSym\n","");
				code~=replace(part,"QSym.Certificate",prefix~".ValueCertificate");
			}
		}
		foreach(i,r;result.ranks){
			auto prefix="QSym.BindingRank"~to!string(i);
			if(!r.iterations.length) code~=replace(replace(scalarExport(arena,r.result),"import QSym\n",""),"QSym.Certificate",prefix~".Certificate");
			if(r.lower.output!=Term.init){
				code~=replace(replace(scalarExport(arena,r.lower),"import QSym\n",""),"QSym.Certificate",prefix~".Lower");
				code~=replace(replace(scalarExport(arena,r.upper),"import QSym\n",""),"QSym.Certificate",prefix~".Upper");
			}
			foreach(j,step;r.iterations) code~=replace(replace(scalarExport(arena,step),"import QSym\n",""),"QSym.Certificate",prefix~".Step"~to!string(j));
			foreach(j,d;r.leaves){
				auto p=prefix~".Leaf"~to!string(j),part=replace(exportDomainLean(arena,d.value,d.domain,ScalarClaims.refinement),"import QSym\n","");
				part=replace(part,"QSym.Certificate",p~".Certificate");
				code~=replace(part,"QSym.DomainCertificate",p~".DomainCertificate");
			}
		}
		foreach(i,s;result.solutions) foreach(j,f;s.facts){
			auto prefix="QSym.Linear"~to!string(i)~"_"~to!string(j),part=replace(exportDomainLean(arena,f.input,f.domain,ScalarClaims.refinement),"import QSym\n","");
			part=replace(part,"QSym.Certificate",prefix~".Certificate");
			code~=replace(part,"QSym.DomainCertificate",prefix~".DomainCertificate");
			code~=replace(replace(scalarExport(arena,f.value,ScalarClaims.refinement),"import QSym\n",""),"QSym.Certificate",prefix~".ValueCertificate");
		}
		foreach(i,s;result.spectra){
			foreach(kind,fs;[s.parameters,s.checks]) foreach(j,f;fs){
				auto prefix="QSym.Spectral"~to!string(i)~"_"~to!string(kind)~"_"~to!string(j);
				auto part=replace(exportDomainLean(arena,f.input,f.domain,ScalarClaims.refinement),"import QSym\n","");
				part=replace(part,"QSym.Certificate",prefix~".Certificate"); code~=replace(part,"QSym.DomainCertificate",prefix~".DomainCertificate");
				if(f.value.traced) code~=replace(replace(scalarExport(arena,f.value,ScalarClaims.refinement),"import QSym\n",""),"QSym.Certificate",prefix~".ValueCertificate");
			}
		}
		code~="namespace QSym.BindingCertificate\nattribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv\n";
		foreach(s;result.solutions) if(s.cfinite){ code~="attribute [local semireducible] Nat.div Nat.modCore\n"; break; }
		Term[] stepNumerics;string stepDeclarations;string[] stepProofs=new string[result.integrals.length],stepOutputs=new string[result.integrals.length];
		uint[] proofRoots;
		foreach(p;result.proofs) if(p.rule==BindingRule.closedRationalValue) stepNumerics~=arena.at(p.extra);
		foreach(i,s;result.integrals) if(s.piecewise||s.ae){
			auto c=new SourceCertificates("step"~to!string(i)~"_",s.from[0]);
			stepProofs[i]=stepGridProof(s,c,stepOutputs[i]);stepNumerics~=c.numericTerms;stepDeclarations~=c.declarations;proofRoots~=c.roots;
		}
		string[] limitProofs=new string[result.limits.length];
		foreach(i,s;result.limits){
			auto c=new SourceCertificates("limit"~to!string(i)~"_",s.body);
			limitProofs[i]=limitProof(s,c);stepNumerics~=c.numericTerms;stepDeclarations~=c.declarations;proofRoots~=c.roots;
		}
		Table!(uint,string) squareWeights;
		foreach(i,p;result.proofs) if(p.rule==BindingRule.distributionWeightedSquare&&p.left!=uint.max){
			uint weight,point; enforce(realAtomRow(at(p.from),weight,point));
			auto c=new SourceCertificates("weight"~to!string(i)~"_",weight);
			squareWeights.set(cast(uint)i,c.functionAt(weight)~" "~borelProof(weight,c));
			stepDeclarations~=c.declarations;
		}
		string[] coordinateProofs;
		foreach(i,coordinate;result.coordinates){
			auto c=new SourceCertificates("grid"~to!string(i)~"_",coordinate.body);
			coordinateProofs~=coordinateGridProof(coordinate,c); proofRoots~=c.roots;
			stepNumerics~=c.numericTerms;stepDeclarations~=c.declarations;
		}
		Table!(uint,string) smoothCoordinates;
		foreach(i,p;result.proofs) if(p.rule==BindingRule.distributionSmoothCoordinate){
			auto n=nodes[p.from]; bool restricted=n.op==BoundOp.distributionInversePart;
			auto body=at(nodes[nodes[restricted?n.b:n.a].a].a);
			auto c=new SourceCertificates("slope"~to!string(i)~"_",body.id);
			string w; enforce(smoothSlope(body,w,c)!=BoundTerm.init,"missing smooth coordinate derivative");
			auto rule=restricted?"restricted "~c.functionAt(nodes[n.a].a):"length";
			smoothCoordinates.set(cast(uint)i,"Distribution.GraphFibre.Coordinates.Grid.Slope."~rule~" "~w);
			proofRoots~=c.roots; stepNumerics~=c.numericTerms; stepDeclarations~=c.declarations;
		}
		Table!(uint,string) affineCovers;
		foreach(i,p;result.proofs) if(p.rule==BindingRule.distributionCoverAffine){
			auto fn=nodes[nodes[nodes[p.from].a].a],c=new SourceCertificates("coordinate"~to!string(i)~"_",fn.a);
			auto f=c.affineProof(fn.a),j=arena.number(arena.at(nodes[p.extra].data)).re;
			auto args=c.q(f.slope)~" "~c.q(f.offset)~" "~c.q(j)~" rfl "~f.proof~" "~c.numericProof(p.extra,Rational(0),c.q(j));
			affineCovers.set(cast(uint)i,args~(j==Rational(1)?" true":" false")~" (of_decide_eq_true rfl)");
			stepNumerics~=c.numericTerms; stepDeclarations~=c.declarations;
		}
		string radiusArguments(BoundNode image){
			auto centre=arena.at(nodes[image.a].data);
			string form; auto scale=sqrtRadiusScale(image.b,form);
			alias q=SourceCertificates.q;
			string number(Term t){return "(Numeric.calculate_sound ξ n"~to!string(t.id)~" "~q(arena.number(t).re)~" rfl)";}
			auto unit=form=="one"||form=="guardedOne";
			auto shape="(Distribution.GraphFibre.sqrtRadius_"~form~(unit?"":" _")~")";
			return q(arena.number(centre).re)~" "~q(arena.number(scale).re)~" (of_decide_eq_true rfl) "~number(centre)~
				" "~(unit?"rfl":number(scale))~" "~shape;
		}
		string[] chartProofs;
		foreach(i,chart;result.affineCharts){
			auto c=new SourceCertificates("affine"~to!string(i)~"_",chart.map);
			auto f=c.affineProof(chart.map);
			auto invProof=chart.inverse==uint.max?"":c.affineProof(chart.inverse).proof~" ";
			auto reciprocal=Rational(1)/f.slope,jac=reciprocal<Rational(0)?-reciprocal:reciprocal;
			auto hj=c.numericProof(chart.jacobian,Rational(0),c.q(jac));
			if(chart.radiusCentre!=uint.max){
				auto centre=c.numericProof(chart.radiusCentre,Rational(0),c.q(-f.offset/f.slope));
				chartProofs~=c.q(f.slope)~" "~c.q(f.offset)~" "~c.q(jac)~" (of_decide_eq_true rfl) rfl "~
					f.proof~" "~centre~" "~hj~(chart.squareProduct?" true":" false");
				if(chart.bandLo!=uint.max){
					string number(uint n){return c.q(arena.number(arena.at(nodes[n].data)).re);}
					auto lo=number(chart.bandLo),hi=number(chart.bandHi),cap=number(chart.cutoff);
					chartProofs[$-1]~=" "~lo~" "~hi~" "~cap~" (of_decide_eq_true rfl) rfl rfl "~c.numericProof(chart.bandLo,Rational(0),lo)~
						" "~c.numericProof(chart.bandHi,Rational(0),hi)~" "~c.numericProof(chart.cutoff,Rational(0),cap);
				}
				stepNumerics~=c.numericTerms; stepDeclarations~=c.declarations; continue;
			}
			chartProofs~=c.q(f.slope)~" "~c.q(f.offset)~" "~c.q(jac)~" (of_decide_eq_true rfl) rfl "~
				f.proof~" "~invProof~hj;
			if(chart.powerDegree){
				auto num=arena.number(arena.at(nodes[chart.derivativeNumerator].data)).re;
				auto den=arena.number(arena.at(nodes[chart.derivativeDenominator].data)).re;
				if(chart.powerDegree!=2) chartProofs[$-1]~=" "~to!string((chart.powerDegree-3)/2);
				chartProofs[$-1]~=" "~c.q(num)~" "~c.q(den)~" (of_decide_eq_true rfl) rfl "~
					c.numericProof(chart.derivativeNumerator,Rational(0),c.q(num))~" "~
					c.numericProof(chart.derivativeDenominator,Rational(0),c.q(den));
				if(chart.powerDegree==2) chartProofs[$-1]~=chart.squareProduct?" true":" false";
			}
			if(chart.punctureBody!=uint.max){
				auto g=c.affineProof(chart.punctureBody);
				chartProofs[$-1]~=" "~c.q(g.slope)~" "~c.q(g.offset)~" (of_decide_eq_true rfl) "~g.proof;
			}
			if(chart.borelPredicate!=uint.max)
				chartProofs[$-1]~=" "~c.functionAt(chart.borelPredicate)~" "~borelProof(chart.borelPredicate,c);
			stepNumerics~=c.numericTerms;stepDeclarations~=c.declarations;
		}
		bool[] used=new bool[nodes.length]; uint[] stack=[result.input.id,result.output.id]~proofRoots;
		foreach(p;result.proofs){ stack~=p.from; stack~=p.to; }
		foreach(s;result.sums) stack~=s.candidate;
		foreach(witness;result.fibres) foreach(f;witness){ stack~=[f.source,f.charge,f.regular]; stack~=f.weights; }
		foreach(c;result.affineCharts){
			stack~=[c.map,c.jacobian];
			if(c.radiusCentre!=uint.max) stack~=c.radiusCentre;
			if(c.inverse!=uint.max) stack~=c.inverse;
			if(c.powerDegree) stack~=[c.derivativeNumerator,c.derivativeDenominator];
		}
		void integralRoots(IntegralSolution s){
			stack~=s.from; stack~=s.to; foreach(r;s.bounds.terms) if(r.primitive!=uint.max) stack~=r.primitive;
			// The bounds and the literal of a difference are named by the theorem
			// also where the result does not mention them.
			if(s.interval&&!s.pieces.length){ stack~=[s.bounds.lower,s.bounds.upper]; if(!s.bounds.below) stack~=s.bounds.minusOne; }
			// The masks of a split weight are named by its certificate.
			if(s.split!=uint.max) stack~=s.split;
			// So is the literal of `h` under a curvature that is a term, also
			// where no row of the moments has a power of it.
			if(s.gaussian&&s.bell.curved) stack~=s.bell.factor;
			foreach(piece;s.pieces) integralRoots(piece);
		}
		foreach(s;result.integrals) integralRoots(s);
		foreach(s;result.solutions) if(s.divide){stack~=s.seedFunction;stack~=s.tollFunction;}
		foreach(p;result.proofs) if(p.rule==BindingRule.sumMissingGuard||p.rule==BindingRule.sumInterval||p.rule==BindingRule.sumBounds||p.rule==BindingRule.sumBoundedAdd||p.rule==BindingRule.distributionCoverAffine) stack~=p.extra;
		while(stack.length){
			auto id=stack[$-1]; --stack.length; if(used[id]) continue;
			used[id]=true; auto n=nodes[id];
			if(n.a!=uint.max) stack~=n.a; if(n.b!=uint.max) stack~=n.b; if(n.c!=uint.max) stack~=n.c;
		}
		uint[] scalarNodes;
		foreach(t;stepNumerics)scalarNodes~=arena.viewPostorder(t);
		foreach(i,n;nodes) if(used[i]&&n.op==BoundOp.scalar) scalarNodes~=arena.viewPostorder(arena.at(n.data));
		foreach(d;result.domains){
			scalarNodes~=arena.viewPostorder(d.input); if(d.result.output!=Term.init)scalarNodes~=arena.viewPostorder(d.result.output);
			if(d.value.traced) scalarNodes~=arena.viewPostorder(arena.castTo(d.value.output,arena.sort(d.input)));
			if(d.mode==BoundOp.primitive) scalarNodes~=arena.viewPostorder(arena.number(Number(0),d.sort));
		}
		foreach(r;result.ranks) foreach(step;r.iterations) scalarNodes~=arena.viewPostorder(step.output);
		foreach(r;result.ranks) if(r.lower.output!=Term.init) scalarNodes~=arena.viewPostorder(r.result.output);
		foreach(r;result.ranks) if(r.step!=Term.init) foreach(t;[r.slope,r.bound,r.step]) scalarNodes~=arena.viewPostorder(t);
		foreach(s;result.solutions) if(s.cfinite) foreach(m;s.cfModels){
			if(m.value!=Term.init) scalarNodes~=arena.viewPostorder(m.value);
			foreach(t;m.matrix~m.initial~m.output) scalarNodes~=arena.viewPostorder(t);
		}
		foreach(s;result.solutions) foreach(f;s.facts){ scalarNodes~=arena.viewPostorder(f.input); scalarNodes~=arena.viewPostorder(arena.castTo(f.value.output,arena.sort(f.input))); }
		foreach(s;result.spectra){
			foreach(fs;[s.parameters,s.checks]) foreach(f;fs){
				scalarNodes~=arena.viewPostorder(f.input);
				if(f.value.traced) scalarNodes~=arena.viewPostorder(arena.castTo(f.value.output,arena.sort(f.input)));
				Number value; if(literalNumber(f.input,value)&&(value.zero||value.one)) scalarNodes~=arena.viewPostorder(arena.number(value,arena.sort(f.input)));
			}
			scalarNodes~=arena.viewPostorder(arena.number(Number(0),elementSort(typeLeaf(type(at(s.source))))));
		}
		if(lowerResult) scalarNodes~=arena.viewPostorder(lowered);
		bool[] needed=new bool[arena.length]; foreach(id;scalarNodes) needed[id]=true;
		foreach(i,yes;needed) if(yes) code~=leanSyntaxCode(arena,arena.at(cast(uint)i));
		foreach(i,ctx;contexts){
			code~="abbrev c"~to!string(i)~dimDecl~" : List Binding.Ty := ";
			code~=i==0?"[]\n":leanType(types[ctx.type])~" :: "~ctxName(ctx.parent)~"\n";
		}
		foreach(i,n;nodes) if(used[i]){
			string expr;
			final switch(n.op){
				case BoundOp.conditional:expr=".conditional "~name(n.a)~" "~name(n.b)~" "~name(n.c); break;
				case BoundOp.distributionZero:expr=".constant Distribution.zeroValue"; break;
				case BoundOp.distributionLebesgue:expr=".constant Distribution.lebesgueValue"; break;
				case BoundOp.unit:expr=".constant (some ())"; break;
				case BoundOp.vectorNil:expr=".constant Tensor.nilValue"; break;
				case BoundOp.scalar:expr=".scalar n"~to!string(n.data); break;
				case BoundOp.variable:
					expr=".here"; foreach(j;0..n.data) expr="(.there "~expr~")";
					expr=".var "~expr; break;
				case BoundOp.distributionFixed,BoundOp.distributionRetry,BoundOp.distributionDirac,BoundOp.distributionAdd,BoundOp.distributionScale,BoundOp.distributionWeight,BoundOp.distributionIntegral,BoundOp.distributionSum,BoundOp.distributionMass,BoundOp.distributionDensityAt,BoundOp.distributionBind,BoundOp.distributionPushforwardOn,BoundOp.distributionInverseCover,BoundOp.distributionInversePart,BoundOp.distributionRadiusImage,BoundOp.distributionMaskedGraph,BoundOp.distributionGraphFibre,BoundOp.distributionGraphMass,BoundOp.finiteSum,BoundOp.summation,BoundOp.limit,BoundOp.primitive,BoundOp.member,BoundOp.subset,BoundOp.domain,BoundOp.defined,BoundOp.holds,BoundOp.guard,BoundOp.typeEq,BoundOp.equal,BoundOp.vectorCons,BoundOp.pair,BoundOp.first,BoundOp.rest,BoundOp.get,BoundOp.tensor:
					expr="."~(n.b==uint.max?"unary":"binary")~" "~valueOperation(n)~" "~name(n.a);
					if(n.b!=uint.max) expr~=" "~name(n.b); break;
				case BoundOp.lambda:expr=".lam "~name(n.a); break;
				case BoundOp.set:expr=".set "~name(n.a); break;
				case BoundOp.global:expr=".constant (some (γ "~leanType(types[n.type])~" "~to!string(n.data)~"))"; break;
				case BoundOp.typeValue:expr=".constant (some "~leanType(types[n.data])~")"; break;
				case BoundOp.bottom:expr=".constant none"; break;
				case BoundOp.fixed:expr=".unary Recursion.fixedValue (.lam "~name(n.a)~")"; break;
				case BoundOp.apply:expr=".app "~name(n.a)~" "~name(n.b); break;
				case BoundOp.sequence:expr=".seq "~name(n.a)~" "~name(n.b); break;
			}
			code~="noncomputable def t"~to!string(i)~dimDecl~" (γ : Binding.Globals) : Binding.Expr "~ctxName(n.context)~" "~leanType(types[n.type])~" := "~expr~"\n";
		}
		code~=stepDeclarations;
		foreach(i,n;nodes) if(used[i]&&n.op==BoundOp.fixed){
			auto v=pool.view(types[n.type]),a="("~leanType(v.fields[0])~" : Binding.Ty).denote",b="("~leanType(v.fields[1])~" : Binding.Ty).denote";
			auto env="(Binding.Env.cons (a := "~leanType(v.fields[0])~") (some x) (Binding.Env.cons (a := "~leanType(types[n.type])~") (some (fun (_ : "~a~") => (none : Option "~b~"))) ρ))";
			string program(uint id){
				auto t=at(id),q=nodes[id];
				if(!depends(t,1)) return "(.constant (fun x => "~name(id)~".eval ξ "~env~"))";
				if(q.op==BoundOp.apply) return "(.call "~program(q.b)~")";
				if(q.op==BoundOp.conditional) return "(.branch "~program(q.a)~" "~program(q.b)~" "~program(q.c)~")";
				auto x=program(q.a),y=q.b==uint.max?"":program(q.b);
				if(q.op==BoundOp.guard) return "(.branch "~x~" "~y~" (.constant (fun _ => none)))";
				if(q.op==BoundOp.primitive){
					auto op=arena.view(arena.at(q.data)).op;
					if(op==Op.mask||op==Op.and_) return "(.branch "~x~" "~y~" (.constant (fun _ => some "~(op==Op.mask?"0":"false")~")))";
					if(op==Op.or_) return "(.branch "~x~" (.constant (fun _ => some true)) "~y~")";
				}
				auto op=q.op==BoundOp.sequence?"(fun (x : Option ("~leanType(types[nodes[q.a].type])~" : Binding.Ty).denote) (y : Option ("~leanType(types[nodes[q.b].type])~" : Binding.Ty).denote) => x.bind (fun _ => y))":valueOperation(q);
				return q.b==uint.max?"(.unary "~op~" rfl "~x~")":
					"(.binary "~op~" (fun _ => rfl) (fun x => Option.casesOn x rfl (fun _ => rfl)) "~x~" "~y~")";
			}
			string programProof(uint id){
				auto q=nodes[id]; if(!depends(at(id),1)) return "rfl";
				if(q.op==BoundOp.apply){ auto h=programProof(q.b); return h=="rfl"?h:"(congrArg (fun z : Option "~a~" => z.bind g) "~h~")"; }
				if(q.op==BoundOp.conditional) return "(Binding.conditional_congr "~programProof(q.a)~" "~programProof(q.b)~" "~programProof(q.c)~")";
				auto x=programProof(q.a),y=q.b==uint.max?"":programProof(q.b);
				auto op=q.op==BoundOp.sequence?"(fun (x : Option ("~leanType(types[nodes[q.a].type])~" : Binding.Ty).denote) (y : Option ("~leanType(types[nodes[q.b].type])~" : Binding.Ty).denote) => x.bind (fun _ => y))":valueOperation(q);
				auto proof=q.b==uint.max?"(congrArg "~op~" "~x~")":"(congrArg₂ "~op~" "~x~" "~y~")";
				string bridge;
				if(q.op==BoundOp.guard) bridge="Binding.guard_branch";
				else if(q.op==BoundOp.primitive){
					auto kind=arena.view(arena.at(q.data)).op;
					if(kind==Op.mask) bridge="Recursion.mask_branch";
					if(kind==Op.and_) bridge="Recursion.and_branch";
					if(kind==Op.or_) bridge="Recursion.or_branch";
				}
				return bridge.length?"(Eq.trans "~proof~" ("~bridge~" _ _))":x=="rfl"&&(q.b==uint.max||y=="rfl")?"rfl":proof;
			}
			auto id=to!string(i),args=dimDecl~" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctxName(n.context)~")";
			auto h="(fun g => congrArg some (funext (fun x => "~programProof(nodes[n.a].a)~")))";
			code~="noncomputable def rec"~id~args~" : Recursion.Program "~a~" "~b~" "~b~" := "~program(nodes[n.a].a)~"\n";
			code~="theorem fixed"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = some (FixedPoint.value (rec"~id~dimArg~" γ ξ ρ).functional) := Recursion.fixed_program (rec"~id~dimArg~" γ ξ ρ) _ "~h~"\n";
			code~="theorem unroll"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = (Binding.Expr.app (.lam "~name(n.a)~") "~name(cast(uint)i)~").eval ξ ρ := Recursion.program_unfold (rec"~id~dimArg~" γ ξ ρ) _ "~h~"\n";
			foreach(ri,r;result.ranks) if(r.source==i){
				auto prefix="QSym.BindingRank"~to!string(ri),field=leanSort(r.sort),eta="({ ξ with "~field~" := fun i => if i = "~to!string(r.variable)~" then x else ξ."~field~" i })";
				string constant(Term t){ return "((n"~to!string(t.id)~".eval ξ).getD 0)"; }
				string leafProof(uint q){ foreach(j,l;r.leaves) if(l.node==q) return "("~prefix~".Leaf"~to!string(j)~".DomainCertificate.domain_correct "~eta~")"; assert(0,"missing rank leaf"); }
				string value(uint q){ return "("~name(q)~".eval ξ "~env~")"; }
				string dp(uint q){
					auto z=nodes[q]; if(!depends(at(q),1)) return "(.pure (fun x => Value.Defined "~value(q)~"))";
					if(z.op==BoundOp.apply) return "(.call (fun x => "~value(z.b)~"))";
					auto op=z.op==BoundOp.primitive?arena.view(arena.at(z.data)).op:Op.variable;
					if(z.op==BoundOp.guard||op==Op.mask||op==Op.and_||op==Op.or_){
						auto yes="(.pure (fun x => "~value(z.a)~" = some true))",no="(.pure (fun x => "~value(z.a)~" = some false))",d=dp(z.b);
						return z.op==BoundOp.guard?"(.both "~yes~" "~d~")":op==Op.or_?"(.either "~yes~" (.both "~no~" "~d~"))":"(.either "~no~" (.both "~yes~" "~d~"))";
					}
					auto x=dp(z.a); return z.b==uint.max?x:"(.both "~x~" "~dp(z.b)~")";
				}
				string erase(uint q){
					auto z=nodes[q]; if(!depends(at(q),1)) return "Iff.rfl";
					if(z.op==BoundOp.apply) return "(SetFixed.defined_bind _ _)";
					auto op=z.op==BoundOp.primitive?arena.view(arena.at(z.data)).op:Op.variable;
					if(z.op==BoundOp.guard||op==Op.mask||op==Op.and_||op==Op.or_){
						auto d="(and_congr Iff.rfl "~erase(z.b)~")",lemma=z.op==BoundOp.guard?"SetFixed.defined_guard":op==Op.mask?"Value.defined_mask":op==Op.and_?"Value.defined_and":"Value.defined_or";
						return "(("~lemma~" _ _).trans "~(z.op==BoundOp.guard?d:"(or_congr Iff.rfl "~d~")")~")";
					}
					string lemma;
					if(z.op==BoundOp.sequence) lemma="SetFixed.defined_sequence _ _";
					else if(op==Op.builtin){ auto qv=arena.view(arena.at(z.data)),info=builtinInfo(cast(Builtin)qv.value); lemma="SetFixed.defined_total"~to!string(qv.arity)~" Functions."~info.code~(qv.arity==1?" (fun _ => True.intro) _":" (fun _ _ => True.intro) _ _"); }
					else{
						auto s=op==Op.add?"add":op==Op.mul?"mul":op==Op.lt?"lt":op==Op.le?"le":op==Op.nonzero?"nonzero":op==Op.not_?"not":op==Op.conj?"conj":"map _";
						lemma="Value.defined_"~s~(z.b==uint.max?" _":" _ _");
					}
					return "(("~lemma~").trans "~(z.b==uint.max?erase(z.a):"(and_congr "~erase(z.a)~" "~erase(z.b)~")")~")";
				}
				Term previous; string previousTotal,previousFunction; bool restricted;
				string substituteProof(Term t){
					auto z=arena.view(t); if(t==arena.variable(r.sort,r.variable)) return "h";
					if(!z.arity) return "rfl";
					auto x=substituteProof(arena.at(z.a)),y=z.arity==1?"":substituteProof(arena.at(z.b)),op=leanValueOperation(arena,t);
					if(x=="rfl"&&(y==""||y=="rfl")) return "rfl";
					return z.arity==1?"(congrArg "~op~" "~x~")":"(congrArg₂ "~op~" "~x~" "~y~")";
				}
				string rankProof(uint q){
					auto z=nodes[q]; if(!depends(at(q),1)) return "(SetFixed.pure_rank "~leafProof(q)~")";
					if(z.op==BoundOp.apply){
						if(r.step!=Term.init) return "(SetFixed.call_measure x "~constant(r.slope)~" "~constant(r.bound)~" "~constant(r.step)~" "~leafProof(z.b)~")";
						if(previous==Term.init) return "(SetFixed.call_rank x "~leafProof(z.b)~")";
						if(restricted) return "(SetFixed.call_rank_test x "~previousFunction~" "~leafProof(z.b)~" "~previousTotal~" (fun y h => "~substituteProof(previous)~"))";
						return "(SetFixed.call_test "~previousFunction~" "~leafProof(z.b)~" "~previousTotal~" (fun y h => "~substituteProof(previous)~"))";
					}
					auto op=z.op==BoundOp.primitive?arena.view(arena.at(z.data)).op:Op.variable;
					if(z.op==BoundOp.guard||op==Op.mask||op==Op.and_||op==Op.or_){
						auto d=rankProof(z.b);
						return z.op==BoundOp.guard?"(SetFixed.both_rank (SetFixed.true_rank "~leafProof(z.a)~") "~d~")":"(SetFixed."~(op==Op.or_?"or_test":"mask_test")~" "~leafProof(z.a)~" "~d~")";
					}
					auto x=rankProof(z.a); return z.b==uint.max?x:"(SetFixed.both_rank "~x~" "~rankProof(z.b)~")";
				}
				auto body=nodes[n.a].a,tag=to!string(ri),d="(drec"~tag~dimArg~" γ ξ ρ)",p="(rec"~id~dimArg~" γ ξ ρ)";
				code~="noncomputable def drec"~tag~args~" : SetFixed.Predicate "~a~" := "~dp(body)~"\n";
				code~="theorem erase"~tag~args~" (g : "~a~" → Option "~b~") (x : "~a~") : Value.Defined ("~p~".eval g x) ↔ "~d~".eval {y | Value.Defined (g y)} x :=\n  ((Iff.of_eq (congrArg Value.Defined "~programProof(body)~")).symm).trans "~erase(body)~"\n";
				if(r.iterations.length){
					auto full=dimArg~" γ ξ ρ";
					previous=arena.boolean(false); previousTotal="(fun _ => ⟨false, rfl⟩)"; previousFunction="(fun (_ : "~a~") => some false)";
					string subset="(SetFixed.Predicate.start_least "~d~")",lastTest,lastSet;
					foreach(j,step;r.iterations){
						auto name="iter"~tag~"_"~to!string(j),function_="("~name~full~")",test="("~name~"_test"~full~")";
						code~="noncomputable def "~name~args~" (x : "~a~") : Option Bool := n"~to!string(step.output.id)~".eval "~eta~"\n";
						code~="theorem "~name~"_test"~args~" (x : "~a~") : SetFixed.Test ("~function_~" x) ("~d~".eval {y | "~previousFunction~" y = some true} x) :=\n  SetFixed.Test.refine "~rankProof(body)~" ("~prefix~".Step"~to!string(j)~".refinement "~eta~")\n";
						lastSet="{x | "~function_~" x = some true}"; lastTest=test;
						code~="theorem "~name~"_subset"~args~" : "~lastSet~" ⊆ "~d~".least := SetFixed.Predicate.step_least "~d~" "~subset~" (fun x => ("~test~" x).1)\n";
						subset="("~name~"_subset"~full~")"; previous=step.output; previousTotal="(fun x => ("~test~" x).2)"; previousFunction=function_;
					}
					code~="theorem domainTotal"~tag~args~" : Binding.inputDomain ("~name(cast(uint)i)~".eval ξ ρ) = some "~lastSet~" :=\n  SetFixed.domain_set "~p~" "~d~" _ (fixed"~id~full~") (erase"~tag~full~") _ (SetFixed.Predicate.least_of_stable "~d~" _ "~subset~" (fun x => ("~lastTest~" x).1.symm))\n";
				}else if(r.lower.output!=Term.init){
					auto full=dimArg~" γ ξ ρ",function_="(candidate"~tag~full~")",test="(candidate"~tag~"_test"~full~")",set_="{x | "~function_~" x = some true}";
					code~="noncomputable def candidate"~tag~args~" (x : ℕ) : Option Bool := n"~to!string(r.result.output.id)~".eval "~eta~"\n";
					code~="theorem candidate"~tag~"_test"~args~" (x : ℕ) : SetFixed.Test ("~function_~" x) ("~d~".eval {y | y < x} x) :=\n  SetFixed.Test.refine "~rankProof(body)~" ("~prefix~".Certificate.refinement "~eta~")\n";
					previous=r.result.output; previousTotal="(fun x => ("~test~" x).2)"; previousFunction=function_; restricted=true;
					auto self="(And.intro Iff.rfl ("~test~" x).2)";
					code~="theorem lower"~tag~args~" (x : ℕ) : "~function_~" x = some true → "~d~".eval {y | y < x ∧ "~function_~" y = some true} x :=\n  SetFixed.rank_true (SetFixed.implies_test "~self~" "~rankProof(body)~") ("~prefix~".Lower.refinement "~eta~")\n";
					restricted=false;
					code~="theorem upper"~tag~args~" (x : ℕ) : "~d~".eval "~set_~" x → "~function_~" x = some true :=\n  SetFixed.rank_true (SetFixed.implies_test "~rankProof(body)~" "~self~") ("~prefix~".Upper.refinement "~eta~")\n";
					code~="theorem domainTotal"~tag~args~" : Binding.inputDomain ("~name(cast(uint)i)~".eval ξ ρ) = some "~set_~" :=\n  SetFixed.domain_set "~p~" "~d~" _ (fixed"~id~full~") (erase"~tag~full~") _ (SetFixed.Predicate.least_nat_of_closed "~d~" _ (lower"~tag~full~") (upper"~tag~full~"))\n";
				}else if(r.step!=Term.init){
					auto c=constant(r.slope),bnd=constant(r.bound),e=constant(r.step),full=dimArg~" γ ξ ρ";
					code~="theorem rank"~tag~args~" (x : ℝ) : "~d~".eval {y | "~bnd~" < "~c~" * x ∧ "~c~" * y + "~e~" ≤ "~c~" * x} x :=\n  SetFixed.rank_true "~rankProof(body)~" ("~prefix~".Certificate.refinement "~eta~")\n";
					auto positive="(SetFixed.positive_step "~e~" (Numeric.sound ξ (.ltR (.real 0) n"~to!string(r.step.id)~") (.bool true) (of_decide_eq_true rfl)))";
					code~="theorem domainTotal"~tag~args~" : Binding.inputDomain ("~name(cast(uint)i)~".eval ξ ρ) = some Set.univ :=\n  SetFixed.domain_set "~p~" "~d~" _ (fixed"~id~full~") (erase"~tag~full~") _ (SetFixed.Predicate.total_measure "~d~" (fun x => "~c~" * x) "~bnd~" "~e~" "~positive~" (rank"~tag~full~"))\n";
				}else{
					code~="theorem rank"~tag~args~" (x : ℕ) : "~d~".eval {y | y < x} x :=\n  SetFixed.rank_true "~rankProof(body)~" ("~prefix~".Certificate.refinement "~eta~")\n";
					code~="theorem domainTotal"~tag~args~" : Binding.inputDomain ("~name(cast(uint)i)~".eval ξ ρ) = some Set.univ :=\n  SetFixed.domain_univ "~p~" "~d~" _ (fixed"~id~dimArg~" γ ξ ρ) (erase"~tag~dimArg~" γ ξ ρ) (rank"~tag~dimArg~" γ ξ ρ)\n";
				}
			}
			foreach(si,s;result.solutions) if(s.source==i){
				if(s.prefix){
					auto leaf=pool.view(type(at(s.source))).fields[1],sort=elementSort(leaf),add=tensorOperation(leaf,TensorOp.add);
					auto ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					auto emptyEnv="(Binding.Env.cons (a := "~leanType(type(at(s.source)))~") none ρ)";
					auto base="("~name(s.base)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some 0) "~emptyEnv~"))";
					auto forcing="(fun (x : Option ℕ) => "~name(s.delta)~".eval ξ (Binding.Env.cons (a := .scalar .natural) x "~emptyEnv~"))";
					auto hp="(fun g x => ("~programProof(nodes[n.a].a)~").symm)";
					code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ := Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (Summation.solve_prefix "~add~" "~ha~" (rec"~id~dimArg~" γ ξ ρ) "~(s.left?"true":"false")~" "~base~" "~forcing~" "~hp~"))\n";
					continue;
				}
				if(s.affine||s.order||s.width||s.indexed||s.cfinite||s.divide){
					auto leaf=pool.view(type(at(s.source))).fields[1]; if(s.width) leaf=pool.view(leaf).fields[0];
					struct Total{ string value,proof; }
					Table!(uint,uint) totalIds; Total[] totals;
					Total total(Term t){
						auto old=totalIds.get(t.id,uint.max); if(old!=uint.max) return totals[old];
						auto q=arena.view(t),source="n"~to!string(t.id)~".eval ξ",tag="affine"~id~"_"~to!string(t.id); Total v;
						if(!q.arity){
							if((q.sort==Sort.real_||q.sort==Sort.complex)&&arena.isNumber(t)&&(arena.number(t).zero||arena.number(t).one)){
								auto suffix=q.sort==Sort.complex?"C":"R"; v.value="("~(arena.number(t).zero?"0":"1")~" : "~(q.sort==Sort.complex?"ℂ":"ℝ")~")"; v.proof="AffineRecurrence."~(arena.number(t).zero?"zero":"one")~suffix;
							}else{ v.value="(("~source~").getD "~(q.sort==Sort.boolean?"false":"0")~")"; v.proof="rfl"; }
						}else{
							auto x=total(arena.viewChild(t,0)); auto op=leanValueOperation(arena,t);
							if(q.op==Op.builtin){
								auto f="Functions."~builtinInfo(cast(Builtin)q.value).code;
								if(q.arity==1){ auto domain=q.value==Builtin.invQ?"(show "~x.value~" ≠ (0 : ℚ) from of_decide_eq_true rfl)":"True.intro"; v.value="("~f~".value "~x.value~")"; v.proof="Eq.trans (congrArg "~op~" "~x.proof~") (Tensor.apply_some "~f~" "~x.value~" "~domain~")"; }
								else{ auto y=total(arena.viewChild(t,1)); v.value="("~f~".value "~x.value~" "~y.value~")"; v.proof="Eq.trans (congrArg₂ "~op~" "~x.proof~" "~y.proof~") (AffineRecurrence.apply2_some "~f~" "~x.value~" "~y.value~" True.intro)"; }
							}else if(q.op==Op.add||q.op==Op.mul){
								auto y=total(arena.viewChild(t,1)); v.value="("~x.value~(q.op==Op.add?" + ":" * ")~y.value~")"; v.proof="congrArg₂ "~op~" "~x.proof~" "~y.proof;
							}else{ v.value=q.op==Op.pow?"("~x.value~" ^ "~to!string(q.value)~")":q.op==Op.abs?"|"~x.value~"|":"(star "~x.value~")"; v.proof="congrArg "~op~" "~x.proof; }
						}
						code~="theorem "~tag~" (ξ : Env) : "~source~" = some "~v.value~" := "~v.proof~"\n";
						v.proof="("~tag~" ξ)"; totalIds.set(t.id,cast(uint)totals.length); totals~=v; return v;
					}
					string value(uint q){ return total(arena.at(nodes[q].data)).value; }
					string expression(uint q){
						auto z=nodes[q];
						if(s.indexed&&recurrenceIndex(q)) return "(.previous ⟨1, of_decide_eq_true rfl⟩)";
						if(s.indexed&&z.op==BoundOp.apply) return "(.previous ⟨0, of_decide_eq_true rfl⟩)";
						if(z.op==BoundOp.scalar) return "(.constant "~value(q)~")";
						if(z.op==BoundOp.get) return "(.previous ⟨"~to!string(arena.number(arena.at(nodes[z.b].data)).re.integer)~", of_decide_eq_true rfl⟩)";
						if(z.op==BoundOp.apply) return s.order?"(.previous ⟨"~to!string(s.order-cast(uint)arena.number(arena.at(nodes[nodes[z.b].b].data)).re.integer)~", of_decide_eq_true rfl⟩)":".previous";
						auto kind=arena.view(arena.at(z.data)),add=arena.view(scalarOperator(leaf,TensorOp.add));
						if(kind.op==add.op&&kind.value==add.value) return "(.add "~expression(z.a)~" "~expression(z.b)~")";
						return nodes[z.a].op==BoundOp.scalar?"(.left "~value(z.a)~" "~expression(z.b)~")":"(.right "~expression(z.a)~" "~value(z.b)~")";
					}
					string constants(uint q){
						auto z=nodes[q];
						if((s.width||s.indexed||s.cfinite)&&z.op==BoundOp.vectorNil) return "(Eq.refl Tensor.nilValue)";
						if(s.indexed&&recurrenceIndex(q)){
							string index(uint id){ auto x=nodes[id]; return x.op==BoundOp.variable?"(some x)":"("~valueOperation(x)~" "~index(x.a)~")"; }
							return "(Eq.refl "~index(q)~")";
						}
						if(z.op==BoundOp.scalar) return total(arena.at(z.data)).proof;
						if(z.op==BoundOp.conditional){
							auto base=constants(z.b);
							if(s.width){
								auto eq="(fun i => i.elim0)"; foreach(j;0..s.width) eq="(Fin.cases rfl "~eq~")";
								base="(Eq.trans "~base~" (congrArg some (funext "~eq~")))";
							}
							return "(Binding.conditional_congr "~constants(z.a)~" "~base~" "~constants(z.c)~")";
						}
						if(s.order&&z.op==BoundOp.apply) return "(congrArg (fun z : Option ℕ => z.bind g) (LinearRecurrence.lag x "~to!string(s.order)~" "~to!string(arena.number(arena.at(nodes[nodes[z.b].b].data)).re.integer)~" (of_decide_eq_true rfl)))";
						if(z.op==BoundOp.vectorCons||z.op==BoundOp.primitive&&z.b!=uint.max)
							return "(congrArg₂ "~valueOperation(z)~" "~constants(z.a)~" "~constants(z.b)~")";
						return "rfl";
					}
					string raw(uint q){ auto z=nodes[q]; return z.op==BoundOp.scalar?"(n"~to!string(z.data)~".eval ξ)":z.op==BoundOp.vectorNil?"Tensor.nilValue":"(Tensor.consValue "~raw(z.a)~" "~raw(z.b)~")"; }
					if(s.divide){
						auto eta="({ ξ with natural := fun i => if i = "~to!string(s.variable)~" then x else ξ.natural i })";
						string specialized(uint q){auto z=nodes[q];if(z.op==BoundOp.scalar||z.op==BoundOp.variable)return "rfl";
							auto op=valueOperation(z);return z.b==uint.max?"(congrArg "~op~" "~specialized(z.a)~")":"(congrArg₂ "~op~" "~specialized(z.a)~" "~specialized(z.b)~")";}
						string forceValue(uint q){foreach(f;s.facts)if(f.node==q)return "((n"~to!string(f.input.id)~".eval "~eta~").getD 0)";assert(0,"missing divide leaf");}
						string forceProof(uint q){foreach(j,f;s.facts)if(f.node==q){
							auto domain="(QSym.Linear"~to!string(si)~"_"~to!string(j)~".DomainCertificate.domain_correct "~eta~")";
							auto bridge="(show "~name(q)~".eval ξ "~env~" = n"~to!string(f.input.id)~".eval "~eta~" from "~specialized(q)~")";
							return "(Eq.trans "~bridge~" (DivideConquer.some_of_domain "~domain~"))";
						}assert(0,"missing divide proof");}
						string divideExpression(uint k){auto e=s.divideExpressions[k];final switch(e.kind){
							case CFiniteExprKind.force:return "(.constant "~forceValue(e.source)~")";
							case CFiniteExprKind.previous:return s.mixed?(e.b?".upper":".lower") : ".previous";
							case CFiniteExprKind.add:return "(.add "~divideExpression(e.a)~" "~divideExpression(e.b)~")";
							case CFiniteExprKind.left:return "(.left "~total(e.value).value~" "~divideExpression(e.a)~")";
							case CFiniteExprKind.right:return "(.right "~divideExpression(e.a)~" "~total(e.value).value~")";
						}}
						string expressionProof(uint k){auto e=s.divideExpressions[k];final switch(e.kind){
							case CFiniteExprKind.force:return forceProof(e.source);
							case CFiniteExprKind.previous:return "rfl";
							case CFiniteExprKind.add:return "(congrArg₂ Functions.addN.apply "~expressionProof(e.a)~" "~expressionProof(e.b)~")";
							case CFiniteExprKind.left:return "(congrArg₂ Functions.mulN.apply "~total(e.value).proof~" "~expressionProof(e.a)~")";
							case CFiniteExprKind.right:return "(congrArg₂ Functions.mulN.apply "~expressionProof(e.a)~" "~total(e.value).proof~")";
						}}
						auto e="divideExpr"~id,seed="divideSeed"~id;
						code~="noncomputable def "~e~args~" (x : ℕ) : "~(s.mixed?"MixedDivide.Expr":"AffineRecurrence.Expr ℕ")~" := "~divideExpression(s.cfRoot)~"\n";
						code~="noncomputable def "~seed~args~" (x : ℕ) : ℕ := "~forceValue(s.base)~"\n";
						e="("~e~dimArg~" γ ξ ρ)";seed="("~seed~dimArg~" γ ξ ρ)";
						string bridge(uint q){if(q==s.base)return forceProof(q);if(q==s.delta)return expressionProof(s.cfRoot);
							auto z=nodes[q];if(z.op==BoundOp.primitive&&z.b!=uint.max)return "(congrArg₂ "~valueOperation(z)~" "~bridge(z.a)~" "~bridge(z.b)~")";return "rfl";}
						auto body=nodes[n.a].a;Total co;if(!s.mixed)co=total(s.divideExpressions[s.cfRoot].coefficient);auto radix=to!string(s.radix);
						auto hp="(fun g x => Eq.trans ("~programProof(body)~").symm "~bridge(body)~")";
						auto sfn="(fun x : Option ℕ => "~name(nodes[s.seedFunction].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) x ρ))";
						auto tfn="(fun x : Option ℕ => "~name(nodes[s.tollFunction].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) x ρ))";
						auto hs="(fun x => "~forceProof(s.base)~")",ht="(fun x => Eq.trans "~expressionProof(s.cfRoot)~" ("~(s.mixed?"MixedDivide":"DivideConquer")~".offset_eq ("~e~" x)))";
						if(s.mixed){
							code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (MixedDivide.solve_sum (rec"~id~dimArg~" γ ξ ρ) "~(s.inclusive?"true":"false")~" "~(s.left?"true":"false")~" "~seed~" "~e~" (fun _ => rfl) (fun _ => rfl) "~hp~" "~sfn~" "~tfn~" "~hs~" "~ht~"))\n";
							continue;
						}
						code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (DivideConquer.solve_sum (rec"~id~dimArg~" γ ξ ρ) "~radix~" "~co.value~" (of_decide_eq_true rfl) "~(s.inclusive?"true":"false")~" "~(s.left?"true":"false")~" "~seed~" "~e~" (fun _ => rfl) "~hp~" (n"~to!string(s.divideExpressions[s.cfRoot].coefficient.id)~".eval ξ) "~co.proof~" "~sfn~" "~tfn~" "~hs~" "~ht~"))\n";
						continue;
					}
					auto add=tensorOperation(leaf,TensorOp.add),mul=tensorOperation(leaf,TensorOp.mul),sort=elementSort(leaf);
					auto suffix=sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":"";
					auto ha=suffix.length?"AffineRecurrence.add"~suffix:"rfl",hm=suffix.length?"AffineRecurrence.mul"~suffix:"rfl";
					auto body=nodes[n.a].a;
					auto get=nodes[s.width?nodes[nodes[s.target].a].a:nodes[s.target].a],product=nodes[get.a],matrix=nodes[product.a].a;
					auto expr=(s.width||s.cfinite)?"":expression(s.delta),hmat=constants(matrix),hv=constants(product.b);
					auto field=sort==Sort.complex?"C":sort==Sort.real_?"R":"";
					auto hz=field.length?"(Option.some.inj AffineRecurrence.zero"~field~")":"rfl",ho=field.length?"(Option.some.inj AffineRecurrence.one"~field~")":"rfl";

					if(s.cfinite){
						string vectorCases(string[] xs){ auto r="(fun i => i.elim0)"; foreach_reverse(x;xs) r="(Fin.cases "~x~" "~r~")"; return r; }
						string hom(Sort target){ final switch(target){
							case Sort.integer:return "(Nat.castRingHom ℤ)";
							case Sort.rational:return "(Int.castRingHom ℚ)";
							case Sort.real_:return "(Rat.castHom ℝ)";
							case Sort.complex:return "Complex.ofRealHom";
							case Sort.natural,Sort.boolean,Sort.density,Sort.measure:assert(0);
						} }
						string[] modelNames; modelNames.length=s.cfModels.length;
						string model(uint k){
							if(modelNames[k].length) return modelNames[k];
							auto m=s.cfModels[k],tag="cf"~id~"_"~to!string(k); string rhs;
							final switch(m.kind){
								case CFiniteKind.zero:rhs=".zero"; break;
								case CFiniteKind.constant:rhs="(.constant "~total(m.value).value~")"; break;
								case CFiniteKind.index:rhs=".index"; break;
								case CFiniteKind.geometric:rhs="(.geometric "~total(m.value).value~")"; break;
								case CFiniteKind.add:rhs="(.add "~model(m.a)~" "~model(m.b)~")"; break;
								case CFiniteKind.mul:rhs="(.mul "~model(m.a)~" "~model(m.b)~")"; break;
								case CFiniteKind.left:rhs="(.left "~total(m.value).value~" "~model(m.a)~")"; break;
								case CFiniteKind.right:rhs="(.right "~model(m.a)~" "~total(m.value).value~")"; break;
								case CFiniteKind.map:rhs="(.map "~model(m.a)~" "~hom(m.sort)~")"; break;
								case CFiniteKind.power:rhs="(.power "~model(m.a)~" "~to!string(m.b)~")"; break;
								case CFiniteKind.coordinate:
									string vector(string[] xs){ auto r="(fun i : Fin 0 => i.elim0)"; foreach_reverse(x;xs)r="(Fin.cons "~x~" "~r~")"; return r; }
									string[] rows,initial;
									foreach(i;0..m.size){ string[] cells; foreach(j;0..m.size)cells~=total(m.matrix[i*m.size+j]).value; rows~=vector(cells); initial~=total(m.initial[i]).value; }
									rhs="(.coordinate "~vector(rows)~" "~vector(initial)~" ⟨"~to!string(m.coordinate)~", of_decide_eq_true rfl⟩)"; break;
							}
							code~="noncomputable def "~tag~" (ξ : Env) : CFinite.Sequence (Ty.denote ."~leanSort(m.sort)~") := "~rhs~"\n";
							return modelNames[k]="("~tag~" ξ)";
						}
						string totalBinary(BoundNode z){
							auto q=arena.view(arena.at(z.data));
							return q.op==Op.builtin?"(fun a b => AffineRecurrence.apply2_some Functions."~builtinInfo(cast(Builtin)q.value).code~" a b True.intro)":"(fun _ _ => rfl)";
						}
						auto forceIndex="(x+"~to!string(s.order)~")";
						string forceProof(uint k){
							auto m=s.cfModels[k],z=nodes[m.source];
							final switch(m.kind){
								case CFiniteKind.constant:return "(CFinite.constant_eq "~total(m.value).value~" "~forceIndex~" "~total(m.value).proof~")";
								case CFiniteKind.index:return "(CFinite.index_eq (R := ℕ) "~forceIndex~" (Eq.refl (some "~forceIndex~")))";
								case CFiniteKind.geometric:return "(CFinite.geometric_eq "~valueOperation(z)~" "~totalBinary(z)~" "~total(m.value).value~" "~forceIndex~" "~total(m.value).proof~")";
								case CFiniteKind.add, CFiniteKind.mul:return "(CFinite."~(m.kind==CFiniteKind.add?"add":"mul")~"_eq "~valueOperation(z)~" "~totalBinary(z)~" "~model(m.a)~" "~model(m.b)~" "~forceIndex~" "~forceProof(m.a)~" "~forceProof(m.b)~")";
								case CFiniteKind.map:return "(CFinite.map_eq "~hom(m.sort)~" "~valueOperation(z)~" (fun a => Tensor.apply_some Functions."~builtinInfo(cast(Builtin)arena.view(arena.at(z.data)).value).code~" a True.intro) "~model(m.a)~" "~forceIndex~" "~forceProof(m.a)~")";
								case CFiniteKind.power:
									auto operation=valueOperation(z); if(z.b!=uint.max) operation="(fun a => "~operation~" a (n"~to!string(nodes[z.b].data)~".eval ξ))";
									auto proof=z.b==uint.max?"(fun _ => rfl)":"(fun a => AffineRecurrence.apply2_some Functions."~builtinInfo(cast(Builtin)arena.view(arena.at(z.data)).value).code~" a "~to!string(m.b)~" True.intro)";
									return "(CFinite.power_eq "~operation~" "~to!string(m.b)~" "~proof~" "~model(m.a)~" "~forceIndex~" "~forceProof(m.a)~")";
								case CFiniteKind.coordinate:
									auto leaf=scalarType(m.sort),add=tensorOperation(leaf,TensorOp.add),mul=tensorOperation(leaf,TensorOp.mul);
									auto suffix=m.sort==Sort.natural?"N":m.sort==Sort.integer?"Z":m.sort==Sort.rational?"Q":"";
									auto ha=suffix.length?"AffineRecurrence.add"~suffix:"rfl",hm=suffix.length?"AffineRecurrence.mul"~suffix:"rfl";
									auto field=m.sort==Sort.complex?"C":m.sort==Sort.real_?"R":"";
									auto hz=field.length?"(Option.some.inj AffineRecurrence.zero"~field~")":"rfl",ho=field.length?"(Option.some.inj AffineRecurrence.one"~field~")":"rfl";
									return "(CFinite.coordinate_eq "~add~" "~mul~" "~ha~" "~hm~" "~tensorLiteral(leaf,0)~" "~tensorLiteral(leaf,1)~" "~hz~" "~ho~" "~to!string(m.size)~" "~raw(m.a)~" "~raw(m.b)~" _ _ ⟨"~to!string(m.coordinate)~", of_decide_eq_true rfl⟩ "~constants(m.a)~" "~constants(m.b)~" "~forceIndex~")";
								case CFiniteKind.zero,CFiniteKind.left,CFiniteKind.right:assert(0);
							}
						}
						string cfExpression(uint k){
							auto e=s.cfExpressions[k]; final switch(e.kind){
								case CFiniteExprKind.force:return "(.force "~model(e.a)~")";
								case CFiniteExprKind.previous:return ".previous";
								case CFiniteExprKind.add:return "(.add "~cfExpression(e.a)~" "~cfExpression(e.b)~")";
								case CFiniteExprKind.left:return "(.left "~total(e.value).value~" "~cfExpression(e.a)~")";
								case CFiniteExprKind.right:return "(.right "~cfExpression(e.a)~" "~total(e.value).value~")";
							}
						}
						string cfProof(uint k){
							auto e=s.cfExpressions[k],z=nodes[e.source]; final switch(e.kind){
								case CFiniteExprKind.force:return forceProof(e.a);
								case CFiniteExprKind.previous:return "(congrArg (fun z : Option ℕ => z.bind g) (LinearRecurrence.lag x "~to!string(s.order)~" 1 (of_decide_eq_true rfl)))";
								case CFiniteExprKind.add:return "(congrArg₂ "~valueOperation(z)~" "~cfProof(e.a)~" "~cfProof(e.b)~")";
								case CFiniteExprKind.left:return "(congrArg₂ "~valueOperation(z)~" "~total(e.value).proof~" "~cfProof(e.a)~")";
								case CFiniteExprKind.right:return "(congrArg₂ "~valueOperation(z)~" "~cfProof(e.a)~" "~total(e.value).proof~")";
							}
						}
						string eta="({ ξ with natural := fun i => if i = "~to!string(s.variable)~" then x else ξ.natural i })";
						string specialized(uint q,uint index){
							auto z=nodes[q]; if(z.op==BoundOp.scalar) return "rfl";
							if(z.op==BoundOp.variable) return index==uint.max?"(AffineRecurrence.apply2_some Functions.addN x "~to!string(s.order)~" True.intro).symm":"rfl";
							auto a=specialized(z.a,index),op=valueOperation(z);
							return z.b==uint.max?"(congrArg "~op~" "~a~")":"(congrArg₂ "~op~" "~a~" "~specialized(z.b,index)~")";
						}
						string fact(uint q,uint index){
							foreach(j,f;s.facts) if(f.node==q&&f.index==index){
								auto p="QSym.Linear"~to!string(si)~"_"~to!string(j),e=index==uint.max?eta:"ξ";
								auto at=index==uint.max?"x+"~to!string(s.order):to!string(index),rho=replace(env,"(some x)","(some ("~at~"))");
								auto bridge="(show "~name(q)~".eval ξ "~rho~" = n"~to!string(f.input.id)~".eval "~e~" from "~specialized(q,index)~")";
								return "(Eq.trans "~bridge~" (LinearRecurrence.known ("~p~".DomainCertificate.domain_correct "~e~") ("~p~".ValueCertificate.refinement "~e~")))";
							}
							assert(0,"missing recurrence fact");
						}
						string select(uint q,uint index){
							if(index==uint.max&&q==s.delta) return cfProof(s.cfRoot);
							if(!depends(at(q),1)){
								foreach(f;s.facts) if(f.node==q&&f.index==index) return "(Eq.trans "~fact(q,index)~" "~total(arena.castTo(f.value.output,sort)).proof~")";
								assert(0,"missing recurrence seed");
							}
							uint test,yes,no; bool reverse; enforce(recurrenceBranches(q,test,yes,no,reverse),"missing recurrence branch"); bool selected;
							foreach(f;s.facts) if(f.node==test&&f.index==index) selected=f.value.output==arena.boolean(true);
							return "(Eq.trans (LinearRecurrence."~(reverse?"select_rev":"select")~" "~add~" "~ha~" "~(selected?"true":"false")~" _ _ "~fact(test,index)~") "~select(selected?yes:no,index)~")";
						}
						string cases(string[] proofs){
							auto r="(fun i => i.elim0)"; foreach_reverse(p;proofs) r="(Fin.cases "~p~" "~r~")"; return r;
						}
						string vector(string[] values){
							auto r="(fun i : Fin 0 => i.elim0)"; foreach_reverse(v;values) r="(Fin.cons "~v~" "~r~")"; return r;
						}
						auto cexpr=cfExpression(s.cfRoot),ctag="cfExpr"~id;
						code~="noncomputable def "~ctag~" (ξ : Env) : CFiniteRecurrence.Expr (Ty.denote ."~leanSort(sort)~") := "~cexpr~"\n";
						cexpr="("~ctag~" ξ)";
						string[] seeds,baseProofs;
						foreach(j,seed;s.seeds){ seeds~=total(seed).value; baseProofs~="(Eq.trans ("~programProof(body)~").symm "~select(body,cast(uint)j)~")"; }
						auto cseq="cfSequence"~id;
						code~="noncomputable def "~cseq~" (ξ : Env) := CFiniteRecurrence.Prefix.sequence (k := "~to!string(s.order-1)~") "~cexpr~" "~vector(seeds)~"\n";
						auto sequence="("~cseq~" ξ)",hb="(fun g => "~cases(baseProofs)~")";
						string[] eqs; foreach(j;0..s.cfSize)eqs~="rfl";
						auto heq="(funext "~vectorCases(eqs)~")"; string[] rows; foreach(j;0..s.cfSize)rows~=heq;
						hmat="(Eq.trans "~hmat~" (congrArg some (funext "~vectorCases(rows)~")))";
						hv="(Eq.trans "~hv~" (congrArg some "~heq~"))";
						auto hp="(fun g x => Eq.trans ("~programProof(body)~").symm "~select(body,uint.max)~")";
						// Check rows independently: a single nested matrix equality causes
						// elaboration to repeatedly expand the whole tensor-product state.
						string[] rowProofs; auto row=matrix;
						foreach(j;0..s.cfSize){
							auto item=nodes[row].a,tag="cfRow"~id~"_"~to!string(j);
							auto proof="(Eq.trans "~constants(item)~" (congrArg some "~heq~"))";
							code~="set_option maxHeartbeats 2000000 in\ntheorem "~tag~" (ξ : Env) : "~raw(item)~" = some ("~sequence~".matrix ⟨"~to!string(j)~", of_decide_eq_true rfl⟩) := "~proof~"\n";
							rowProofs~="("~tag~" ξ)"; row=nodes[row].b;
						}
						auto matrixProof="(Eq.refl Tensor.nilValue)";
						foreach_reverse(proof;rowProofs) matrixProof="(congrArg₂ Tensor.consValue "~proof~" "~matrixProof~")";
						hmat="(Eq.trans "~matrixProof~" (congrArg some "~heq~"))";
						code~="set_option maxHeartbeats 2000000 in\ntheorem cfMatrix"~id~" (ξ : Env) : "~raw(matrix)~" = some "~sequence~".matrix := "~hmat~"\n";
						code~="set_option maxHeartbeats 2000000 in\ntheorem cfSeed"~id~" (ξ : Env) : "~raw(product.b)~" = some "~sequence~".initial := "~hv~"\n";
						code~="set_option maxHeartbeats 2000000 in\ntheorem cfStep"~id~args~" : ∀ g x, (rec"~id~dimArg~" γ ξ ρ).eval g (x+"~to!string(s.order)~") = CFiniteRecurrence.Expr.eval "~add~" "~mul~" (g (x+"~to!string(s.order-1)~")) (x+"~to!string(s.order)~") "~cexpr~" := "~hp~"\n";
						code~="set_option maxHeartbeats 2000000 in\ntheorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (CFiniteRecurrence.Prefix.solve_matrix (k := "~to!string(s.order-1)~") (rec"~id~dimArg~" γ ξ ρ) "~add~" "~mul~" "~ha~" "~hm~" "~cexpr~" "~vector(seeds)~" "~hb~" (cfStep"~id~dimArg~" γ ξ ρ) "~tensorLiteral(leaf,0)~" "~tensorLiteral(leaf,1)~" "~hz~" "~ho~" "~raw(matrix)~" "~raw(product.b)~" (cfMatrix"~id~" ξ) (cfSeed"~id~" ξ)))\n";
						continue;
					}
					if(s.indexed){
						auto cast_="(fun n : Option ℕ => n)",hc="IndexedRecurrence.castN";
						if(sort!=Sort.natural){
							cast_="Functions.castNZ.apply"; hc="IndexedRecurrence.castZ";
							if(sort>=Sort.rational){ cast_="(fun n => Functions.castZQ.apply (Functions.castNZ.apply n))"; hc="RepeatedSpectra.castQ"; }
							if(sort==Sort.real_){ cast_="(fun n => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n)))"; hc="RepeatedSpectra.castR"; }
							if(sort==Sort.complex){ cast_="(fun n => Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))))"; hc="RepeatedSpectra.castC"; }
						}
						auto eq="(funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))))";
						hmat="(Eq.trans "~hmat~" (congrArg some (funext (Fin.cases "~eq~" (Fin.cases "~eq~" (Fin.cases "~eq~" (fun i => i.elim0)))))))";
						hv="(Eq.trans "~hv~" (congrArg some "~eq~"))";
						auto hp="(fun g x => Eq.trans ("~programProof(body)~").symm "~constants(body)~")";
						code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (IndexedRecurrence.solve_matrix (rec"~id~dimArg~" γ ξ ρ) "~add~" "~mul~" "~cast_~" "~ha~" "~hm~" "~hc~" "~value(s.base)~" "~expr~" "~hp~" "~tensorLiteral(leaf,0)~" "~tensorLiteral(leaf,1)~" "~hz~" "~ho~" "~raw(matrix)~" "~raw(product.b)~" "~hmat~" "~hv~"))\n";
						continue;
					}
					if(s.width){
						string vector(string[] xs){ auto r="(fun i : Fin 0 => i.elim0)"; foreach_reverse(x;xs) r="(Fin.cons "~x~" "~r~")"; return r; }
						string cases(string[] xs){ auto r="(fun i => i.elim0)"; foreach_reverse(x;xs) r="(Fin.cases "~x~" "~r~")"; return r; }
						string[] seeds,expressions,eqs; auto seed=s.base;
						foreach(j;0..s.width){ seeds~=value(nodes[seed].a); seed=nodes[seed].b; expressions~=expression(s.components[j]); }
						foreach(j;0..s.width+1) eqs~="rfl";
						auto heq="(funext "~cases(eqs)~")"; string[] rows; foreach(j;0..s.width+1) rows~=heq;
						hmat="(Eq.trans "~hmat~" (congrArg some (funext "~cases(rows)~")))";
						hv="(Eq.trans "~hv~" (congrArg some "~heq~"))";
						auto hp="(fun g x => Eq.trans ("~programProof(body)~").symm "~constants(body)~")";
						code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (CoupledRecurrence.solve_matrix (d := "~to!string(s.width)~") (rec"~id~dimArg~" γ ξ ρ) "~add~" "~mul~" "~ha~" "~hm~" "~vector(seeds)~" "~vector(expressions)~" "~hp~" "~tensorLiteral(leaf,0)~" "~tensorLiteral(leaf,1)~" "~hz~" "~ho~" "~raw(matrix)~" "~raw(product.b)~" "~hmat~" "~hv~"))\n";
						continue;
					}
					if(s.order){
						string eta="({ ξ with natural := fun i => if i = "~to!string(s.variable)~" then x else ξ.natural i })";
						string specialized(uint q,uint index){
							auto z=nodes[q]; if(z.op==BoundOp.scalar) return "rfl";
							if(z.op==BoundOp.variable) return index==uint.max?"(AffineRecurrence.apply2_some Functions.addN x "~to!string(s.order)~" True.intro).symm":"rfl";
							auto a=specialized(z.a,index),op=valueOperation(z);
							return z.b==uint.max?"(congrArg "~op~" "~a~")":"(congrArg₂ "~op~" "~a~" "~specialized(z.b,index)~")";
						}
						string fact(uint q,uint index){
							foreach(j,f;s.facts) if(f.node==q&&f.index==index){
								auto p="QSym.Linear"~to!string(si)~"_"~to!string(j),e=index==uint.max?eta:"ξ";
								auto at=index==uint.max?"x+"~to!string(s.order):to!string(index),rho=replace(env,"(some x)","(some ("~at~"))");
								auto bridge="(show "~name(q)~".eval ξ "~rho~" = n"~to!string(f.input.id)~".eval "~e~" from "~specialized(q,index)~")";
								return "(Eq.trans "~bridge~" (LinearRecurrence.known ("~p~".DomainCertificate.domain_correct "~e~") ("~p~".ValueCertificate.refinement "~e~")))";
							}
							assert(0,"missing recurrence fact");
						}
						string select(uint q,uint index){
							if(index==uint.max&&q==s.delta) return constants(q);
							if(!depends(at(q),1)){
								foreach(f;s.facts) if(f.node==q&&f.index==index) return "(Eq.trans "~fact(q,index)~" "~total(arena.castTo(f.value.output,sort)).proof~")";
								assert(0,"missing recurrence seed");
							}
							uint test,yes,no; bool reverse; enforce(recurrenceBranches(q,test,yes,no,reverse),"missing recurrence branch"); bool selected;
							foreach(f;s.facts) if(f.node==test&&f.index==index) selected=f.value.output==arena.boolean(true);
							return "(Eq.trans (LinearRecurrence."~(reverse?"select_rev":"select")~" "~add~" "~ha~" "~(selected?"true":"false")~" _ _ "~fact(test,index)~") "~select(selected?yes:no,index)~")";
						}
						string cases(string[] proofs){
							auto r="(fun i => i.elim0)"; foreach_reverse(p;proofs) r="(Fin.cases "~p~" "~r~")"; return r;
						}
						string vector(string[] values){
							auto r="(fun i : Fin 0 => i.elim0)"; foreach_reverse(v;values) r="(Fin.cons "~v~" "~r~")"; return r;
						}
						string[] seeds,baseProofs,eqs;
						foreach(j,seed;s.seeds){ seeds~=total(seed).value; baseProofs~="(Eq.trans ("~programProof(body)~").symm "~select(body,cast(uint)j)~")"; }
						foreach(j;0..s.order+1) eqs~="rfl";
						auto heq="(funext "~cases(eqs)~")"; string[] rows; foreach(j;0..s.order+1) rows~=heq;
						hmat="(Eq.trans "~hmat~" (congrArg some (funext "~cases(rows)~")))";
						hv="(Eq.trans "~hv~" (congrArg some "~heq~"))";
						auto hb="(fun g => "~cases(baseProofs)~")",hs="(fun g x => Eq.trans ("~programProof(body)~").symm "~select(body,uint.max)~")";
						code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (LinearRecurrence.solve_matrix (k := "~to!string(s.order-1)~") (rec"~id~dimArg~" γ ξ ρ) "~add~" "~mul~" "~ha~" "~hm~" "~expr~" "~vector(seeds)~" "~hb~" "~hs~" "~tensorLiteral(leaf,0)~" "~tensorLiteral(leaf,1)~" "~hz~" "~ho~" "~raw(matrix)~" "~raw(product.b)~" "~hmat~" "~hv~"))\n";
						continue;
					}
					auto base=value(s.base),hp="(fun g x => Eq.trans ("~programProof(body)~").symm "~constants(body)~")";
					code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (AffineRecurrence.solve_matrix (rec"~id~dimArg~" γ ξ ρ) "~add~" "~mul~" "~ha~" "~hm~" "~base~" "~expr~" "~hp~" "~tensorLiteral(leaf,0)~" "~tensorLiteral(leaf,1)~" "~hz~" "~ho~" "~raw(matrix)~" "~raw(product.b)~" "~hmat~" "~hv~"))\n";
					continue;
				}
				auto base="(n"~to!string(nodes[s.base].data)~".eval ξ)",delta="(n"~to!string(nodes[s.delta].data)~".eval ξ)";
				if(s.cutoff){
					auto hp="(fun g x => ("~programProof(nodes[n.a].a)~").symm)";
					auto lemma=s.band==2?"solve_nat_interval":s.band==1?"solve_nat_cutoff_lt":"solve_nat_cutoff";
					auto lower=s.band==2?" ((n"~to!string(nodes[s.lower].data)~".eval ξ).getD 0)":"";
					auto side=s.band?" (of_decide_eq_true rfl)":"";
					code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n"~
						"  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (Recursion."~lemma~" (rec"~id~dimArg~" γ ξ ρ) ("~base~".getD 0)"~lower~" ("~delta~".getD 0)"~side~" "~hp~"))\n";
					continue;
				}
				auto op=s.zero==Law.natural_recurrence_mul_base?"Functions.mulN.apply":"Functions.addN.apply";
				if(s.left) op="(fun x y => "~op~" y x)";
				auto k="(fun (x : ℕ) => "~name(nodes[s.target].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some x) ρ))";
				auto hp="(fun g x => ("~programProof(nodes[n.a].a)~").symm)";
				auto hz="(Generated.r_"~to!string(s.zero)~" "~base~" "~delta~" ⟨_, rfl⟩)";
				auto successor="(congrArg (fun (z : Option ℕ) => "~name(nodes[s.target].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) z ρ)) (Recursion.nat_successor x).symm)";
				auto hs="(fun x => Eq.trans "~successor~" (Generated.r_"~to!string(s.law)~" "~base~" "~delta~" (some x)).symm)";
				code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n"~
					"  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (Recursion.solve_nat_step (rec"~id~dimArg~" γ ξ ρ) "~op~" "~base~" "~delta~" "~k~" "~hp~" "~hz~" "~hs~"))\n";
			}
		}
		foreach(si,s;result.spectra){
			auto tag=to!string(si),source=nodes[s.source],powerNode=nodes[source.a],element=typeLeaf(type(at(s.source))),sort=elementSort(element);
			auto add=tensorOperation(element,TensorOp.add),mul=tensorOperation(element,TensorOp.mul);
			auto suffix=sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":sort==Sort.real_?"R":"C";
			auto ha=sort==Sort.real_||sort==Sort.complex?"rfl":"AffineRecurrence.add"~suffix,hm=sort==Sort.real_||sort==Sort.complex?"rfl":"AffineRecurrence.mul"~suffix;
			auto pow="Functions.pow"~suffix~"N.apply",hp="Spectral.pow"~suffix;
			auto hz=sort==Sort.real_||sort==Sort.complex?"(Option.some.inj AffineRecurrence.zero"~suffix~")":sort==Sort.rational?"(div_one (0 : ℚ))":"rfl",ho=sort==Sort.real_||sort==Sort.complex?"(Option.some.inj AffineRecurrence.one"~suffix~")":sort==Sort.rational?"(div_one (1 : ℚ))":"rfl";
			auto units=" "~tensorLiteral(element,0)~" "~tensorLiteral(element,1)~" "~hz~" "~ho;
			string raw(Term t){ return "(n"~to!string(t.id)~".eval ξ)"; }
			string val(Term t){ Number v; return !s.cubeZero&&literalNumber(t,v)&&(v.zero||v.one)?"("~(v.zero?"0":"1")~" : "~"("~leanType(element)~" : Binding.Ty).denote"~")":"("~raw(t)~".getD 0)"; }
			string[uint] totalProofs;
			string total(Term t){
				if(s.zeroRoot) if(auto old=t.id in totalProofs) return *old;
				foreach(j,f;s.parameters) if(f.input==t){
					auto id="spectral"~tag~"_"~to!string(j),v=val(t),h="Spectral.some_of_domain 0 "~raw(t)~" (QSym.Spectral"~tag~"_0_"~to!string(j)~".DomainCertificate.domain_correct ξ)";
					Number number;
					if(!s.cubeZero&&literalNumber(t,number)&&(number.zero||number.one)){
						auto literal=arena.number(number,sort),last=sort==Sort.real_||sort==Sort.complex?"AffineRecurrence."~(number.zero?"zero":"one")~suffix:sort==Sort.rational?"(congrArg some (div_one ("~(number.zero?"0":"1")~" : ℚ)))":"rfl";
						h="Eq.trans (LinearRecurrence.known (QSym.Spectral"~tag~"_0_"~to!string(j)~".DomainCertificate.domain_correct ξ) (Numeric.sound ξ n"~to!string(t.id)~" n"~to!string(literal.id)~" (of_decide_eq_true rfl))) "~last;
						if(sort==Sort.rational) h=arena.isNumber(t)?last:"Numeric.calculate_sound ξ n"~to!string(t.id)~" ("~(number.zero?"0":"1")~" : ℚ) rfl";
					}
					if(s.zeroRoot){
						auto name="spectralTotal"~tag~"_"~to!string(j),reference="("~name~" ξ)";
						code~="theorem "~name~" (ξ : Env) : "~raw(t)~" = some "~v~" := "~h~"\n";
						totalProofs[t.id]=reference; return reference;
					}
					return "(show "~raw(t)~" = some "~v~" from "~h~")";
				}
				assert(0,"missing spectral parameter");
			}
			string cases(string[] proofs){ auto r="(fun i => i.elim0)"; foreach_reverse(p;proofs) r="(Fin.cases "~p~" "~r~")"; return r; }
			string vector(string[] xs){ auto r="(fun i : Fin 0 => i.elim0)"; foreach_reverse(x;xs) r="(Fin.cons "~x~" "~r~")"; return r; }
			string constants(uint q){
				auto z=nodes[q]; if(z.op==BoundOp.scalar) return total(arena.at(z.data));
				if(z.op==BoundOp.vectorNil) return "rfl";
				return "(congrArg₂ Tensor.consValue "~constants(z.a)~" "~constants(z.b)~")";
			}
			auto mat="("~name(powerNode.a)~".eval ξ ρ)",vec="("~name(source.b)~".eval ξ ρ)",exponent="("~name(powerNode.b)~".eval ξ ρ)";
			auto hmat=constants(powerNode.a),hv=constants(source.b); string proof;
			auto spectralArgs=dimDecl~" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctxName(source.context)~")";
			if(s.split){
				string[] matrices,vectors; auto left=s.split,right=s.size-left;
				foreach(part;0..2){
					auto start=part?left:0,count=part?right:left; string[] rows,seed;
					foreach(i;start..start+count){
						string[] cells; foreach(j;start..start+count) cells~=val(s.matrix[i*s.size+j]);
						rows~=vector(cells); seed~=val(s.vector[i]);
					}
					matrices~=vector(rows); vectors~=vector(seed);
				}
				string[] eqs,rows; foreach(i;0..s.size) eqs~="rfl";
				auto heq="(funext "~cases(eqs)~")"; foreach(i;0..s.size) rows~=heq;
				hmat="(Eq.trans "~hmat~" (congrArg some (funext "~cases(rows)~")))";
				hv="(Eq.trans "~hv~" (congrArg some "~heq~"))";
				proof="MatrixBlocks.split_value (m := "~to!string(left)~") (n := "~to!string(right)~") (of_decide_eq_true rfl) (of_decide_eq_true rfl) "~add~" "~mul~" "~ha~" "~hm~units~" "~matrices[0]~" "~matrices[1]~" "~vectors[0]~" "~vectors[1]~" "~mat~" "~vec;
				foreach(q;s.blocks) proof~=" ("~name(q)~".eval ξ ρ)";
				proof~=" "~hmat~" "~hv;
				foreach(q;s.blocks) proof~=" "~constants(q);
				proof~=" "~exponent;
			}else if(s.zeroRoot||s.jordan){
				code~="attribute [local irreducible] Value.add Value.mul\n";
				string[] av,ar,at_,vv,vr,vt,rv,rr,rt,cv,cr,ct;
				foreach(i;0..3){
					string[] vals,raws,totals,cvals,craws,ctotals;
					foreach(j;0..3){
						auto a=s.matrix[i*3+j],c=s.components[i*3+j];
						vals~=val(a); raws~=raw(a); totals~=total(a);
						cvals~=val(c); craws~=raw(c); ctotals~=total(c);
					}
					av~=vector(vals); ar~=vector(raws); at_~=cases(totals);
					cv~=vector(cvals); cr~=vector(craws); ct~=cases(ctotals);
					vv~=val(s.vector[i]); vr~=raw(s.vector[i]); vt~=total(s.vector[i]);
					rv~=val(s.roots[i]); rr~=raw(s.roots[i]); rt~=total(s.roots[i]);
				}
				auto scalar="("~leanType(element)~" : Binding.Ty).denote";
				auto rawMatrix="("~vector(ar)~" : Fin 3 → Fin 3 → Option ("~scalar~"))";
				auto hn=sort==Sort.real_||sort==Sort.complex?"Spectral.minus"~suffix:"(congrArg some (div_one (-1 : ℚ)))";
				string checked(uint k){
					auto f=s.checks[k],prefix="QSym.Spectral"~tag~"_1_"~to!string(k),out_=arena.castTo(f.value.output,sort),zero=arena.number(Number(0),sort);
					auto hz=sort==Sort.real_||sort==Sort.complex?"AffineRecurrence.zero"~suffix:"(congrArg some (div_one (0 : ℚ)))";
					return "Spectral.checked_eq "~add~" "~mul~" "~ha~" "~hm~" "~raw(s.minus)~" _ _ "~hn~" (Eq.trans (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) (Value.Refines.trans ("~prefix~".ValueCertificate.refinement ξ) (Numeric.sound ξ n"~to!string(out_.id)~" n"~to!string(zero.id)~" (of_decide_eq_true rfl)))) "~hz~")";
				}
				string[] sums,eigen;
				foreach(i;0..3){
					auto id="spectralRoot"~tag~"_"~to!string(i);
					auto lhs=s.jordan?add~" "~raw(s.components[i])~" "~raw(s.components[3+i]):add~" ("~add~" "~raw(s.components[i])~" "~raw(s.components[3+i])~") "~raw(s.components[6+i]);
					code~="theorem "~id~" (ξ : Env) : "~lhs~" = "~vr[i]~" := "~checked(i)~"\n";
					sums~="("~id~" ξ)";
				}
				foreach(j;0..3){
					string[] row;
					foreach(i;0..3){
						auto k=3+j*3+i,id="spectralRoot"~tag~"_"~to!string(k);
						auto rhs=mul~" "~rr[j]~" "~raw(s.components[j*3+i]);
						if(s.jordan&&j==1) rhs=add~" ("~rhs~") "~raw(s.components[6+i]);
						code~="theorem "~id~" (ξ : Env) : CubeZeroSpectra.step "~add~" "~mul~" "~rawMatrix~" "~cr[j]~" "~to!string(i)~" = "~rhs~" := "~checked(k)~"\n";
						row~="("~id~" ξ)";
					}
					eigen~=cases(row);
				}
				code~="theorem spectralMatrix"~tag~spectralArgs~" : "~mat~" = some "~vector(av)~" := "~hmat~"\n";
				code~="theorem spectralVector"~tag~spectralArgs~" : "~vec~" = some "~vector(vv)~" := "~hv~"\n";
				auto ops=add~" "~mul~" "~pow~" "~ha~" "~hm~" "~hp;
				if(s.jordan){
					auto cast_="(fun n => Functions.castZQ.apply (Functions.castNZ.apply n))";
					if(sort==Sort.real_) cast_="(fun n => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n)))";
					if(sort==Sort.complex) cast_="(fun n => Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))))";
					auto inv=sort==Sort.rational?"Functions.invQ.apply":"Value.inv",hi=sort==Sort.rational?"Spectral.invQ":"rfl";
					ops=add~" "~mul~" "~inv~" "~pow~" "~cast_~" "~ha~" "~hm~" "~hi~" "~hp~" RepeatedSpectra.cast"~suffix;
				}
				proof=(s.jordan?"JordanSpectra.":"ZeroRootSpectra.")~"three_value "~ops~units~" "~vector(av)~" "~vector(vv)~" "~vector(rv)~" "~vector(cv)~" "~vector(ar)~" "~vector(vr)~" "~vector(rr)~" "~vector(cr)~" "~cases(at_)~" "~cases(vt)~" "~cases(rt)~" "~cases(ct)~" "~cases(sums)~" "~cases(eigen)~(s.jordan?" (QSym.Spectral"~tag~"_1_12.DomainCertificate.domain_correct ξ)":"")~" "~mat~" "~vec~" (spectralMatrix"~tag~dimArg~" γ ξ ρ) (spectralVector"~tag~dimArg~" γ ξ ρ) "~exponent;
			}else if(s.cubeZero){
				code~="attribute [local irreducible] Value.add Value.mul\n";
				string[] matrixValues,matrixRaw,matrixTotal,cube,vectorValues,vectorRaw,vectorTotal,zeroProofs;
				foreach(i;0..3){
					string[] vals,raws,totals,zeros;
					foreach(j;0..3){
						auto entry=s.matrix[i*3+j]; vals~=val(entry); raws~=raw(entry); totals~=total(entry);
						auto f=s.checks[i*3+j],prefix="QSym.Spectral"~tag~"_1_"~to!string(i*3+j),out_=arena.castTo(f.value.output,sort),zero=arena.number(Number(0),sort);
						auto hzero=sort==Sort.real_||sort==Sort.complex?"AffineRecurrence.zero"~suffix:sort==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":"rfl";
						zeros~="(Eq.trans (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) (Value.Refines.trans ("~prefix~".ValueCertificate.refinement ξ) (Numeric.sound ξ n"~to!string(out_.id)~" n"~to!string(zero.id)~" (of_decide_eq_true rfl)))) "~hzero~")";
					}
					matrixValues~=vector(vals); matrixRaw~=vector(raws); matrixTotal~=cases(totals); zeroProofs~=zeros;
					vectorValues~=val(s.vector[i]); vectorRaw~=raw(s.vector[i]); vectorTotal~=total(s.vector[i]);
				}
				// Keep each scalar-to-matrix bridge in its own declaration, so elaboration
				// does not repeatedly unfold all nine arithmetic expressions in the final proof.
				auto scalar="("~leanType(element)~" : Binding.Ty).denote";
				auto rawMatrix="("~vector(matrixRaw)~" : Fin 3 → Fin 3 → Option ("~scalar~"))",rawVector="("~vector(vectorRaw)~" : Fin 3 → Option ("~scalar~"))";
				foreach(i;0..3){
					string[] row;
					foreach(j;0..3){
						auto id="spectralCube"~tag~"_"~to!string(i*3+j);
						code~="theorem "~id~" (ξ : Env) : CubeZeroSpectra.step "~add~" "~mul~" "~rawMatrix~" (fun k => CubeZeroSpectra.step "~add~" "~mul~" "~rawMatrix~" (fun l => "~rawMatrix~" l "~to!string(j)~") k) "~to!string(i)~" = some 0 := "~zeroProofs[i*3+j]~"\n";
						row~="("~id~" ξ)";
					}
					cube~=cases(row);
				}
				string compactArgs; string[] compactProofs;
				foreach(part;0..2){
					string[] vals,proofs;
					foreach(i;0..3){
						auto index=9+part*3+i,f=s.checks[index],prefix="QSym.Spectral"~tag~"_1_"~to!string(index);
						vals~=raw(arena.castTo(f.value.output,sort));
						auto id="spectralCube"~tag~"_"~to!string(index),matrix=part?"(CubeZeroSpectra.square "~add~" "~mul~" "~rawMatrix~")":rawMatrix;
						code~="theorem "~id~" (ξ : Env) : CubeZeroSpectra.step "~add~" "~mul~" "~matrix~" "~rawVector~" "~to!string(i)~" = "~vals[$-1]~" := LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) ("~prefix~".ValueCertificate.refinement ξ)\n";
						proofs~="("~id~" ξ)";
					}
					compactArgs~=" "~vector(vals); compactProofs~=cases(proofs);
				}
				foreach(p;compactProofs) compactArgs~=" "~p;
				proof="CubeZeroSpectra.three_compact_value "~add~" "~mul~" "~ha~" "~hm~units~" "~vector(matrixValues)~" "~vector(vectorValues)~" "~vector(matrixRaw)~" "~vector(vectorRaw)~" "~cases(matrixTotal)~" "~cases(vectorTotal)~" "~cases(cube)~compactArgs~" "~mat~" "~vec~" "~hmat~" "~hv~" "~exponent;
			}else if(s.diagonal){
				string[] vals,vs,ars,vrs,da,dv,eqs,rows;
				foreach(j;0..s.size){ auto a=s.matrix[j*s.size+j],v=s.vector[j]; vals~=val(a); vs~=val(v); ars~=raw(a); vrs~=raw(v); da~=total(a); dv~=total(v); eqs~="rfl"; }
				foreach(j;0..s.size) rows~="(funext "~cases(eqs)~")";
				hmat="(Eq.trans "~hmat~" (congrArg some (funext "~cases(rows)~")))";
				proof="Spectral.diagonal_value "~add~" "~mul~" "~pow~" "~ha~" "~hm~" "~hp~units~" "~vector(vals)~" "~vector(vs)~" "~vector(ars)~" "~vector(vrs)~" "~cases(da)~" "~cases(dv)~" "~mat~" "~vec~" "~hmat~" "~hv~" "~exponent;
			}else{
				auto inv=sort==Sort.rational?"Functions.invQ.apply":"Value.inv",hi=sort==Sort.rational?"Spectral.invQ":"rfl";
				auto hn=sort==Sort.real_||sort==Sort.complex?"Spectral.minus"~suffix:sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"rfl";
				string check(uint j){
					auto f=s.checks[j],prefix="QSym.Spectral"~tag~"_1_"~to!string(j),out_=arena.castTo(f.value.output,sort),zero=arena.number(Number(0),sort);
					auto hz=sort==Sort.real_||sort==Sort.complex?"AffineRecurrence.zero"~suffix:sort==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":"rfl";
					return "(Spectral.checked_eq "~add~" "~mul~" "~ha~" "~hm~" "~raw(s.minus)~" _ _ "~hn~" (Eq.trans (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) (Value.Refines.trans ("~prefix~".ValueCertificate.refinement ξ) (Numeric.sound ξ n"~to!string(out_.id)~" n"~to!string(zero.id)~" (of_decide_eq_true rfl)))) "~hz~"))";
				}
				Term[] ps=[s.matrix[0],s.matrix[1],s.matrix[s.size],s.matrix[s.size+1],s.first];
				if(!s.repeated) ps~=s.second;
				ps~=[s.vector[0],s.vector[1]];
				if(s.size==3) ps~=[s.matrix[8],s.vector[2]];
				string args,raws,totals;
				foreach(t;ps){ args~=" "~val(t); raws~=" "~raw(t); totals~=" "~total(t); }
				string cast_,hc;
				if(s.repeated){
					cast_=" (fun n => Functions.castZQ.apply (Functions.castNZ.apply n))";
					if(sort==Sort.real_) cast_=" (fun n => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n)))";
					if(sort==Sort.complex) cast_=" (fun n => Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))))";
					hc=" RepeatedSpectra.cast"~suffix;
				}
				if(s.nilpotent){
					proof="NilpotentSpectra."~(s.size==2?"two_value":"block_value")~" "~add~" "~mul~" "~pow~" "~ha~" "~hm~" "~hp~units~args~raws~" "~raw(s.minus)~totals~" "~hn~" "~check(0)~" "~check(1)~" rfl "~mat~" "~vec~" "~hmat~" "~hv~" "~exponent;
				}else{
					proof=(s.repeated?"RepeatedSpectra.":"Spectral.")~(s.size==2?"two_value":"block_value")~" "~add~" "~mul~" "~inv~" "~pow~cast_~" "~ha~" "~hm~" "~hi~" "~hp~hc~units~args~raws~" "~raw(s.minus)~totals~" "~hn~" "~check(0)~" "~check(1)~" (QSym.Spectral"~tag~"_1_2.DomainCertificate.domain_correct ξ) "~mat~" "~vec~" "~hmat~" "~hv~" "~exponent;
				}
			}
			code~="theorem spectral"~tag~spectralArgs~" : "~name(s.source)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ := "~proof~"\n";
			if(s.cubeZero||s.zeroRoot) code~="attribute [local semireducible] Value.add Value.mul\n";
		}
		foreach(j,s;result.sums){
			auto n=nodes[s.source],sort=elementSort(types[n.type]),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":"C";
			auto add=tensorOperation(types[n.type],TensorOp.add),mul=tensorOperation(types[n.type],TensorOp.mul),ha=sort==Sort.rational?"AffineRecurrence.addQ":"rfl",hm=sort==Sort.rational?"AffineRecurrence.mulQ":"rfl";
			auto field="natural",env="({ ξ with natural := fun i => if i = "~to!string(s.variable)~" then x else ξ.natural i })";
			string known(uint id,string en){
				auto prefix="QSym.BindingScalar"~to!string(id),actual=arena.sort(result.domains[id].input);
				auto hz=actual==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":actual==Sort.real_?"AffineRecurrence.zeroR":"AffineRecurrence.zeroC";
				auto proof=(result.domains[id].polynomial||result.domains[id].rational)?"("~prefix~".zero "~en~")":"(Eq.trans (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct "~en~") ("~prefix~".ValueCertificate.refinement "~en~")) "~hz~")";
				return sort==Sort.rational&&actual==Sort.real_?"(Summation.rational_zero_of_real _ "~proof~")":proof;
			}
			auto initial=s.zero==uint.max?"":known(s.zero,"ξ"),step=known(s.step,env),minus="(n"~to!string(arena.number(Number(-1),sort).id)~".eval ξ)",hn=sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"Spectral.minus"~suffix;
			auto hs="(fun x => Spectral.checked_eq "~add~" "~mul~" "~ha~" "~hm~" "~minus~" _ _ "~hn~" "~step~")";
			auto f="(fun (x : ℕ) => "~name(nodes[n.a].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some x) ρ))",g="(fun (x : Option ℕ) => "~name(nodes[s.candidate].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) x ρ))";
			if(s.tail.length){
				auto pow="Functions.pow"~suffix~"N.apply",hp="Spectral.pow"~suffix;
				auto cast_="(fun n => Functions.castZQ.apply (Functions.castNZ.apply n))";
				if(sort==Sort.real_) cast_="(fun n => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n)))";
				if(sort==Sort.complex) cast_="(fun n => Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))))";
				string raw(Term t){ return "(n"~to!string(t.id)~".eval ξ)"; }
				string val(Term t){ return "("~raw(t)~".getD 0)"; }
				string total(Term t,uint k){ return "(Spectral.some_of_domain 0 "~raw(t)~" (QSym.BindingScalar"~to!string(k)~".DomainCertificate.domain_correct ξ))"; }
				string tree="Summation.Tail.nil",converges="True.intro",value="0";
				string rawTail=raw(arena.number(Number(0),sort)),ht=sort==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":"AffineRecurrence.zero"~suffix;
				foreach_reverse(k,p;s.tail){
					auto c=val(p.coefficient),q=val(p.ratio),degree=to!string(p.degree);
					tree="(Summation.Tail.cons "~c~" "~q~" "~degree~" "~tree~")";
					auto prefix="QSym.BindingScalar"~to!string(s.convergence[k]);
					converges="And.intro (Summation.norm_lt"~suffix~" "~raw(p.ratio)~" "~q~" "~raw(arena.real_(1))~" "~total(p.ratio,s.totals[2*k+1])~" AffineRecurrence.oneR (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) ("~prefix~".ValueCertificate.refinement ξ))) ("~converges~")";
					ht="(Summation.Tail.cons_value "~add~" "~mul~" "~pow~" "~cast_~" "~ha~" "~hm~" "~hp~" RepeatedSpectra.cast"~suffix~" "~raw(p.coefficient)~" "~raw(p.ratio)~" "~rawTail~" "~c~" "~q~" "~value~" "~total(p.coefficient,s.totals[2*k])~" "~total(p.ratio,s.totals[2*k+1])~" "~ht~" "~degree~" x)";
					value="("~c~" * (x : "~(sort==Sort.rational?"ℚ":sort==Sort.real_?"ℝ":"ℂ")~")^"~degree~" * "~q~"^x + "~value~")";
					rawTail="("~add~" ("~mul~" ("~mul~" "~raw(p.coefficient)~" ("~pow~" ("~cast_~" (some x)) (some "~degree~"))) ("~pow~" "~raw(p.ratio)~" (some x))) "~rawTail~")";
				}
				code~="theorem summation"~to!string(j)~dimDecl~" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctxName(n.context)~") : "~name(s.source)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ := Summation.tail_solution "~f~" "~g~" "~tree~" ("~converges~") (fun x => "~ht~") "~add~" "~mul~" "~(sort==Sort.rational?"Summation.addQ":"Summation.add")~" (Summation.mul_eq "~mul~" "~hm~") "~minus~" "~hn~" "~hs~"\n";
				continue;
			}
			auto proof="Summation.range_solution_partial "~f~" "~g~" "~add~" "~(sort==Sort.rational?"Summation.addQ":"Summation.add")~" "~initial~" "~hs~" ("~name(n.b)~".eval ξ ρ)";
			code~="theorem summation"~to!string(j)~dimDecl~" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctxName(n.context)~") : "~name(s.source)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ := "~proof~"\n";
		}
		string proofName(uint id){ return "(p"~to!string(id)~dimArg~" γ)"; }
		string realBody(uint fn){ return "(fun x : ℝ => "~name(nodes[fn].a)~
			".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))"; }
		string rowTotalProof(uint id){
			auto index=to!string(result.domains[id].variable);
			auto env="({ ξ with real := fun i => if i = "~index~" then x else ξ.real i })";
			return "(fun x : ℝ => (QSym.BindingScalar"~to!string(id)~".DomainCertificate.domain_correct "~env~").iff.mpr rfl)";
		}
		string densityProgram(uint[] bodies){
			string value="Distribution.DensityProgram.lebesgue";
			foreach(id;bodies) value="(Distribution.DensityProgram.weight (fun x : ℝ => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ)) "~value~")";
			return "("~value~")";
		}
		foreach(i,p;result.proofs){
			auto n=nodes[p.from]; string proof;
			string sumZeroProof(){ auto sort=elementSort(types[n.type]); return sort==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":sort==Sort.real_?"AffineRecurrence.zeroR":sort==Sort.complex?"AffineRecurrence.zeroC":"rfl"; }
			string sumRawZero(){ return "(n"~to!string(arena.number(Number(0),elementSort(types[n.type])).id)~".eval ξ)"; }
			final switch(p.rule){
				case BindingRule.sumMaskMerge:
					auto inner=nodes[n.b];
					proof=".ofEq (fun ξ ρ => (SummationAlgebra.mask_and ("~name(n.a)~".eval ξ ρ) ("~name(inner.a)~".eval ξ ρ) ("~name(inner.b)~".eval ξ ρ)).symm)";break;
				case BindingRule.sumMaskAnd:
					auto pred=nodes[n.a];
					proof=".ofEq (fun ξ ρ => SummationAlgebra.mask_and ("~name(pred.a)~".eval ξ ρ) ("~name(pred.b)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.rangeUndefinedBound:
					proof=".ofEq (fun ξ ρ => SummationLinearity.undefined_bound ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ) (QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct ξ))";break;
				case BindingRule.sumRationalSelector:
					auto add=nodes[n.a];
					proof=".ofEq (fun ξ ρ => SummationAffine.rational_selector ("~name(add.a)~".eval ξ ρ) ("~name(add.b)~".eval ξ ρ))";break;
				case BindingRule.sumIntegerBound:
					proof=".ofEq (fun ξ ρ => SummationAffine.integer_"~(arena.view(arena.at(n.data)).value==Builtin.ltZ?"lt":"le")~" ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumNaturalBound:
					proof=".ofEq (fun ξ ρ => SummationAffine.natural_"~(arena.view(arena.at(n.data)).value==Builtin.ltN?"lt":"le")~" ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumDistribute:
					auto sum=nodes[p.extra?n.b:n.a],other=p.extra?n.a:n.b,sort=elementSort(types[n.type]);
					auto suffix=sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":"";
					auto add=tensorOperation(types[n.type],TensorOp.add),mul=tensorOperation(types[n.type],TensorOp.mul);
					auto ha=suffix.length?"AffineRecurrence.add"~suffix:"rfl",hm=suffix.length?"AffineRecurrence.mul"~suffix:"rfl";
					proof=".ofEq (fun ξ ρ => SummationLinearity.distribute "~add~" "~mul~" "~ha~" "~hm~" ("~name(sum.a)~".eval ξ ρ) ("~name(sum.b)~".eval ξ ρ) ("~name(other)~".eval ξ ρ) "~(p.extra?"true":"false")~")";break;
				case BindingRule.sumAddLeft,BindingRule.sumAddRight:
					auto body=nodes[nodes[n.a].a],index=pool.view(type(at(n.a))).fields[0],sort=elementSort(types[n.type]);
					auto add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					string fn(uint id){return "(fun i => "~name(id)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") (some i) ρ))";}
					proof=".ofEq (fun ξ ρ => SummationLinearity.add_known"~(p.rule==BindingRule.sumAddRight?"_right":"")~" "~add~" "~ha~" "~fn(body.a)~" "~fn(body.b)~" (Option.some.inj ("~proofName(p.extra)~".sound ξ ρ)))";break;
				case BindingRule.sumRealExclude:
					auto add=nodes[nodes[n.a].a],sort=elementSort(types[n.type]);
					auto suffix=sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":"",ha=suffix.length?"AffineRecurrence.add"~suffix:"rfl";
					proof=".ofEq (fun ξ ρ => SummationAffine.real_ne_mask "~tensorOperation(types[n.type],TensorOp.add)~" "~ha~" ("~name(add.a)~".eval ξ ρ) ("~name(add.b)~".eval ξ ρ) (n"~to!string(arena.real_(-1).id)~".eval ξ) Spectral.minusR ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumRealEquality:
					auto add=nodes[nodes[n.a].a];
					proof=".ofEq (fun ξ ρ => SummationAffine.real_eq_offset ("~name(add.a)~".eval ξ ρ) ("~name(add.b)~".eval ξ ρ) (n"~to!string(arena.real_(-1).id)~".eval ξ) Spectral.minusR)";break;
				case BindingRule.sumScaleInteger:
					auto expression=p.extra?n.b:n.a,bound=p.extra?n.a:n.b,mul=nodes[nodes[nodes[expression].a].a];
					auto m=arena.number(arena.at(nodes[mul.a].data)).re;
					proof=".ofEq (fun ξ ρ => SummationAffine.scaleZ ("~name(mul.a)~".eval ξ ρ) ("~name(mul.b)~".eval ξ ρ) ("~name(bound)~".eval ξ ρ) "~to!string(m)~" (of_decide_eq_true rfl) rfl "~(arena.view(arena.at(n.data)).op==Op.le?"true":"false")~" "~(p.extra?"true":"false")~")";break;
				case BindingRule.sumAffineInteger,BindingRule.sumShiftInteger:
					auto expression=p.extra?n.b:n.a,bound=p.extra?n.a:n.b;
					auto add=nodes[nodes[nodes[expression].a].a],mul=nodes[add.a];
					auto neg="(n"~to!string(arena.real_(-1).id)~".eval ξ) Spectral.minusR ";
					auto flags=(arena.view(arena.at(n.data)).op==Op.le?"true":"false")~" "~(p.extra?"true":"false");
					if(p.rule==BindingRule.sumShiftInteger)
						proof=".ofEq (fun ξ ρ => SummationAffine.shiftZ ("~name(add.b)~".eval ξ ρ) ("~name(add.a)~".eval ξ ρ) ("~name(bound)~".eval ξ ρ) "~neg~flags~")";
					else{
						auto m=arena.number(arena.at(nodes[mul.a].data)).re;
						proof=".ofEq (fun ξ ρ => SummationAffine.affineZ ("~name(mul.a)~".eval ξ ρ) ("~name(add.b)~".eval ξ ρ) ("~name(mul.b)~".eval ξ ρ) ("~name(bound)~".eval ξ ρ) "~to!string(m)~" (of_decide_eq_true rfl) rfl "~neg~flags~")";
					}break;
				case BindingRule.sumAffineNatural:
					auto expr=p.extra?n.b:n.a,bound=p.extra?n.a:n.b;
					foreach(_;0..3)expr=nodes[expr].a;
					auto add=nodes[expr],mul=nodes[add.a],m=arena.number(arena.at(nodes[mul.a].data)).re.integer;
					proof=".ofEq (fun ξ ρ => SummationAffine.affineN ("~name(mul.a)~".eval ξ ρ) ("~name(add.b)~".eval ξ ρ) ("~name(mul.b)~".eval ξ ρ) ("~name(bound)~".eval ξ ρ) "~to!string(m)~" (of_decide_eq_true rfl) rfl (n"~to!string(arena.real_(-1).id)~".eval ξ) Spectral.minusR "~(arena.view(arena.at(n.data)).op==Op.le?"true":"false")~" "~(p.extra?"true":"false")~")";break;
				case BindingRule.sumMulSwap:
					proof=".ofEq (fun ξ ρ => SummationElementary.mul_swap ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumMulAssoc:
					auto right=nodes[n.b];
					proof=".ofEq (fun ξ ρ => SummationElementary.mul_assoc ("~name(n.a)~".eval ξ ρ) ("~name(right.a)~".eval ξ ρ) ("~name(right.b)~".eval ξ ρ))";break;
				case BindingRule.sumCastMul:
					auto child=nodes[n.a],suffix=["NZ","ZQ","QR","RC"][arena.view(arena.at(n.data)).value-Builtin.castNZ];
					proof=".ofEq (fun ξ ρ => SummationElementary.cast"~suffix~"_mul ("~name(child.a)~".eval ξ ρ) ("~name(child.b)~".eval ξ ρ))";break;
				case BindingRule.sumNaturalPowerMul:
					auto e=nodes[n.b],suffix=["N","Z","Q","R","C"][arena.view(arena.at(n.data)).value-Builtin.powNN];
					proof=".ofEq (fun ξ ρ => SummationElementary.pow"~suffix~"_mul"~(p.extra?"_rev":"")~" ("~name(n.a)~".eval ξ ρ) ("~name(p.extra?e.b:e.a)~".eval ξ ρ) ("~name(p.extra?e.a:e.b)~".eval ξ ρ))";break;
				case BindingRule.sumElementaryPower:
					auto op=arena.view(arena.at(n.data)).value,suffix=op==Builtin.expR?"expR":op==Builtin.expC?"expC":op==Builtin.cisR?"cis":"expi";
					auto target=nodes[p.to],ratio=nodes[target.a];
					proof=".ofEq (fun ξ ρ => SummationElementary."~suffix~(p.extra==0?"_index":p.extra==1?"_mul":"_mul_rev")~" "~(p.extra?"("~name(ratio.a)~".eval ξ ρ) ":"")~"("~name(target.b)~".eval ξ ρ))";break;
				case BindingRule.sumElementaryAdd:
					auto op=arena.view(arena.at(n.data)).value,suffix=op==Builtin.expR?"expR":op==Builtin.expC?"expC":op==Builtin.cisR?"cis":"expi",arg=nodes[n.a];
					proof=".ofEq (fun ξ ρ => SummationElementary."~suffix~"_add ("~name(arg.a)~".eval ξ ρ) ("~name(arg.b)~".eval ξ ρ))";break;
				case BindingRule.sumGeneralPower:
					auto target=nodes[p.to],suffix=elementSort(types[n.type])==Sort.real_?"R":"C";
					proof=".ofEq (fun ξ ρ => SummationElementary.power"~suffix~"_natural ("~name(n.a)~".eval ξ ρ) ("~name(target.b)~".eval ξ ρ))";break;
				case BindingRule.sumExp2:
					proof=".ofEq (fun ξ ρ => SummationElementary.exp2_exp ("~name(n.a)~".eval ξ ρ))";break;
				case BindingRule.sumTrigReal:
					proof=".ofEq (fun ξ ρ => SummationElementary."~(arena.view(arena.at(n.data)).value==Builtin.sinR?"sin_phase":"cos_phase")~" ("~name(n.a)~".eval ξ ρ))";break;
				case BindingRule.sumHyperbolic:
					auto op=arena.view(arena.at(n.data)).value,suffix=op==Builtin.sinhR?"sinhR":op==Builtin.coshR?"coshR":op==Builtin.sinhC?"sinhC":op==Builtin.coshC?"coshC":op==Builtin.sinC?"sinC":"cosC";
					proof=".ofEq (fun ξ ρ => SummationElementary."~suffix~"_exp ("~name(n.a)~".eval ξ ρ))";break;
				case BindingRule.rangeGuard:
					auto body=nodes[nodes[n.a].a];
					auto f="(fun (i : ℕ) => "~name(body.b)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))";
					proof=".ofEq (fun ξ ρ => SummationElementary.range_guard ("~name(p.extra)~".eval ξ ρ) "~f~" ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.rangeProjection:
					auto body=nodes[nodes[n.a].a],imaginary=arena.view(arena.at(body.data)).value==Builtin.imC;
					auto f="(fun (i : ℕ) => "~name(body.a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))";
					proof=".ofEq (fun ξ ρ => SummationElementary.range_"~(imaginary?"im":"re")~" "~f~" ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.rangeScale:
					auto sort=elementSort(types[n.type]),args=nodes[p.extra],fn=nodes[args.b].a;
					auto mul=tensorOperation(types[n.type],TensorOp.mul),hm=sort==Sort.natural?"AffineRecurrence.mulN":sort==Sort.integer?"AffineRecurrence.mulZ":sort==Sort.rational?"AffineRecurrence.mulQ":"rfl";
					auto reverse=arena.number(arena.at(nodes[nodes[nodes[args.b].b].a].data)).re.integer;
					auto f="(fun (i : ℕ) => "~name(nodes[fn].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))";
					proof=".ofEq (fun ξ ρ => SummationElementary.scale"~(reverse?"_rev":"")~" "~mul~" "~hm~" ("~name(args.a)~".eval ξ ρ) "~f~" ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.rangeConstant:
					auto sort=elementSort(types[n.type]),suffix=sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":sort==Sort.real_?"R":"C";
					proof=".ofEq (fun ξ ρ => SummationElementary.constant"~suffix~" ("~name(p.extra)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumPowerNatural:
					auto suffix=["Q","R","C"][arena.view(arena.at(n.data)).value-Builtin.powQZ];
					proof=".ofEq (fun ξ ρ => SummationPowers.natural"~suffix~" ("~name(n.a)~".eval ξ ρ) ("~name(nodes[n.b].a)~".eval ξ ρ))";break;
				case BindingRule.sumPowerNegative:
					auto suffix=["Q","R","C"][arena.view(arena.at(n.data)).value-Builtin.powQZ],exponent=nodes[n.b];
					auto offset=p.extra?exponent.b:exponent.a,product=nodes[p.extra?exponent.a:exponent.b],iv=nodes[product.b].a;
					auto m=-arena.number(arena.at(nodes[offset].data)).re.integer-1;
					proof=".ofEq (fun ξ ρ => SummationPowers.negative"~(p.extra?"Reverse":"")~suffix~" ("~name(n.a)~".eval ξ ρ) ("~name(iv)~".eval ξ ρ) "~to!string(m)~" ("~name(offset)~".eval ξ ρ) ("~name(product.a)~".eval ξ ρ) rfl rfl)";break;
				case BindingRule.sumPowerProduct:{
					enum ns="SummationElementary.PowerAt.";
					string suffix(TypeId ty){
						auto s=elementSort(ty);return s==Sort.natural?"N":s==Sort.integer?"Z":s==Sort.rational?"Q":s==Sort.real_?"R":"C";
					}
					string operations(string s){ return "Functions.pow"~s~"N.apply Spectral.pow"~s; }
					string powered(uint id){
						auto v=nodes[id],op=arena.view(arena.at(v.data)).value;
						if(op>=Builtin.castNZ&&op<=Builtin.castRC)
							return " ("~ns~"cast"~["NZ","ZQ","QR","RC"][op-Builtin.castNZ]~powered(v.a)~")";
						return " ("~ns~"source "~operations(suffix(types[v.type]))~" ("~name(v.a)~".eval ξ ρ) ("~name(v.b)~".eval ξ ρ))";
					}
					auto s=suffix(types[n.type]),mul=tensorOperation(types[n.type],TensorOp.mul);
					auto hm=s=="R"||s=="C"?"rfl":"AffineRecurrence.mul"~s;
					proof=".ofEq (fun ξ ρ => "~ns~"product "~mul~" "~hm~" "~operations(s)~powered(n.a)~powered(n.b)~")";break;
				}
				case BindingRule.sumMissingGuard:{
					auto body=nodes[nodes[n.a].a],witness=nodes[p.extra],index=type(at(witness.a));
					// Tuples store the remaining fields in their right child.
					auto predicate=nodes[nodes[witness.b].a];
					auto k=to!string(arena.number(arena.at(nodes[witness.a].data)).re.numerator);
					auto ty=index==scalarType(Sort.natural)?"ℕ":"ℤ";
					string fn(uint id){return "(fun i : "~ty~" => "~name(id)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") (some i) ρ))";}
					auto args=fn(body.a)~" "~fn(body.b)~" ("~k~" : "~ty~") (Numeric.calculate_sound ξ n"~to!string(predicate.data)~" false rfl)";
					if(n.op==BoundOp.summation){
						auto weight=elementSort(types[n.type])==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
						proof=".ofEq (fun ξ ρ => SummationLinearity.missing_guard "~weight~" "~args~")";
					}else{
						auto size=to!string(arena.number(arena.at(nodes[n.b].data)).re.numerator);
						proof=".ofEq (fun ξ ρ => SummationLinearity.range_missing_guard "~args~" "~size~" (of_decide_eq_true rfl) (Numeric.calculate_sound ξ n"~
							to!string(nodes[n.b].data)~" "~size~" rfl))";
					}
					break;
				}
				case BindingRule.sumMissingConstant:
					auto idx=pool.view(types[nodes[n.a].type]).fields[0]==scalarType(Sort.natural)?"ℕ":"ℤ";
					auto weight=elementSort(types[n.type])==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					proof=".ofEq (fun _ _ => Summation.undefined_term "~weight~" (fun _ : "~idx~" => none) 0 rfl)";break;
				case BindingRule.mulBottom:
					auto sort=elementSort(types[n.type]),mul=tensorOperation(types[n.type],TensorOp.mul);
					auto hm=sort==Sort.natural?"AffineRecurrence.mulN":sort==Sort.integer?"AffineRecurrence.mulZ":sort==Sort.rational?"AffineRecurrence.mulQ":"rfl";
					auto left=nodes[n.a].op==BoundOp.bottom;
					proof=".ofEq (fun ξ ρ => SummationLinearity.mul_missing "~mul~" "~hm~" "~(left?"true":"false")~" ("~name(left?n.b:n.a)~".eval ξ ρ))";break;
				case BindingRule.addBottom:
					auto sort=elementSort(types[n.type]),add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					auto left=nodes[n.a].op==BoundOp.bottom;
					proof=".ofEq (fun ξ ρ => SummationMasks.add_none_"~(left?"left":"right")~" "~add~" "~ha~" ("~name(left?n.b:n.a)~".eval ξ ρ))";break;
				case BindingRule.sumExcludeZero:
					auto body=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm",hw=sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero";
					auto f="(fun (i : Option ℕ) => "~name(body.b)~".eval ξ (Binding.Env.cons (a := .scalar .natural) i ρ))";
					proof=".ofEq (fun ξ ρ => SummationMasks.exclude_zero "~w~" "~hw~" "~f~")";break;
				case BindingRule.sumExcludeOffset:
					auto body=nodes[nodes[n.a].a],sort=elementSort(types[n.type]);
					auto add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					auto f="(fun (i : Option ℕ) => "~name(body.b)~".eval ξ (Binding.Env.cons (a := .scalar .natural) i ρ))";
					proof=".ofEq (fun ξ ρ => SummationPrefix.exclude_offset norm "~add~" "~ha~" "~f~" ("~name(p.extra)~".eval ξ ρ))";break;
				case BindingRule.sumCastMask,BindingRule.sumCastAdd:
					auto child=nodes[n.a],suffix=["NZ","ZQ","QR","RC"][arena.view(arena.at(n.data)).value-Builtin.castNZ];
					proof=".ofEq (fun ξ ρ => SummationMasks.cast"~suffix~(p.rule==BindingRule.sumCastMask?"_mask":"_add")~" ("~name(child.a)~".eval ξ ρ) ("~name(child.b)~".eval ξ ρ))";break;
				case BindingRule.sumBoundedAdd:
					auto body=nodes[nodes[n.a].a],bounds=nodes[p.extra],sort=elementSort(types[n.type]);
					auto add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					auto w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm",hw=sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero";
					string fn(uint id){return "(fun (i : ℕ) => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))";}
					auto flags=arena.number(arena.at(nodes[nodes[nodes[bounds.b].b].a].data)).re.integer;
					proof=".ofEq (fun ξ ρ => SummationMasks.bounded_add "~w~" "~hw~" "~add~" "~ha~" "~fn(nodes[body.a].b)~" "~fn(nodes[body.b].b)~" ("~name(bounds.a)~".eval ξ ρ) ("~name(nodes[bounds.b].a)~".eval ξ ρ) "~(flags&1?"true":"false")~" "~(flags&2?"true":"false")~")";break;
				case BindingRule.sumDeltaZero:
					auto body=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),index=pool.view(type(at(n.a))).fields[0],ns=index==scalarType(Sort.natural);
					auto w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm",hw=sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero";
					auto f="(fun (i : "~(ns?"ℕ":"ℤ")~") => "~name(body.b)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") (some i) ρ))";
					proof=".ofEq (fun ξ ρ => SummationMasks.delta"~(ns?(p.extra==1?"N_nonzeroN":"N_zero"):"Z_zero")~" "~w~" "~hw~" "~f~")";break;
				case BindingRule.rangeAdd:
					auto body=nodes[nodes[n.a].a],sort=elementSort(types[n.type]);
					auto add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					string fn(uint id){return "(fun (i : ℕ) => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))";}
					proof=".ofEq (fun ξ ρ => SummationAlgebra.range_add "~add~" "~ha~" "~fn(body.a)~" "~fn(body.b)~" ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.rangeMaskLt,BindingRule.rangeMaskGe:
					auto body=nodes[nodes[n.a].a],ge=p.rule==BindingRule.rangeMaskGe;
					auto f="(fun (i : "~(ge?"Option ℕ":"ℕ")~") => "~name(body.b)~".eval ξ (Binding.Env.cons (a := .scalar .natural) "~(ge?"i":"(some i)")~" ρ))";
					proof=".ofEq (fun ξ ρ => SummationAlgebra.range_mask_"~(ge?"ge":"lt")~" "~f~" ("~name(n.b)~".eval ξ ρ) ("~name(p.extra)~".eval ξ ρ))";break;
				case BindingRule.sumMaskEqOffset,BindingRule.sumMaskNeOffset:
					auto equal=p.rule==BindingRule.sumMaskEqOffset,sort=elementSort(types[n.type]);
					auto iv=variable(context(at(n.a)),0),add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					proof=".ofEq (fun ξ ρ => SummationAlgebra.mask_"~(equal?"eq_offset":"ne_offset_op "~add~" "~ha)~" ("~name(iv.id)~".eval ξ ρ) ("~name(p.extra)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumTail,BindingRule.sumTailInclusive:
					auto body=nodes[nodes[n.a].a],pred=nodes[body.a],index=pool.view(type(at(n.a))).fields[0],sort=elementSort(types[n.type]);
					auto ns=index==scalarType(Sort.natural),lower=arena.view(arena.at(pred.data)).value==(ns?Builtin.leN:Builtin.leZ);
					auto w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : Option "~(ns?"ℕ":"ℤ")~") => "~name(body.b)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") i ρ))";
					proof=".ofEq (fun ξ ρ => SummationTails."~(p.rule==BindingRule.sumTailInclusive?"upperZLe":ns?"lowerN":lower?"lowerZ":"upperZ")~" "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(p.extra)~".eval ξ ρ))";break;
				case BindingRule.sumRationalBound:
					proof=".ofEq (fun ξ ρ => SummationBounds.rational_"~(arena.view(arena.at(n.data)).value==Builtin.ltQ?"lt":"le")~" ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumRound:
					auto reverse=(p.extra&2)!=0,natural=(p.extra&4)==0,index=reverse?n.b:n.a,bound=reverse?n.a:n.b;
					index=nodes[nodes[index].a].a; if(natural) index=nodes[index].a;
					auto suffix=["lt","le","gt","ge"][p.extra&3];
					proof=".ofEq (fun ξ ρ => SummationBounds.round"~(natural?"N":"Z")~"_"~suffix~" ("~name(index)~".eval ξ ρ) ("~name(bound)~".eval ξ ρ))"; break;
				case BindingRule.rangeSolution:proof=".ofEq (summation"~to!string(p.extra)~dimArg~" γ)"; break;
				case BindingRule.rangeRootsUnity:
					proof=".ofEq (fun ξ ρ => SummationRoots.range_value ("~name(n.b)~".eval ξ ρ) "~(p.extra&4?"true":"false")~" "~(p.extra&2?"true":"false")~" ⟨"~to!string(p.extra/8)~", of_decide_eq_true rfl⟩ "~(p.extra&1?"true":"false")~")";break;
				case BindingRule.rangeGeometric:
					auto sort=elementSort(types[n.type]),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":"C",leaf=types[n.type];
					auto add=tensorOperation(leaf,TensorOp.add),mul=tensorOperation(leaf,TensorOp.mul),inv=sort==Sort.rational?"Functions.invQ.apply":"Value.inv";
					auto ha=sort==Sort.rational?"AffineRecurrence.addQ":"rfl",hm=sort==Sort.rational?"AffineRecurrence.mulQ":"rfl",hi=sort==Sort.rational?"Spectral.invQ":"rfl";
					auto cast_="(fun n => Functions.castZQ.apply (Functions.castNZ.apply n))";
					if(sort==Sort.real_) cast_="(fun n => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n)))";
					if(sort==Sort.complex) cast_="(fun n => Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))))";
					auto minus="(n"~to!string(arena.number(Number(-1),sort).id)~".eval ξ)",hn=sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"Spectral.minus"~suffix;
					proof=".ofEq (fun ξ ρ => Summation.range_geometric_value "~add~" "~mul~" "~inv~" Functions.pow"~suffix~"N.apply "~cast_~" "~(sort==Sort.rational?"Functions.nonzeroQ.apply Summation.nonzeroQ":"Value.nonzero rfl")~" "~ha~" "~hm~" "~hi~" Spectral.pow"~suffix~" RepeatedSpectra.cast"~suffix~" "~sumRawZero()~" "~minus~" "~sumZeroProof()~" "~hn~" ("~name(p.extra)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.sumConstant:
					auto sort=elementSort(types[n.type]),index=pool.view(type(at(n.a))).fields[0];
					auto suffix=sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":"_norm";
					proof=".ofEq (fun ξ ρ => Summation.constant"~suffix~" (ι := "~(index==scalarType(Sort.natural)?"ℕ":"ℤ")~") ("~name(p.extra)~".eval ξ ρ) "~sumRawZero()~" "~sumZeroProof()~")"; break;
				case BindingRule.sumBounds:
					auto bounds=nodes[p.extra],sourceBody=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),index=pool.view(type(at(n.a))).fields[0];
					auto ns=index==scalarType(Sort.natural),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : "~(ns?"ℕ":"ℤ")~") => "~name(sourceBody.b)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") (some i) ρ))";
					auto flags=arena.number(arena.at(nodes[nodes[nodes[bounds.b].b].a].data)).re.integer;
					proof=".ofEq (fun ξ ρ => Summation.bounds"~(ns?"N":"Z")~" "~w~" "~f~" ("~name(bounds.a)~".eval ξ ρ) ("~name(nodes[bounds.b].a)~".eval ξ ρ) "~(flags&1?"true":"false")~" "~(flags&2?"true":"false")~")"; break;
				case BindingRule.sumShiftGeometric:
					auto args=nodes[p.extra],sort=elementSort(types[n.type]),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":"C";
					auto mul=sort==Sort.rational?"Functions.mulQ.apply":"Value.mul",hm=sort==Sort.rational?"AffineRecurrence.mulQ":"rfl";
					string raw(Term t){ return "(n"~to!string(t.id)~".eval ξ)"; }
					auto one=raw(arena.number(Number(1),sort)),minus=raw(arena.number(Number(-1),sort)),rOne=raw(arena.real_(1));
					auto ho=sort==Sort.rational?"(congrArg some (div_one (1 : ℚ)))":"AffineRecurrence.one"~suffix,hn=sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"Spectral.minus"~suffix;
					auto q="("~name(args.a)~".eval ξ ρ)",h="(Summation.geometric"~suffix~"_literals "~q~" "~one~" "~minus~(sort==Sort.real_?"":" "~rOne)~" "~ho~" "~hn~(sort==Sort.real_?"":" AffineRecurrence.oneR")~")";
					proof=".ofEq (fun ξ ρ => Summation.geometric_shift_guard Functions.pow"~suffix~"N.apply Spectral.pow"~suffix~" "~mul~" "~hm~" "~q~" ("~name(nodes[args.b].a)~".eval ξ ρ) _ _ "~h~")"; break;
				case BindingRule.sumTailNatural,BindingRule.sumTailStrict:
					auto sourceBody=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : Option ℕ) => "~name(sourceBody.b)~".eval ξ (Binding.Env.cons (a := .scalar .natural) i ρ))";
					proof=".ofEq (fun ξ ρ => Summation.tailN_value "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(p.extra)~".eval ξ ρ) "~(p.rule==BindingRule.sumTailStrict?"true":"false")~")"; break;
				case BindingRule.sumInterval:
					auto bounds=nodes[p.extra],sourceBody=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),index=pool.view(type(at(n.a))).fields[0];
					auto ns=index==scalarType(Sort.natural),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : Option "~(ns?"ℕ":"ℤ")~") => "~name(sourceBody.b)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") i ρ))";
					proof=".ofEq (fun ξ ρ => Summation.interval_convert"~(ns?"N":"Z")~" "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(bounds.a)~".eval ξ ρ) ("~name(nodes[bounds.b].a)~".eval ξ ρ))"; break;
				case BindingRule.sumRealIndex:{
					auto resultApp=nodes[nodes[p.to].b],query=nodes[resultApp.b].a;
					auto index=pool.view(type(at(n.a))).fields[0],sort=elementSort(types[n.type]);
					bool natural=index==scalarType(Sort.natural);
					auto f="(fun i : "~(natural?"ℕ":"ℤ")~" => "~name(nodes[resultApp.a].a)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") (some i) ρ))";
					proof=".ofEq (fun ξ ρ => Summation.select_real_"~(natural?"N":"Z")~
						(sort==Sort.natural?" (fun n : ℕ => (n : ℝ)) Summation.nat_weight_zero ":" norm norm_zero ")~
						(p.extra?"true ":"false ")~f~" ("~name(query)~".eval ξ ρ))"; break;
				}
				case BindingRule.sumDelta,BindingRule.sumDeltaOffset:
					auto out_=nodes[p.to],sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm",index=pool.view(type(at(n.a))).fields[0];
					auto f="(fun (i : "~(index==scalarType(Sort.natural)?"ℕ":"ℤ")~") => "~name(nodes[out_.a].a)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") (some i) ρ))";
					proof=".ofEq (fun ξ ρ => Summation.delta"~(p.rule==BindingRule.sumDeltaOffset?"Z_offset":index==scalarType(Sort.natural)?"N":"Z")~" "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(p.rule==BindingRule.sumDeltaOffset?p.extra:out_.b)~".eval ξ ρ))"; break;
				case BindingRule.sumGeometric:
					auto sort=elementSort(types[n.type]),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":"C";
					string raw(Term t){ return "(n"~to!string(t.id)~".eval ξ)"; }
					auto one=raw(arena.number(Number(1),sort)),minus=raw(arena.number(Number(-1),sort)),rOne=raw(arena.real_(1));
					auto ho=sort==Sort.rational?"(congrArg some (div_one (1 : ℚ)))":"AffineRecurrence.one"~suffix;
					auto hm=sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"Spectral.minus"~suffix;
					proof=".ofEq (fun ξ ρ => Summation.geometric"~suffix~"_literals ("~name(p.extra)~".eval ξ ρ) "~one~" "~minus~(sort==Sort.real_?"":" "~rOne)~" "~ho~" "~hm~(sort==Sort.real_?"":" AffineRecurrence.oneR")~")"; break;
				case BindingRule.sumZero:
					auto sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					proof=".ofEq (fun ξ ρ => Summation.zero_literal "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~sumRawZero()~" "~sumZeroProof()~")"; break;
				case BindingRule.sumRange,BindingRule.sumRangeLe:
					auto out_=nodes[p.to],sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : ℕ) => "~name(nodes[out_.a].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))";
					proof=".ofEq (fun ξ ρ => Summation."~(p.rule==BindingRule.sumRangeLe?"range_convert_le":"range_convert")~" "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(p.rule==BindingRule.sumRangeLe?p.extra:out_.b)~".eval ξ ρ))"; break;
				case BindingRule.rangeZero:proof=".ofEq (fun ξ ρ => Summation.range_zero_literal ("~name(n.a)~".eval ξ ρ) rfl "~sumRawZero()~" "~sumZeroProof()~")"; break;
				case BindingRule.rangeStep:
					auto count=arena.number(arena.at(nodes[n.b].data)).re.integer;
					auto f="(fun (i : ℕ) => "~name(nodes[n.a].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))",sort=elementSort(types[n.type]);
					auto op=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					proof=".ofEq (fun ξ ρ => Summation.range_step "~f~" "~to!string(count-1)~" "~op~" "~ha~")"; break;
				case BindingRule.rangeLift:
					proof=".ofEq (fun ξ ρ => Summation.range_"~(elementSort(types[n.type])==Sort.natural?"nat":"int")~"_lift ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.getScalarUndefined:
					proof="Tensor.getScalarUndefined "~name(n.a)~" n"~to!string(nodes[n.b].data)~" QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct"; break;
				case BindingRule.getBottom:
					auto left=nodes[n.a].op==BoundOp.bottom;
					proof=".ofEq (fun ξ ρ => Tensor.get_none_"~(left?"left":"right")~" ("~name(left?n.b:n.a)~".eval ξ ρ))"; break;
				case BindingRule.getCons:
					auto index=arena.number(arena.at(nodes[n.b].data)).re.integer,cons=nodes[n.a];
					proof=".ofEq (fun ξ ρ => Tensor.get_cons_"~(index?"succ":"zero")~" ("~name(cons.a)~".eval ξ ρ) ("~name(cons.b)~".eval ξ ρ)"~(index?" "~to!string(index-1):"")~")"; break;
				case BindingRule.tensorSpectrumCast:
					auto source=nodes[p.from],power=nodes[source.a],lifted=nodes[p.extra],liftedPower=nodes[lifted.a];
					auto from=elementSort(typeLeaf(type(at(p.from)))),targetSort=elementSort(typeLeaf(type(at(p.extra)))),size=pool.view(type(at(p.from))).length;
					auto tag=(from==Sort.natural?"N":"Z")~(targetSort==Sort.real_?"R":"C"),hom="("~(from==Sort.natural?"Nat":"Int")~".castRingHom "~(targetSort==Sort.real_?"ℝ":"ℂ")~")";
					string raw(uint id){ return "("~name(id)~".eval ξ ρ)"; }
					string mapped(uint original,uint converted,uint depth){
						if(!depth) return "(IntegerSpectra.cast"~tag~" "~raw(original)~")";
						auto a=nodes[original],b=nodes[converted],f=depth==1?hom:"(fun v : Fin "~to!string(size)~" → _ => fun i => "~hom~" (v i))";
						if(a.op==BoundOp.vectorNil) return "(IntegerSpectra.map_nil "~f~")";
						return "(IntegerSpectra.map_cons "~f~" "~raw(a.a)~" "~raw(a.b)~" "~raw(b.a)~" "~raw(b.b)~" "~mapped(a.a,b.a,depth-1)~" "~mapped(a.b,b.b,depth)~")";
					}
					auto element=scalarType(targetSort),field=targetSort==Sort.real_?"R":"C";
					auto units=" "~tensorLiteral(element,0)~" "~tensorLiteral(element,1)~" (Option.some.inj AffineRecurrence.zero"~field~") (Option.some.inj AffineRecurrence.one"~field~")";
					proof=".ofEq (fun ξ ρ => IntegerSpectra.lift"~tag~" "~to!string(size-1)~units~" "~raw(power.a)~" "~raw(source.b)~" "~raw(power.b)~" "~raw(liftedPower.a)~" "~raw(lifted.b)~" "~mapped(power.a,liftedPower.a,2)~" "~mapped(source.b,lifted.b,1)~")"; break;
				case BindingRule.tensorSpectral:proof=".ofEq (fun ξ ρ => spectral"~to!string(p.extra)~dimArg~" γ ξ ρ)"; break;
				case BindingRule.tensorEval:proof=tensorEvaluationProof(p.from,p.to); break;
				case BindingRule.tensorPower:
					auto v=pool.view(types[n.type]),element=typeLeaf(types[n.type]),exponent=arena.number(arena.at(nodes[n.b].data)).re.integer;
					proof=".ofEq (fun ξ ρ => Tensor.matrixPowerValue_succ "~tensorOperation(element,TensorOp.add)~" "~tensorOperation(element,TensorOp.mul)~" "~tensorLiteral(element,0)~" "~tensorLiteral(element,1)~" "~v.dimension.lean~" ("~name(n.a)~".eval ξ ρ) "~to!string(exponent-1)~")"; break;
				case BindingRule.tensorDomain:
					auto child=nodes[n.a];
					proof=".ofEq (fun ξ ρ => TensorDomains.Binary.defined "~tensorDomainProof(child)~" ("~name(child.a)~".eval ξ ρ) ("~name(child.b)~".eval ξ ρ))"; break;
				case BindingRule.getDomain:
					auto child=nodes[n.a],index=arena.number(arena.at(nodes[child.b].data)).re.integer;
					proof=".ofEq (fun ξ ρ => TensorDomains.get "~to!string(pool.view(type(at(child.a))).length)~" "~to!string(index)~" (of_decide_eq_true rfl) ("~name(child.a)~".eval ξ ρ))"; break;
				case BindingRule.tensorDefined:
					auto child=nodes[n.a];
					proof=".ofEq (fun ξ ρ => Tensor."~(child.op==BoundOp.pair?"defined_pair":"defined_cons")~" ("~name(child.a)~".eval ξ ρ) ("~name(child.b)~".eval ξ ρ))"; break;
				case BindingRule.fixedRecurrence:proof=".ofEq (fun ξ ρ => solve"~to!string(p.from)~dimArg~" γ ξ ρ)"; break;
				case BindingRule.domainFixedTotal:proof=".ofEq (fun ξ ρ => "~(result.ranks[p.extra].iterations.length||result.ranks[p.extra].lower.output!=Term.init?"domainTotal"~to!string(p.extra)~dimArg~" γ ξ ρ":"Eq.trans (domainTotal"~to!string(p.extra)~dimArg~" γ ξ ρ) (congrArg some (Set.ext (fun _ => iff_of_true True.intro rfl)))")~")"; break;
				case BindingRule.refl:proof=".refl "~name(p.from); break;
				case BindingRule.conditionalTrue:proof=".conditionalTrue "~name(n.b)~" "~name(n.c); break;
				case BindingRule.conditionalFalse:proof=".conditionalFalse "~name(n.b)~" "~name(n.c); break;
				case BindingRule.conditionalBottom:proof=".conditionalBottom "~name(n.b)~" "~name(n.c); break;
				case BindingRule.conditionalUndefined:
					proof=".ofEq (fun ξ ρ => Binding.conditional_undefined ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ) ("~name(n.c)~
						".eval ξ ρ) (QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct ξ))"; break;
				case BindingRule.conditionalSame:proof=".conditionalSame "~name(n.a)~" "~name(n.b); break;
				case BindingRule.conditionalBool:proof=".conditionalBool "~name(n.a)~" "~name(n.b)~" "~name(n.c); break;
				case BindingRule.closedRationalValue:{
					auto literal=arena.at(nodes[p.to].data),q=SourceCertificates.q(arena.number(literal).re);
					auto exact="(Numeric.calculate_sound ξ n"~to!string(p.extra)~" "~q~" rfl)";
					auto literalProof="(Numeric.calculate_sound ξ n"~to!string(literal.id)~" "~q~" rfl)";
					proof=".ofEq (fun ξ _ => "~exact~".trans "~literalProof~".symm)"; break;
				}
				case BindingRule.conditionalNumeric:
					auto sort=elementSort(types[n.type]);
					auto add=sort==Sort.natural?"Functions.addN.apply":sort==Sort.integer?"Functions.addZ.apply":sort==Sort.rational?"Functions.addQ.apply":"Value.add";
					auto h=sort==Sort.natural?"AffineRecurrence.addN":sort==Sort.integer?"AffineRecurrence.addZ":sort==Sort.rational?"AffineRecurrence.addQ":"rfl";
					proof=".ofEq (fun ξ ρ => Binding.conditional_numeric "~add~" "~h~" ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ) ("~name(n.c)~".eval ξ ρ))"; break;
				case BindingRule.conditionalMap,BindingRule.conditionalLeft,BindingRule.conditionalRight:
					auto right=p.rule==BindingRule.conditionalRight,q=nodes[right?n.b:n.a];
					string operation;
					if(n.op==BoundOp.apply||n.op==BoundOp.sequence){
						operation="(fun (f : Option ("~leanType(types[nodes[n.a].type])~" : Binding.Ty).denote) (x : Option ("~leanType(types[nodes[n.b].type])~" : Binding.Ty).denote) => f.bind (fun g => "~(n.op==BoundOp.apply?"x.bind g":"x")~"))";
					}else operation=valueOperation(n);
					auto strict="rfl";
					if(n.b!=uint.max){
						auto other="("~name(right?n.a:n.b)~".eval ξ ρ)";
						auto binary=operation;
						operation=right?"(fun v => "~operation~" "~other~" v)":"(fun v => "~operation~" v "~other~")";
						// Case splitting also covers operations represented by a strict
						// two-argument match, rather than nested Option.bind calls.
						strict=n.op==BoundOp.tensor?"("~tensorDomainProof(n)~(right?".right ":".left ")~other~")":"(Option.rec (motive := fun other => "~binary~(right?" other none":" none other")~" = none) rfl (fun _ => rfl) "~other~")";
					}
					proof=".ofEq (fun ξ ρ => Binding.conditional_map "~operation~" "~strict~" ("~name(q.a)~".eval ξ ρ) ("~name(q.b)~".eval ξ ρ) ("~name(q.c)~".eval ξ ρ))"; break;
				case BindingRule.conditionalDefined:
					auto q=nodes[n.a]; proof=".definedConditional "~name(q.a)~" "~name(q.b)~" "~name(q.c); break;
				case BindingRule.trans:proof=".trans "~proofName(p.left)~" "~proofName(p.right); break;
				case BindingRule.beta:proof=".beta "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.seqScalar:proof=".seqScalar n"~to!string(nodes[n.a].data)~" "~name(n.b)~" (fun _ => ⟨_, rfl⟩)"; break;
				case BindingRule.seqLam:proof=".seqLam "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.seqSelf:proof=".seqSelf "~name(n.a); break;
				case BindingRule.shortCircuit:
					if(n.op==BoundOp.primitive&&nodes[n.a].op==BoundOp.scalar&&arena.view(arena.at(n.data)).op==Op.mask&&!arena.view(arena.at(nodes[n.a].data)).value){
						auto sort=arena.sort(arena.at(n.data)),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":sort==Sort.complex?"C":"";
						if(suffix.length){ proof=".maskFalse"~suffix~" "~name(n.b); break; }
					}
					goto case BindingRule.fold;
				case BindingRule.fold,BindingRule.seqTotal:proof=".ofEq (fun _ _ => rfl)"; break;
				case BindingRule.domainBottom:proof=".domainBottom"; break;
				case BindingRule.appBottom:proof=".appBottom "~name(n.a); break;
				case BindingRule.appScalarUndefined:
					proof=".appScalarUndefined "~name(n.a)~" n"~to!string(nodes[n.b].data)~" QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct"; break;
				case BindingRule.definedFixed:proof=".ofEq (fun ξ ρ => congrArg Binding.definedValue (fixed"~to!string(n.a)~dimArg~" γ ξ ρ))"; break;
				case BindingRule.fixedApp:
					proof=".ofEq (fun ξ ρ => Binding.Expr.eval_unroll_app "~name(n.a)~" "~name(nodes[nodes[n.a].a].a)~" "~name(n.b)~
						" ξ ρ (fixed"~to!string(n.a)~dimArg~" γ ξ ρ) (unroll"~to!string(n.a)~dimArg~" γ ξ ρ))"; break;
				case BindingRule.fixedConstant:
					proof=".ofEq (fun ξ ρ => Recursion.fixed_constant (fun x => "~name(nodes[p.to].a)~".eval ξ (ρ.cons (some x))))"; break;
				case BindingRule.fixedIdentity:proof=".ofEq (fun _ _ => Recursion.fixed_identity)"; break;
				case BindingRule.seqGuard:proof=".seqGuard "~name(n.a)~" "~name(n.b); break;
				case BindingRule.domainLam:proof=".domainLam "~name(nodes[n.a].a); break;
				case BindingRule.memberDomain:proof=".memberDomain "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.memberSet:proof=".memberSet "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.guardTrue:proof=".guardTrue "~name(n.b); break;
				case BindingRule.guardAnd:proof=".guardAnd "~name(n.a)~" "~name(nodes[n.b].a)~" "~name(nodes[n.b].b); break;
				case BindingRule.guardLeft,BindingRule.guardRight:
					auto left=p.rule==BindingRule.guardLeft,g=nodes[left?n.a:n.b];
					proof=".ofEq (fun ξ ρ => Tensor.guard_"~(n.op==BoundOp.pair?"pair":n.op==BoundOp.get?"get":"cons")~(left?"_left":"_right")~
						" ("~name(g.a)~".eval ξ ρ) ("~name(left?g.b:n.a)~".eval ξ ρ) ("~name(left?n.b:g.b)~".eval ξ ρ))"; break;
				case BindingRule.guardMap:
					auto g=nodes[n.a];
					proof=".ofEq (fun ξ ρ => Tensor.guard_map "~(n.op==BoundOp.first?"Prod.fst":"Prod.snd")~" ("~name(g.a)~".eval ξ ρ) ("~name(g.b)~".eval ξ ρ))"; break;
				case BindingRule.holdsGuard:proof=".holdsGuard "~name(nodes[n.a].a)~" "~name(nodes[n.a].b); break;
				case BindingRule.setHolds:proof=".setHolds "~name(n.a); break;
				case BindingRule.typeEqSelf:proof=".typeEqSelf "~name(n.a); break;
				case BindingRule.equalSelf:proof=".equalSelf "~name(n.a); break;
				case BindingRule.equalBottomLeft:proof=".equalBottomLeft "~name(n.b); break;
				case BindingRule.equalBottomRight:proof=".equalBottomRight "~name(n.a); break;
				case BindingRule.definedEqual:proof=".definedEqual "~name(nodes[n.a].a)~" "~name(nodes[n.a].b); break;
				case BindingRule.typeEqValues:proof=".ofEq (fun _ _ => rfl)"; break;
				case BindingRule.definedGuardFalse:proof=".definedGuardFalse "~name(nodes[n.a].b); break;
				case BindingRule.definedTotal:proof=".ofEq (fun _ _ => rfl)"; break;
				case BindingRule.subsetRefl:proof=".subsetRefl "~name(n.a); break;
				case BindingRule.subsetEmpty:proof=".subsetEmpty "~name(n.b); break;
				case BindingRule.subsetUniv:proof=".subsetUniv "~name(n.a); break;
				case BindingRule.subsetUnivEmpty,BindingRule.equalUnivEmpty,BindingRule.equalEmptyUniv:
					auto ty=pool.view(types[nodes[n.a].type]).fields[0],witness=leanWitness(ty);
					auto op=p.rule==BindingRule.subsetUnivEmpty?"subsetUnivEmpty":p.rule==BindingRule.equalUnivEmpty?"equalUnivEmpty":"equalEmptyUniv";
					proof="."~op~" (a := "~leanType(ty)~") "~witness; break;
				case BindingRule.definedMember,BindingRule.definedSubset,BindingRule.definedGuard,BindingRule.definedApp:
					auto op=p.rule==BindingRule.definedMember?"definedMember":p.rule==BindingRule.definedSubset?"definedSubset":p.rule==BindingRule.definedGuard?"definedGuard":"definedApp";
					proof="."~op~" "~name(nodes[n.a].a)~" "~name(nodes[n.a].b); break;
				case BindingRule.definedNot:proof=".definedNot "~name(nodes[n.a].a); break;
				case BindingRule.domainGuardFalse:proof=".domainGuardFalse "~name(nodes[n.a].b); break;
				case BindingRule.pointwise:
					auto d=result.domains[p.extra],prefix="QSym.BindingScalar"~to!string(p.extra),field=leanSort(d.sort);
					auto env="({ ξ with "~field~" := fun i => if i = "~to!string(d.variable)~" then x else ξ."~field~" i })";
					auto hd="("~prefix~".DomainCertificate.domain_correct "~env~")";
					auto input="(n"~to!string(d.input.id)~".eval "~env~")",domain="(n"~to!string(d.result.output.id)~".eval "~env~")";
					string equality;
					if(d.mode==BoundOp.defined) equality=hd~".symm";
					else if(d.mode==BoundOp.holds) equality="(Binding.holdsDomain "~input~" "~domain~" "~hd~")";
					else if(d.mode!=BoundOp.primitive) equality="(Binding.preserveDomain "~input~" (n"~to!string(arena.castTo(d.value.output,arena.sort(d.input)).id)~".eval "~env~") "~domain~
						" "~hd~" ("~prefix~".ValueCertificate.refinement "~env~"))";
					string wrap(uint id,size_t depth){
						if(depth==d.path.length){
							if(d.mode!=BoundOp.primitive) return equality;
							auto mask=nodes[id],z=arena.number(Number(0),d.sort);
							auto value=arena.castTo(d.value.output,arena.sort(d.input));
							string zeroProof(Term a){
								auto term="n"~to!string(a.id);
								if(arena.sort(a)==Sort.real_) return "(Numeric.calculate_real_zero ξ "~term~" rfl)";
								if(arena.sort(a)==Sort.complex) return "(Eq.trans (Numeric.calculate_sound ξ "~term~" (0, 0) rfl) (congrArg some ((Numeric.complex_zero (0, 0)).mpr rfl)))";
								return "(Numeric.calculate_sound ξ "~term~" 0 rfl)";
							}
							string fn(uint child){return "(fun u => "~name(child)~".eval ξ (Binding.Env.cons (a := .scalar ."~field~") u ρ))";}
							auto h0="(Eq.trans (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) ("~prefix~".ValueCertificate.refinement ξ)) "~zeroProof(value)~")";
							return "(Value.mask_nonzero_of_zero "~fn(mask.a)~" "~binderNonzero(mask.a)~" "~fn(mask.b)~" (n"~to!string(z.id)~".eval ξ) "~zeroProof(z)~" "~h0~" x)";
						}
						auto q=nodes[id],left=d.path[depth]==0?wrap(q.a,depth+1):"rfl";
						if(q.b==uint.max) return "(congrArg "~valueOperation(q)~" "~left~")";
						auto right=d.path[depth]==1?wrap(q.b,depth+1):"rfl";
						if(q.op==BoundOp.conditional) return "(Binding.conditional_congr "~left~" "~right~" "~(d.path[depth]==2?wrap(q.c,depth+1):"rfl")~")";
						return "(congrArg₂ "~valueOperation(q)~" "~left~" "~right~")";
					}
					proof=(n.op==BoundOp.lambda?".lamPointwise":".setPointwise")~" (fun ξ ρ x => "~wrap(n.a,0)~")"; break;
				case BindingRule.scalarNeutral:{
					bool left=n.b==p.to,add=arena.view(arena.at(n.data)).op==Op.add;
					auto literal=nodes[left?n.a:n.b].data,other="("~name(p.to)~".eval ξ ρ)";
					auto op=add?"add":"mul",v=add?"zero":"one";
					auto f="(fun z => Value."~op~" "~(left?"z "~other:other~" z")~")";
					proof=".ofEq (fun ξ ρ => Eq.trans (congrArg "~f~" (Numeric.calculate_real_"~v~" ξ n"~
						to!string(literal)~" rfl)) (Value."~op~"_"~v~(left?"_left ":"_right ")~other~"))"; break;
				}
				case BindingRule.scalarSimplify:
					auto d=result.domains[p.extra],prefix="QSym.BindingScalar"~to!string(p.extra);
					proof=".scalarSimplify n"~to!string(d.input.id)~" n"~to!string(d.result.output.id)~" n"~to!string(arena.castTo(d.value.output,arena.sort(d.input)).id)~
						" "~prefix~".DomainCertificate.domain_correct "~prefix~".ValueCertificate.refinement"; break;
				case BindingRule.scalarDomain,BindingRule.scalarHolds:
					auto d=result.domains[p.extra];
					proof=p.rule==BindingRule.scalarDomain?".scalarDomain ":".scalarHolds ";
					proof~="n"~to!string(d.input.id)~" n"~to!string(d.result.output.id)~" QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct"; break;


				case BindingRule.distributionMassZero:
					proof=".ofEq (fun ξ ρ => Distribution.mass_zeroValue)"; break;
				case BindingRule.distributionDefinedBinary:{
					auto d=nodes[n.a],ctor=d.op==BoundOp.distributionAdd?"add":"scale";
					proof=".ofEq (fun ξ ρ => Binding.defined_binary_data Distribution.Presentation."~ctor~" ("~name(d.a)~".eval ξ ρ) ("~name(d.b)~".eval ξ ρ))"; break;
				}
				case BindingRule.distributionFixedRetry:
				case BindingRule.distributionFixedAffine:
				case BindingRule.distributionFixedTail:
				case BindingRule.distributionFixedBody:
				case BindingRule.distributionRetryPoint:
				case BindingRule.distributionRetryEmpty:
				case BindingRule.distributionRetryZeroPoint:
				case BindingRule.distributionRetryInfinitePoint:
				case BindingRule.distributionRetryZero:
				case BindingRule.distributionRetryMissing:
				case BindingRule.distributionDefinedRetry:
				case BindingRule.distributionRetryMass:
				case BindingRule.distributionRetryDensity:
				case BindingRule.distributionShiftObservation:
				case BindingRule.distributionInvolutionObservation:
				case BindingRule.distributionInvolutionUnbounded:
				case BindingRule.distributionShiftMoment:
				case BindingRule.distributionRetryUnbounded:
				case BindingRule.distributionRetryObservation:{
					enum ns="Distribution.Atomic.";
					alias q=SourceCertificates.q;
					string ev(uint id){return " ("~name(id)~".eval ξ ρ)";}
					Rational literal(uint id){return arena.number(arena.at(nodes[id].data)).re;}
					string number(uint id){return "(Numeric.calculate_sound ξ n"~to!string(nodes[id].data)~" "~q(literal(id))~" rfl)";}
					enum yes=" (of_decide_eq_true rfl)";
					string admissible(uint id){
						auto v=nodes[id];
						switch(v.op){
							case BoundOp.bottom:return ns~"admissible_none";
							case BoundOp.distributionZero:return ns~"admissible_zero";
							case BoundOp.distributionDirac:return " ("~ns~"admissible_dirac"~ev(v.a)~")";
							case BoundOp.distributionAdd:return " ("~ns~"admissible_add "~admissible(v.a)~" "~admissible(v.b)~")";
							case BoundOp.distributionScale:return " ("~ns~"admissible_scale "~q(literal(v.a))~yes~" "~number(v.a)~" "~admissible(v.b)~")";
							default:throw new Exception("missing atomic seed certificate");
						}
					}
					AtomicVisits[uint] shapes;
					string visitProof(uint id){
						auto v=nodes[id],shape=shapes[id];
						switch(v.op){
							case BoundOp.distributionZero:return " "~ns~"EmptySeed.zero";
							case BoundOp.distributionDirac:return " ("~ns~"point_dirac"~ev(v.a)~")";
							case BoundOp.distributionScale:{
								auto w=q(literal(v.a)),sub=visitProof(v.b);
								if(shape.kind==VisitKind.empty) return " ("~ns~"EmptySeed.scale "~w~yes~" "~number(v.a)~sub~")";
								return " ("~ns~"point_scale "~w~" "~q(shape.weight)~yes~yes~" "~number(v.a)~sub~")";
							}
							case BoundOp.distributionAdd:{
								auto left=visitProof(v.a),right=visitProof(v.b);
								if(shape.kind==VisitKind.empty) return " ("~ns~"EmptySeed.add"~left~right~")";
								if(shapes[v.a].kind==VisitKind.empty) return " ("~ns~"point_add_empty true"~right~left~")";
								if(shapes[v.b].kind==VisitKind.empty) return " ("~ns~"point_add_empty false"~left~right~")";
								return " ("~ns~"point_add "~q(shape.weight)~yes~yes~yes~left~right~")";
							}
							default:throw new Exception("missing atomic visit certificate");
						}
					}
					string tail(uint id,out Rational coefficient){
						auto v=nodes[id];
						if(v.op==BoundOp.variable){ coefficient=Rational(1); return ns~"Tail.self"; }
						Rational a,b;
						if(v.op==BoundOp.distributionAdd){
							auto left=tail(v.a,a),right=tail(v.b,b);
							coefficient=a+b;
							return " ("~ns~"Tail.add "~q(coefficient)~yes~" "~left~" "~right~")";
						}
						uint factor; enforce(retryFactor(v,factor,a));
						auto sub=tail(v.b,b);
						coefficient=a*b;
						return " ("~ns~"Tail.scale "~(v.op==BoundOp.distributionWeight?"true ":"false ")~
							q(a)~" "~q(coefficient)~yes~yes~" "~number(factor)~" "~sub~")";
					}
					string affine(uint id,uint base,ref AffineForm[uint] forms){
						auto v=nodes[id],form=forms[id];
						final switch(form.op){
							case AffineOp.constant:
								return " ("~ns~"Affine.constant "~(form.empty?ns~"admissible_zero":admissible(base))~")";
							case AffineOp.self:return " "~ns~"Affine.self";
							case AffineOp.reemit:{
								auto kind=reemitKernel(v.b);
								auto point=kind==Reemit.self?"(fun _ => rfl)":"("~ns~"reemit_nat_zero "~(kind==Reemit.zeroPlus?"true":"false")~" rfl)";
								auto law=type(at(id))==pool.distribution(scalarType(Sort.real_))?"realBind_self":"bind_self";
								return " ("~ns~"Affine."~law~affine(v.a,base,forms)~" "~point~")";
							}
							case AffineOp.add:{
								bool left=forms[v.a].empty,right=forms[v.b].empty;
								auto rule=left?"add_left_zero":right?"add_right_zero":"add";
								auto l=left?uint.max:right?base:nodes[base].a;
								auto r=right?uint.max:left?base:nodes[base].b;
								return " ("~ns~"Affine."~rule~" "~q(form.ratio)~yes~affine(v.a,l,forms)~affine(v.b,r,forms)~")";
							}
							case AffineOp.scale,AffineOp.weight:{
								uint factor; Rational r; enforce(retryFactor(v,factor,r));
								return " ("~ns~(form.empty?"Affine.scale_zero ":"Affine.scale ")~(form.op==AffineOp.weight?"true ":"false ")~
									q(r)~" "~q(form.ratio)~yes~yes~" "~number(factor)~affine(v.b,form.empty?uint.max:nodes[base].b,forms)~")";
							}
						}
					}
					string law;
					if(p.rule==BindingRule.distributionFixedRetry||p.rule==BindingRule.distributionFixedAffine||p.rule==BindingRule.distributionFixedTail||p.rule==BindingRule.distributionFixedBody){
						RetryParts parts; enforce(retrySource(nodes[n.a].a,parts)); Rational coefficient;
						if(p.rule==BindingRule.distributionFixedTail){
							law=ns~"fixed_tail "~tail(parts.tail,coefficient)~" (fun _ => rfl)";
						}else{
							auto target=nodes[p.to],swap=parts.swapped?"true ":"false ";
							if(parts.forms.length) law=ns~"fixed_affine "~q(parts.ratio)~" "~number(target.a)~
								affine(parts.tail,target.b,parts.forms)~" (fun _ => rfl)";
							else if(parts.direct) law=ns~"fixed_retry "~swap~(parts.weighted?"true ":"false ")~q(parts.ratio)~yes~
								" "~number(target.a)~" "~admissible(target.b)~" (fun _ => rfl)";
							else law=ns~"fixed_add_tail "~swap~q(parts.ratio)~" "~number(target.a)~" "~admissible(target.b)~
								" "~tail(parts.tail,coefficient)~" (fun _ => rfl)";
						}
					}else if(p.rule==BindingRule.distributionInvolutionObservation||p.rule==BindingRule.distributionInvolutionUnbounded){
						uint[] ops; auto loop=nodes[observationInput(n.a,ops)]; InvolutiveLoop source;
						enforce(involutiveLoop(nodes[loop.a].a,source));
						BoundTerm seed,mapped; involutionEmissions(context(at(p.from)),loop,source,seed,mapped);
						bool flip=source.map==Involution.flip;
						auto transport="("~ns~(flip?"Transport.bind (":"Transport.realBind (")~"("~name(node(mapped).b)~".eval ξ ρ).getD (fun _ => none)))";
						auto involution=flip?"(fun a : Bool => Bool.not_not a)":"(fun a : ℝ => neg_neg a)";
						auto point=flip?"(fun _ => rfl)":"("~ns~"dirac_neg "~(source.map==Involution.negLeft?"true ":"false ")~number(source.unit)~")";
						auto args=" "~massObserver(ops,true)~" "~transport~" "~involution~" "~point~" "~admissible(seed.id);
						if(p.rule==BindingRule.distributionInvolutionUnbounded){
							if(source.ratio==uint.max) law=ns~"CountableObservation.fixed_involution_unscaled"~args~" (fun _ => rfl)";
							else law=ns~"CountableObservation.fixed_involution_noncontracting"~args~" "~q(literal(source.ratio))~yes~" "~number(source.ratio)~" (fun _ => rfl)";
						}else{
							uint[] after;auto pair=nodes[observationInput(nodes[p.to].a,after)],first=nodes[pair.a],second=nodes[pair.b];
							law=ns~"CountableObservation.fixed_involution_q"~args~" "~q(literal(source.ratio))~" "~q(literal(first.a))~" "~q(literal(second.a))~yes~yes~yes~yes~
								" "~number(source.ratio)~" "~number(first.a)~" "~number(second.a)~" (fun _ => rfl)";
						}
					}else if(p.rule==BindingRule.distributionShiftMoment){
						uint[] ops;auto loop=nodes[observationInput(n.a,ops)];
						NatShift parts;enforce(naturalShift(nodes[loop.a].a,parts));
						Rational[] primitive_;MomentPolynomial source;enforce(shiftMoment(parts,ops,primitive_,source,true));
						bool weighted=parts.mass!=uint.max;
						auto mass=weighted?literal(parts.mass):Rational(1),start=to!string(literal(parts.start).numerator);
						string cs="[";foreach(j,c;primitive_) cs~=(j?", ":"")~q(c);cs~="]";
						auto tag="moment"~to!string(i),stride=to!string(literal(parts.stride).numerator);
						code~="private def "~tag~"Primitive : List ℚ := "~cs~"\n";
						code~="private theorem "~tag~"Check : GeometricMoments.checks "~source.polynomial~" "~tag~"Primitive "~q(literal(parts.ratio))~
							" "~q(mass)~" "~start~" "~stride~" = true := rfl\n";
						law=ns~"nat_shift_polynomial "~(weighted?"true ":"false ")~(parts.strideLeft?"true ":"false ")~
							stride~yes~" "~q(mass)~" "~q(literal(parts.ratio))~yes~yes~yes~" "~
							(weighted?number(parts.mass):ns~"one_weight")~" "~number(parts.ratio)~" "~start~" (Numeric.calculate_sound ξ n"~
							to!string(nodes[parts.start].data)~" "~start~" rfl) (fun _ => rfl) "~source.proof~" "~tag~"Primitive "~q(literal(p.to))~
							" "~tag~"Check"~yes~" "~number(p.to);
					}else if(p.rule==BindingRule.distributionShiftObservation){
						uint[] ops; auto loop=nodes[observationInput(n.a,ops)],seq=nodes[p.to];
						NatShift parts; enforce(naturalShift(nodes[loop.a].a,parts));
						bool weighted=parts.mass!=uint.max;
						auto mass=weighted?literal(parts.mass):Rational(1);
						auto witness=weighted?number(parts.mass):ns~"one_weight";
						auto stride=to!string(literal(parts.stride).numerator);
						auto args=(parts.strideLeft?"true ":"false ")~stride~yes~" "~q(mass)~" "~q(literal(parts.ratio))~yes~yes~
							" "~witness~" "~number(parts.ratio)~ev(seq.a);
						if(!ops.length){
							bool missing=nodes[seq.b].op==BoundOp.bottom;
							auto total=missing?"none":"(some "~q(literal(seq.b))~")";
							law=ns~"nat_shift_mass "~(weighted?"true ":"false ")~args~" (fun _ => rfl) "~total~yes~
								(missing?" rfl":" "~number(seq.b));
						}else{
							auto index=parts.zeroStart?(parts.unitStride?ns~"ShiftIndex.self":"("~ns~"ShiftIndex.mul "~stride~")"):
								parts.unitStride?"("~ns~"ShiftIndex.add"~ev(seq.a)~")":"("~ns~"ShiftIndex.add_mul"~ev(seq.a)~" "~stride~")";
							bool factored=weighted&&!mass.zero;
							law=ns~(factored?"CountableObservation.nat_shift_factored ":"CountableObservation.nat_shift ")~
								massObserver(ops,true)~(factored?" ":weighted?" true ":" false ")~args~
								" "~index~" (fun _ => rfl) (fun _ => rfl)";
						}
					}else if(p.rule==BindingRule.distributionDefinedRetry||p.rule==BindingRule.distributionRetryDensity){
						auto loop=nodes[n.a];
						auto args=q(literal(loop.a))~yes~" "~number(loop.a)~" "~admissible(loop.b);
						law=p.rule==BindingRule.distributionDefinedRetry?"congrArg some ("~ns~"retry_isSome "~args~")":
							ns~"density_retry_seed "~args~ev(n.b);
					}else if(p.rule==BindingRule.distributionRetryMissing) law=ns~"retry_missing"~ev(n.a);
					else if(p.rule==BindingRule.distributionRetryZero) law=ns~"retry_zero "~q(literal(n.a))~yes~" "~number(n.a);
					else if(p.rule==BindingRule.distributionRetryPoint||p.rule==BindingRule.distributionRetryZeroPoint||p.rule==BindingRule.distributionRetryEmpty||p.rule==BindingRule.distributionRetryInfinitePoint){
						auto v=atomicVisits(n.b,shapes),r=literal(n.a),evidence=visitProof(n.b);
						if(p.rule==BindingRule.distributionRetryEmpty) law=ns~"retry_empty "~q(r)~yes~" "~number(n.a)~evidence;
						else if(p.rule==BindingRule.distributionRetryInfinitePoint) law=ns~"retry_infinite_point "~q(r)~" "~q(v.weight)~yes~yes~" "~number(n.a)~evidence;
						else if(p.rule==BindingRule.distributionRetryZeroPoint) law=ns~"retry_zero_point "~q(r)~yes~" "~number(n.a)~" "~number(nodes[p.to].a)~evidence;
						else{
							auto z=v.weight/(Rational(1)-r);
							auto scale=z==Rational(1)?"(weight := some (1 : ℝ)) ":"";
							auto hv=z==Rational(1)?ns~"one_weight":number(nodes[p.to].a);
							law=ns~"retry_point "~scale~q(r)~" "~q(v.weight)~" "~q(z)~yes~yes~yes~yes~" "~number(n.a)~" "~hv~evidence;
						}
					}else{
						bool unbounded=p.rule==BindingRule.distributionRetryUnbounded;
						uint source=n.a,target=nodes[p.to].a;
						string observer;
						if(unbounded||p.rule==BindingRule.distributionRetryObservation){
							uint[] ops;
							source=observationInput(source,ops);
							observer=massObserver(ops,unbounded);
							if(!unbounded) foreach(id;ops) target=nodes[id].op==BoundOp.distributionWeight?nodes[target].b:nodes[target].a;
						}
						auto loop=nodes[source];
						if(unbounded) law=ns~"CountableObservation.retry_noncontracting "~observer~" "~q(literal(loop.a))~yes~
							" "~number(loop.a)~" "~admissible(loop.b);
						else{
							auto gain=nodes[target].a;
							law=ns~(observer.length?"Observation.retry "~observer~" ":"mass_retry ")~
								q(literal(loop.a))~" "~q(literal(gain))~yes~yes~yes~
								" "~number(loop.a)~" "~number(gain)~" "~admissible(loop.b);
						}
					}
					proof=".ofEq (fun ξ ρ => "~law~")";break;
				}
				case BindingRule.distributionMassCountdown:{
					uint[] ops;
					auto call=nodes[observationInput(n.a,ops)],target=nodes[p.to];
					bool partial=target.op==BoundOp.conditional;
					auto branch=nodes[nodes[nodes[call.a].a].a],step=nodes[branch.c];
					bool emitting=step.op==BoundOp.distributionAdd;
					uint observedInput(uint mass){
						auto d=nodes[mass].a;
						foreach(id;ops) d=nodes[id].op==BoundOp.distributionWeight?nodes[d].b:nodes[d].a;
						return d;
					}
					auto f=to!string(call.a)~dimArg~" γ ξ ρ";
					bool swapped=emitting&&depends(at(step.a),1);
					auto emission=swapped?step.b:step.a;
					bool indexed=emitting&&depends(at(emission),0);
					string indexedVisit(){
						return "(fun (u : Option ℕ) => "~name(emission)~".eval ξ (Binding.Env.cons (a := .scalar .natural) u (Binding.Env.cons (a := "~leanType(type(at(call.a)))~") none ρ)))";
					}
					if(indexed&&partial){
						auto positive=nodes[target.c],ratio=nodes[nodes[positive.a].a].a;
						proof=".ofEq (fun ξ ρ => Distribution.observe_convolution_countdown "~massObserver(ops,false)~" (rec"~f~") (fixed"~f~") ("~
							name(observedInput(target.b))~".eval ξ ρ) "~indexedVisit()~" ("~name(ratio)~".eval ξ ρ) "~(swapped?"true":"false")~
							" (fun _ _ => rfl) ("~name(call.b)~".eval ξ ρ))";
						break;
					}
					if(emitting&&!partial){
						auto tail=nodes[swapped?step.a:step.b];
						bool discounted=indexed&&primitiveOp(p.to,Op.mul);
						auto total=discounted?nodes[target.b]:target;
						string factor="(some 1) rfl false";
						if(discounted){
							auto sum=nodes[total.b],row=nodes[nodes[sum.a].a],inverse=nodes[row.a].a;
							auto r=nodes[tail.a].data,s=nodes[inverse].data; Number rate;
							enforce(literalNumber(arena.at(r),rate),"missing indexed countdown scale");
							auto q=SourceCertificates.q(rate.re),inv=SourceCertificates.q(arena.number(arena.at(s)).re);
							auto raw="n"~to!string(r),reciprocal="n"~to!string(s);
							factor=q~" "~inv~" (of_decide_eq_true rfl) ("~raw~".eval ξ) ("~reciprocal~".eval ξ) (Numeric.calculate_sound ξ "~raw~" "~q~" rfl) (Numeric.calculate_sound ξ "~reciprocal~" "~inv~" rfl)";
						}else if(tail.op==BoundOp.distributionScale){
							auto id=to!string(nodes[tail.a].data);
							factor="(n"~id~".eval ξ) (Numeric.calculate_real_one ξ n"~id~" rfl) true";
						}
						string visit;
						if(indexed) visit=indexedVisit();
						else{
							auto mask=nodes[target.b],amount=nodes[mask.b];
							visit="("~name(observedInput(amount.b))~".eval ξ ρ)";
						}
						auto law=discounted?"observe_discounted_countdown":indexed?"observe_indexed_countdown":"observe_unit_countdown";
						proof=".ofEq (fun ξ ρ => Distribution."~law~" "~massObserver(ops,false)~" (rec"~f~") (fixed"~f~") ("~
							name(observedInput(total.a))~".eval ξ ρ) "~visit~" "~factor~" "~
							(swapped?"true":"false")~" (fun _ _ => rfl) ("~name(call.b)~".eval ξ ρ))";
						break;
					}
					auto positive=partial?nodes[target.c]:target;
					bool centered=emitting&&nodes[nodes[positive.a].a].op==BoundOp.scalar;
					auto product=emitting?nodes[centered?positive.b:positive.a]:positive,ratio=nodes[product.a].a;
					auto base=observedInput(partial?target.b:product.b);
					string law,scale;
					if(emitting){
						law="observe_emitting_countdown "~massObserver(ops,false);
						auto e=observedInput(nodes[centered?positive.a:positive.b].b);
						scale="("~name(e)~".eval ξ ρ) ("~name(ratio)~".eval ξ ρ) "~(depends(at(step.a),1)?"true":"false");
					}else if(partial){
						law="observe_partial_scale_countdown "~massObserver(ops,false);
						scale="("~name(ratio)~".eval ξ ρ)";
					}else{
						law=ops.length?"observe_scale_countdown "~massObserver(ops,false):"mass_scale_countdown";
						auto literal=arena.at(nodes[ratio].data),q=SourceCertificates.q(arena.number(literal).re),id=to!string(literal.id);
						scale="(n"~id~".eval ξ) (Numeric.calculate_sound ξ n"~id~" "~q~" rfl)";
					}
					auto application="Distribution."~law~" (rec"~f~") (fixed"~f~") ("~name(base)~".eval ξ ρ) "~scale~
						" (fun _ _ => rfl) ("~name(call.b)~".eval ξ ρ)";
					if(centered){
						auto limit=nodes[positive.a],q=arena.number(arena.at(nodes[ratio].data)).re;
						auto neg=nodes[nodes[product.b].b];
						string numeric(uint d){
							auto id=nodes[d].data,v=arena.number(arena.at(id)).re;
							return "(Numeric.calculate_sound ξ n"~to!string(id)~" "~SourceCertificates.q(v)~" rfl)";
						}
						application="Eq.trans ("~application~") (Distribution.geometric_emission "~SourceCertificates.q(q)~" (of_decide_eq_true rfl) "~
							numeric(ratio)~" "~numeric(limit.a)~" "~numeric(neg.a)~" ("~name(target.b)~".eval ξ ρ) ("~name(limit.b)~".eval ξ ρ) ("~name(call.b)~".eval ξ ρ))";
					}
					proof=".ofEq (fun ξ ρ => "~application~")"; break;
				}
				case BindingRule.distributionDefinedDirac:
					proof=".ofEq (fun ξ ρ => congrArg some (Option.isSome_map' (f := Distribution.Presentation.dirac) (x := "~name(nodes[n.a].a)~".eval ξ ρ)))"; break;
				case BindingRule.distributionMassAdd:
					proof=".ofEq (fun ξ ρ => Distribution.mass_addValue ("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(nodes[n.a].b)~".eval ξ ρ))"; break;
				case BindingRule.distributionMassScale:
					proof=".ofEq (fun ξ ρ => Distribution.mass_scaleValue ("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(nodes[n.a].b)~".eval ξ ρ))"; break;
				case BindingRule.distributionMassIntegral,BindingRule.distributionMassBind:{
					auto d=nodes[n.a],body=nodes[p.rule==BindingRule.distributionMassIntegral?d.a:d.b].a;
					auto continuation="(fun x : ℝ => "~name(body)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))";
					bool integral=p.rule==BindingRule.distributionMassIntegral;
					string theorem="Distribution."~(integral?"model_mass_integralValue ":"model_mass_bind_density "~densityProgram(result.integrals[p.extra].from)~" ")~continuation;
					if(type(at(n.a))==pool.distribution(scalarType(Sort.real_))){
						auto bridge=integral?"realIntegral_mass":"realBind_mass";
						auto source=integral?"":" ("~name(d.a)~".eval ξ ρ)";
						theorem="(Distribution.GraphFibre."~bridge~source~" (some "~continuation~")).trans ("~theorem~")";
					}
					proof=".ofEq (fun ξ ρ => "~theorem~")"; break;
				}
				case BindingRule.distributionInterval,BindingRule.distributionIntegralAE:{
					auto s=result.integrals[p.extra];enforce(s.piecewise||s.ae,"missing compositional integral certificate");
					if(s.interval||s.gaussian){ proof=".ofEq (fun ξ ρ => let h := "~stepProofs[p.extra]~"; h)"; break; }
					if(s.polynomial){ proof=".ofEq (fun ξ ρ => ("~stepProofs[p.extra]~").trans (Eq.symm "~stepOutputs[p.extra]~"))"; break; }
					string rationalQ(Rational q){return q.denominator==1?"("~to!string(q.numerator)~" : ℚ)":"(("~to!string(q.numerator)~") / ("~to!string(q.denominator)~") : ℚ)";}
					string tail="[";foreach(k,q;s.exceptions[1..$]){if(k)tail~=",";tail~=rationalQ(q);}tail~="]";
					proof=".ofEq (fun ξ ρ => (Distribution.DensityProgram.presentation_mass_"~(s.ae?"grid_null_edit":s.closed?"grid_known":"grid")~" "~densityProgram(s.from)~(s.ae?" "~densityProgram(s.to):"")~" (a := "~rationalQ(s.exceptions[0])~") (bs := "~tail~") "~(s.closed?"(v := "~rationalQ(s.value)~") ":"")~stepProofs[p.extra]~")"~(s.ae?"":".trans (Eq.symm "~stepOutputs[p.extra]~")")~")";break;
				}
				case BindingRule.distributionMassWeightedDirac:
					proof=".ofEq (fun ξ ρ => Distribution.model_mass_weight_diracValue ("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(nodes[nodes[n.a].b].a)~".eval ξ ρ))"; break;
				case BindingRule.distributionMassDirac:
					proof=".ofEq (fun ξ ρ => Distribution.model_mass_diracValue ("~name(nodes[n.a].a)~".eval ξ ρ))"; break;
				case BindingRule.distributionMassSum:{
					bool natural=naturalIndex(nodes[n.a].a);
					proof=".ofEq (fun ξ ρ => Distribution.mass_sum"~(natural?"Nat":"")~"Value (fun i : "~(natural?"ℕ":"ℤ")~" => "~name(nodes[nodes[n.a].a].a)~
						".eval ξ (Binding.Env.cons (a := .scalar ."~(natural?"natural":"integer")~") (some i) ρ)))"; break;
				}
				case BindingRule.distributionWeightSum,BindingRule.distributionBindSum:{
					// The target is other; sumD(λi. row) with the copy of other in the row.
					bool weight=p.rule==BindingRule.distributionWeightSum;
					auto row=nodes[nodes[nodes[nodes[p.to].b].a].a],term=weight?row.b:row.a,copy=weight?row.a:row.b;
					bool natural=naturalIndex(nodes[weight?n.b:n.a].a);
					string under(uint id){ return "(fun i : "~(natural?"ℕ":"ℤ")~" => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar ."~(natural?"natural":"integer")~") (some i) ρ))"; }
					auto other="("~name(weight?n.a:n.b)~".eval ξ ρ)";
					bool realTarget=!weight&&pool.view(type(at(n.b))).fields[1]==pool.distribution(scalarType(Sort.real_));
					auto sum=natural?"sumNatValue ":"sumValue ";
					auto law=weight?"Distribution.weight_"~sum~other~" "~under(copy)~" "~under(term):
						(realTarget?"Distribution.GraphFibre.realBind_":"Distribution.bind_")~sum~under(term)~" "~other~" "~under(copy);
					proof=".ofEq (fun ξ ρ => "~law~" (fun _ => rfl))"; break;
				}
				case BindingRule.distributionStrict:{
					bool left=nodes[n.a].op==BoundOp.bottom&&n.op!=BoundOp.distributionScale&&n.op!=BoundOp.distributionWeight;
					string law;
					switch(n.op){
						case BoundOp.distributionAdd:law="add_none"; break;
						case BoundOp.distributionScale:law="scale_none"; break;
						case BoundOp.distributionWeight:law="weight_none"; break;
						case BoundOp.distributionDensityAt:law="densityAt_none"; break;
						case BoundOp.distributionBind:
							law=pool.view(type(at(n.b))).fields[1]==pool.distribution(scalarType(Sort.real_))?"GraphFibre.realBind_none":"bind_none"; break;
						default:enforce(false,"strictness certificate for an unsupported constructor");
					}
					proof=".ofEq (fun ξ ρ => Distribution."~law~(left?"_left (":"_right (")~name(left?n.b:n.a)~".eval ξ ρ))"; break;
				}
				case BindingRule.distributionWeightWeightLebesgue:{
					string body(uint fn){ return "(fun x => "~name(nodes[fn].a)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))"; }
					proof=".ofEq (fun ξ ρ => Distribution.weight_weight_lebesgue "~body(nodes[n.b].a)~" "~body(n.a)~")"; break;
				}
				case BindingRule.distributionWeightZero:
					proof=".ofEq (fun ξ ρ => Distribution.weight_zeroValue ("~name(n.a)~".eval ξ ρ))"; break;
				case BindingRule.distributionWeightDirac:
					proof=".ofEq (fun ξ ρ => Distribution.weight_diracValue ("~name(n.a)~".eval ξ ρ) ("~name(nodes[n.b].a)~".eval ξ ρ))"; break;
				case BindingRule.distributionWeightAdd,BindingRule.distributionWeightScale:
					proof=".ofEq (fun ξ ρ => Distribution.weight_"~(p.rule==BindingRule.distributionWeightAdd?"add":"scale")~"Value ("~name(n.a)~".eval ξ ρ) ("~name(nodes[n.b].a)~".eval ξ ρ) ("~name(nodes[n.b].b)~".eval ξ ρ))"; break;
				case BindingRule.distributionBindDirac,BindingRule.distributionBindAdd,BindingRule.distributionBindScale,BindingRule.distributionBindZero:{
					auto d=nodes[n.a],k=" ("~name(n.b)~".eval ξ ρ)";
					bool realTarget=pool.view(type(at(n.b))).fields[1]==pool.distribution(scalarType(Sort.real_));
					auto law=realTarget?"Distribution.GraphFibre.realBind_":"Distribution.bind_";
					string arguments;
					if(p.rule==BindingRule.distributionBindDirac) arguments=" ("~name(d.a)~".eval ξ ρ)"~k;
					else if(p.rule==BindingRule.distributionBindZero) arguments=k;
					else arguments=" ("~name(d.a)~".eval ξ ρ) ("~name(d.b)~".eval ξ ρ)"~k;
					auto which=p.rule==BindingRule.distributionBindDirac?"dirac":p.rule==BindingRule.distributionBindAdd?"add":p.rule==BindingRule.distributionBindScale?"scale":"zero";
					proof=".ofEq (fun ξ ρ => "~law~which~"Value"~arguments~")"; break;
				}
				case BindingRule.distributionGraphMass:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.mass_eq_marginal ("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(nodes[n.a].b)~".eval ξ ρ))"; break;
				case BindingRule.distributionWeightedSquare,BindingRule.distributionWeightedSquareDensity:{
					bool observe=p.rule==BindingRule.distributionWeightedSquareDensity;
					auto sourceId=observe?n.a:p.from,graph=nodes[sourceId];
					uint weight,point; enforce(realAtomRow(at(sourceId),weight,point));
					auto product=arena.view(arena.at(nodes[point].data)).op==Op.mul?" true":" false";
					auto placement=graph.op==BoundOp.distributionIntegral?"integral":nodes[graph.a].op==BoundOp.distributionWeight?"weighted_bind":"bind";
					auto rows="Distribution.GraphFibre.SquareRows."~placement;
					if(observe){
						auto body="(fun x : ℝ => "~name(weight)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))";
						auto setup="(w := "~body~") "~rowTotalProof(p.extra);
						proof=".ofEq (fun ξ ρ => let h := "~rows~" "~setup~product~"; let k := Distribution.GraphFibre.SquareRows.density "~setup~
							" ("~name(n.b)~".eval ξ ρ); Eq.trans (congrArg (fun d => Distribution.densityAtValue d ("~name(n.b)~".eval ξ ρ)) h) k)"; break;
					}
					string source="Distribution.GraphFibre.absSquareSource",chart="Distribution.GraphFibre.absSquareChart";
					if(p.left!=uint.max){
						auto prefix="QSym.BindingScalar"~to!string(p.left);
						auto env="({ ξ with real := fun i => if i = "~to!string(result.domains[p.left].variable)~" then x else ξ.real i })";
						auto sign="(fun x : ℝ => LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct "~env~") ("~
							prefix~".ValueCertificate.refinement "~env~"))";
						source="Distribution.GraphFibre.squareWeightSource_of_product "~
							squareWeights.get(cast(uint)i,"")~" "~sign~" ("~proofName(p.right)~".sound ξ ρ)";
						chart="c.chart";
					}
					proof=".ofEq (fun ξ ρ => let c := "~source~"; let h := Eq.trans ("~rows~" c.total"~product~") "~chart~"; h)"; break;
				}
				case BindingRule.distributionAtomRows:{
					auto graph=nodes[p.to],map=nodes[nodes[graph.b].a];
					auto kind=n.op==BoundOp.distributionIntegral?"integral":
						nodes[n.a].op==BoundOp.distributionWeight?"weighted_bind":"bind";
					auto row=nodes[nodes[n.op==BoundOp.distributionIntegral?n.a:n.b].a];
					if(row.op==BoundOp.distributionDirac&&kind!="weighted_bind"){
						proof=".ofEq (fun ξ ρ => Distribution.GraphFibre."~kind~"_dirac_graph "~
							realBody(graph.b)~" "~rowTotalProof(p.extra)~")"; break;
					}
					if(p.extra!=uint.max){
						proof=".ofEq (fun ξ ρ => Distribution.GraphFibre."~kind~"_total_graph "~
							realBody(graph.a)~" "~realBody(graph.b)~" "~rowTotalProof(p.extra)~" "~rowTotalProof(p.extra+1)~")"; break;
					}
					string f="id";
					if(map.op==BoundOp.primitive){
						auto op=arena.view(arena.at(map.data));
						f=op.op==Op.pow?"(fun x : ℝ => x ^ "~to!string(op.value)~")":"(fun x : ℝ => x * x)";
					}
					proof=".ofEq (fun _ _ => Distribution.GraphFibre."~kind~"_openUnit_graph "~f~")"; break;
				}
				case BindingRule.distributionMaskAbsorb:{
					auto mask=nodes[nodes[n.a].a],pred=nodes[mask.a];
					string fn(uint id){ return "(fun x : ℝ => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))"; }
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.weight_mask_absorb "~fn(pred.a)~" "~fn(pred.b)~" "~fn(mask.b)~")"; break;
				}
				case BindingRule.distributionAffineChart:{
					auto chart=result.affineCharts[p.extra];
					// Infer the chart witnesses before conversion against the full
					// binding evaluations. This avoids expensive backward unification.
					proof=".ofEq (fun ξ ρ => let h := Distribution.GraphFibre.affine_chart_rule "~realBody(n.a)~" "~
						rowTotalProof(chart.predicateDomain)~" "~chartProofs[p.extra]~"; h)"; break;
				}
				case BindingRule.limitTerms:
					proof=".ofEq (fun ξ ρ => let h := "~limitProofs[p.extra]~"; h)"; break;
				case BindingRule.distributionMassStrictGuard:{
					uint[] weights;size_t position;uint condition;BoundTerm rest;
					enforce(massStrictGuard(p.from,weights,position,condition,rest),"missing strict guard free of the axis");
					enum program_="Distribution.DensityProgram.";
					string fn(uint id){return "(fun x : ℝ => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))";}
					// The guard at the top or in a factor, by the path to it.
					string hoist(uint id){
						auto q=nodes[id];uint inside;BoundTerm without;
						if(q.op==BoundOp.guard&&!depends(at(q.a),0))return "("~program_~"Hoists.here ("~name(nodes[p.to].a)~".eval ξ ρ) "~fn(q.b)~")";
						if(axisFreeStrictGuard(q.a,inside,without))return "("~program_~"Hoists.left "~fn(q.b)~" "~hoist(q.a)~")";
						return "("~program_~"Hoists.right "~fn(q.a)~" "~hoist(q.b)~")";
					}
					string program=program_~"lebesgue";
					foreach(w;weights[0..position])program="("~program_~"weight "~fn(nodes[w].a)~" "~program~")";
					auto evidence="("~program_~"Guarded.here "~hoist(nodes[weights[position]].a)~" "~program~")";
					foreach(w;weights[position+1..$])evidence="("~program_~"Guarded.there "~fn(nodes[w].a)~" "~evidence~")";
					proof=".ofEq (fun ξ ρ => "~program_~"mass_strict_guard "~evidence~")"; break;
				}
				case BindingRule.distributionMassSpread:{
					auto s=result.integrals[p.extra];
					enforce(s.from.length==1&&s.to.length==1,"missing weight with a sum");
					string under(uint id){return "("~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))";}
					string fn(uint id){return "(fun x : ℝ => "~under(id)~")";}
					// The split at the changes of sign, then the factors under the sums.
					auto source=s.from[0];string cut;
					if(s.split!=uint.max){auto pieces=splitAt(source,s.kinks,&under);enforce(pieces.id==s.split,"missing split of a weight");cut=pieces.proof;source=s.split;}
					auto spread=spreadProducts(source,16,&under);
					enforce(spread.id!=uint.max&&(cut.length||spread.proof.length),"missing factor of a sum");
					if(cut.length)spread.proof=spread.proof.length?"(Eq.trans "~cut~" "~spread.proof~")":cut;
					// Each summand in its normal form, under the guard of its domain;
					// then the guards around the sum.
					size_t next;bool guarded;
					string normal(uint id,out string lift){
						auto q=nodes[id];enum sum="Distribution.DensityProgram.GuardedSum.";
						if(q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.add&&type(at(id))==scalarType(Sort.real_)){
							string la,lb;auto a=normal(q.a,la),b=normal(q.b,lb);
							lift="("~sum~"add "~la~" "~lb~")";
							return a.length||b.length?"(congrArg₂ Value.add "~(a.length?a:"rfl")~" "~(b.length?b:"rfl")~")":"";
						}
						enforce(next<s.summands.length,"missing summand");
						auto k=s.summands[next++];lift="("~sum~"bare _)";if(k==uint.max)return "";
						auto d=result.domains[k],prefix="QSym.BindingScalar"~to!string(k);
						auto env="({ ξ with real := fun i => if i = "~to!string(d.variable)~" then x else ξ.real i })";
						auto value="(n"~to!string(arena.castTo(d.value.output,arena.sort(d.input)).id)~".eval "~env~")",domain="(n"~to!string(d.result.output.id)~".eval "~env~")";
						// A domain that does not mention the axis leaves the sum.
						bool axis;foreach(part;arena.viewPostorder(d.result.output))axis|=arena.at(part)==arena.variable(d.sort,d.variable);
						if(d.result.output!=arena.boolean(true)&&!axis){guarded=true;lift="("~sum~"guard "~domain~" "~value~")";}
						return "(Binding.preserveDomain (n"~to!string(d.input.id)~".eval "~env~") "~value~" "~domain~" ("~prefix~".DomainCertificate.domain_correct "~env~") ("~
							prefix~".ValueCertificate.refinement "~env~"))";
					}
					string lift;auto tail=normal(spread.id,lift);enforce(next==s.summands.length,"missing summand");
					auto equation=tail.length?"(Eq.trans "~spread.proof~" "~tail~")":spread.proof;
					if(guarded)equation="(Eq.trans "~equation~" (Distribution.DensityProgram.GuardedSum.sound "~lift~"))";
					proof=".ofEq (fun ξ ρ => let h := Distribution.DensityProgram.mass_pointwise (w := "~fn(s.from[0])~") (v := "~fn(s.to[0])~") (fun x => "~equation~"); h)"; break;
				}
				case BindingRule.distributionMassGuard:{
					uint guard;BoundTerm rest;string shape;
					enforce(axisFreeGuard(p.from,guard,rest,shape),"missing guard free of the axis");
					string fn(uint id){return "(fun x : ℝ => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ))";}
					auto outside=nodes[p.to].a;
					proof=".ofEq (fun ξ ρ => Distribution.DensityProgram.mass_guard ("~name(outside)~".eval ξ ρ) (w := "~fn(nodes[nodes[n.a].a].a)~") (r := "~fn(rest.id)~") "~shape~")"; break;
				}
				case BindingRule.distributionWeightedAffine:{
					auto chart=result.affineCharts[p.extra];uint weight,point;
					enforce(realAtomRow(at(p.from),weight,point)&&weight!=uint.max,"missing weighted affine row");
					auto kind=n.op==BoundOp.distributionIntegral?"integral":nodes[n.a].op==BoundOp.distributionWeight?"weighted_bind":"bind";
					proof=".ofEq (fun ξ ρ => let h := Distribution.GraphFibre."~kind~"_affine_weighted_rule (fun x : ℝ => "~name(weight)~
						".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ)) "~rowTotalProof(chart.predicateDomain)~" "~chartProofs[p.extra]~"; h)"; break;
				}
				case BindingRule.distributionMaskedAffine:{
					proof=".ofEq (fun ξ ρ => let h := Distribution.GraphFibre.masked_affine_rule ("~name(nodes[n.a].a)~
						".eval ξ ρ) ("~name(n.b)~".eval ξ ρ) "~chartProofs[p.extra]~"; h)"; break;
				}
				case BindingRule.distributionAffineFibre,BindingRule.distributionAffineMass:{
					auto lemma=p.rule==BindingRule.distributionAffineFibre?"affine_fibre_rule":"affine_mass_rule";
					proof=".ofEq (fun ξ ρ => let h := Distribution.GraphFibre."~lemma~" ("~name(n.b)~
						".eval ξ ρ) "~chartProofs[p.extra]~"; h)"; break;
				}
				case BindingRule.distributionScaleUndefined:
					proof=".ofEq (fun ξ ρ => Distribution.scaleValue_of_undefined ("~name(n.a)~".eval ξ ρ) ("~
						name(n.b)~".eval ξ ρ) (QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct ξ))"; break;
				case BindingRule.distributionAffineOdd,BindingRule.distributionAffineSquare:{
					auto args=chartProofs[p.extra];
					if(result.affineCharts[p.extra].punctureBody!=uint.max){
						proof=".ofEq (fun ξ ρ => let h := Distribution.GraphFibre.affineSquare_puncture_rule "~args~
							" ("~proofName(p.right)~".sound ξ ρ); h)";
					}else if(n.op==BoundOp.distributionPushforwardOn){
						auto square=p.rule==BindingRule.distributionAffineSquare;
						auto lemma=square?"affineSquare_chart_rule":"affineOdd_chart_rule";
						if(!square) args~=" "~realBody(n.a);
						proof=".ofEq (fun ξ ρ => let h := Distribution.GraphFibre."~lemma~" "~args~" "~
							rowTotalProof(p.left)~" ("~proofName(p.right)~".sound ξ ρ); h)";
					}else{
						auto lemma=p.rule==BindingRule.distributionAffineSquare?"affineSquareExpression":"affineOddExpression";
						auto certificate="(Distribution.GraphFibre."~lemma~" "~args~")";
						auto observer=n.op==BoundOp.distributionGraphMass?"mass_rule":n.op==BoundOp.distributionGraphFibre?
							"fibre_rule":n.op==BoundOp.apply?"masked_rule":"density_rule";
						auto predicate=n.op==BoundOp.apply||n.op==BoundOp.distributionDensityAt?
							" ("~name(nodes[n.a].a)~".eval ξ ρ)":"";
						proof=".ofEq (fun ξ ρ => let h := "~certificate~"."~observer~predicate~" ("~name(n.b)~".eval ξ ρ); h)";
					}
					break;
				}
				case BindingRule.distributionRadiusSublevel:{
					auto d=nodes[n.a]; bool casts,strict;
					sublevelBound(d.a,casts,strict);
					proof=".ofEq (fun ξ ρ => let h := Distribution.GraphFibre."~(strict?"radius_sqrt_open_sublevel ":"radius_sqrt_sublevel ")~radiusArguments(nodes[d.b])~
						(casts?" true":" false")~" ("~name(p.extra)~".eval ξ ρ); h)"; break;
				}
				case BindingRule.distributionSquarePartDensity:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.Coordinates.square_density ("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionSquarePartMass:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.Coordinates.square_mass ("~name(nodes[n.a].a)~".eval ξ ρ))"; break;
				case BindingRule.distributionSquarePartPairing:{
					auto weight=nodes[n.a],part=nodes[weight.b];
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.Coordinates.square_pairing ("~name(part.a)~".eval ξ ρ) ("~name(weight.a)~".eval ξ ρ))"; break;
				}
				case BindingRule.distributionRadiusPairing:{
					auto d=nodes[n.a];
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.radius_sqrt_pairing "~radiusArguments(nodes[d.b])~" ("~name(d.a)~".eval ξ ρ))"; break;
				}
				case BindingRule.distributionWeightWeightChart:{
					auto inner=nodes[n.b],graph=nodes[inner.b];
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.Coordinates.weight_weight_chart "~realBody(inner.a)~" "~realBody(n.a)~
						" ("~name(graph.a)~".eval ξ ρ) ("~name(graph.b)~".eval ξ ρ))"; break;
				}
				case BindingRule.distributionCornerPairing:{
					auto d=nodes[n.a]; Term offset; bool swap; enforce(cornerChart(d.b,offset,swap));
					string lemma="Distribution.GraphFibre.Coordinates.corner_pairing ";
					if(offset!=Term.init){
						auto a=SourceCertificates.q(arena.number(offset).re);
						lemma="Distribution.GraphFibre.Coordinates.Grid.shifted_pairing "~a~(swap?" true ":" false ")~
							"(Numeric.calculate_sound ξ n"~to!string(offset.id)~" "~a~" rfl) ";
					}
					proof=".ofEq (fun ξ ρ => "~lemma~realBody(d.a)~" "~rowTotalProof(p.extra)~")"; break;
				}
				case BindingRule.distributionDensityAddWeight:{
					auto sum=nodes[n.a];
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.Coordinates.density_add_weight ("~name(sum.a)~".eval ξ ρ) "~realBody(nodes[sum.b].a)~" ("~name(n.b)~".eval ξ ρ))"; break;
				}
				case BindingRule.distributionSmoothCoordinate:
					proof=".ofEq (fun ξ ρ => "~smoothCoordinates.get(cast(uint)i,"")~")"; break;
				case BindingRule.distributionCoordinateGrid:
					proof=".ofEq (fun ξ ρ => "~coordinateProofs[p.extra]~")"; break;
				case BindingRule.distributionCoordinateTwoJumps:{
					JumpRays rays; enforce(jumpRays(nodes[n.a].a,rays),"missing jump certificate");
					alias q=SourceCertificates.q;
					string number(Term t){ return "(Numeric.calculate_sound ξ n"~to!string(t.id)~" "~q(arena.number(t).re)~" rfl)"; }
					proof=".ofEq (fun ξ _ => Distribution.GraphFibre.Coordinates.twoRayJumps "~q(arena.number(rays.a).re)~" "~q(arena.number(rays.b).re)~
						" (of_decide_eq_true rfl) (of_decide_eq_true rfl) "~number(rays.a)~" "~number(rays.b)~(rays.swap?" true)":" false)"); break;
				}
				case BindingRule.distributionCoordinateRayLinear:
					proof=".ofEq (fun _ _ => Distribution.GraphFibre.Coordinates.rayLinear "~
						(p.extra&1?"true ":"false ")~(p.extra&2?"true)":"false)"); break;
				case BindingRule.distributionCoordinateRayPower:{
					auto fn=nodes[nodes[n.a].a],power=nodes[nodes[fn.a].b];
					auto degree=arena.view(arena.at(power.data)).value;
					proof=".ofEq (fun _ _ => Distribution.GraphFibre.Coordinates.rayPower "~
						(p.extra&1?"true ":"false ")~(p.extra&2?"true ":"false ")~to!string(degree)~" (of_decide_eq_true rfl))"; break;
				}
				case BindingRule.distributionCoordinateSquare:
					proof=".ofEq (fun _ _ => Distribution.GraphFibre.Coordinates.square "~(p.extra?"true":"false")~")"; break;
				case BindingRule.distributionCoverSinh,BindingRule.distributionCoverAsinh:
					proof=".ofEq (fun _ _ => Distribution.GraphFibre.Coordinates."~(p.rule==BindingRule.distributionCoverSinh?"sinh":"asinh")~")"; break;
				case BindingRule.distributionCoverAffine:
					proof=".ofEq (fun ξ ρ => let h := Distribution.GraphFibre.Coordinates.affine "~affineCovers.get(cast(uint)i,"")~"; h)"; break;
				case BindingRule.distributionCoverRadius:{
					auto image=nodes[p.to];
					string form;
					auto scale=sqrtRadiusScale(image.b,form);
					auto step=result.covers[p.extra];
					auto neg=SourceCertificates.q(step.nested?Rational(-1):-arena.number(scale).re);
					auto k=to!string(nodes[step.coefficient].data);
					string flag(bool value){ return value?" true":" false"; }
					auto args=radiusArguments(image)~flag(step.centred)~" (of_decide_eq_true rfl)"~
						flag(step.nested)~" (Numeric.calculate_sound ξ n"~k~" "~neg~" rfl)"~
						flag(step.lowerSwap)~flag(step.upperSwap)~flag(step.factorSwap);
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.Coordinates.sqrtCover "~args~")"; break;
				}
				case BindingRule.distributionCutoffDensity:{
					auto weight=nodes[n.a],image=nodes[weight.b]; bool casts,strict;
					sublevelBound(weight.a,casts,strict);
					auto q=arena.at(nodes[p.extra].data),k=SourceCertificates.q(arena.number(q).re);
					auto y="("~name(n.b)~".eval ξ ρ)",limit="("~name(p.extra)~".eval ξ ρ)";
					auto term="Distribution.GraphFibre."~(strict?"radius_sqrt_window_density true ":"radius_sqrt_cutoff_density ")~radiusArguments(image)~
						(casts?" true ":" false ")~k~" (Numeric.calculate_sound ξ n"~to!string(q.id)~" "~k~" rfl) "~y;
					if(nodes[n.b].op==BoundOp.scalar&&arena.at(nodes[n.b].data)==arena.real_(0))
						term="Eq.trans ("~term~") (congrArg (Value.mask ("~(strict?"Value.lt ":"Value.le ")~y~" "~limit~")) (Distribution.GraphFibre.unrestrictedSquareDensity_zero _))";
					proof=".ofEq (fun ξ ρ => let h := "~term~"; h)"; break;
				}
				case BindingRule.distributionRadiusDensity:{
					auto term="Distribution.GraphFibre.radius_sqrt_density "~radiusArguments(nodes[n.a])~" ("~name(n.b)~".eval ξ ρ)";
					if(nodes[p.to].op==BoundOp.bottom&&nodes[n.b].op!=BoundOp.bottom)
						term="Eq.trans ("~term~") (Distribution.GraphFibre.unrestrictedSquareDensity_zero _)";
					proof=".ofEq (fun ξ ρ => let h := "~term~"; h)"; break;
				}
				case BindingRule.distributionRadiusChart:{
					auto chart=result.affineCharts[p.extra];
					auto law=chart.bandLo==uint.max?"affineSquare_radius_image":chart.openBand?"openBand_square_chart":"closedBand_square_chart";
					auto term="Distribution.GraphFibre."~law~" "~chartProofs[p.extra];
					if(chart.polynomialCheck!=uint.max){
						auto id=chart.polynomialCheck,index=to!string(result.domains[id].variable);
						auto env="({ ξ with real := fun i => if i = "~index~" then x else ξ.real i })";
						auto square="(fun x : ℝ => Distribution.GraphFibre.squareInput false ("~name(chart.map)~
							".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ)))";
						auto congr="Distribution.GraphFibre.graph_square_congr ("~name(n.a)~".eval ξ ρ) (f := "~realBody(n.b)~
							") (g := "~square~") (fun x => QSym.BindingScalar"~to!string(id)~".zero "~env~")";
						term="Eq.trans ("~congr~") ("~term~")";
					}
					proof=".ofEq (fun ξ ρ => let h := "~term~"; h)"; break;
				}
				case BindingRule.distributionClosedSquare:{
					auto observer=n.op==BoundOp.distributionGraphMass?"mass":"density";
					auto term="Distribution.GraphFibre.affineSquare_unrestricted_"~observer~" "~chartProofs[p.extra]~
						" ("~name(n.b)~".eval ξ ρ)";
					if(nodes[p.to].op==BoundOp.bottom&&nodes[n.b].op!=BoundOp.bottom)
						term="Eq.trans ("~term~") (Distribution.GraphFibre.unrestrictedSquareDensity_zero _)";
					proof=".ofEq (fun ξ ρ => let h := "~term~"; h)"; break;
				}
				case BindingRule.distributionOddChart:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.oddPower_chart_rule "~to!string(p.extra)~" "~
						realBody(n.a)~" "~rowTotalProof(p.left)~" ("~proofName(p.right)~".sound ξ ρ))"; break;
				case BindingRule.distributionOddDensity:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.oddPower_density_rule "~to!string(p.extra)~" "~
						"("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionMaskedOdd:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.oddPower_masked_rule "~to!string(p.extra)~
						" ("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionOddFibre,BindingRule.distributionOddMass:{
					auto lemma=p.rule==BindingRule.distributionOddFibre?"oddPower_fibre_rule":"oddPower_mass_rule";
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre."~lemma~" "~to!string(p.extra)~
						" ("~name(n.b)~".eval ξ ρ))"; break;
				}
				case BindingRule.distributionIdentityChart:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.realPushforward_identity "~
						"(fun x : ℝ => "~name(nodes[n.a].a)~".eval ξ (Binding.Env.cons (a := .scalar .real) (some x) ρ)))"; break;
				case BindingRule.distributionSquareChart:
					proof=".ofEq (fun _ _ => Distribution.GraphFibre."~(p.extra?"square_mul_openUnit_chart":"square_openUnit_chart")~")"; break;
				case BindingRule.distributionChartMass:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.openUnit_chart_mass ("~proofName(p.extra)~".sound ξ ρ))"; break;
				case BindingRule.distributionTotalGraphMass:{
					auto graph=nodes[n.a];
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.mass_total_graph ("~name(graph.a)~
						".eval ξ ρ) "~realBody(graph.b)~" "~rowTotalProof(p.extra)~")"; break;
				}
				case BindingRule.distributionPushforwardMass:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre.realPushforward_mass_total "~
						"("~name(nodes[n.a].a)~".eval ξ ρ) (fun x : ℝ => "~(p.extra?"x * x":"x ^ 2")~"))"; break;
				case BindingRule.distributionRestrictedSquare:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre."~(p.extra?"square_mul_openUnit_rule":"square_openUnit_rule")~" ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionSquareMass:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre."~(p.extra?"square_mul_mass_rule":"square_mass_rule")~" ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionMaskedSquare:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre."~(p.extra?"masked_square_mul_rule":"masked_square_rule")~
						" ("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionSquareGraph:
					proof=".ofEq (fun ξ ρ => Distribution.GraphFibre."~(p.extra?"square_mul_rule":"square_rule")~" ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionDensitySum,BindingRule.distributionDensityFibre:{
					string ev(uint id){ return "("~name(id)~".eval ξ ρ)"; }
					string witness(uint id){ return "h"~to!string(id); }
					auto series=p.rule==BindingRule.distributionDensitySum;
					auto q=series?"query":ev(n.b);
					auto rows=result.fibres[p.extra];
					proof=".ofEq (fun ξ ρ =>\n";
					string indent="  ";
					if(series){
						bool natural=naturalIndex(nodes[n.a].a);
						auto env="(Binding.Env.cons (a := .scalar ."~(natural?"natural":"integer")~") (some i) ρ)";
						string row(uint id){return "(fun i => "~name(id)~".eval ξ "~env~")";}
						auto root=rows[$-1];
						proof~="  let query := "~ev(n.b)~"\n  Distribution.FibreCertificate."~(natural?"extract_nat_sum":"extract_sum")~
							" (x := query) (d := "~row(root.source)~") (c := "~row(root.charge)~") (w := "~row(root.regular)~") (fun i =>\n    let ρ : Binding.Env "~ctxName(nodes[root.source].context)~" := "~env~"\n";
						indent="    ";
					}
					foreach(f;rows){
						auto d=nodes[f.source]; string lemma; Term offset; bool swap;
						if(d.op==BoundOp.distributionAdd) lemma="add "~witness(d.a)~" "~witness(d.b);
						else if(d.op==BoundOp.distributionScale) lemma="scale "~ev(d.a)~" "~witness(d.b);
						else if(d.op==BoundOp.bottom||(d.op==BoundOp.distributionDirac&&nodes[d.a].op==BoundOp.bottom)) lemma="missing "~q;
						else if(d.op==BoundOp.distributionDirac) lemma="dirac "~ev(d.a)~" "~q;
						else if(d.op==BoundOp.distributionZero) lemma="zero "~q;
						else if(d.op==BoundOp.distributionWeight&&nodes[d.b].op==BoundOp.distributionDirac)
							lemma="weightDirac "~ev(d.a)~" "~ev(nodes[d.b].a)~" "~q;
						else if(cornerChart(f.source,offset,swap)){
							bool bare=offset==Term.init;
							if(bare) offset=arena.real_(0);
							auto a=SourceCertificates.q(arena.number(offset).re);
							auto hv="(Numeric.calculate_sound ξ n"~to!string(offset.id)~" "~a~" rfl)";
							auto shape="Distribution.GraphFibre.Coordinates.Grid."~(bare?"cornerBare":(swap?"cornerSwapped ":"cornerTerm ")~a~" "~hv);
							lemma="corner "~a~" "~hv~" ("~shape~") "~q;
						}else lemma="chart "~densityProgram(f.weights)~" "~q;
						proof~=indent~"let "~witness(f.source)~" : Distribution.FibreCertificate "~ev(f.source)~" "~q~" "~ev(f.charge)~" "~ev(f.regular)~" := Distribution.FibreCertificate."~lemma~"\n";
					}
					proof~=series?indent~witness(rows[$-1].source)~"))":"  Distribution.FibreCertificate.extract "~witness(n.a)~")";
					break;
				}
				case BindingRule.distributionCountingDensity:
					proof=".ofEq (fun ξ ρ => Distribution.counting_"~(naturalIndex(nodes[n.a].a)?"N":"Z")~" ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionDensityInfiniteSeries:
					proof=".ofEq (fun ξ ρ => Distribution.Atomic.density_constant_dirac_series ("~name(nodes[nodes[p.to].a].a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionDensityDirac:
					proof=".ofEq (fun ξ ρ => Distribution.model_density_dirac ("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionDensityAtomAdd:{
					auto sum=nodes[n.a];
					bool atomFirst=nodes[sum.a].op==BoundOp.distributionDirac;
					auto atom=nodes[atomFirst?sum.a:sum.b];
					proof=".ofEq (fun ξ ρ => Distribution.model_density_atom_add "~(atomFirst?"true":"false")~" "~densityProgram(result.integrals[p.extra].from)~" ("~name(atom.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				}
				case BindingRule.distributionDensityLebesgue:
					proof=".ofEq (fun ξ ρ => Distribution.model_density_lebesgueValue ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.distributionDensityWeight:
					proof=".ofEq (fun ξ ρ => Distribution.model_density_weight_lebesgueValue ("~name(nodes[n.a].a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.congr:
					if(n.op==BoundOp.conditional){ proof=".conditional "~proofName(p.left)~" "~proofName(p.right)~" "~proofName(p.extra); break; }
					if(n.op==BoundOp.fixed){ auto ty=leanType(types[n.type]); proof=".unary (a := .arrow "~ty~" "~ty~") (b := "~ty~") Recursion.fixedValue (.lam "~proofName(p.left)~")"; break; }
					auto generic=n.op>=BoundOp.distributionDirac||n.op==BoundOp.finiteSum||n.op==BoundOp.summation||n.op==BoundOp.limit||n.op==BoundOp.equal||n.op==BoundOp.typeEq||n.op==BoundOp.primitive||n.op==BoundOp.member||n.op==BoundOp.subset||n.op==BoundOp.domain||n.op==BoundOp.defined||n.op==BoundOp.holds||n.op==BoundOp.guard||n.op==BoundOp.pair||n.op==BoundOp.vectorCons||n.op==BoundOp.get||n.op==BoundOp.first||n.op==BoundOp.rest||n.op==BoundOp.tensor;
					auto op=generic?(n.b==uint.max?"unary":"binary"):
						n.op==BoundOp.lambda?"lam":n.op==BoundOp.set?"set":n.op==BoundOp.apply?"app":"seq";
					proof="."~op;
					if(generic){
						proof~=" (a := "~leanType(types[nodes[n.a].type])~")";
						if(n.b!=uint.max) proof~=" (b := "~leanType(types[nodes[n.b].type])~")";
						proof~=" ("~(n.b==uint.max?"b":"c")~" := "~leanType(types[n.type])~") "~valueOperation(n);
					}
					proof~=" "~proofName(p.left);
					if(p.right!=uint.max) proof~=" "~proofName(p.right); break;
			}
			code~="theorem p"~to!string(i)~dimDecl~" (γ : Binding.Globals) : Binding.Reduction "~name(p.from)~" "~name(p.to)~" := "~proof~"\n";
		}
		code~="theorem reduction"~dimDecl~" (γ : Binding.Globals) : Binding.Reduction "~name(result.input.id)~" "~name(result.output.id)~" := "~proofName(result.proof)~"\n";
		string left=replace(name(result.input.id)," δ γ"," ξ.natural γ")~".eval ξ ρ",right=replace(name(result.output.id)," δ γ"," ξ.natural γ")~".eval ξ ρ";
		auto ctx=replace(ctxName(node(result.input).context)," δ)"," ξ.natural)"),sizes=dependent_?" ξ.natural":"";
		code~="theorem sound (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctx~") : "~left~" = "~right~" := Binding.Reduction.sound (reduction"~sizes~" γ) ξ ρ\n";
		code~="theorem domain (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctx~") : Value.Defined ("~left~") ↔ Value.Defined ("~right~") := Binding.Reduction.defined (reduction"~sizes~" γ) ξ ρ\n";
		if(lowerResult){
			code~="theorem lowered (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctx~") : "~left~" = n"~to!string(lowered.id)~".eval ξ := Eq.trans (sound γ ξ ρ) rfl\n";
			code~="#qsym_check_axioms lowered\n";
		}
		return code~"#qsym_check_axioms sound\n#qsym_check_axioms domain\nend QSym.BindingCertificate\n";
	}
}
