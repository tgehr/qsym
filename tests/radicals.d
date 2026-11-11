module radical_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; size_t maxBytes; }
Example[] examples(){
	return [
		Example("SquareFactor","sqrt(72)","6*sqrt(2)"),
		Example("SquareFactorOdd","sqrt(98)","7*sqrt(2)"),
		Example("SquareFactorRational","sqrt(8/9)","2/3*sqrt(2)"),
		Example("SquareFactorDenominator","sqrt(3/50)","sqrt(6)/10"),
		Example("SquareFactorLarge","sqrt(1000003^2*2)","1000003*sqrt(2)"),
		Example("SquareFactorComplex","csqrt(72)","toℂ(6*sqrt(2))"),
		Example("SquareFactorImaginary","csqrt(-72)","6*sqrt(2)*ⅈ"),
		Example("SquareFactorSum","sqrt(72)+sqrt(98)","13*sqrt(2)"),
		Example("SquareFactorProduct","sqrt(18)*sqrt(12)","6*sqrt(6)"),
		Example("SquareFactorComparison","[sqrt(72)=6*sqrt(2)]","1"),
		Example("SquareFourth","sqrt(x^4)","x^2"),
		Example("SquareSixth","sqrt(x^6)","abs(x)^3"),
		Example("SquareEighth","sqrt(x^8)","x^4"),
		Example("SquareProduct","sqrt(x^2*y^2)","abs(x)*abs(y)"),
		Example("SquareMixedProduct","sqrt(x^4*y^6)","x^2*abs(y)^3"),
		Example("SquareShiftedProduct","sqrt(x^2*(y+1)^2)","abs(x)*abs(y+1)"),
		Example("SquareAssumption","sqrt(x^2*y)","abs(x)*sqrt(y)",["0≤y"]),
		Example("SquareGuard","[0≤y]*sqrt(x^2*y)","[0≤y]*abs(x)*sqrt(y)"),
		Example("SquareZeroNegative","sqrt(x^2*y)","0",["x=0","y=-1"]),
		Example("CubePower","cbrt(x^3)","x"),
		Example("CubeSixth","cbrt(x^6)","x^2"),
		Example("CubeNinth","cbrt(x^9)","x^3"),
		Example("CubeRootPower","cbrt(x)^3","x"),
		Example("CubeNegative","cbrt(-x)","-cbrt(x)"),
		Example("CubeProduct","cbrt(x)*cbrt(y)","cbrt(x*y)"),
		Example("CubeProductExact","cbrt(2)*cbrt(4)","2"),
		Example("CubeNegativeProduct","cbrt(-2)*cbrt(4)","-2"),
		Example("CubePartial","cbrt(log(x)^3)","log(x)"),
		Example("CubeGuard","[x<0]*cbrt(x^3)","[x<0]*x"),
		Example("CubeFactor","cbrt(54)","3*2^(1/3)"),
		Example("CubeFactorNegative","cbrt(-54)","-3*2^(1/3)"),
		Example("CubeFactorRational","cbrt(2/9)","6^(1/3)/3"),
		Example("FourthFactor","48^(1/4)","2*3^(1/4)"),
		Example("FourthFactorNumerator","48^(3/4)","8*3^(3/4)"),
		Example("FifthFactor","96^(1/5)","2*3^(1/5)"),
		Example("FifthFactorRational","(3/32)^(1/5)","3^(1/5)/2"),
		Example("MaskedUndefined","[false]*sqrt(-1)","0"),
		Example("ComplexBranch","csqrt(z^2)","csqrt(z^2)"),
		Example("RepeatedSumCompact","(x+1)*(x+1)","(x+1)^2"),
		Example("PhaseProductCompact","cis(π/6)*cis(-π/6)","toℂ(1)",[],35000),
		Example("PhaseNormCompact","cabs(cis(π/6))","1",[],15000),
		Example("PhasePowerCompact","exp(π*ⅈ/3)^6","toℂ(1)",[],60000)
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected,a.sort(input)),facts).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected),fast.exhausted?" (exhausted)":""); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		auto certificate=exportLean(a,checked);
		if(c.maxBytes&&certificate.length>c.maxBytes){
			writeln("FAIL ",c.name,": ",certificate.length," certificate bytes; limit ",c.maxBytes); ++failures;
		}
	}
	assert(!failures,"radical and enclosing-expression regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	auto branch=s.parse(a,"csqrt(z^2)");
	assert(simplify(a,branch).output==branch,"complex square root keeps its branch");
	auto t=a.call(Builtin.sqrtR,[a.real_(Rational(BigInt("170141183460469231731687303715884105727"),BigInt(1)))]);
	auto options=Options.init; options.maxAlgebraWork=20000;
	auto r=simplify(a,t,options);
	assert(!r.exhausted&&r.output==t,"bounded search on a large prime");
}
unittest{
	import qsym.generated.rules:Law,match,instantiate;
	auto owner=Session.open(); auto a=owner.arena; auto x=a.variable(Sort.real_,0);
	foreach(n;[0u,1u,2u,3u,4u,6u,9u,1000002u,uint.max]){
		auto t=a.call(Builtin.cbrtR,[a.pow(x,n)]); Term[] bindings;
		auto found=match(a,Law.real_cbrt_power,-1,t,bindings);
		assert(found==(n>=3&&n%3==0));
		if(found){
			assert(bindings==[x,a.real_((n-3)/3)]);
			assert(instantiate(a,Law.real_cbrt_power,bindings).before==t);
		}
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: radical-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length," radical certificates.");
}
