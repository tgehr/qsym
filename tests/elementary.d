module elementary_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce,assertThrown;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("ExpProduct","exp(x)*exp(y)","exp(x+y)"),
		Example("ExpNonAdjacent","exp(x)*t*exp(y)","t*exp(x+y)"),
		Example("ExpQuotient","exp(x)/exp(y)","exp(x-y)"),
		Example("ExpPower","exp(x)^3","exp(3*x)"),
		Example("ExpBase","e^x","exp(x)"),
		Example("AbsExp","abs(exp(x))","exp(x)"),
		Example("PositiveExp","0<exp(x)","true"),
		Example("LogProduct","log(x*y)","log(x)+log(y)",["x>0","y>0"]),
		Example("LogPower","log(x^3)","3*log(x)",["x>0"]),
		Example("LogSquare","log(x^2)","2*log(abs(x))"),
		Example("LogInverse","log(1/x)","-log(x)",["x>0"]),
		Example("LogRoot","log(sqrt(x))","log(x)/2",["x>0"]),
		Example("HalfPowerSquare","(x^(1/2))^2","x"),
		Example("ExactRoot","sqrt(81/16)","9/4"),
		Example("ExactCube","8^(1/3)","2"),
		Example("ExactFourth","(81/16)^(3/4)","27/8"),
		Example("PowerProduct","x^y*x^t","x^(y+t)",["x>0"]),
		Example("PowerNonAdjacent","x^y*exp(t)*x^t","exp(t)*x^(y+t)",["x>0"]),
		Example("NestedPower","(x^y)^t","x^(y*t)",["x>0"]),
		Example("OnePower","1^x","1"),
		Example("ZeroPower","0^x","0",["x>0"]),
		Example("Minimum","min(x,y)","x",["x≤y"]),
		Example("Maximum","max(x,y)","y",["x≤y"]),
		Example("SignPositive","sign(x)","int(1)",["x>0"]),
		Example("SignNegative","sign(x)","int(-1)",["x<0"]),
		Example("TrigIdentity","sin(x)^2+cos(x)^2","1"),
		Example("TrigNonAdjacent","sin(x)^2+y+cos(x)^2","y+1"),
		Example("ComplexTrigIdentity","sin(z)^2+cos(z)^2","complex(1,0)"),
		Example("OddSine","sin(-x)","-sin(x)"),
		Example("EvenCosine","cos(-x)","cos(x)"),
		Example("SinePi","sin(π)","0"),
		Example("CosineHalfPi","cos(π/2)","0"),
		Example("SineSixth","sin(π/6)","1/2"),
		Example("CosineQuarter","cos(π/4)","sqrt(2)/2"),
		Example("SinePeriod","sin(17*π/2)","1"),
		Example("NegativeSinePeriod","sin(-π/2)","-1"),
		Example("SymbolicSinePeriod","sin(x+6*π)","sin(x)"),
		Example("SymbolicCosinePeriod","cos(x-4*π)","cos(x)"),
		Example("SymbolicPhasePeriod","cis(x+8*π)","cis(x)"),
		Example("BigRoot","sqrt(2^200)","2^100"),
		Example("RationalCube","(8/27)^(1/3)","2/3"),
		Example("ZeroCube","0^(1/3)","0"),
		Example("TangentInverse","tan(atan(x))","x"),
		Example("SineInverse","sin(asin(x))","x"),
		Example("InverseSineRange","asin(sin(x))","x",["-π/2≤x","x≤π/2"]),
		Example("ComplexExpProduct","exp(z)*exp(w)","exp(z+w)"),
		Example("ComplexConjugateExp","conj(exp(z))","exp(conj(z))"),
		Example("RealPartProduct","creal(z*w)","creal(z)*creal(w)-cimag(z)*cimag(w)"),
		Example("ImaginaryPartProduct","cimag(z*w)","creal(z)*cimag(w)+cimag(z)*creal(w)"),
		Example("ComplexReconstruction","cfromri(creal(z),cimag(z))","z"),
		Example("ComplexNormProduct","cabs(z*w)","cabs(z)*cabs(w)"),
		Example("PhaseProduct","cis(x)*cis(y)","cis(x+y)"),
		Example("PhaseNorm","cabs(cis(x))","1"),
		Example("PhaseExp","cexp(ⅈ*x)","cis(x)"),
		Example("PhaseFullTurn","cexp(2*π*ⅈ)","complex(1,0)"),
		Example("AbsFact","abs(x)","x",["x≥0"]),
		Example("AbsNegativeFact","abs(x)","-x",["x≤0"]),
		Example("IntervalFact","abs(x-2)","2-x",["x<1"]),
		Example("RootFact","sqrt(x^2)","x",["x≥0"]),
		Example("NonzeroFact","[x≠0]/x","1/x",["x>0"]),
		Example("EqualityFact","x^2+1","10",["x=3"]),
		Example("AffineEqualityFact","x^2","9",["2*x+1=7"]),
		Example("EqualityChain","y^2","16",["x=3","y=x+1"]),
		Example("EqualitySymbolic","x-y","1",["x=y+1"]),
		Example("EqualityPartial","x","log(y)",["x=log(y)"]),
		Example("ComplexEquality","z^2","complex(0,2)",["z=1+ⅈ"]),
		Example("BooleanFact","[p]*x","x",["p"]),
		Example("ConjunctionFacts","abs(x)+abs(y)","x+y",["x≥0∧y≥0"]),
		Example("HyperbolicIdentity","cosh(x)^2-sinh(x)^2","1"),
		Example("LogNeedsFacts","log(x*y)","log(x*y)"),
		Example("NestedPowerNeedsFacts","(x^y)^t","(x^y)^t"),
		Example("NegativePowerBranch","((-1)^y)^t","((-1)^y)^t"),
		Example("NonlinearFact","x","x",["x^2=4"]),
		Example("DisjunctiveFact","x","x",["x=3∨p"]),
		Example("PartialDisjunct","x","x",["x=log(-1)∨p"]),
		Example("EqualityCycle","x-y","0",["x=y","y=x"]),
		Example("EqualityReverseOrder","y^2","16",["y=x+1","x=3"]),
		Example("AffineSystem","x^2+y^2","2",["2*x+3*y=5","y=1"]),
		Example("ExternalAndScoped","abs(x)+[x<0]*abs(x)","x",["x≥0"]),
		Example("GuardedPartialFact","[p]*x","[p]*log(y)",["x=log(y)"])
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,t:ℝ,z:ℂ,w:ℂ,p:𝔹"); return s; }
private Result run(Arena a,Term t,Term[] facts,bool trace=false){
	return simplify(a,t,facts,Options(DensityMode.preserve,trace));
}
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected,a.sort(input))).output;
		auto fast=run(a,input,facts),checked=run(a,input,facts,true);
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(run(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"elementary simplification regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	auto x=s.parse(a,"x"),abs=s.parse(a,"abs(x)"),positive=s.parse(a,"x>0");
	assert(run(a,abs,[positive]).output==x);
	assert(simplify(a,abs).output==abs); // assumptions never escape a call
	assert(run(a,abs,[s.parse(a,"x<0")]).output==simplify(a,s.parse(a,"-x")).output);
	assertThrown(simplify(a,x,[x]));
	auto other=Session.open(); assertThrown(simplify(a,x,[other.arena.boolean(true)]));
	foreach(work;[size_t(0),1,20]){
		auto options=Options(DensityMode.preserve,true); options.maxAlgebraWork=work;
		auto facts=[positive,s.parse(a,"y>0"),s.parse(a,"t>0")];
		auto limited=simplify(a,abs,facts,options);
		assert(limited.exhausted&&limited.assumptions==facts);
		exportLean(a,limited);
	}
	auto checked=run(a,abs,[positive],true);
	auto plain=run(a,x,[],true);
	assertThrown(exportEquivalence(a,checked,plain));
	auto changed=checked; changed.assumptions=[];
	assertThrown(exportLean(a,changed));
	assert(equivalent(a,abs,x,[positive])==Equivalence.agreeOnCommonDomain);
	assert(equivalent(a,abs,x)==Equivalence.unknown);
}
@system void main(string[] args){
	enforce(args.length==2,"usage: elementary-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,run(a,s.parse(a,c.input),facts,true)));
	}
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	auto x=s.parse(a,"x"),abs=s.parse(a,"abs(x)"),positive=s.parse(a,"x>0");
	write(buildPath(args[1],"ConditionalEquivalence.lean"),exportEquivalence(a,run(a,abs,[positive],true),run(a,x,[positive],true)));
	auto options=Options(DensityMode.preserve,true); options.maxAlgebraWork=0;
	write(buildPath(args[1],"ExhaustedFacts.lean"),exportLean(a,simplify(a,abs,[positive,s.parse(a,"y>0")],options)));
	writeln("Wrote elementary certificates.");
}
