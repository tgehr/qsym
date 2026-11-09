module power_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("ThirdLt","x^(1/3)<y^(1/3)","x<y"),
		Example("ThirdLe","x^(1/3)≤y^(1/3)","x≤y"),
		Example("ThirdEq","x^(1/3)=y^(1/3)","x=y"),
		Example("ThirdNe","x^(1/3)≠y^(1/3)","x≠y"),
		Example("FiveThirds","x^(5/3)<y^(5/3)","x<y"),
		Example("NegativeThirdLt","x^(-1/3)<y^(-1/3)","y<x"),
		Example("NegativeThirdLe","x^(-1/3)≤y^(-1/3)","y≤x"),
		Example("NegativeThirdEq","x^(-1/3)=y^(-1/3)","x=y"),
		Example("NegativeThirdNe","x^(-1/3)≠y^(-1/3)","x≠y"),
		Example("NegativeFiveThirds","x^(-5/3)<y^(-5/3)","y<x"),
		Example("SymbolicNonintegerLt","x^t<y^t","x<y",["¬inZ(t)","0<t"]),
		Example("SymbolicNonintegerLe","x^t≤y^t","x≤y",["¬inZ(t)","0<t"]),
		Example("SymbolicNonintegerNegative","x^t<y^t","y<x",["¬inZ(t)","t<0"]),
		Example("SymbolicNonintegerNegativeLe","x^t≤y^t","y≤x",["¬inZ(t)","t<0"]),
		Example("SymbolicNonintegerEq","x^t=y^t","x=y",["¬inZ(t)"]),
		Example("NonnegativeLt","x^t<y^t","x<y",["0≤x","0≤y","0<t"]),
		Example("NonnegativeLe","x^t≤y^t","x≤y",["0≤x","0≤y","0<t"]),
		Example("NonnegativeNegativeLt","x^t<y^t","y<x",["0≤x","0≤y","t<0"]),
		Example("NonnegativeNegativeLe","x^t≤y^t","y≤x",["0≤x","0≤y","t<0"]),
		Example("NonnegativeNe","x^t≠y^t","x≠y",["0≤x","0≤y","t≠0"]),
		Example("PositiveLt","x^t<y^t","x<y",["0<x","0<y","0<t"]),
		Example("UnknownSignRetained","x^t<y^t","x^t<y^t",["0<x","0<y"]),
		Example("UnknownBasesRetained","x^t<y^t","x^t<y^t",["0<t"]),
		Example("DifferentPowersRetained","x^(1/3)<y^(2/3)","x^(1/3)<y^(2/3)"),
		Example("ZeroExponentLt","x^0<y^0","false"),
		Example("ZeroExponentEq","x^0=y^0","true"),
		Example("EvenNegativeCounterexample","(-2)^2<(-1)^2","false"),
		Example("PartialBases","log(x)^(1/3)<log(y)^(1/3)","x<y"),
		Example("MaskedUndefined","[false]*[log(-1)^(1/3)<x^(1/3)]","0"),
		Example("GuardedPower","[0≤x]*[0≤y]*[x^t<y^t]","[0≤x]*[0≤y]*[x<y]",["0<t"]),
		Example("ComputedExponent","x^(1/6+1/6)<y^(1/3)","x<y"),
		Example("SqrtBases","sqrt(x)^t<sqrt(y)^t","x<y",["0<t"]),
		Example("AbsBases","abs(x)^t≤abs(y)^t","abs(x)≤abs(y)",["0<t"]),
		Example("NormBases","cabs(z)^t<cabs(w)^t","cabs(z)<cabs(w)",["0<t"]),
		Example("NormPower","cabs(cpow(z,t))<cabs(cpow(w,t))","cabs(z)<cabs(w)",["0<t"]),
		Example("NormNegativePower","cabs(cpow(z,t))≤cabs(cpow(w,t))","cabs(w)≤cabs(z)",["t<0"]),
		Example("NonnegativePower","[0≤x^t]","1",["0≤x"]),
		Example("PositivePower","[0<x^t]","1",["0<x"]),
		Example("PositiveInverseLt","1/x<1/y","y<x",["0≤x","0≤y"]),
		Example("PositiveInverseLe","1/x≤1/y","y≤x",["0≤x","0≤y"]),
		Example("NegativeInverseLt","1/x<1/y","y<x",["x≤0","y≤0"]),
		Example("NegativeInverseLe","1/x≤1/y","y≤x",["x≤0","y≤0"]),
		Example("InverseUnknownRetained","1/x<1/y","1/x<1/y"),
		Example("InverseMixedCounterexample","1/(-1)<1/2","true"),
		Example("ComplexThirdEq","cpow(z,1/3)=cpow(w,1/3)","z=w"),
		Example("ComplexThirdNe","cpow(z,1/3)≠cpow(w,1/3)","z≠w"),
		Example("ComplexTwoThirds","cpow(z,2/3)=cpow(w,2/3)","z=w"),
		Example("ComplexNegativeThirdEq","cpow(z,-1/3)=cpow(w,-1/3)","z=w"),
		Example("ComplexNegativeThirdNe","cpow(z,-1/3)≠cpow(w,-1/3)","z≠w"),
		Example("ComplexSymbolicPower","cpow(z,t)=cpow(w,t)","z=w",["0<t","t≤1"]),
		Example("ComplexSymbolicNegative","cpow(z,t)=cpow(w,t)","z=w",["-1≤t","t<0"]),
		Example("ComplexLargePowerRetained","cpow(z,3/2)=cpow(w,3/2)","cpow(z,3/2)=cpow(w,3/2)"),
		Example("ComplexNegativeLargeRetained","cpow(z,-3/2)=cpow(w,-3/2)","cpow(z,-3/2)=cpow(w,-3/2)"),
		Example("ComplexImaginaryRetained","cpow(z,ⅈ)=cpow(w,ⅈ)","cpow(z,ⅈ)=cpow(w,ⅈ)"),
		Example("ComplexZeroPower","cpow(z,0)=cpow(w,0)","true"),
		Example("ComplexZeroBoundary","cpow(z,1/3)=cpow(0,1/3)","z=0"),
		Example("ComplexCutBoundary","cpow(-1,1/3)=cpow(1,1/3)","false"),
		Example("RealBaseInjective","2^x=2^y","x=y"),
		Example("RealSmallBaseInjective","(1/2)^x≠(1/2)^y","x≠y"),
		Example("RealSymbolicBaseInjective","t^x=t^y","x=y",["0<t","t≠1"]),
		Example("RealUnitBase","1^x=1^y","true"),
		Example("RealZeroBaseCounterexample","0^2=0^3","true")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,t:ℝ,z:ℂ,w:ℂ"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected),facts).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected),fast.exhausted?" (exhausted)":""); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"power comparison regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: power-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote power comparison certificates.");
}
