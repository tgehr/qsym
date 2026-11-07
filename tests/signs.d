module sign_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("OddNegative","[x^3<0]","[x<0]"),
		Example("OddNonpositive","[x^3≤0]","[x≤0]"),
		Example("OddPositive","[0<x^5]","[0<x]"),
		Example("OddNonnegative","[0≤x^5]","[0≤x]"),
		Example("OddLarge","x^1000001≤0","x≤0"),
		Example("OddShifted","(x-2)^5≤0","x≤2"),
		Example("OddPartial","log(x)^3≤0","x≤1"),
		Example("OddInverse","x^-3<0","x<0"),
		Example("OddFact","x≤0","true",["x^3≤0"]),
		Example("OddGuard","[x^3≤0]*abs(x)","[x≤0]*(-x)"),
		Example("EvenNegative","x^6<0","false"),
		Example("EvenNonpositive","x^6≤0","x=0"),
		Example("EvenPositive","0<x^6","x≠0"),
		Example("EvenNonnegative","0≤x^6","true"),
		Example("ZeroExponent","x^0≤0","false"),
		Example("OddUnit","x^3<1","x<1"),
		Example("OddLargeUnit","x^1000001≤1","x≤1"),
		Example("OddBound","x^3<8","x<2"),
		Example("OddClosedBound","x^5≤32","x≤2"),
		Example("OddNegativeBound","x^5≤-32","x≤-2"),
		Example("OddLowerBound","-8<x^3","-2<x"),
		Example("OddClosedLower","-8≤x^3","-2≤x"),
		Example("OddRationalBound","x^3<1/8","x<1/2"),
		Example("OddShiftedBound","(x+1)^3<8","x<1"),
		Example("EvenUnit","x^4≤1","-1≤x∧x≤1"),
		Example("EvenBound","x^4<16","-2<x∧x<2"),
		Example("EvenClosedBound","x^6≤64","-2≤x∧x≤2"),
		Example("EvenOutside","16<x^4","x<-2∨2<x"),
		Example("EvenOutsideClosed","16≤x^4","x≤-2∨2≤x"),
		Example("EvenRationalBound","x^4≤1/16","-1/2≤x∧x≤1/2"),
		Example("EvenNegativeBound","x^4≤-1","false"),
		Example("PartialBound","log(x)^3<8","log(x)<2"),
		Example("UnknownBound","x^3<2","x^3<2"),
		Example("OddProduct","x^3*y≤0","x*y≤0"),
		Example("OddProductStrict","x^3*y<0","x*y<0"),
		Example("OddProductPositive","0<x^3*y","0<x*y"),
		Example("OddProductNonnegative","0≤x^3*y","0≤x*y"),
		Example("OddProductRight","x*y^5≤0","x*y≤0"),
		Example("EvenProduct","x^4*y≤0","x=0∨y≤0"),
		Example("EvenProductStrict","x^4*y<0","x≠0∧y<0"),
		Example("EvenProductPositive","0<x^4*y","x≠0∧0<y"),
		Example("EvenProductNonnegative","0≤x^4*y","x=0∨0≤y"),
		Example("EvenProductRight","x*y^6≤0","y=0∨x≤0"),
		Example("PartialProduct","log(x)^4*y≤0","x=1∨y≤0"),
		Example("CommonFactor","x^3-x=0","x=0∨(x=-1∨x=1)"),
		Example("CommonPositive","x^3+x<0","x<0"),
		Example("MonomialCollection","(x+1)*(x^2-x+1)=x^3+1","true"),
		Example("CommonNonpositive","x^3+x≤0","x≤0"),
		Example("CommonEven","x^4≤x^2","-1≤x∧x≤1"),
		Example("CommonComplex","z^3-z=0","z=0∨(z=-1∨z=1)"),
		Example("CommonImaginary","z^3+z=0","z=0∨(z=-ⅈ∨z=ⅈ)")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ"); return s; }
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
	}
	assert(!failures,"power/sign regressions");
}
unittest{
	foreach(trace;[false,true]) foreach(source;["x^1000001≤0","x^3+x<0","x^3-x=0","z^3+z=0"]){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto options=Options(DensityMode.preserve,trace); options.maxAlgebraWork=100_000;
		assert(!simplify(a,s.parse(a,source),options).exhausted,source~" exceeds the power/sign work budget");
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: sign-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote power/sign certificates.");
}
