module discrete_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; }
Example[] examples(){
	Example[] result;
	foreach(vars;[["Natural","n","m","l","nat(0)","nat(1)"],
		["Integer","i","j","k","int(0)","int(1)"],
		["Rational","q","r","s","rat(0,1)","rat(1,1)"]]){
		auto x=vars[1],y=vars[2],z=vars[3];
		void add(string name,string input,string expected){ result~=Example(vars[0]~name,input,expected); }
		add("Double",x~"+"~x,"2*"~x);
		add("Collect","2*"~x~"+3*"~x,"5*"~x);
		add("CollectLeft",x~"+3*"~x,"4*"~x);
		add("CollectRight","3*"~x~"+"~x,"4*"~x);
		add("NestedCoefficient","2*(3*"~x~")","6*"~x);
		add("RepeatedCoefficient","2*(3*(4*"~x~"))","24*"~x);
		add("Square",x~"*"~x,x~"^2");
		add("PowerProduct",x~"^3*"~x~"^4",x~"^7");
		add("PowerLeft",x~"*"~x~"^3",x~"^4");
		add("PowerRight",x~"^3*"~x,x~"^4");
		add("PowerChain","("~x~"^2)^3",x~"^6");
		add("PowerRepeated","("~x~"*"~x~")*("~x~"*"~x~")",x~"^4");
		add("ZeroPowerProduct",x~"^0*"~x~"^3",x~"^3");
		add("NonzeroProduct",x~"*"~y~"≠0",x~"≠0∧"~y~"≠0");
		add("NonzeroPower",x~"^3≠0",x~"≠0");
		add("StrictSelf",x~"<"~x,"false");
		add("WeakSelf",x~"≤"~x,"true");
		add("StrictCommon",x~"+"~y~"<"~x~"+"~z,y~"<"~z);
		add("WeakCommon",x~"+"~y~"≤"~x~"+"~z,y~"≤"~z);
		add("StrictCommonConstants",x~"+1<"~x~"+2","true");
		add("WeakCommonConstants",x~"+2≤"~x~"+1","false");
		add("MaskedCollection","[p]*(2*"~x~"+3*"~x~")","[p]*(5*"~x~")");
		add("MaskedZero","[false]*("~x~"^3*"~x~"^4)",vars[4]);
		add("GuardZero","[p]*"~vars[4],vars[4]);
		add("PartialGuardZero","[log(x)<0]*"~vars[4],vars[4]);
		add("UndefinedGuardZero","[log(0)<0]*"~vars[4],vars[4]);
		add("ZeroPower","("~x~"^2)^0",vars[5]);
	}
	result~=[
		Example("IntegerCancellation","i-i","int(0)"),
		Example("IntegerNegativeCancellation","-i+i","int(0)"),
		Example("IntegerDoubleNegation","-(-i)","i"),
		Example("IntegerNegativeCollection","2*i-3*i","-i"),
		Example("RationalCancellation","q-q","rat(0,1)"),
		Example("RationalNegativeCancellation","-q+q","rat(0,1)"),
		Example("RationalDoubleNegation","-(-q)","q"),
		Example("RationalFractionalCollection","rat(1,2)*q+rat(1,3)*q","rat(5,6)*q"),
		Example("RationalSelfDivision","q/q","rat(1,1)"),
		Example("RationalInverseProduct","q⁻¹*q","rat(1,1)"),
		Example("RationalInverseNonzero","q⁻¹≠0","true"),
		Example("RationalCancelFactor","(q*r)/q","r"),
		Example("RationalCancelRightFactor","(q*r)/r","q"),
		Example("RationalGuardedCancellation","[q≠0]*(q/q)","[q≠0]*rat(1,1)"),
		Example("RationalMaskedUndefined","[false]*(q/rat(0,1))","rat(0,1)"),
		Example("RationalPartialCancellation","q⁻¹-q⁻¹","rat(0,1)"),
		Example("RationalPartialPower","(q⁻¹)^3*(q⁻¹)^4","(q⁻¹)^7"),
		Example("FloorCeilingCancellation","floor(x)+ceil(-x)","int(0)"),
		Example("CeilingFloorCancellation","ceil(x)+floor(-x)","int(0)"),
		Example("FloorCollection","2*floor(x)+3*floor(x)","5*floor(x)"),
		Example("FloorPartialCancellation","floor(log(x))-floor(log(x))","int(0)"),
		Example("FloorPartialComparison","floor(log(x))<floor(log(x))","false"),
		Example("FloorPowerProduct","floor(x)^2*floor(x)^3","floor(x)^5"),
		Example("NaturalPartialCancellation","denominator(qfromnd(i,0))<denominator(qfromnd(i,0))","false"),
		Example("NaturalPartialPower","denominator(qfromnd(i,0))^3*denominator(qfromnd(i,0))^4","denominator(qfromnd(i,0))^7"),
		Example("GuardedFloorPartial","[x>0]*(floor(log(x))-floor(log(x)))","int(0)"),
		Example("IntegerWrongPowerUnchanged","i^2","i^2"),
		Example("RationalPoleUnchanged","rat(0,1)⁻¹","rat(0,1)⁻¹")
	];
	return result;
}
private Syntax syntax(){ Syntax s; s.declare("n:ℕ,m:ℕ,l:ℕ,i:ℤ,j:ℤ,k:ℤ,q:ℚ,r:ℚ,s:ℚ,x:ℝ,p:𝔹"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=s.parse(a,c.input),expected=c.input==c.expected?input:simplify(a,s.parse(a,c.expected)).output;
		auto fast=simplify(a,input),checked=simplify(a,input,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected),fast.exhausted?" (exhausted)":""); ++failures;
		}
		assert(a.sort(fast.output)==a.sort(input),c.name~" changed type");
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"discrete scalar regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena;
	foreach(s;[Sort.natural,Sort.integer,Sort.rational]){
		auto x=a.variable(s,0),large=a.pow(x,uint.max);
		foreach(t;[a.mul(large,x),a.mul(x,large),a.mul(large,large),a.pow(large,2)]){
			auto fast=simplify(a,t),checked=simplify(a,t,Options(DensityMode.preserve,true));
			assert(fast.exhausted&&fast.output==t,"oversized exponent must leave the term intact");
			assert(checked.exhausted&&checked.output==t);
			exportLean(a,checked);
		}
		auto boundary=a.mul(a.pow(x,uint.max-1),x);
		auto r=simplify(a,boundary);
		assert(!r.exhausted&&r.output==large,"largest supported exponent");
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: discrete-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length," discrete scalar certificates.");
}
