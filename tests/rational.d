module rational_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("ReciprocalQuadratic","[1/(x^2-x-1)=2]","[x=(1-sqrt(7))/2∨x=(1+sqrt(7))/2]"),
		Example("ReciprocalRepeatedRoot","1/(x^2-2*x+2)=1","x=1"),
		Example("ReciprocalNoRealRoot","1/(x^2+1)=2","false"),
		Example("ReciprocalZero","1/x=0","false"),
		Example("ReciprocalReverse","2=1/(x^2-x-1)","x=(1-sqrt(7))/2∨x=(1+sqrt(7))/2"),
		Example("ReciprocalSymbolic","1/x=y","1=x*y"),
		Example("QuotientLinear","x/(x+1)=2","x=-2"),
		Example("QuotientQuadratic","(x+1)/(x^2+1)=1","x=0∨x=1"),
		Example("QuotientZero","(x+1)/(x^2+1)=0","x=-1"),
		Example("QuotientSymbolic","x/y=t","x=y*t"),
		Example("TwoReciprocals","1/x=1/y","x=y"),
		Example("TwoQuotients","x/(x+1)=(x-1)/(x+2)","x=-1/2"),
		Example("ReciprocalDisequality","[1/(x^2+1)≠2]","1"),
		Example("ReciprocalFact","x","-2",["1/(x+1)=-1"]),
		Example("ComplexReciprocal","1/(z^2+1)=2","z=-csqrt(-1/2)∨z=csqrt(-1/2)"),
		Example("ComplexQuotient","z/(z+1)=ⅈ","z=(-1+ⅈ)/2"),
		Example("ComplexSymbolic","z/w=ⅈ","z=ⅈ*w"),
		Example("ComplexZero","1/z=0","false"),
		Example("PartialReciprocal","1/log(x)=2","x=exp(1/2)"),
		Example("MaskedPole","[x≠0]*[1/x=2]","[x=1/2]"),
		Example("DeadPole","[false]*[1/0=2]","0"),
		Example("ZeroNumerator","0/(x+1)=2","false"),
		Example("GuardedUndefined","[x=0]*[1/x=2]","[x=0]*[x=1/2]"),
		Example("MaskedNumeratorPole","([x=0]/x+1)≠0","true")
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
	}
	assert(!failures,"rational guard regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: rational-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote rational guard certificates.");
}
