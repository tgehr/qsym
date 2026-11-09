module transcendental_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("FloorShift","floor(x+2)","floor(x)+int(2)"),
		Example("CeilShift","ceil(x-3)","ceil(x)+int(-3)"),
		Example("FloorSymbolicShift","floor(x+n)","floor(x)+n"),
		Example("CeilSymbolicShift","ceil(n+x)","ceil(x)+n"),
		Example("FloorManyShift","floor(x+y+7)","floor(x+y)+int(7)"),
		Example("FloorNeg","floor(-x)","-ceil(x)"),
		Example("CeilNeg","ceil(-x)","-floor(x)"),
		Example("FloorCast","floor(n)","n"),
		Example("CeilCast","ceil(n)","n"),
		Example("FloorFloor","floor(floor(x))","floor(x)"),
		Example("FloorCeil","floor(ceil(x))","ceil(x)"),
		Example("CeilFloor","ceil(floor(x))","floor(x)"),
		Example("CeilCeil","ceil(ceil(x))","ceil(x)"),
		Example("FloorLt","floor(x)<n","x<n"),
		Example("FloorLe","floor(x)≤n","x<toℝ(n)+1"),
		Example("LtFloor","n<floor(x)","toℝ(n)+1≤x"),
		Example("LeFloor","n≤floor(x)","n≤x"),
		Example("CeilLt","ceil(x)<n","x≤toℝ(n)-1"),
		Example("CeilLe","ceil(x)≤n","x≤n"),
		Example("LtCeil","n<ceil(x)","n<x"),
		Example("LeCeil","n≤ceil(x)","toℝ(n)-1<x"),
		Example("FloorLiteralBound","floor(x)≤3","x<4"),
		Example("CeilLiteralBound","2<ceil(x)","2<x"),
		Example("FloorEqual","[floor(x)=2]","[2≤x∧x<3]"),
		Example("CeilEqual","[ceil(x)=2]","[1<x∧x≤2]"),
		Example("FloorUnequal","floor(x)≠n","x<n∨toℝ(n)+1≤x"),
		Example("CeilUnequal","ceil(x)≠n","x≤toℝ(n)-1∨n<x"),
		Example("FloorBound","[floor(x)≤x]","1"),
		Example("CeilBound","[x≤ceil(x)]","1"),
		Example("FloorInterval","[floor(x)<3]*[3≤x]","0"),
		Example("CeilInterval","[ceil(x)≤3]*[3<x]","0"),
		Example("FloorPartial","floor(log(x)+2)","floor(log(x))+int(2)"),
		Example("FloorFractionRetained","floor(x+1/2)","floor(x+1/2)"),
		Example("FloorSumRetained","floor(x+y)","floor(x+y)"),
		Example("FloorPartialSumRetained","floor(x+1/0)","floor(x+1/0)"),
		Example("LogInverse","log(1/x)","-log(x)"),
		Example("LogSqrt","log(sqrt(x))","log(x)/2"),
		Example("LogOddPower","log(x^3)","3*log(x)"),
		Example("LogHighOddPower","log(x^101)","101*log(x)"),
		Example("LogEvenPower","log(x^8)","8*log(abs(x))"),
		Example("LogScale","log(2*x)","log(2)+log(x)"),
		Example("LogNonnegativeProduct","log(x*y)","log(x)+log(y)",["0≤x"]),
		Example("LogOtherProduct","log(x*y)","log(x)+log(y)",["0≤y"]),
		Example("LogProductRetained","log(x*y)","log(x*y)"),
		Example("LogRational","log(3/2)","log(3)-log(2)"),
		Example("LogReciprocalConstant","log(1/8)","-3*log(2)"),
		Example("LogExactRatio","log(8)/log(2)","3"),
		Example("LogRationalRatio","log(9)/log(27)","2/3"),
		Example("LogLargePower","log(2^32)/log(2)","32"),
		Example("LogOtherBase","log(144)/log(12)","2"),
		Example("LogRationalBase","log(81/16)/log(27/8)","4/3"),
		Example("LogUnrelated","log(3)/log(2)","log(3)/log(2)"),
		Example("LogZeroBaseRetained","log(8)/log(1)","3*log(2)/0"),
		Example("LogNegativeRetained","log(-8)","log(-8)"),
		Example("LogGuard","[x>0]*log(sqrt(x))","[x>0]*log(x)/2"),
		Example("LogMaskedUndefined","[false]*log(1/0)","0"),
		Example("ComplexLogReal","clog(toℂ(x))","toℂ(log(x))",["0<x"]),
		Example("ComplexLogRatio","clog(8)/clog(2)","toℂ(3)"),
		Example("ComplexLogNegativeRetained","clog(toℂ(x))","clog(toℂ(x))"),
		Example("ComplexLogScale","clog(2*z)","toℂ(log(2))+clog(z)"),
		Example("ComplexLogProductRetained","clog(z*w)","clog(z*w)"),
		Example("ComplexLogNegativeScaleRetained","clog(-2*z)","clog(-2*z)"),
		Example("ComplexLogInverse","clog(1/z)","-clog(z)",["carg(z)≠π"]),
		Example("ComplexLogInverseRetained","clog(1/z)","clog(1/z)"),
		Example("ComplexLogNegativeCut","clog(1/(-2))","clog(toℂ(-1/2))")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ,n:ℤ"); return s; }
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
	assert(!failures,"transcendental regressions");
}
unittest{
	foreach(trace;[false,true]){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=s.parse(a,"log(2^32)/log(2)");
		auto options=Options(DensityMode.preserve,trace); options.maxAlgebraWork=10_000;
		auto r=simplify(a,input,options);
		assert(!r.exhausted&&r.output==a.real_(32),"perfect-power search work");
		options.maxAlgebraWork=4;
		auto limited=simplify(a,input,options);
		assert(limited.exhausted,"perfect-power search must respect the work budget");
		if(trace) exportLean(a,limited);
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: transcendental-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote transcendental certificates.");
}
