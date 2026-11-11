module assumption_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("NaturalPartition","[p]*n+[¬p∧q]*n","[p∨q]*n"),
		Example("NaturalPartitionNot","[¬p]*n+[p∧q]*n","[¬p∨q]*n"),
		Example("NaturalPartitionReordered","[p]*n+[q∧¬p]*n","[p∨q]*n"),
		Example("NaturalIntersectionPartition","[p∧q]*n+[¬p∧q]*n","[q]*n"),
		Example("NaturalRightPartition","[p∧q]*n+[p∧¬q]*n","[p]*n"),
		Example("NaturalComplement","[p]*n+[¬p]*n","n"),
		Example("NaturalOverlap","[p∨q]*n+[p∧q]*n","[p]*n+[q]*n"),
		Example("NaturalSameMask","[p]*n+[p]*n","[p]*(2*n)"),
		Example("NaturalFalseRight","n*[false]","nat(0)"),
		Example("NaturalTrueRight","n*[true]","n"),
		Example("NaturalBracketRight","n*[p]","[p]*n"),
		Example("NaturalIndicatorPartition","([p]:ℕ)+([¬p∧q]:ℕ)","([p∨q]:ℕ)"),
		Example("IntegerPartition","[p]*k+[¬p∧q]*k","[p∨q]*k"),
		Example("IntegerPartitionNot","[¬p]*k+[p∧q]*k","[¬p∨q]*k"),
		Example("IntegerPartitionReordered","[p]*k+[q∧¬p]*k","[p∨q]*k"),
		Example("IntegerIntersectionPartition","[p∧q]*k+[¬p∧q]*k","[q]*k"),
		Example("IntegerRightPartition","[p∧q]*k+[p∧¬q]*k","[p]*k"),
		Example("IntegerComplement","[p]*k+[¬p]*k","k"),
		Example("IntegerOverlap","[p∨q]*k+[p∧q]*k","[p]*k+[q]*k"),
		Example("IntegerSameMask","[p]*k+[p]*k","[p]*(2*k)"),
		Example("IntegerFalseRight","k*[false]","int(0)"),
		Example("IntegerTrueRight","k*[true]","k"),
		Example("IntegerBracketRight","k*[p]","[p]*k"),
		Example("IntegerIndicatorPartition","([p]:ℤ)+([¬p∧q]:ℤ)","([p∨q]:ℤ)"),
		Example("RationalPartition","[p]*r+[¬p∧q]*r","[p∨q]*r"),
		Example("RationalPartitionNot","[¬p]*r+[p∧q]*r","[¬p∨q]*r"),
		Example("RationalPartitionReordered","[p]*r+[q∧¬p]*r","[p∨q]*r"),
		Example("RationalIntersectionPartition","[p∧q]*r+[¬p∧q]*r","[q]*r"),
		Example("RationalRightPartition","[p∧q]*r+[p∧¬q]*r","[p]*r"),
		Example("RationalComplement","[p]*r+[¬p]*r","r"),
		Example("RationalOverlap","[p∨q]*r+[p∧q]*r","[p]*r+[q]*r"),
		Example("RationalSameMask","[p]*r+[p]*r","[p]*(2*r)"),
		Example("RationalFalseRight","r*[false]","rat(0,1)"),
		Example("RationalTrueRight","r*[true]","r"),
		Example("RationalBracketRight","r*[p]","[p]*r"),
		Example("RationalIndicatorPartition","([p]:ℚ)+([¬p∧q]:ℚ)","([p∨q]:ℚ)"),
		Example("RealPartition","[p]*x+[¬p∧q]*x","[p∨q]*x"),
		Example("RealPartitionNot","[¬p]*x+[p∧q]*x","[¬p∨q]*x"),
		Example("RealPartitionReordered","[p]*x+[q∧¬p]*x","[p∨q]*x"),
		Example("RealIntersectionPartition","[p∧q]*x+[¬p∧q]*x","[q]*x"),
		Example("RealRightPartition","[p∧q]*x+[p∧¬q]*x","[p]*x"),
		Example("RealComplement","[p]*x+[¬p]*x","x"),
		Example("RealOverlap","[p∨q]*x+[p∧q]*x","[p]*x+[q]*x"),
		Example("RealSameMask","[p]*x+[p]*x","[p]*(2*x)"),
		Example("RealFalseRight","x*[false]","0"),
		Example("RealTrueRight","x*[true]","x"),
		Example("RealBracketRight","x*[p]","[p]*x"),
		Example("RealIndicatorPartition","([p]:ℝ)+([¬p∧q]:ℝ)","([p∨q]:ℝ)"),
		Example("ComplexPartition","[p]*z+[¬p∧q]*z","[p∨q]*z"),
		Example("ComplexPartitionNot","[¬p]*z+[p∧q]*z","[¬p∨q]*z"),
		Example("ComplexPartitionReordered","[p]*z+[q∧¬p]*z","[p∨q]*z"),
		Example("ComplexIntersectionPartition","[p∧q]*z+[¬p∧q]*z","[q]*z"),
		Example("ComplexRightPartition","[p∧q]*z+[p∧¬q]*z","[p]*z"),
		Example("ComplexComplement","[p]*z+[¬p]*z","z"),
		Example("ComplexOverlap","[p∨q]*z+[p∧q]*z","[p]*z+[q]*z"),
		Example("ComplexSameMask","[p]*z+[p]*z","[p]*(2*z)"),
		Example("ComplexFalseRight","z*[false]","toℂ(0)"),
		Example("ComplexTrueRight","z*[true]","z"),
		Example("ComplexBracketRight","z*[p]","[p]*z"),
		Example("ComplexIndicatorPartition","([p]:ℂ)+([¬p∧q]:ℂ)","([p∨q]:ℂ)"),
		Example("UserIndicators","[x=0]+[x≠0]*[y=0]","[x=0∨y=0]"),
		Example("UserIndicatorEquality","[x=0]+[x≠0]*[y=0]=[x=0∨y=0]","true"),
		Example("ReverseIndicatorEquality","[x=0∨y=0]=[x=0]+[x≠0]*[y=0]","true"),
		Example("WeightedUserIndicators","[x=0]*y+[x≠0]*[y=0]*y","[x=0]*y"),
		Example("GuardedPartialPartition","[p]*log(x)+[¬p∧q]*log(x)","[p∨q]*log(x)"),
		Example("GuardedPartialComplement","[p]*log(x)+[¬p]*log(x)","log(x)"),
		Example("PartialPredicatePartition","[log(x)<0]+[¬(log(x)<0)∧q]","[log(x)<0∨q]"),
		Example("DisjointIntervalIndicators","[x<0]+[x>1]","[x<0]+[x>1]"),
		Example("OverlappingIndicators","[x<1]+[x>0]","[x<1]+[x>0]"),
		Example("LogRightGuard","clog(z)*[z≠0]","[z≠0]*clog(z)"),
		Example("RealUnit","x^j=1","j=0∨x=1∨(x=-1∧inZ(j/2))"),
		Example("RealNotUnit","x^j≠1","¬(j=0∨x=1∨(x=-1∧inZ(j/2)))"),
		Example("RealNegativeUnit","x^j=-1","x=-1∧inZ((j-1)/2)"),
		Example("RealNotNegativeUnit","x^j≠-1","¬(x=-1∧inZ((j-1)/2))"),
		Example("RealUnitExponentNotOne","x^j=1","j=0∨x=1∨(x=-1∧inZ(j/2))",["j≠1"]),
		Example("RealUnitExponentNonzero","x^j=1","x=1∨(x=-1∧inZ(j/2))",["j≠0"]),
		Example("RealPositiveUnit","x^j=1","j=0∨x=1",["0<x"]),
		Example("RealNonintegerUnit","x^j=1","x=1",["¬inZ(j)"]),
		Example("RealUnitPartial","log(x)^j=1","j=0∨log(x)=1∨(log(x)=-1∧inZ(j/2))"),
		Example("RealMinusOnePower","(-1)^j=1","inZ(j/2)"),
		Example("ComplexRealUnit","z^j=1","j=0∨z=1∨(z=-1∧inZ(j/2))",["cimag(z)=0"]),
		Example("ComplexRealNotUnit","z^j≠1","¬(j=0∨z=1∨(z=-1∧inZ(j/2)))",["cimag(z)=0"]),
		Example("ComplexRealUnitNotOne","z^j=1","j=0∨z=1∨(z=-1∧inZ(j/2))",["cimag(z)=0", "j≠1"]),
		Example("ComplexRealUnitNonzero","z^j=1","z=1∨(z=-1∧inZ(j/2))",["cimag(z)=0", "j≠0"]),
		Example("ComplexNonnegativePower","z^j","toℂ(creal(z)^j)",["cimag(z)=0", "0≤creal(z)"]),
		Example("ComplexPositivePower","z^j","toℂ(creal(z)^j)",["cimag(z)=0", "0<creal(z)"]),
		Example("ComplexRealUnknownSign","z^j","z^j",["cimag(z)=0"]),
		Example("ComplexUnknownUnit","z^j=1","z^j=1"),
		Example("ComplexPowerNonzero","z^w≠0","z≠0∨w=0"),
		Example("ComplexPowerZero","z^w=0","z=0∧w≠0"),
		Example("RealLiteralUnit0Exp0","powerR(0,0)=1","true"),
		Example("RealLiteralUnit0Exp2","powerR(0,2)=1","false"),
		Example("RealLiteralUnit0Exp3","powerR(0,3)=1","false"),
		Example("RealLiteralUnit0ExpNeg2","powerR(0,-2)=1","false"),
		Example("RealLiteralUnit0ExpNeg3","powerR(0,-3)=1","false"),
		Example("RealLiteralUnit1Exp0","powerR(1,0)=1","true"),
		Example("RealLiteralUnit1Exp2","powerR(1,2)=1","true"),
		Example("RealLiteralUnit1Exp3","powerR(1,3)=1","true"),
		Example("RealLiteralUnit1ExpNeg2","powerR(1,-2)=1","true"),
		Example("RealLiteralUnit1ExpNeg3","powerR(1,-3)=1","true"),
		Example("RealLiteralUnitNeg1Exp0","powerR(-1,0)=1","true"),
		Example("RealLiteralUnitNeg1Exp2","powerR(-1,2)=1","true"),
		Example("RealLiteralUnitNeg1Exp3","powerR(-1,3)=1","false"),
		Example("RealLiteralUnitNeg1ExpNeg2","powerR(-1,-2)=1","true"),
		Example("RealLiteralUnitNeg1ExpNeg3","powerR(-1,-3)=1","false"),
		Example("RealLiteralUnit2Exp0","powerR(2,0)=1","true"),
		Example("RealLiteralUnit2Exp2","powerR(2,2)=1","false"),
		Example("RealLiteralUnit2Exp3","powerR(2,3)=1","false"),
		Example("RealLiteralUnit2ExpNeg2","powerR(2,-2)=1","false"),
		Example("RealLiteralUnit2ExpNeg3","powerR(2,-3)=1","false"),
		Example("RealLiteralUnitNeg2Exp0","powerR(-2,0)=1","true"),
		Example("RealLiteralUnitNeg2Exp2","powerR(-2,2)=1","false"),
		Example("RealLiteralUnitNeg2Exp3","powerR(-2,3)=1","false"),
		Example("RealLiteralUnitNeg2ExpNeg2","powerR(-2,-2)=1","false"),
		Example("RealLiteralUnitNeg2ExpNeg3","powerR(-2,-3)=1","false")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,j:ℝ,z:ℂ,w:ℂ,p:𝔹,q:𝔹,n:ℕ,k:ℤ,r:ℚ"); return s; }
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
	assert(!failures,"assumption and indicator regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: assumption-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,run(a,s.parse(a,c.input),facts,true)));
	}
	writeln("Wrote 115 assumption and indicator certificates.");
}
