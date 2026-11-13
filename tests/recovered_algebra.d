module recovered_algebra_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; bool domain; }
Example[] examples(){
	return [
		Example("QuadraticPower0","(1+sqrt(2))^0","1+0*sqrt(2)",[],false),
		Example("QuadraticPower1","(1+sqrt(2))^1","1+1*sqrt(2)",[],false),
		Example("QuadraticNegativePower1","(1+sqrt(2))^-1","-1--1*sqrt(2)",[],false),
		Example("QuadraticPower2","(1+sqrt(2))^2","3+2*sqrt(2)",[],false),
		Example("QuadraticNegativePower2","(1+sqrt(2))^-2","3-2*sqrt(2)",[],false),
		Example("QuadraticPower3","(1+sqrt(2))^3","7+5*sqrt(2)",[],false),
		Example("QuadraticNegativePower3","(1+sqrt(2))^-3","-7--5*sqrt(2)",[],false),
		Example("QuadraticPower4","(1+sqrt(2))^4","17+12*sqrt(2)",[],false),
		Example("QuadraticNegativePower4","(1+sqrt(2))^-4","17-12*sqrt(2)",[],false),
		Example("QuadraticPower8","(1+sqrt(2))^8","577+408*sqrt(2)",[],false),
		Example("QuadraticNegativePower8","(1+sqrt(2))^-8","577-408*sqrt(2)",[],false),
		Example("QuadraticPower16","(1+sqrt(2))^16","665857+470832*sqrt(2)",[],false),
		Example("QuadraticNegativePower16","(1+sqrt(2))^-16","665857-470832*sqrt(2)",[],false),
		Example("QuadraticPower32","(1+sqrt(2))^32","886731088897+627013566048*sqrt(2)",[],false),
		Example("QuadraticNegativePower32","(1+sqrt(2))^-32","886731088897-627013566048*sqrt(2)",[],false),
		Example("QuadraticPower64","(1+sqrt(2))^64","1572584048032918633353217+1111984844349868137938112*sqrt(2)",[],false),
		Example("QuadraticPower128","(1+sqrt(2))^128","4946041176255201878775086487573351061418968498177+3497379255757941172020851852070562919437964212608*sqrt(2)",[],false),
		Example("QuadraticProduct","(1+sqrt(2))*(1-sqrt(2))","-1",[],false),
		Example("QuadraticInverse","1/(1+sqrt(2))","sqrt(2)-1",[],false),
		Example("PairInverse","1/(sqrt(2)+sqrt(3))","sqrt(3)-sqrt(2)",[],false),
		Example("TripleSquare","(sqrt(2)+sqrt(3)+sqrt(5))^2","10+2*sqrt(6)+2*sqrt(10)+2*sqrt(15)",[],false),
		Example("TripleProduct","(sqrt(2)+sqrt(3)+sqrt(5))*(sqrt(2)+sqrt(3)-sqrt(5))","2*sqrt(6)",[],false),
		Example("TripleInverse","1/(sqrt(2)+sqrt(3)+sqrt(5))","sqrt(2)/4+sqrt(3)/6-sqrt(30)/12",[],false),
		Example("DependentTripleInverse","1/(sqrt(2)+sqrt(3)+sqrt(6))","(7*sqrt(2)+5*sqrt(3)-sqrt(6)-12)/23",[],false),
		Example("AffineTripleInverse","1/(1+sqrt(2)+sqrt(3)+sqrt(5))","(93-61*sqrt(2)-55*sqrt(3)+53*sqrt(5)+46*sqrt(6)-34*sqrt(10)-26*sqrt(15)+14*sqrt(30))/71",[],false),
		Example("QuadraticComplex","1/(1+sqrt(2)*ⅈ)","1/3-sqrt(2)*ⅈ/3",[],false),
		Example("ComplexTriple","1/(sqrt(2)+sqrt(3)+sqrt(5)*ⅈ)","sqrt(2)/19+3*sqrt(3)/38-5*sqrt(5)*ⅈ/38+sqrt(30)*ⅈ/38",[],false),
		Example("NegativeRadicand","csqrt(-2)^4","4",[],false),
		Example("RationalRootInverse","1/(sqrt(1/2)+sqrt(1/3))","3*sqrt(2)-2*sqrt(3)",[],false),
		Example("RepeatedRoot","1/(sqrt(2)+sqrt(8))","sqrt(2)/6",[],false),
		Example("ZeroPole","1/(sqrt(2)-sqrt(2))","1/0",[],false),
		Example("FalseMask","[false]/(sqrt(2)-sqrt(2))","0",[],false),
		Example("UndefinedGuard","[1/0=0]/(1+sqrt(2))","[1/0=0]*(sqrt(2)-1)",[],false),
		Example("GuardedTriple","[x>0]/(sqrt(2)+sqrt(3)+sqrt(5))","[x>0]*(sqrt(2)/4+sqrt(3)/6-sqrt(30)/12)",[],false),
		Example("PartialFactor","log(x)/(sqrt(2)+sqrt(3)+sqrt(5))","log(x)*(sqrt(2)/4+sqrt(3)/6-sqrt(30)/12)",[],false),
		Example("UnknownRoot","1/(sqrt(x)+sqrt(2))","1/(sqrt(x)+sqrt(2))",[],false),
		Example("FourthIndependent","1/(sqrt(2)+sqrt(3)+sqrt(5)+sqrt(7))","1/(sqrt(2)+sqrt(3)+sqrt(5)+sqrt(7))",[],false),
		Example("SqrtBase","sqrt(x)^t","x^(t/2)",[],false),
		Example("FractionExponents","x^(5/3)/x^(2/3)","x",[],false),
		Example("FractionNegativeExponents","x^(-2/3)/x^(-5/3)","x",[],false),
		Example("FractionSymbolic","x^y/x^t","x^(y-t)",[],false),
		Example("FractionComplex","cpow(z,w)/cpow(z,u)","cpow(z,w-u)",[],false),
		Example("FractionPartial","log(x)^y/log(x)^t","log(x)^(y-t)",[],false),
		Example("FractionGuard","[x<0]*(x^y/x^t)","[x<0]*x^(y-t)",[],false),
		Example("FractionZeroNumerator","0^3/2^3","0",[],false),
		Example("FractionZeroDenominator","0^3/0^2","0/0",[],false),
		Example("FractionZeroPower","0^y/0^0","0^y",[],false),
		Example("BoundedPower","(1+sqrt(2))^257","(1+sqrt(2))^257",[],false),
		Example("OuterFraction","(x^(1/3))^6","x^2",[],false),
		Example("EvenInner","(x^4)^(1/3)","abs(x)^(4/3)",[],false),
		Example("EvenInnerSymbolic","(x^2)^t","abs(x)^(2*t)",[],false),
		Example("EvenInnerPartial","(log(x)^2)^t","abs(log(x))^(2*t)",[],false),
		Example("NegativePowerOuter","((-2)^t)^3","(-2)^(3*t)",[],false),
		Example("PowerGuard","[x<0]*(x^2)^t","[x<0]*abs(x)^(2*t)",[],false),
		Example("NaturalOuterZero","(0^t)^3","0^(3*t)",[],false),
		Example("SqrtBasePartial","sqrt(log(x))^t","log(x)^(t/2)",[],false),
		Example("ComplexOuter","cpow(z,w)^3","cpow(z,3*w)",[],false),
		Example("ComplexRootOuter","cpow(z,1/3)^6","z^2",[],false),
		Example("ZeroExponentDenominator","x^0/0^0","1",[],false),
		Example("ZeroExponentQuotient","0^0/0^0","1",[],false),
		Example("NegativeBranchPreserved","((-2)^2)^(1/2)","2",[],false),
		Example("ComplexLowerCut","cpow(cpow(-1,-1),1/2)","ⅈ",[],false),
		Example("ComplexUpperCut","cpow(cpow(-1,1),1/2)","ⅈ",[],false),
		Example("ComplexBeyondCut","cpow(cpow(-1,2),1/2)","toℂ(1)",[],false),
		Example("PowerFalseMask","[false]*sqrt(log(-1))^t","0",[],false),
		Example("NonnegativeNested","(x^y)^t","x^(y*t)",["0≤x"],false),
		Example("SqrtPower","sqrt(x^t)","x^(t/2)",["0≤x"],false),
		Example("NaturalOuter","(x^t)^3","x^(3*t)",["0≤x"],false),
		Example("NaturalInner","(x^3)^t","x^(3*t)",["0≤x"],false),
		Example("PowerQuotient","x^t/y^t","(x/y)^t",["0<x","0<y"],false),
		Example("PowerSubtract","x^y/x^t","x^(y-t)",["0<x"],false),
		Example("ComplexSubtract","cpow(z,w)/cpow(z,u)","cpow(z,w-u)",["z≠0"],false),
		Example("InverseBase","(1/x)^t","1/x^t",["0≤x"],false),
		Example("ComplexNested","cpow(cpow(z,w),u)","cpow(z,w*u)",["z≠0","-π<cimag(clog(z)*w)","cimag(clog(z)*w)≤π"],false),
		Example("InverseDomain","1/(sqrt(2)+sqrt(3)+sqrt(5))","true",[],true),
		Example("ZeroPoleDomain","1/(sqrt(2)-sqrt(2))","false",[],true),
		Example("FalseMaskDomain","[false]/(sqrt(2)-sqrt(2))","true",[],true),
		Example("TrueMaskDomain","[true]/(sqrt(2)-sqrt(2))","false",[],true),
		Example("InvalidGuardDomain","[1/0=0]/(1+sqrt(2))","false",[],true),
		Example("UndefinedRadical","sqrt(-1)^3","false",[],true),
		Example("SqrtBaseDomain","sqrt(x)^(-1)","0<x",[],true),

	];
}
@system void main(string[] args){
	enforce(args.length==2,"usage: recovered-algebra-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; Syntax s; s.declare("x:ℝ,y:ℝ,t:ℝ,z:ℂ,w:ℂ,u:ℂ,p:𝔹");
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input); if(c.domain) input=definedness(a,input);
		auto expectedResult=simplify(a,s.parse(a,c.expected,a.sort(input)),facts);
		enforce(!expectedResult.exhausted,c.name~" expected normalization");
		auto expected=expectedResult.output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		enforce(!fast.exhausted&&fast.output==expected,c.name~": "~s.format(a,fast.output)~"; expected "~s.format(a,expected));
		enforce(fast.output==checked.output&&!checked.exhausted,c.name~" tracing");
		auto again=simplify(a,fast.output,facts);
		enforce(!again.exhausted&&again.output==fast.output,c.name~" idempotence");
		auto roundtrip=simplify(a,s.parse(a,s.format(a,fast.output),a.sort(fast.output)),facts);
		enforce(!roundtrip.exhausted&&roundtrip.output==fast.output,c.name~" round trip");
		write(buildPath(args[1],c.name~".lean"),exportLean(a,checked));
		writeln(c.name,": ",s.format(a,fast.output));
	}
	writeln("Checked ",examples().length," recovered-algebra cases and wrote certificates.");
}
