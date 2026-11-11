module numeral_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce,assertThrown;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	Example[] result=[
		Example("DecimalSum","0.1+0.2","rat(3,10)"),
		Example("DecimalDifference","0.3-0.2","rat(1,10)"),
		Example("DecimalProduct","1.25*0.08","rat(1,10)"),
		Example("DecimalQuotient",".125/.25","rat(1,2)"),
		Example("DecimalScientific","1.25e-2","rat(1,80)"),
		Example("DecimalPositiveExponent","2.5E+2","rat(250,1)"),
		Example("DecimalNegative","-.125","rat(-1,8)"),
		Example("DecimalIntegral","2.0","rat(2,1)"),
		Example("DecimalLeadingZeros","0000.000125","rat(1,8000)"),
		Example("DecimalCancellation","0.1+0.2-0.3","rat(0,1)"),
		Example("DecimalAdjacency","0.5x+0.5x","x"),
		Example("DecimalNegativeAdjacency","-0.5x+1.5x","x"),
		Example("DecimalScientificAdjacency","-1e-3q+2e-3q","rat(1,1000)*q"),
		Example("DecimalRationalAdjacency",".5q+.5q","q"),
		Example("DecimalFloor","floor(-1.1)","int(-2)"),
		Example("DecimalCeil","ceil(-1.1)","int(-1)"),
		Example("DecimalPower","0.2^3","rat(1,125)"),
		Example("DecimalRealContext","x+0.1+0.2","x+real(3,10)"),
		Example("RealRationalZero","toℝ(q)=0","q=0"),
		Example("RealRationalEquality","toℝ(q)=toℝ(r)","q=r"),
		Example("RealRationalInequality","toℝ(q)≠toℝ(r)","q≠r"),
		Example("RealRationalOrder","toℝ(q)<toℝ(r)","q<r"),
		Example("RealRationalBound","toℝ(q)≤1/2","q≤1/2"),
		Example("RealRationalIntegrality","inZ(toℝ(q)/2)","denominator(q/2)=1"),
		Example("RationalIntegerDenominator","denominator(toℚ(k))","nat(1)"),
		Example("RationalNaturalDenominator","denominator(toℚ(n))","nat(1)"),
		Example("RealIntegerOrder","toℝ(k)≤toℝ(j)","k≤j"),
		Example("RealIntegerZero","toℝ(k)=0","k=0"),
		Example("ComplexRationalEquality","toℂ(q)=toℂ(r)","q=r"),
		Example("ComplexRationalPartialEquality","toℂ(q⁻¹)=toℂ(r)","q⁻¹=r"),
		Example("EmbeddedSum","toℝ(q)+toℝ(r)=toℝ(q+r)","true"),
		Example("EmbeddedProduct","toℝ(q)*toℝ(r)=toℝ(q*r)","true"),
		Example("EmbeddedPower","toℝ(q)^3=toℝ(q^3)","true"),
		Example("EmbeddedInverse","toℝ(q)⁻¹=toℝ(q⁻¹)","true"),
		Example("EmbeddedMask","[p]*toℝ(q)=toℝ([p]*q)","true"),
		Example("EmbeddedNaturalProduct","toℤ(n)*toℤ(m)=toℤ(n*m)","true"),
		Example("EmbeddedFractionalBound","toℝ(k)<1/2","toℚ(k)<1/2"),
		Example("EmbeddedNegativeBound","toℝ(n)<-1","toℤ(n)<-1"),
		Example("RationalUnit","x^q=1","q=0∨x=1∨(x=-1∧denominator(q/2)=1)"),
		Example("ExplicitRealExponent","x^toℝ(q)=1","q=0∨x=1∨(x=-1∧denominator(q/2)=1)"),
		Example("UnknownComplexUnit","z^n=1","z^n=1"),
		Example("UnknownComplexIntegerUnit","z^k=1","z^k=1")
	];
	foreach(row;[["ZN","ℤ","n"],["QN","ℚ","n"],["RN","ℝ","n"],["QZ","ℚ","k"],["RZ","ℝ","k"]]){
		auto f="pow"~row[0],v=row[1]=="ℤ"?"j":row[1]=="ℚ"?"q":"x",n=row[2];
		auto even="denominator(toℚ("~n~")/2)=1",odd="denominator((toℚ("~n~")-1)/2)=1";
		auto positive=n~"=0∨"~v~"=1∨("~v~"=-1∧"~even~")",negative=v~"=-1∧"~odd;
		result~=Example(row[0]~"Unit",f~"("~v~","~n~")=1",positive);
		result~=Example(row[0]~"NotUnit",f~"("~v~","~n~")≠1","¬("~positive~")");
		result~=Example(row[0]~"NegativeUnit",f~"("~v~","~n~")=-1",negative);
		result~=Example(row[0]~"NotNegativeUnit",f~"("~v~","~n~")≠-1","¬("~negative~")");
	}
	foreach(n;["n","k"]){
		auto expected=n~"=0∨z=1∨(z=-1∧denominator(toℚ("~n~")/2)=1)";
		result~=Example("ComplexUnit"~n,"z^"~n~"=1",expected,["cimag(z)=0"]);
		result~=Example("ComplexNotUnit"~n,"z^"~n~"≠1","¬("~expected~")",["cimag(z)=0"]);
		result~=Example("PartialRealBase"~n,"log(x)^"~n~"=1",n~"=0∨log(x)=1∨(log(x)=-1∧denominator(toℚ("~n~")/2)=1)");
	}
	return result;
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,q:ℚ,r:ℚ,j:ℤ,k:ℤ,n:ℕ,m:ℕ,p:𝔹"); return s; }
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	foreach(source;["0","1","123","1+2","2*3","2^3","2^3^2","2^(1+2)"]) assert(a.sort(s.parse(a,source))==Sort.natural,source);
	foreach(source;["-1","1-2","-2*3"]) assert(a.sort(s.parse(a,source))==Sort.integer,source);
	foreach(source;["1/2","1.0",".5","2.","2e3","3E-2","-0.125"]) assert(a.sort(s.parse(a,source))==Sort.rational,source);
	assert(a.sort(s.parse(a,"0.1+x"))==Sort.real_);
	assert(a.sort(s.parse(a,"0.1+z"))==Sort.complex);
	assert(a.sort(s.parse(a,"[p]"))==Sort.real_);
	assert(s.format(a,simplify(a,s.parse(a,"x/2=toℝ(floor(x/2))")).output)=="x·(1/2)=floor(x·(1/2))");
	foreach(pair;[["3/2","3/2"],["-3/2","-3/2"],["rat(6,4)","3/2"],[".125","1/8"],
		["2.0","2"],["0.0","0"],["-2.0","-2"],["rat(3,2)^n","(3/2)^n"]]){
		auto input=simplify(a,s.parse(a,pair[0])).output,printed=s.format(a,input);
		assert(printed==pair[1],pair[0]~" printed as "~printed);
		auto output=s.parse(a,printed);
		assert(promotes(a.sort(output),Sort.rational),printed~" changed its scalar type");
		assert(simplify(a,output).output==input,printed~" failed to round-trip");
	}
	// Fraction notation must retain grouping and exponent kinds in context.
	foreach(source;["rat(3,2)^k","q*rat(3,2)","q+rat(-3,2)","rat(-3,2)-q",
		"rat(3,2)/(q+1)","q/rat(3,2)","q<rat(3,2)","rat(3,2)<q",
		"powQN(rat(2,1),n)","powQZ(rat(2,1),k)","mulQ(([p]:ℚ),rat(3,2))"]){
		auto input=s.parse(a,source),printed=s.format(a,input),output=s.parse(a,printed);
		assert(promotes(a.sort(simplify(a,output).output),a.sort(input)),printed~" changed its scalar type");
		assert(simplify(a,output).output==simplify(a,input).output,printed~" changed meaning");
		assert(simplifyDomain(a,output).output==simplifyDomain(a,input).output,
			printed~" changed its domain");
	}
	foreach(source;[".","1.2.3","1e+","1e-","0.1:ℕ","0.1:ℤ","1e99999","1e-99999","1e19","1e-19"])
		assertThrown(s.parse(a,source));
}
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected,a.sort(input)),facts).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		assert(promotes(a.sort(fast.output),a.sort(input)),c.name~" changes type");
		assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		auto printed=s.format(a,fast.output),roundtrip=s.parse(a,printed);
		assert(a.sort(simplify(a,roundtrip,facts).output)==a.sort(fast.output),c.name~" printed type");
		assert(simplify(a,roundtrip,facts).output==fast.output,c.name~" failed to round-trip: "~printed);
		exportLean(a,checked);
	}
	assert(!failures,"numeral and scalar regressions");
}
@system void main(string[] args){
	enforce(args.length==2,"usage: numeral-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length," numeral and scalar certificates.");
}
