module quadratic_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	return [
		Example("RealEmpty","[x^2+x+1=0]","0"),
		Example("RealRepeated","[x^2-2*x+1=0]","[x=1]"),
		Example("RealIrrational","x^2=2","x=-sqrt(2)∨x=sqrt(2)"),
		Example("RealShifted","x^2+2*x-2=0","x=-1-sqrt(3)∨x=-1+sqrt(3)"),
		Example("RealNonmonic","4*x^2-3=0","x=-sqrt(3)/2∨x=sqrt(3)/2"),
		Example("RealSelectPositive","x","sqrt(2)",["x^2=2","0<x"]),
		Example("RealSelectNegative","x","-sqrt(2)",["x^2=2","x<0"]),
		Example("RealSelectReverse","x","sqrt(2)",["0<x","x^2=2"]),
		Example("RealAmbiguous","x","x",["x^2=2"]),
		Example("ComplexEmptyReal","z^2+z+1=0","z=-1/2-ⅈ*sqrt(3)/2∨z=-1/2+ⅈ*sqrt(3)/2"),
		Example("ComplexOtherCenter","z^2-z+1=0","z=1/2-ⅈ*sqrt(3)/2∨z=1/2+ⅈ*sqrt(3)/2"),
		Example("ComplexRepeated","[z^2-2*z+1=0]","[z=1]"),
		Example("ComplexUnit","z^2+1=0","z=-ⅈ∨z=ⅈ"),
		Example("ComplexRealRoots","z^2=2","z=-sqrt(2)∨z=sqrt(2)"),
		Example("ComplexGaussian","z^2-2*ⅈ=0","z=-1-ⅈ∨z=1+ⅈ"),
		Example("ComplexNonmonic","ⅈ*z^2+z=0","z=0∨z=ⅈ"),
		Example("ComplexLinear","(1+ⅈ)*z+2=0","z=-1+ⅈ"),
		Example("ComplexSelectUpper","z","-1/2+ⅈ*sqrt(3)/2",["z^2+z+1=0","im(z)>0"]),
		Example("ComplexSelectLower","z","-1/2-ⅈ*sqrt(3)/2",["z^2+z+1=0","im(z)<0"]),
		Example("ComplexSelectReverse","z","-1/2+ⅈ*sqrt(3)/2",["im(z)>0","z^2+z+1=0"]),
		Example("ComplexSelectConjunction","z","-1/2+ⅈ*sqrt(3)/2",["z^2+z+1=0∧im(z)>0"]),
		Example("ComplexAmbiguous","z","z",["z^2+z+1=0"]),
		Example("ComplexRepeatedFact","z","complex(1,0)",["z^2-2*z+1=0"]),
		Example("PartialAtom","clog(z)^2+1=0","clog(z)=-ⅈ∨clog(z)=ⅈ"),
		Example("GuardRoot","[x^2=2]*[0<x]*x","[x=sqrt(2)]*sqrt(2)"),
		Example("RationalRadical","sqrt(3/4)","sqrt(3)/2"),
		Example("ReciprocalRadical","sqrt(1/2)","sqrt(2)/2"),
		Example("NegativeRadical","sqrt(-1)","sqrt(-1)"),
		Example("ImplicitReal","[x^2-2x+1=0]","[x=1]"),
		Example("ImplicitComplex","[z^2-2z+1=0]","[z=1]"),
		Example("ImplicitPower","2x^2-8","2*(x^2-4)"),
		Example("ImplicitGrouping","2(x+1)","2*x+2"),
		Example("ImplicitImaginary","2ⅈ*z+2=0","z=ⅈ"),
		Example("PartialSelectedAtom","[log(x)^2=2]*[0<log(x)]*log(x)","[log(x)=sqrt(2)]*sqrt(2)"),
		Example("PartialBody","[x^2=2]*[0<x]*log(-1)","[x=sqrt(2)]*log(-1)"),
		Example("ScopeIsolation","[x^2=2]*[0<x]*x+x","[x=sqrt(2)]*sqrt(2)+x"),
		Example("ComplexArbitrary","z^2+z+ⅈ=0","z=-1/2-csqrt(1/4-ⅈ)∨z=-1/2+csqrt(1/4-ⅈ)"),
		Example("ComplexAffineFact","z","complex(-1,1)",["(1+ⅈ)*z+2=0"]),
		Example("SelectedPolynomial","z^2+z+1","complex(0,0)",["z^2+z+1=0","im(z)>0"]),
		Example("SelectedCube","z^3","complex(1,0)",["z^2+z+1=0","im(z)>0"]),
		Example("RadicalCube","sqrt(3)^3","3*sqrt(3)"),
		Example("RadicalFourth","sqrt(x)^4","x^2")
	];
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,p:𝔹"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=simplify(a,s.parse(a,c.expected)).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected)); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"quadratic simplification regressions");
}
unittest{
	import std.exception:assertThrown;
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	foreach(source;["x=-sqrt(2)","x=-1-sqrt(3)","z=-1/2-ⅈ*sqrt(3)/2","-x+sqrt(2)=0","x+y+sqrt(2)=0"]){
		auto t=simplify(a,s.parse(a,source)).output;
		assert(simplify(a,s.parse(a,s.format(a,t))).output==t,source);
	}
	assert(s.format(a,simplify(a,s.parse(a,"x^2=2")).output)=="x=-sqrt(2)∨x=sqrt(2)");
	foreach(source;["2 x","x y","2^2x"]) assertThrown(s.parse(a,source));
	foreach(work;[size_t(0),1,100]){
		auto options=Options(DensityMode.preserve,true); options.maxAlgebraWork=work;
		auto r=simplify(a,s.parse(a,"z"),[s.parse(a,"z^2+z+1=0"),s.parse(a,"im(z)>0")],options);
		assert(r.exhausted); exportLean(a,r);
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: quadratic-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote quadratic certificates.");
}
