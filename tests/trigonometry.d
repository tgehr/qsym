module trigonometry_tests;
import qsym;
import std.conv:to;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	Example[] result;
	// Independent exact values, including every quadrant and translated turns.
	string[][] circle=[
		["0","0","1"],["1/6","1/2","sqrt(3)/2"],
		["1/4","sqrt(2)/2","sqrt(2)/2"],["1/3","sqrt(3)/2","1/2"],
		["1/2","1","0"],["2/3","sqrt(3)/2","-1/2"],
		["3/4","sqrt(2)/2","-sqrt(2)/2"],["5/6","1/2","-sqrt(3)/2"],
		["1","0","-1"],["7/6","-1/2","-sqrt(3)/2"],
		["5/4","-sqrt(2)/2","-sqrt(2)/2"],["4/3","-sqrt(3)/2","-1/2"],
		["3/2","-1","0"],["5/3","-sqrt(3)/2","1/2"],
		["7/4","-sqrt(2)/2","sqrt(2)/2"],["11/6","-1/2","sqrt(3)/2"]
	];
	foreach(i,p;circle) foreach(j,turn;["0","-2","8"]){
		auto angle="("~p[0]~"+"~turn~")*π",suffix=i.to!string~"_"~j.to!string;
		result~=Example("Sin"~suffix,"sin("~angle~")",p[1]);
		result~=Example("Cos"~suffix,"cos("~angle~")",p[2]);
		result~=Example("Phase"~suffix,"exp(ⅈ*("~angle~"))","toℂ("~p[2]~")+ⅈ*("~p[1]~")");
		if(p[2]!="0") result~=Example("Tan"~suffix,"tan("~angle~")","("~p[1]~")/("~p[2]~")");
	}
	result~=[
		Example("SinShift","sin(x+π/2)","cos(x)"),
		Example("CosShift","cos(x+π/2)","-sin(x)"),
		Example("SinHalfTurn","sin(x+π)","-sin(x)"),
		Example("CosHalfTurn","cos(x+π)","-cos(x)"),
		Example("NegativeShift","cos(x-π/2)","sin(x)"),
		Example("TanShift","tan(x+3*π)","tan(x)"),
		Example("PhaseShift","cis(x+3*π/2)","-ⅈ*cis(x)"),
		Example("PhaseSymbolic","cis(x)","cis(x)"),
		Example("UnrecognizedAngle","cis(real(1,7)*π)","cis(real(1,7)*π)"),
		Example("TanPole","tan(real(1,2)*π)","tan(real(1,2)*π)"),
		Example("TanMaskedPole","[false]*tan(π/2)","0"),
		Example("SinCosRatio","sin(x)/cos(x)","tan(x)"),
		Example("SinhCoshRatio","sinh(x)/cosh(x)","tanh(x)"),
		Example("TanCancellation","tan(x)*cos(x)","sin(x)"),
		Example("TanhCancellation","tanh(x)*cosh(x)","sinh(x)"),
		Example("HyperbolicSum","cosh(x)+sinh(x)","exp(x)"),
		Example("HyperbolicDifference","cosh(x)-sinh(x)","exp(-x)"),
		Example("HyperbolicQuotient","(cosh(x)+sinh(x))/(cosh(x)-sinh(x))","exp(2*x)"),
		Example("SinAddition","sin(x)*cos(y)+cos(x)*sin(y)","sin(x+y)"),
		Example("CosDifference","cos(x)*cos(y)+sin(x)*sin(y)","cos(x-y)"),
		Example("CosDouble","cos(x)^2-sin(x)^2","cos(2*x)"),
		Example("SinAtan","sin(atan(x))","x/sqrt(1+x^2)"),
		Example("CosAtan","cos(atan(x))","1/sqrt(1+x^2)"),
		Example("CoshAsinh","cosh(asinh(x))","sqrt(1+x^2)"),
		Example("ComplexSinCosRatio","csin(z)/ccos(z)","ctan(z)"),
		Example("ComplexSinhCoshRatio","csinh(z)/ccosh(z)","ctanh(z)"),
		Example("ComplexTanCancellation","ctan(z)*ccos(z)","csin(z)"),
		Example("ComplexTanhCancellation","ctanh(z)*ccosh(z)","csinh(z)"),
		Example("ComplexHyperbolicSum","ccosh(z)+csinh(z)","cexp(z)"),
		Example("ComplexHyperbolicDifference","ccosh(z)-csinh(z)","cexp(-z)"),
		Example("ComplexSinAddition","csin(z)*ccos(w)+ccos(z)*csin(w)","csin(z+w)"),
		Example("ComplexCosDifference","ccos(z)*ccos(w)+csin(z)*csin(w)","ccos(z-w)"),
		Example("ComplexCosDouble","ccos(z)^2-csin(z)^2","ccos(2*z)"),
		Example("ComplexTanConjugate","conj(ctan(z))","ctan(conj(z))"),
		Example("ComplexTanhConjugate","conj(ctanh(z))","ctanh(conj(z))"),
		Example("SinRealPart","creal(csin(z))","sin(creal(z))*cosh(cimag(z))"),
		Example("SinImaginaryPart","cimag(csin(z))","cos(creal(z))*sinh(cimag(z))"),
		Example("CosRealPart","creal(ccos(z))","cos(creal(z))*cosh(cimag(z))"),
		Example("CosImaginaryPart","cimag(ccos(z))","-sin(creal(z))*sinh(cimag(z))"),
		Example("SinhRealPart","creal(csinh(z))","sinh(creal(z))*cos(cimag(z))"),
		Example("SinhImaginaryPart","cimag(csinh(z))","cosh(creal(z))*sin(cimag(z))"),
		Example("CoshRealPart","creal(ccosh(z))","cosh(creal(z))*cos(cimag(z))"),
		Example("CoshImaginaryPart","cimag(ccosh(z))","sinh(creal(z))*sin(cimag(z))"),
		Example("ImaginarySinhPhase","cimag(csinh(x+π*ⅈ/2))","cosh(x)"),
		Example("ImaginaryCoshPhase","creal(ccosh(x+π*ⅈ))","-cosh(x)"),
		Example("PhaseAssumption","exp(ⅈ*x)","-ⅈ",["x=3*π/2"]),
		Example("PhaseRootOfUnity","exp(π*ⅈ/3)^6","complex(1,0)"),
		Example("PhaseEighthPower","cis(π/4)^8","complex(1,0)"),
		Example("PhaseConjugateProduct","cis(π/6)*cis(-π/6)","complex(1,0)"),
		Example("PhaseNorm","cabs(exp(π*ⅈ/3))","1"),
		Example("CartesianNorm","cabs(1+ⅈ*x)","sqrt(1+x^2)"),
		Example("CartesianNormReal","cabs(x+ⅈ*y)","sqrt(x^2+y^2)"),
		Example("ComplexNormCompact","cabs(z)","cabs(z)"),
		Example("DifferenceSquares","(x+y)*(x-y)","x^2-y^2"),
		Example("DifferenceSquaresLiterals","(sqrt(3)+1)*(sqrt(3)-1)","2"),
		Example("ComplexDifferenceSquares","(z+w)*(z-w)","z^2-w^2"),
		Example("TrigonometricComposition","sin(atan(x))/cos(atan(x))","x"),
		Example("TrigonometricGuard","[sin(x)*cos(y)+cos(x)*sin(y)=0]","[sin(x+y)=0]"),
		Example("MaskedCancellation","[cos(x)≠0]*tan(x)*cos(x)","[cos(x)≠0]*sin(x)"),
		Example("ComplexMaskedUndefined","[false]*ctan(1/0)","complex(0,0)")
	];
	return result;
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ"); return s; }
unittest{
	size_t failures;
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),expected=c.input==c.expected?input:simplify(a,s.parse(a,c.expected),facts).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		if(fast.exhausted||fast.output!=expected){
			writeln("FAIL ",c.name,": ",s.format(a,fast.output),"; expected ",s.format(a,expected),fast.exhausted?" (exhausted)":""); ++failures;
		}
		assert(fast.output==checked.output&&fast.exhausted==checked.exhausted,c.name);
		if(!fast.exhausted) assert(simplify(a,fast.output,facts).output==fast.output,c.name~" is not idempotent");
		exportLean(a,checked);
	}
	assert(!failures,"trigonometry regressions");
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	assert(simplify(a,s.parse(a,"tan(π/2)")).output==s.parse(a,"tan(real(1,2)*π)"));
	foreach(pair;[["exp(π*ⅈ)","-toℂ(1)"],["exp(2*π*ⅈ)","toℂ(1)"],
		["exp(3*π*ⅈ/2)","-ⅈ"],["complex(0,0)","toℂ(0)"],["z+complex(-1,0)","z-1"]]){
		auto t=simplify(a,s.parse(a,pair[0])).output,printed=s.format(a,t);
		assert(printed==pair[1],pair[0]~": "~printed);
		auto roundtrip=simplify(a,s.parse(a,printed)).output;
		assert(roundtrip==t&&a.sort(roundtrip)==a.sort(t),printed);
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: trigonometry-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	writeln("Wrote ",examples().length," trigonometry certificates.");
}
