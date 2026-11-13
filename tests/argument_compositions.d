module argument_composition_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; bool domain; }
Example[] examples(){
	return [
		Example("Sin","sin(carg(z))","cimag(z)/cabs(z)"),
		Example("Cos","cos(carg(z))","creal(z)/cabs(z)"),
		Example("Tan","tan(carg(z))","cimag(z)/creal(z)"),
		Example("Cis","cis(carg(z))","z/toℂ(cabs(z))"),
		Example("SinAtan2","sin(atan2(y,x))","y/sqrt(x^2+y^2)"),
		Example("CosAtan2","cos(atan2(y,x))","x/sqrt(x^2+y^2)"),
		Example("TanAtan2","tan(atan2(y,x))","y/x"),
		Example("CisAtan2","cis(atan2(y,x))","cfromri(x,y)/toℂ(sqrt(x^2+y^2))"),
		Example("SinLog","sin(carg(clog(z)))","cimag(clog(z))/cabs(clog(z))"),
		Example("CosLog","cos(carg(clog(z)))","creal(clog(z))/cabs(clog(z))"),
		Example("TanLog","tan(carg(clog(z)))","cimag(clog(z))/creal(clog(z))"),
		Example("CisLog","cis(carg(clog(z)))","clog(z)/toℂ(cabs(clog(z)))"),
		Example("SinProduct","sin(carg((z*w)))","cimag((z*w))/cabs((z*w))"),
		Example("CosProduct","cos(carg((z*w)))","creal((z*w))/cabs((z*w))"),
		Example("TanProduct","tan(carg((z*w)))","cimag((z*w))/creal((z*w))"),
		Example("CisProduct","cis(carg((z*w)))","(z*w)/toℂ(cabs((z*w)))"),
		Example("SinInverse","sin(carg((1/z)))","cimag((1/z))/cabs((1/z))"),
		Example("CosInverse","cos(carg((1/z)))","creal((1/z))/cabs((1/z))"),
		Example("TanInverse","tan(carg((1/z)))","cimag((1/z))/creal((1/z))"),
		Example("CisInverse","cis(carg((1/z)))","(1/z)/toℂ(cabs((1/z)))"),
		Example("SinMask","[p]*sin(carg(z))","[p]*(cimag(z)/cabs(z))"),
		Example("CosMask","[p]*cos(carg(z))","[p]*(creal(z)/cabs(z))"),
		Example("TanMask","[p]*tan(carg(z))","[p]*(cimag(z)/creal(z))"),
		Example("CisMask","[p]*cis(carg(z))","[p]*(z/toℂ(cabs(z)))"),
		Example("SinFalse","[false]*sin(carg(z))","0"),
		Example("CosFalse","[false]*cos(carg(z))","0"),
		Example("TanFalse","[false]*tan(carg(z))","0"),
		Example("CisFalse","[false]*cis(carg(z))","toℂ(0)"),
		Example("SinTrue","[true]*sin(carg(z))","[true]*(cimag(z)/cabs(z))"),
		Example("CosTrue","[true]*cos(carg(z))","[true]*(creal(z)/cabs(z))"),
		Example("TanTrue","[true]*tan(carg(z))","[true]*(cimag(z)/creal(z))"),
		Example("CisTrue","[true]*cis(carg(z))","[true]*(z/toℂ(cabs(z)))"),
		Example("SinUndefinedMask","[1/0=1]*sin(carg(z))","[1/0=1]*(cimag(z)/cabs(z))"),
		Example("CosUndefinedMask","[1/0=1]*cos(carg(z))","[1/0=1]*(creal(z)/cabs(z))"),
		Example("TanUndefinedMask","[1/0=1]*tan(carg(z))","[1/0=1]*(cimag(z)/creal(z))"),
		Example("CisUndefinedMask","[1/0=1]*cis(carg(z))","[1/0=1]*(z/toℂ(cabs(z)))"),
		Example("SinNegativeAxis","sin(carg(-1))","0"),
		Example("CosNegativeAxis","cos(carg(-1))","-1"),
		Example("TanNegativeAxis","tan(carg(-1))","0"),
		Example("CisNegativeAxis","cis(carg(-1))","toℂ(-1)"),
		Example("SinUpperAxis","sin(carg(ⅈ))","1"),
		Example("CosUpperAxis","cos(carg(ⅈ))","0"),
		Example("TanUpperAxis","tan(carg(ⅈ))","false",[],true),
		Example("CisUpperAxis","cis(carg(ⅈ))","ⅈ"),
		Example("SinLowerAxis","sin(carg(-ⅈ))","-1"),
		Example("CosLowerAxis","cos(carg(-ⅈ))","0"),
		Example("TanLowerAxis","tan(carg(-ⅈ))","false",[],true),
		Example("CisLowerAxis","cis(carg(-ⅈ))","-ⅈ"),
		Example("SinZeroDomain","sin(carg(0))","false",[],true),
		Example("CosZeroDomain","cos(carg(0))","false",[],true),
		Example("TanZeroDomain","tan(carg(0))","false",[],true),
		Example("CisZeroDomain","cis(carg(0))","false",[],true),
		Example("SinDomain","sin(carg(z))","z≠0",[],true),
		Example("CosDomain","cos(carg(z))","z≠0",[],true),
		Example("TanDomain","tan(carg(z))","creal(z)≠0",[],true),
		Example("CisDomain","cis(carg(z))","z≠0",[],true),
		Example("SinAtan2Domain","sin(atan2(y,x))","x≠0∨y≠0",[],true),
		Example("TanAtan2Domain","tan(atan2(y,x))","x≠0",[],true),
		Example("FalseUndefinedDomain","[false]*cis(carg(0))","true",[],true),
		Example("TrueUndefinedDomain","[true]*cis(carg(0))","false",[],true),
		Example("PositiveRealAssumption","cis(carg(z))","toℂ(1)",["0<creal(z)","cimag(z)=0"]),
		Example("NegativeRealAssumption","cos(carg(z))","-1",["creal(z)<0","cimag(z)=0"]),
		Example("UnitNorm","cabs(cis(carg(z)))","1"),
		Example("Pythagorean","sin(carg(z))^2+cos(carg(z))^2","1"),
	];
}
@system void main(string[] args){
	enforce(args.length==2,"usage: argument-composition-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ,p:𝔹");
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input); if(c.domain) input=definedness(a,input);
		auto expected=simplify(a,s.parse(a,c.expected,a.sort(input)),facts).output;
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
	writeln("Checked ",examples().length," argument-composition cases and wrote certificates.");
}
