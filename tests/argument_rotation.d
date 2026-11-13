module argument_rotation_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; bool domain; }
Example[] examples(){
	return [
		Example("ExpLeft","carg(toℂ(exp(x))*z)","carg(z)"),
		Example("ExpRight","carg(z*toℂ(exp(x)))","carg(z)"),
		Example("ExpDivide","carg(z/toℂ(exp(x)))","carg(z)"),
		Example("RealLeft","carg(toℂ(x)*z)","carg(z)",["0<x"]),
		Example("RealRight","carg(z*toℂ(x))","carg(z)",["0<x"]),
		Example("GenericLeft","carg(w*z)","carg(z)",["cimag(w)=0","0<creal(w)"]),
		Example("GenericRight","carg(z*w)","carg(z)",["cimag(w)=0","0<creal(w)"]),
		Example("LiteralScale","carg(2*z)","carg(z)"),
		Example("NegativeLiteral","carg(-2*z)","carg(-z)"),
		Example("NegativeLiteralUpper","carg(-2*z)","carg(z)-π",["0<cimag(z)"]),
		Example("NegativeLiteralLower","carg(-2*z)","carg(z)+π",["cimag(z)<0"]),
		Example("NegativeRealLeft","carg(toℂ(x)*z)","carg(-z)",["x<0"]),
		Example("NegativeRealRight","carg(z*toℂ(x))","carg(-z)",["x<0"]),
		Example("NegativeGenericLeft","carg(w*z)","carg(-z)",["cimag(w)=0","creal(w)<0"]),
		Example("NegativeGenericRight","carg(z*w)","carg(-z)",["cimag(w)=0","creal(w)<0"]),
		Example("NegativeExp","carg(toℂ(-exp(x))*z)","carg(-z)"),
		Example("UnknownScale","carg(z*toℂ(x))","carg(z*toℂ(x))"),
		Example("WeakScale","carg(z*toℂ(x))","carg(z*toℂ(x))",["0≤x"]),
		Example("ArgUnknown","carg(-z)","carg(-z)"),
		Example("ArgPositive","carg(-z)","carg(z)-π",["0<carg(z)"]),
		Example("ArgNonpositive","carg(-z)","carg(z)+π",["carg(z)≤0"]),
		Example("ArgUpper","carg(-z)","carg(z)-π",["0<cimag(z)"]),
		Example("ArgLower","carg(-z)","carg(z)+π",["cimag(z)<0"]),
		Example("ArgCut","carg(-z)","0",["carg(z)=π"]),
		Example("ArgZeroArgument","carg(-z)","π",["carg(z)=0"]),
		Example("ArgNegativeAxis","carg(-z)","0",["cimag(z)=0","creal(z)<0"]),
		Example("ArgPositiveAxis","carg(-z)","π",["cimag(z)=0","0<creal(z)"]),
		Example("LogUnknown","clog(-z)","clog(-z)"),
		Example("LogPositive","clog(-z)","clog(z)-toℂ(π)*ⅈ",["0<carg(z)"]),
		Example("LogNonpositive","clog(-z)","clog(z)+toℂ(π)*ⅈ",["carg(z)≤0"]),
		Example("LogUpper","clog(-z)","clog(z)-toℂ(π)*ⅈ",["0<cimag(z)"]),
		Example("LogLower","clog(-z)","clog(z)+toℂ(π)*ⅈ",["cimag(z)<0"]),
		Example("LogCut","clog(-z)","clog(z)-toℂ(π)*ⅈ",["carg(z)=π"]),
		Example("LogZeroArgument","clog(-z)","clog(z)+toℂ(π)*ⅈ",["carg(z)=0"]),
		Example("LogNegativeAxis","clog(-z)","toℂ(log(-creal(z)))",["cimag(z)=0","creal(z)<0"]),
		Example("LogPositiveAxis","clog(-z)","toℂ(log(creal(z)))+toℂ(π)*ⅈ",["cimag(z)=0","0<creal(z)"]),
		Example("ExactArgUpper","carg(-ⅈ)","-π/2"),
		Example("ExactArgLower","carg(-(-ⅈ))","π/2"),
		Example("ExactArgNegative","carg(-(-1))","0"),
		Example("ExactArgPositive","carg(-1)","π"),
		Example("ExactArgScaledUpper","carg(-2*ⅈ)","-π/2"),
		Example("ExactArgScaledLower","carg(-2*(-ⅈ))","π/2"),
		Example("ExactLogUpper","clog(ⅈ)","toℂ(π/2)*ⅈ"),
		Example("ExactLogLower","clog(-ⅈ)","-toℂ(π/2)*ⅈ"),
		Example("ExactLogNegative","clog(-1)","toℂ(π)*ⅈ"),
		Example("ExactLogNegativeTwo","clog(-2)","toℂ(log(2))+toℂ(π)*ⅈ"),
		Example("NegativeExpLog","clog(cfromri(-exp(x),0))","toℂ(x)+toℂ(π)*ⅈ"),
		Example("NegativeCastExpLog","clog(toℂ(-exp(x)))","toℂ(x)+toℂ(π)*ⅈ"),
		Example("NegativeRealLog","clog(z)","toℂ(log(-creal(z)))+toℂ(π)*ⅈ",["cimag(z)=0","creal(z)<0"]),
		Example("WeakRealLog","clog(z)","clog(z)",["cimag(z)=0","creal(z)≤0"]),
		Example("ArgNegDomain","carg(-z)","z≠0",[],true),
		Example("LogNegDomain","clog(-z)","z≠0",[],true),
		Example("ScaledDomain","carg(z*toℂ(x))","z≠0∧x≠0",[],true),
		Example("ZeroArgDomain","carg(-toℂ(0))","false",[],true),
		Example("ZeroLogDomain","clog(-toℂ(0))","false",[],true),
		Example("ZeroScaleDomain","carg(z*toℂ(0))","false",[],true),
		Example("ZeroLeftScaleDomain","carg(toℂ(0)*z)","false",[],true),
		Example("ImaginaryLogDomain","clog(-ⅈ)","true",[],true),
		Example("ArgGuard","[0<carg(z)]*carg(-z)","[0<carg(z)]*(carg(z)-π)"),
		Example("ArgFalseMask","[false]*carg(-z)","0"),
		Example("ArgFalseZeroDomain","[false]*carg(-toℂ(0))","true",[],true),
		Example("ArgTrueZeroDomain","[true]*carg(-toℂ(0))","false",[],true),
		Example("ArgUndefinedGuard","[1/0=0]*carg(-z)","false",[],true),
		Example("ArgNested","carg(-clog(z))","carg(clog(z))-π",["0<carg(clog(z))"]),
		Example("LogGuard","[0<carg(z)]*clog(-z)","[0<carg(z)]*(clog(z)-toℂ(π)*ⅈ)"),
		Example("LogFalseMask","[false]*clog(-z)","0"),
		Example("LogFalseZeroDomain","[false]*clog(-toℂ(0))","true",[],true),
		Example("LogTrueZeroDomain","[true]*clog(-toℂ(0))","false",[],true),
		Example("LogUndefinedGuard","[1/0=0]*clog(-z)","false",[],true),
		Example("LogNested","clog(-clog(z))","clog(clog(z))-toℂ(π)*ⅈ",["0<carg(clog(z))"]),
	];
}
@system void main(string[] args){
	enforce(args.length==2,"usage: argument-rotation-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; Syntax s; s.declare("x:ℝ,y:ℝ,z:ℂ,w:ℂ,p:𝔹");
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
	writeln("Checked ",examples().length," argument-rotation cases and wrote certificates.");
}
