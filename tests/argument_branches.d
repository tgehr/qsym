module argument_branch_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; bool domain; }
Example[] examples(){
	return [
		Example("UnknownArgConj","carg(conj(z))","carg(conj(z))"),
		Example("OffCutArgConj","carg(conj(z))","-carg(z)",["carg(z)≠π"]),
		Example("NonrealArgConj","carg(conj(z))","-carg(z)",["cimag(z)≠0"]),
		Example("NonnegativeArgConj","carg(conj(z))","-carg(z)",["0≤creal(z)"]),
		Example("UpperArgConj","carg(conj(z))","-carg(z)",["0<cimag(z)"]),
		Example("LowerArgConj","carg(conj(z))","-carg(z)",["cimag(z)<0"]),
		Example("UnknownArgInv","carg(1/z)","carg(1/z)"),
		Example("OffCutArgInv","carg(1/z)","-carg(z)",["carg(z)≠π"]),
		Example("NonrealArgInv","carg(1/z)","-carg(z)",["cimag(z)≠0"]),
		Example("NonnegativeArgInv","carg(1/z)","-carg(z)",["0≤creal(z)"]),
		Example("UpperArgInv","carg(1/z)","-carg(z)",["0<cimag(z)"]),
		Example("LowerArgInv","carg(1/z)","-carg(z)",["cimag(z)<0"]),
		Example("UnknownLogConj","clog(conj(z))","clog(conj(z))"),
		Example("OffCutLogConj","clog(conj(z))","conj(clog(z))",["carg(z)≠π"]),
		Example("NonrealLogConj","clog(conj(z))","conj(clog(z))",["cimag(z)≠0"]),
		Example("NonnegativeLogConj","clog(conj(z))","conj(clog(z))",["0≤creal(z)"]),
		Example("UpperLogConj","clog(conj(z))","conj(clog(z))",["0<cimag(z)"]),
		Example("LowerLogConj","clog(conj(z))","conj(clog(z))",["cimag(z)<0"]),
		Example("UnknownLogInv","clog(1/z)","clog(1/z)"),
		Example("OffCutLogInv","clog(1/z)","-clog(z)",["carg(z)≠π"]),
		Example("NonrealLogInv","clog(1/z)","-clog(z)",["cimag(z)≠0"]),
		Example("NonnegativeLogInv","clog(1/z)","-clog(z)",["0≤creal(z)"]),
		Example("UpperLogInv","clog(1/z)","-clog(z)",["0<cimag(z)"]),
		Example("LowerLogInv","clog(1/z)","-clog(z)",["cimag(z)<0"]),
		Example("CutArgConj","carg(conj(z))","π",["carg(z)=π"]),
		Example("NegativeAxisArgConj","carg(conj(z))","π",["creal(z)<0","cimag(z)=0"]),
		Example("CutArgInv","carg(1/z)","π",["carg(z)=π"]),
		Example("NegativeAxisArgInv","carg(1/z)","π",["creal(z)<0","cimag(z)=0"]),
		Example("CutLogConj","clog(conj(z))","clog(z)",["carg(z)=π"]),
		Example("NegativeAxisLogConj","clog(conj(z))","clog(z)",["creal(z)<0","cimag(z)=0"]),
		Example("CutLogInv","clog(1/z)","-conj(clog(z))",["carg(z)=π"]),
		Example("NegativeAxisLogInv","clog(1/z)","-conj(clog(z))",["creal(z)<0","cimag(z)=0"]),
		Example("OnCutPredicate","carg(z)=π","creal(z)<0∧cimag(z)=0"),
		Example("OnCutPredicateDomain","carg(z)=π","z≠0",[],true),
		Example("OffCutPredicate","carg(z)≠π","0≤creal(z)∨cimag(z)≠0"),
		Example("OffCutPredicateDomain","carg(z)≠π","z≠0",[],true),
		Example("CutPi","π","π",["carg(z)=π"]),
		Example("CutArgument","carg(z)","π",["carg(z)=π"]),
		Example("ConstantE","exp(1)","exp(1)",["x=exp(1)"]),
		Example("ConstantPi","π","π",["x=π"]),
		Example("ConstantEqual","x","π",["x=π"]),
		Example("PositiveAxisConj","carg(conj(z))","0",["0<creal(z)","cimag(z)=0"]),
		Example("PositiveAxisInv","carg(1/z)","0",["0<creal(z)","cimag(z)=0"]),
		Example("ArgConjDomain","carg(conj(z))","z≠0",[],true),
		Example("ArgConjZeroDomain","carg(conj(toℂ(0)))","false",[],true),
		Example("ArgConjFalseMask","[false]*carg(conj(z))","0"),
		Example("ArgConjFalseZeroDomain","[false]*carg(conj(toℂ(0)))","true",[],true),
		Example("ArgInvDomain","carg(1/z)","z≠0",[],true),
		Example("ArgInvZeroDomain","carg(1/toℂ(0))","false",[],true),
		Example("ArgInvFalseMask","[false]*carg(1/z)","0"),
		Example("ArgInvFalseZeroDomain","[false]*carg(1/toℂ(0))","true",[],true),
		Example("LogConjDomain","clog(conj(z))","z≠0",[],true),
		Example("LogConjZeroDomain","clog(conj(toℂ(0)))","false",[],true),
		Example("LogConjFalseMask","[false]*clog(conj(z))","0"),
		Example("LogConjFalseZeroDomain","[false]*clog(conj(toℂ(0)))","true",[],true),
		Example("LogInvDomain","clog(1/z)","z≠0",[],true),
		Example("LogInvZeroDomain","clog(1/toℂ(0))","false",[],true),
		Example("LogInvFalseMask","[false]*clog(1/z)","0"),
		Example("LogInvFalseZeroDomain","[false]*clog(1/toℂ(0))","true",[],true),
		Example("ExactUpperArgConj","carg(conj(ⅈ))","-π/2"),
		Example("ExactLowerArgConj","carg(conj(-ⅈ))","π/2"),
		Example("ExactUpperArgInv","carg(1/ⅈ)","-π/2"),
		Example("ExactLowerArgInv","carg(1/(-ⅈ))","π/2"),
		Example("ExactNegativeArgConj","carg(conj(-1))","π"),
		Example("ExactNegativeArgInv","carg(1/(-1))","π"),
		Example("ExactNegativeLogConj","clog(conj(-1))","toℂ(π)*ⅈ"),
		Example("ExactNegativeLogInv","clog(1/(-1))","toℂ(π)*ⅈ"),
		Example("NestedArgConj","carg(conj(clog(z)))","-carg(clog(z))",["carg(clog(z))≠π"]),
		Example("NestedArgInv","carg(1/clog(z))","-carg(clog(z))",["carg(clog(z))≠π"]),
		Example("NestedLogConj","clog(conj(clog(z)))","conj(clog(clog(z)))",["carg(clog(z))≠π"]),
		Example("NestedLogInv","clog(1/clog(z))","-clog(clog(z))",["carg(clog(z))≠π"]),
		Example("MaskOffCut","[carg(z)≠π]*carg(conj(z))","[carg(z)≠π]*(-carg(z))"),
		Example("MaskOnCut","[carg(z)=π]*carg(conj(z))","[carg(z)=π]*π"),
		Example("UnknownInverseDefined","carg(1/(z-z))","false",[],true),
	];
}
@system void main(string[] args){
	enforce(args.length==2,"usage: argument-branch-tests DIRECTORY"); mkdirRecurse(args[1]);
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
	writeln("Checked ",examples().length," argument-branch cases and wrote certificates.");
}
