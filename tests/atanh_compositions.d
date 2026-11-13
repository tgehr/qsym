module atanh_composition_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:replace;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; bool domain; }
struct Composition{ string name,input,expected; bool isReal; }
Example[] examples(){
	Composition[] forms=[
		Composition("RealExp","exp(atanh($))","(1+($))/sqrt(1-($)^2)",true),
		Composition("ComplexExp","cexp(catanh($))","csqrt(1+($))/csqrt(1-($))"),
		Composition("ComplexCosh","ccosh(catanh($))","(csqrt(1+($))*csqrt(1-($)))⁻¹"),
		Composition("ComplexSinh","csinh(catanh($))","($)/(csqrt(1+($))*csqrt(1-($)))"),
		Composition("ComplexCos","ccos(catan($))","(csqrt(1+ⅈ*($))*csqrt(1-ⅈ*($)))⁻¹"),
		Composition("ComplexSin","csin(catan($))","($)/(csqrt(1+ⅈ*($))*csqrt(1-ⅈ*($)))"),
	];
	Example[] result;
	foreach(f;forms){
		auto variable=f.isReal?"x":"z",partial=f.isReal?"log(x)":"clog(z)",reciprocal=f.isReal?"1/x":"1/z";
		auto input=f.input.replace("$",variable),expected=f.expected.replace("$",variable);
		result~=Example(f.name,input,expected);
		result~=Example(f.name~"Partial",f.input.replace("$",partial),f.expected.replace("$",partial));
		result~=Example(f.name~"Reciprocal",f.input.replace("$",reciprocal),f.expected.replace("$",reciprocal));
		result~=Example(f.name~"Mask","[p]*("~input~")","[p]*("~expected~")");
		result~=Example(f.name~"False","[false]*("~input~")",f.isReal?"0":"toℂ(0)");
		result~=Example(f.name~"True","[true]*("~input~")",expected);
		result~=Example(f.name~"UndefinedMask","[1/0=1]*("~input~")","[1/0=1]*("~expected~")");
		result~=Example(f.name~"Zero",f.input.replace("$","0"),f.expected.replace("$","0"));
		result~=Example(f.name~"Assumed",input,expected,f.isReal?["-1<x","x<1"]:["z≠1","z≠-1","z≠ⅈ","z≠-ⅈ"]);
	}
	foreach(f;forms){
		if(f.isReal){
			result~=Example(f.name~"Half",f.input.replace("$","1/2"),f.expected.replace("$","1/2"));
			result~=Example(f.name~"NegativeHalf",f.input.replace("$","-1/2"),f.expected.replace("$","-1/2"));
			result~=Example(f.name~"Domain",f.input.replace("$","x"),"-1<x∧x<1",[],true);
			foreach(i,v;["1","-1","2","-2"]) result~=Example(f.name~"Outside"~cast(char)('A'+i),f.input.replace("$",v),"false",[],true);
		}else{
			foreach(i,v;["2","-2","2*ⅈ","-2*ⅈ","2+ⅈ/4","2-ⅈ/4"])
				result~=Example(f.name~"Branch"~cast(char)('A'+i),f.input.replace("$",v),f.expected.replace("$",v));
			bool tangent=f.name=="ComplexCos"||f.name=="ComplexSin";
			foreach(i,v;tangent?["ⅈ","-ⅈ"]:["1","-1"]){
				auto input=f.input.replace("$",v),name=f.name~"Pole"~cast(char)('A'+i);
				result~=Example(name,input,"false",[],true);
				result~=Example(name~"False","[false]*("~input~")","true",[],true);
				result~=Example(name~"True","[true]*("~input~")","false",[],true);
			}
		}
	}
	return result;
}

@system void main(string[] args){
	enforce(args.length==2,"usage: atanh-composition-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; Syntax s; s.declare("x:ℝ,z:ℂ,p:𝔹");
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
	writeln("Checked ",examples().length," atanh-composition cases and wrote certificates.");
}
