module zero_power_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
@safe:

struct Example{ string name,input,expected; string[] facts; bool domain,unchanged; }
Example[] examples(){
	Example[] r;
	foreach(t;["ℕ","ℤ","ℚ","ℝ","ℂ"]){
		auto z="(0:"~t~")";
		r~=[
			Example(t~"Natural",z~"^n","[n=0]"),
			Example(t~"Positive",z~"^(n+1)","0"),
			Example(t~"Partial",z~"^(n sub 1)","[n sub 1=0]"),
			Example(t~"PartialDomain",z~"^(n sub 1)","1≤n",[],true),
			Example(t~"UndefinedIndex",z~"^(0 sub 1)","false",[],true),
			Example(t~"Zero",z~"^(0:ℕ)","1"),
			Example(t~"One",z~"^(1:ℕ)","0"),
			Example(t~"Mask","[p]*"~z~"^n","[p]*[n=0]"),
			Example(t~"FalseMask","[false]*"~z~"^(0 sub 1)","0"),
			Example(t~"AssumedZero",z~"^n","1",["n=0"]),
			Example(t~"AssumedPositive",z~"^n","0",["0<n"])
		];
	}
	foreach(t;["ℚ","ℝ","ℂ"]){
		auto z="(0:"~t~")";
		r~=[
			Example(t~"Integer",z~"^k","[k=0]",["0≤k"]),
			Example(t~"IntegerPositive",z~"^k","0",["0<k"]),
			Example(t~"IntegerUnknown",z~"^k",z~"^k",[],false,t=="ℚ"),
			Example(t~"IntegerDomain",z~"^k","0≤k",[],true),
			Example(t~"IntegerNegative",z~"^(-1:ℤ)","false",[],true),
			Example(t~"IntegerFalseMask","[false]*"~z~"^(-1:ℤ)","0"),
			Example(t~"IntegerTrueMask","[true]*"~z~"^(-1:ℤ)","false",[],true)
		];
	}
	r~=[
		Example("RealNonnegative","powerR(0,x)","[x=0]",["0≤x"]),
		Example("RealPositive","powerR(0,x)","0",["0<x"]),
		Example("RealUnknown","powerR(0,x)","powerR(0,x)",[],false,true),
		Example("RealNegative","powerR(0,-1)","false",[],true),
		Example("RealFraction","powerR(0,1/2)","0"),
		Example("ComplexNonnegative","powerC(0,z)","[z=0]",["cimag(z)=0","0≤creal(z)"]),
		Example("ComplexPositive","powerC(0,z)","0",["cimag(z)=0","0<creal(z)"]),
		Example("ComplexUnknown","powerC(0,z)","powerC(0,z)",[],false,true),
		Example("ComplexRealOnly","powerC(0,z)","powerR(0,creal(z))",["cimag(z)=0"]),
		Example("ComplexPositiveRealOnly","powerC(0,z)","powerC(0,z)",["0<creal(z)"],false,true),
		Example("ComplexNegative","powerC(0,-1)","false",[],true),
		Example("ComplexNonreal","powerC(0,1+ⅈ)","false",[],true),
		Example("ComplexImaginary","powerC(0,ⅈ)","false",[],true),
		Example("ComplexFraction","powerC(0,toℂ(1/2))","0")
	];
	return r;
}
@system void main(string[] args){
	enforce(args.length==2,"usage: zero-power-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; Syntax s; s.declare("n:ℕ,k:ℤ,x:ℝ,z:ℂ,p:𝔹");
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input); if(c.domain) input=definedness(a,input);
		auto expected=simplify(a,s.parse(a,c.expected,a.sort(input)),facts).output;
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		enforce(!fast.exhausted&&fast.output==expected,c.name~": "~s.format(a,fast.output)~"; expected "~s.format(a,expected));
		enforce(fast.output==checked.output&&!checked.exhausted,c.name~" tracing");
		enforce(!c.unchanged||fast.output==input,c.name~" branch boundary");
		auto again=simplify(a,fast.output,facts);
		enforce(!again.exhausted&&again.output==fast.output,c.name~" idempotence");
		auto roundtrip=simplify(a,s.parse(a,s.format(a,fast.output),a.sort(fast.output)),facts);
		enforce(!roundtrip.exhausted&&roundtrip.output==fast.output,c.name~" round trip");
		write(buildPath(args[1],c.name~".lean"),exportLean(a,checked));
		writeln(c.name,": ",s.format(a,fast.output));
	}
	writeln("Checked ",examples().length," zero-power cases and wrote certificates.");
}
