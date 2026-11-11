module convergence_tests;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.exception:enforce;
import std.conv:to;
@safe:

struct Example{ string name,input,expected; string[] facts; }
Example[] examples(){
	Example[] cases;
	foreach(f;["floor","ceil","round"]){
		auto interval=f=="floor"?"1≤x∧x<2":f=="ceil"?"0<x∧x≤1":"1/2≤x∧x<3/2";
		auto outside=f=="floor"?"x<1∨2≤x":f=="ceil"?"x≤0∨1<x":"x<1/2∨3/2≤x";
		auto zero=f=="floor"?"0≤x∧x<1":f=="ceil"?"-1<x∧x≤0":"-1/2≤x∧x<1/2";
		cases~=[
			Example(f~"Scaled","2*"~f~"(x)=2",interval),
			Example(f~"ScaledNotEqual","2*"~f~"(x)≠2",outside),
			Example(f~"NegativeScale","-3*"~f~"(x)=-3",interval),
			Example(f~"Unit",f~"(x)=1",interval),
			Example(f~"Zero",f~"(x)=0",zero),
			Example(f~"FoldedOffset",f~"(x)+int(-1)=0",interval),
			Example(f~"CommutedOffset","int(-1)+"~f~"(x)=0",interval),
			Example(f~"GeneratedOffset",f~"(x)+(2-3)=0",interval),
			Example(f~"NestedIndicator","[2*"~f~"(x)=2]","["~interval~"]"),
			Example(f~"Guarded","p∧(2*"~f~"(x)=2)","p∧("~interval~")"),
			Example(f~"FalseMask","[false]*(2*"~f~"(log(0))-2)","0"),
			Example(f~"Assumed","2*"~f~"(x)=2","true",[interval])
		];
	}
	cases~=[
		Example("PartialFloor","2*floor(log(x))=2","1≤log(x)∧log(x)<2"),
		Example("PartialCeiling","2*ceil(x⁻¹)=2","0<x⁻¹∧x⁻¹≤1"),
		Example("NestedRounding","2*floor(ceil(x)/2)=2","1<x∧x≤3"),
		Example("NaturalInterval","1/2<n<3/2","n=1"),
		Example("NestedSubtype","sin(toℝ(q)+toℝ(r))","sin(q+r)"),
		Example("LoweredPower","powCN(3,n)","3^n"),
		Example("AbsoluteComposition","cos(abs(sinh(x)))","cos(sinh(x))"),
		Example("HyperbolicComposition","cosh(abs(sinh(x)))","cosh(sinh(x))")
	];
	return cases;
}
private Syntax syntax(){ Syntax s; s.declare("x:ℝ,q:ℚ,r:ℚ,n:ℕ,p:𝔹"); return s; }
unittest{
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		auto input=s.parse(a,c.input),want=simplify(a,s.parse(a,c.expected),facts);
		auto fast=simplify(a,input,facts),checked=simplify(a,input,facts,Options(DensityMode.preserve,true));
		enforce(!fast.exhausted&&!checked.exhausted&&!want.exhausted,c.name~" exhausted");
		enforce(fast.output==want.output,c.name~": "~s.format(a,fast.output)~" != "~s.format(a,want.output));
		enforce(fast.output==checked.output,c.name~" trace disagreement");
		auto next=simplify(a,fast.output,facts);
		enforce(!next.exhausted&&next.output==fast.output,c.name~" is not idempotent");
		auto printed=s.format(a,fast.output),parsed=s.parse(a,printed),roundtrip=simplify(a,parsed,facts);
		enforce(!roundtrip.exhausted&&roundtrip.output==fast.output,c.name~" round-trip: "~printed);
		exportLean(a,checked);
	}
}
unittest{
	// Every incomplete result remains exportable, and passes share their limits.
	foreach(limit;[0,1,2,5,10,20,50,100]){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto input=s.parse(a,"2*round(x)=2"); Options options; options.trace=true; options.maxRewrites=limit;
		auto r=simplify(a,input,options); exportLean(a,r);
		if(!r.exhausted) enforce(simplify(a,r.output).output==r.output,"limited result is not stable");
		options.maxRewrites=100_000; options.maxAlgebraWork=limit;
		r=simplify(a,input,options); enforce(r.exhausted,"work limit was reset"); exportLean(a,r);
	}
}
int main(string[] args){
	enforce(args.length==2,"expected certificate directory"); mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Term[] facts; foreach(f;c.facts) facts~=s.parse(a,f);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,simplify(a,s.parse(a,c.input),facts,Options(DensityMode.preserve,true))));
	}
	foreach(limit;[0,1,10,100]) foreach(work;[false,true]){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		Options options; options.trace=true;
		if(work) options.maxAlgebraWork=limit; else options.maxRewrites=limit;
		write(buildPath(args[1],(work?"Work":"Rewrites")~to!string(limit)~".lean"),
			exportLean(a,simplify(a,s.parse(a,"2*round(x)=2"),options)));
	}
	writeln("Exported ",examples().length+8," convergence certificates."); return 0;
}
