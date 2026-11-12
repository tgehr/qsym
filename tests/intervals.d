module interval_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.conv:to;
import std.string:indexOf;
@safe:

private string strict(string upper="10"){
	return "μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 7 else if n<"~upper~" then f(n sub 1) else f(n+1)";
}
private string interval(string lower="10",string upper="20"){
	return "μ(f:ℕ→ℕ).λ(n:ℕ).if n<"~lower~" then f(n sub 1) else if n="~lower~" then 7 else if n<"~upper~" then f(n sub 1) else f(n+1)";
}
private struct Case{ string name,source,expected; }
private Case[] cases(){
	return [
		Case("StrictFunction",strict(),"λ(n:{n:ℕ | n≤9}). 7"),
		Case("StrictDomain","domain("~strict()~")","{n:ℕ | n≤9}"),
		Case("StrictInside","("~strict()~")(9)","7"),
		Case("StrictOutside","defined(("~strict()~")(10))","false"),
		Case("ShiftedFunction",interval(),"λ(n:{n:ℕ | 10≤n∧n≤19}). 7"),
		Case("ShiftedDomain","domain("~interval()~")","{n:ℕ | 10≤n∧n≤19}"),
		Case("ShiftedBase","("~interval()~")(10)","7"),
		Case("ShiftedInside","("~interval()~")(19)","7"),
		Case("ShiftedBelow","defined(("~interval()~")(9))","false"),
		Case("ShiftedZero","defined(("~interval()~")(0))","false"),
		Case("ShiftedAbove","defined(("~interval()~")(20))","false"),
		Case("ShiftedPartial","defined(("~interval()~")(0 sub 1))","false")
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true)),text=s.format(a,r);
		enforce(!r.exhausted&&text==c.expected,c.name~": "~text);
		enforce(s.format(a,s.run(a,text))==text,c.name~" round trip");
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
}
unittest{
	run();
	foreach(lower;1..5) foreach(width;1..5) foreach(n;0..11){
		auto owner=Session.open(); FunctionSyntax s;
		auto r=s.run(owner.arena,"defined(("~interval(to!string(lower),to!string(lower+width))~")("~to!string(n)~"))");
		enforce(!r.exhausted&&s.format(owner.arena,r)==(lower<=n&&n<lower+width?"true":"false"),"interval boundary");
	}
	foreach(upper;1..5) foreach(n;0..7){
		auto owner=Session.open(); FunctionSyntax s;
		auto r=s.run(owner.arena,"defined(("~strict(to!string(upper))~")("~to!string(n)~"))");
		enforce(!r.exhausted&&s.format(owner.arena,r)==(n<upper?"true":"false"),"strict boundary");
	}
	auto owner=Session.open(); FunctionSyntax s;
	auto source="μ(f:ℕ→ℕ).λ(n:ℕ).if n<10 then f(n sub 2) else if n=10 then 7 else if n<20 then f(n sub 1) else f(n+1)";
	enforce(s.format(owner.arena,s.run(owner.arena,source)).indexOf("μ(")>=0,"unsupported interval solved");
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/intervals"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," interval certificates"); return 0;
}
