module cutoff_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.conv:to;
import std.string:indexOf;
@safe:

private string cutoff(string bound="10",string base="0"){
	return "μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then "~base~" else if n≤"~bound~" then f(n sub 1) else f(n+1)";
}
private struct Case{ string name,source,expected; }
private Case[] cases(){
	return [
		Case("Domain","domain("~cutoff()~")","{n:ℕ | n≤10}"),
		Case("Function",cutoff(),"λ(n:{n:ℕ | n≤10}). 0"),
		Case("Parameters",cutoff("b","a"),"λ(n:{n:ℕ | n≤b}). a"),
		Case("ZeroBoundDomain","domain("~cutoff("0")~")","{n:ℕ | n=0}"),
		Case("Boundary","("~cutoff("10","5")~")(10)","5"),
		Case("Outside","defined(("~cutoff()~")(11))","false"),
		Case("UndefinedInput","defined(("~cutoff()~")(0 sub 1))","false"),
		Case("SymbolicMembership","k∈domain("~cutoff()~")","k≤10"),
		Case("Nested","λ(k:ℕ)."~cutoff(),"λ(k:ℕ). λ(n:{n:ℕ | n≤10}). 0")
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s; s.declare("a:ℕ,b:ℕ,k:ℕ");
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true)); auto output=s.format(a,r);
		enforce(!r.exhausted&&output==c.expected,c.name~": "~output);
		auto again=s.run(a,output); enforce(s.format(a,again)==output,c.name~" round trip");
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
}
unittest{
	run();
	foreach(b;0..5) foreach(n;0..9){
		auto owner=Session.open(); FunctionSyntax s;
		auto r=s.run(owner.arena,"defined(("~cutoff(to!string(b),"7")~")("~to!string(n)~"))");
		enforce(s.format(owner.arena,r)==(n<=b?"true":"false"),"cutoff boundary");
	}
	foreach(source;[
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else if n≤10 then f(n sub 2) else f(n+1)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else if n≤10 then f(n sub 1) else f(n sub 1)",
		"μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else if n≤10 then f(n sub 1) else f(n)"]){
		auto owner=Session.open(); FunctionSyntax s; auto r=s.run(owner.arena,source);
		enforce(s.format(owner.arena,r).indexOf("μ(")>=0,"unsupported cutoff replaced");
	}
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/cutoff"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," cutoff certificates"); return 0;
}
