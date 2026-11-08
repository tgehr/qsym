module qsym.tests.lookup;
import qsym;
import qsym.derive:Derivation;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.conv:to;
import std.string:indexOf;
import std.stdio:writeln;
@safe:

private Result example(Arena a,Sort s,Op op,uint count){
	auto unit=a.number(Number(op==Op.add?0:1),s),raw=unit;
	Operand[] operands;
	foreach(i;0..count){
		auto x=a.mask(a.variable(Sort.boolean,i),a.inv(a.variable(s,i)));
		operands~=Operand(x,1);
		raw=op==Op.add?a.add(x,raw,true):a.mul(x,raw,true);
	}
	// Exercise an empty atom environment and unit elimination in a large bridge.
	foreach(i;0..10) raw=op==Op.add?a.add(unit,raw,true):a.mul(unit,raw,true);
	auto result=a.region(op,s,operands),d=new Derivation(a,true);
	Result r; r.input=r.proofInput=raw; r.output=result; r.traced=true;
	r.derivation=d; r.certificate=d.ac(raw,result,op,0); return r;
}
unittest{
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]) foreach(count;[0u,1u,3u,17u,64u]){
		auto owner=Session.open(); auto a=owner.arena,r=example(a,s,op,count);
		auto code=exportLean(a,r);
		assert(a.canonical(r.input)==r.output);
		assert(code.indexOf("Replay.Lookup.get")>=0,"AC atom lookup still walks a list");
		assert(code.indexOf("List (Option")<0,"large AC environment is still linear");
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: lookup-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]) foreach(count;[0u,1u,3u,17u,64u]){
		auto owner=Session.open(); auto a=owner.arena;
		auto name=(s==Sort.real_?"Real":"Complex")~(op==Op.add?"Sum":"Product")~to!string(count);
		write(buildPath(args[1],name~".lean"),exportLean(a,example(a,s,op,count)));
	}
	writeln("Wrote AC lookup certificates.");
}
