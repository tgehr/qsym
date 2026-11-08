module bench_joins;
import qsym;
import std.stdio:writeln;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.string:replace;
import std.conv:to;
import std.datetime.stopwatch:StopWatch,AutoStart;
import std.exception:enforce;
@system void main(string[] args){
	enforce(args.length==2,"usage: join-bench DIRECTORY"); mkdirRecurse(args[1]);
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]) foreach(count;[16u,64u]){
		auto owner=Session.open(); auto a=owner.arena; Operand[] inputs,outputs;
		foreach(i;0..count){
			auto x=a.variable(s,i); inputs~=Operand(a.inv(a.inv(x)),1); outputs~=Operand(x,1);
		}
		auto input=a.region(op,s,inputs),watch=StopWatch(AutoStart.yes);
		auto r=simplify(a,input,Options(DensityMode.preserve,true));
		enforce(!r.exhausted&&r.output==a.region(op,s,outputs),"region mapping failed");
		auto name=(s==Sort.real_?"Real":"Complex")~(op==Op.add?"Sum":"Product")~to!string(count);
		auto code=exportLean(a,r).replace("QSym.Certificate","QSym.Benchmark."~name);
		writeln(name,"\t",watch.peek.total!"usecs","\t",code.length,"\t",r.derivation.deductions.length);
		write(buildPath(args[1],name~".lean"),code);
	}
}
