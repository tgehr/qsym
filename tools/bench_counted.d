module bench_counted;
import qsym;
import std.stdio:writeln;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.string:replace;
import std.conv:to;
import std.datetime.stopwatch:StopWatch,AutoStart;
import std.exception:enforce;
@system void main(string[] args){
	enforce(args.length==2||args.length==3,"usage: counted-bench DIRECTORY [COUNT]");
	auto count=args.length==3?to!uint(args[2]):257u;
	enforce(count>0,"positive count expected"); mkdirRecurse(args[1]);
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]){
		auto owner=Session.open(); auto a=owner.arena,x=a.variable(s,0);
		auto input=a.region(op,s,[Operand(x,count)]),watch=StopWatch(AutoStart.yes);
		auto fast=simplify(a,input); auto fastTime=watch.peek.total!"usecs";
		watch.reset(); watch.start();
		auto r=simplify(a,input,Options(DensityMode.preserve,true));
		enforce(!fast.exhausted&&!r.exhausted&&fast.output==r.output,"counted benchmark failed");
		auto name=(s==Sort.real_?"Real":"Complex")~(op==Op.add?"Sum":"Product")~to!string(count);
		auto code=exportLean(a,r).replace("QSym.Certificate","QSym.Benchmark."~name);
		writeln(name,"\t",fastTime,"\t",watch.peek.total!"usecs","\t",code.length,"\t",r.derivation.deductions.length);
		write(buildPath(args[1],name~".lean"),code);
	}
}
