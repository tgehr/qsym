module bench_associative;
import qsym;
import std.stdio:writeln;
import std.datetime.stopwatch:StopWatch,AutoStart;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.string:replace;
import std.conv:to;
import std.exception:enforce;
@system void main(string[] args){
	enforce(args.length==2,"usage: associative-bench DIRECTORY"); mkdirRecurse(args[1]);
	foreach(count;[16u,64u,128u,256u]){
		auto session=Session.open(); auto a=session.arena; auto t=a.real_(0);
		foreach(i;0..count){
			t=a.add(t,a.pow(a.call(Builtin.sinR,[a.variable(Sort.real_,i)]),2));
			t=a.add(t,a.pow(a.call(Builtin.cosR,[a.variable(Sort.real_,i+count)]),2));
		}
		auto options=Options.init; options.maxTerms=1024; options.maxAlgebraWork=100_000;
		auto watch=StopWatch(AutoStart.yes),r=simplify(a,t,options);
		writeln("unmatched pairs ",count,": ",watch.peek.total!"usecs"," us, exhausted=",r.exhausted);
		enforce(!r.exhausted,"pair-search budget exceeded");
	}
	foreach(count;[128u,512u]){
		auto session=Session.open(); auto a=session.arena; auto t=a.variable(Sort.real_,0);
		foreach(i;0..count) t=a.add(t,a.real_(1));
		auto watch=StopWatch(AutoStart.yes),r=simplify(a,t,Options(DensityMode.preserve,true));
		enforce(!r.exhausted&&r.output==a.add(a.variable(Sort.real_,0),a.real_(count)),"incorrect deep sum");
		auto name="Deep"~to!string(count),output=exportLean(a,r).replace("QSym.Certificate","QSym.Benchmark."~name);
		writeln(name,": ",watch.peek.total!"usecs"," us, ",output.length," bytes, ",r.derivation.deductions.length," steps");
		write(buildPath(args[1],name~".lean"),output);
	}
}
