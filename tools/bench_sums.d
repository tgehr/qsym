module bench_sums;
import qsym;
import qsym.sum;
import qsym.sumproof;
import std.stdio:writeln;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.string:replace;
import std.conv:to;
import std.datetime.stopwatch:StopWatch,AutoStart;
import std.exception:enforce;
@system void main(string[] args){
	enforce(args.length==2||args.length==3,"usage: sum-bench DIRECTORY [SIZE]");
	auto count=args.length==3?to!uint(args[2]):128u;
	enforce(count>0&&count<=4096,"size must be between 1 and 4096"); mkdirRecurse(args[1]);
	foreach(shape;["Repeated","Distinct","Shared","Guarded","Product"]){
		auto owner=Session.open(); auto a=owner.arena; auto x=a.variable(Sort.real_,0);
		auto t=shape=="Repeated"?x:shape=="Product"?a.real_(1):a.real_(0);
		if(shape=="Shared"){
			auto chunk=a.add(x,a.real_(1));
			for(auto n=count;n;n>>=1){
				if(n&1) t=a.add(t,chunk);
				if(n>1) chunk=a.add(chunk,chunk);
			}
		}
		else foreach(i;0..count){
			auto term=shape=="Repeated"?a.real_(1):shape=="Product"?a.add(x,a.real_(1)):a.variable(Sort.real_,i);
			if(shape=="Guarded") term=a.mask(a.variable(Sort.boolean,i),term);
			t=shape=="Product"?a.mul(t,term):a.add(t,term);
		}
		foreach(native;[false,true]){
			if(native&&shape=="Product") continue;
			auto name=(native?"SumFold":"Native")~shape; string code; size_t steps;
			auto watch=StopWatch(AutoStart.yes);
			if(native){
				auto pool=new SumPool(a,Sort.real_),input=pool.from(t),output=pool.fold(input);
				code=exportSumLean(pool,input,output).replace("QSym.SumCertificate","QSym.Benchmark."~name);
				steps=pool.terms(output).length;
			}else{
				auto options=Options(DensityMode.preserve,true); options.maxTerms=count*2+1024;
				auto r=simplify(a,t,options); enforce(!r.exhausted,"benchmark budget exhausted: "~shape);
				code=exportLean(a,r).replace("QSym.Certificate","QSym.Benchmark."~name);
				steps=r.derivation.deductions.length;
			}
			auto micros=watch.peek.total!"usecs";
			write(buildPath(args[1],name~".lean"),code);
			writeln(name,"\t",micros,"\t",code.length,"\t",steps);
		}
	}
}
