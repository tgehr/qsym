module main;
import qsym;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln,stderr;
import std.conv:to;
import std.datetime.stopwatch:StopWatch,AutoStart;
import std.exception:enforce;
import qsym.tools.repl:repl;

int main(string[] args){
	try{
		if(args.length==1||args.length==2&&args[1]=="repl") return repl();
		auto session=Session.open();
		auto a=session.arena;
		auto x=a.variable(Sort.real_,0);
		auto masked=a.mask(a.nonzero(x),a.inv(x));
		auto input=a.add(a.mul(masked,a.real_(1)),a.real_(0));
		auto strict=simplify(a,input,Options(DensityMode.preserve,true));
		if(args[1]=="demo"){
			writeln("Guarded reciprocal: ",domain(a,input).must);
			writeln("Simplified IR:\n",dump(a,strict.output));
			auto d=a.puncture(a.lebesgue());
			writeln("Density mode retains puncture: ",simplify(a,d).output==d);
			auto erased=simplify(a,d,Options(DensityMode.distributionOnly));
			writeln("Distribution-only result:\n",dump(a,erased.output));
			writeln("Native results are unchecked until the exported Lean certificate passes.");
			return 0;
		}
		if(args[1]=="export"){
			enforce(args.length==3,"usage: qsym export DIRECTORY");
			mkdirRecurse(args[2]);
			write(buildPath(args[2],"Guarded.lean"),exportLean(a,strict));
			auto d=a.puncture(a.puncture(a.lebesgue()));
			write(buildPath(args[2],"Density.lean"),exportLean(a,
				simplify(a,d,Options(DensityMode.preserve,true))));
			write(buildPath(args[2],"Erasure.lean"),exportLean(a,
				simplify(a,d,Options(DensityMode.distributionOnly,true))));
			write(buildPath(args[2],"Equivalence.lean"),exportEquivalence(a,
				simplify(a,d,Options(DensityMode.distributionOnly,true)),
				simplify(a,a.lebesgue(),Options(DensityMode.distributionOnly,true))));
			auto z=a.variable(Sort.complex,0);
			write(buildPath(args[2],"Complex.lean"),exportLean(a,
				simplify(a,a.add(a.conj(a.conj(z)),a.complex(0)),Options(DensityMode.preserve,true))));
			write(buildPath(args[2],"Undefined.lean"),exportLean(a,
				simplify(a,a.mul(a.real_(0),a.inv(a.real_(0))),Options(DensityMode.preserve,true))));
			write(buildPath(args[2],"Masked.lean"),exportLean(a,
				simplify(a,a.mask(a.boolean(false),a.inv(a.real_(0))),Options(DensityMode.preserve,true))));
			writeln("Wrote seven certificates; run make verify to check them.");
			return 0;
		}
		if(args[1]=="bench"){
			auto count=args.length>2?to!uint(args[2]):50_000;
			enforce(count<=1_000_000,"benchmark node limit is 1,000,000");
			auto t=x;
			foreach(i;0..count) t=a.add(t,a.real_(0));
			auto watch=StopWatch(AutoStart.yes);
			auto r=simplify(a,t,Options(DensityMode.preserve,false,count+1));
			watch.stop(); enforce(r.output==x&&!r.exhausted,"benchmark normalization failed");
			writeln(count," nested additions, ",a.length," interned nodes, ",
				watch.peek.total!"msecs"," ms (synthetic benchmark; no PSI comparison)");
			return 0;
		}
		throw new Exception("usage: qsym [repl | demo | export DIRECTORY | bench [N]]");
	}catch(Exception e){ stderr.writeln(e.msg); return 1; }
}
