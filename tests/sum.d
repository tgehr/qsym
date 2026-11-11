module sum_tests;
import qsym;
import qsym.sum;
import qsym.sumproof;
import std.exception:assertThrown,enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.conv:to;
import std.stdio:writeln;
@safe:

unittest{
	auto owner=Session.open(); auto a=owner.arena;
	auto pool=new SumPool(a,Sort.real_),x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1);
	auto b=pool.builder(); b.add(x); b.add(y); b.add(x);
	auto s=b.finish();
	assert(s==pool.from(a.add(x,a.add(y,x))));
	assert(pool.terms(s)==[Summand(x,2),Summand(y,1)]);
	auto snapshot=pool.terms(s); snapshot[0].count=7;
	assert(pool.terms(s)[0].count==2);
	auto c=pool.builder(); c.add(s,3);
	assert(pool.terms(c.finish())==[Summand(x,6),Summand(y,3)]);
	auto n=pool.length; assert(b.finish()==s&&pool.length==n);
	b.add(a.real_(1),128); auto folded=pool.fold(b.finish());
	auto expected=pool.builder(); expected.add(x,2); expected.add(y); expected.add(a.real_(128));
	assert(folded==expected.finish());
	auto partial=a.inv(a.real_(0)),cancel=pool.builder(); cancel.add(partial); cancel.add(a.neg(partial));
	assert(pool.fold(cancel.finish())==cancel.finish());
	assertThrown(exportSumLean(pool,cancel.finish(),pool.from(a.real_(0))));
	auto overflow=pool.builder(); overflow.add(x,uint.max); assertThrown(overflow.add(x));
	auto other=Session.open(); assertThrown(b.add(other.arena.real_(0)));
	assertThrown(b.add(a.complex(0)));
	auto foreign=new SumPool(a,Sort.real_); assertThrown(b.add(foreign.from(x)));
	Sum invalid; assertThrown(pool.terms(invalid));
	owner.close(); assertThrown(pool.terms(s)); assertThrown(b.finish());
}
unittest{
	auto owner=Session.open(); auto a=owner.arena; auto pool=new SumPool(a,Sort.real_);
	auto x=a.variable(Sort.real_,0),t=pool.from(x);
	foreach(i;0..20){ auto b=pool.builder(); b.add(t,2); t=b.finish(); }
	assert(pool.terms(t)==[Summand(x,1u<<20)]);
}

@system void main(string[] args){
	enforce(args.length==2,"usage: sum-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(scalar;[Sort.real_,Sort.complex]){
		auto owner=Session.open(); auto a=owner.arena; auto pool=new SumPool(a,scalar);
		auto x=a.variable(scalar,0),b=pool.builder();
		b.add(x,2); b.add(a.number(Number(1),scalar),128);
		if(scalar==Sort.complex) b.add(a.complex(Rational(0),Rational(BigInt(1),BigInt(2))),6);
		auto input=b.finish(),output=pool.fold(input),expected=pool.builder();
		expected.add(x,2); expected.add(scalar==Sort.complex?a.complex(128,3):a.real_(128));
		assert(output==expected.finish());
		write(buildPath(args[1],to!string(scalar)~".lean"),exportSumLean(pool,input,output));
	}
	foreach(i,source;["x+1/2+3/2","1/x+1-1","log(x)+1+2","1/0-1/0","[false]*(1/0)+3+4"]){
		auto owner=Session.open(); auto a=owner.arena; auto pool=new SumPool(a,Sort.real_);
		Syntax syntax; syntax.declare("x:ℝ"); auto input=pool.from(syntax.parse(a,source,Sort.real_));
		auto filename="Partial"~to!string(i)~".lean";
		write(buildPath(args[1],filename),exportSumLean(pool,input,pool.fold(input)));
	}
	writeln("Wrote native sum certificates.");
}
