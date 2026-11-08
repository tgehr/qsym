module qsym.sum;
import qsym.ir;
import qsym.table:Table;
import qsym.associative:Regions;
import qsym.field:compare;
import std.algorithm:sort;
import std.exception:enforce;
@safe:

// Experimental native n-ary sums. No cancellation or distribution is implicit.
struct Sum{
	private SumPool owner;
	private uint index=uint.max;
	uint id()const{ return index; }
	bool opEquals(Sum other)const{ return owner is other.owner&&index==other.index; }
}
struct Summand{ Term term; uint count; }

final class SumPool{
	private Arena a;
	private Sort scalar;
	private Term zero;
	private Regions regions;
	private struct Count{ uint atom,count; }
	private struct Span{ uint start,length; }
	private Count[] data;
	private Span[] nodes;
	private Table!(string,uint) interned;
	this(Arena a,Sort scalar){
		enforce(scalar==Sort.real_||scalar==Sort.complex,"sum requires a real or complex scalar type");
		this.a=a; this.scalar=scalar; zero=a.number(Number(0),scalar); regions=new Regions(a);
	}
	Arena arena(){ a.check(zero); return a; }
	Sort type(){ a.check(zero); return scalar; }
	size_t length()const{ return nodes.length; }
	private void check(Sum sum){ a.check(zero); enforce(sum.owner is this&&sum.index<nodes.length,"invalid or foreign sum"); }
	private const(Count)[] view(Sum sum){ check(sum); auto r=nodes[sum.index]; return data[r.start..r.start+r.length]; }
	Summand[] terms(Sum sum){
		Summand[] result; foreach(c;view(sum)) result~=Summand(a.at(c.atom),c.count); return result;
	}
	SumBuilder builder(){ a.check(zero); return new SumBuilder(this); }
	Sum from(Term t){ auto b=builder(); b.add(t); return b.finish(); }
	private Sum intern(Count[] cs){
		a.check(zero);
		sort!((x,y)=>compare(a,a.at(x.atom),a.at(y.atom))<0)(cs);
		char[] bytes;
		foreach(c;cs) foreach(v;[c.atom,c.count]) foreach(i;0..4) bytes~=cast(char)(v>>(8*i));
		auto key=bytes.idup,found=interned.get(key,uint.max);
		if(found!=uint.max) return Sum(this,found);
		enforce(nodes.length<uint.max&&cs.length<=uint.max-data.length,"sum pool exceeds 32-bit limit");
		auto id=cast(uint)nodes.length;
		nodes~=Span(cast(uint)data.length,cast(uint)cs.length); data~=cs;
		interned.set(key,id); return Sum(this,id);
	}
	Sum fold(Sum sum,size_t maxWords=1024){
		auto b=builder(); Number constant;
		foreach(c;view(sum)){
			auto t=a.at(c.atom);
			if(!a.isNumber(t)){ b.addAtom(t,c.count); continue; }
			auto q=a.number(t);
			enforce(q.words<=maxWords,"sum literal exceeds coefficient limit");
			constant=constant+q*Number(c.count);
			enforce(constant.words<=maxWords,"sum coefficient limit exceeded");
		}
		if(!constant.zero) b.addAtom(a.number(constant,scalar),1);
		return b.finish();
	}
}

final class SumBuilder{
	private SumPool pool;
	private Table!(uint,uint) counts;
	private uint[] atoms;
	private this(SumPool pool){ this.pool=pool; }
	private void addAtom(Term t,uint count){
		auto a=pool.arena(); enforce(a.sort(t)==pool.scalar,"sum operand type mismatch");
		if(!count||a.isNumber(t)&&a.number(t).zero) return;
		auto old=counts.get(t.id,0);
		enforce(count<=uint.max-old,"sum multiplicity overflow");
		if(!old) atoms~=t.id;
		counts.set(t.id,old+count);
	}
	void add(Term t,uint count=1){
		auto a=pool.arena(); enforce(a.sort(t)==pool.scalar,"sum operand type mismatch");
		if(!count) return;
		foreach(e;pool.regions.terms(t,Op.add)){
			enforce(e.count<=uint.max/count,"sum multiplicity overflow"); addAtom(e.term,e.count*count);
		}
	}
	void add(Sum sum,uint count=1){
		foreach(c;pool.view(sum)){
			enforce(!count||c.count<=uint.max/count,"sum multiplicity overflow"); addAtom(pool.a.at(c.atom),c.count*count);
		}
	}
	Sum finish(){
		SumPool.Count[] cs;
		foreach(id;atoms) cs~=SumPool.Count(id,counts.get(id,0));
		return pool.intern(cs);
	}
}
