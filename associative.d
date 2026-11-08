module qsym.associative;
import qsym.ir;
import qsym.table:Table;
import qsym.budget;
import std.algorithm:sort;
import std.exception:enforce;
@safe:

package final class Regions{
	private Arena a;
	this(Arena a){ this.a=a; }
	size_t length(){ return a.multisetStorage; }
	uint from(Term t,Op op,Budget budget=null){
		if(budget !is null) budget.spend();
		auto result=a.multiset(t,op);
		if(budget !is null&&a.multisetSize(result)>budget.maxTerms) throw new Limit;
		return result;
	}
	Operand[] terms(Term t,Op op,Budget budget=null){
		auto result=a.multisetTerms(from(t,op,budget));
		if(budget !is null) budget.spend(result.length);
		return result;
	}
}

// Independent flat-DAG oracle for representation tests.
version(unittest) private Operand[] operands(Arena a,Term root,Op op,Budget budget=null){
	enforce(op==Op.add||op==Op.mul,"associative operation expected");
	uint[] nodes; Term[] pending=[root]; Table!(uint,bool) seen;
	Operand[] result; Table!(uint,uint) indices,counts;
	while(pending.length){
		auto t=pending[$-1]; --pending.length;
		if(seen.get(t.id,false)) continue;
		if(budget !is null) budget.spend();
		seen.set(t.id,true); auto n=a.view(t); nodes~=t.id;
		if(n.op==op) pending~=[a.at(n.b),a.at(n.a)];
		else if(!a.isNumber(t)||!(op==Op.add?a.number(t).zero:a.number(t).one)){
			indices.set(t.id,cast(uint)result.length); result~=Operand(t,0);
			if(budget !is null&&result.length>budget.maxTerms) throw new Limit;
		}
	}
	// Arena edges always point to older nodes. No recursive traversal or copying
	// of a growing operand array is needed for an incrementally constructed sum.
	sort!"a>b"(nodes); counts.set(root.id,1);
	foreach(id;nodes){
		auto n=a.view(a.at(id)),count=counts.get(id,0);
		if(n.op==op) foreach(child;[n.a,n.b]){
			auto old=counts.get(child,0);
			if(count>uint.max-old) throw new Limit;
			counts.set(child,old+count);
		}else if(indices.contains(id)) result[indices.get(id,0)].count=count;
	}
	return result;
}

unittest{
	auto session=Session.open(); auto a=session.arena;
	auto x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1);
	auto common=a.add(x,y),t=a.add(a.add(common,common),a.add(x,a.real_(0)));
	auto terms=operands(a,t,Op.add);
	assert(terms==[Operand(x,3),Operand(y,2)]);
	foreach(i;0..20) common=a.add(common,common);
	terms=operands(a,common,Op.add);
	assert(terms==[Operand(x,1u<<20),Operand(y,1u<<20)]);
}

unittest{
	import std.exception:assertThrown;
	auto session=Session.open(); auto a=session.arena; auto pool=new Regions(a);
	auto x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1),zero=a.real_(0),one=a.real_(1);
	foreach(op;[Op.add,Op.mul]){
		Term join(Term l,Term r){ return op==Op.add?a.add(l,r):a.mul(l,r); }
		auto left=join(join(x,y),x),right=join(y,join(x,x));
		assert(pool.from(left,op)==pool.from(right,op));
		assert(pool.terms(left,op)==[Operand(x,2),Operand(y,1)]);
		assert(pool.from(join(x,op==Op.add?zero:one),op)==pool.from(x,op));
		auto snapshot=pool.terms(left,op); snapshot[0].count=17;
		assert(pool.terms(left,op)[0].count==2);
		assertThrown!Limit(pool.from(left,op,new Budget(100,1,1)));
		auto partial=a.inv(zero);
		assert(pool.from(join(zero,partial),op)!=pool.from(zero,op));
		auto t=x;
		foreach(i;0..31) t=join(t,t);
		assert(pool.terms(t,op)==[Operand(x,1u<<31)]);
		assertThrown(join(t,t));
	}
	// Persistent prefixes share branches; neither storage nor construction
	// scales with the sum of all prefix lengths.
	auto t=zero,u=zero;
	foreach(i;0..1024){
		auto v=a.variable(Sort.real_,i+2); t=a.add(t,v); u=a.add(v,u);
		assert(pool.from(t,Op.add)==pool.from(u,Op.add));
	}
	assert(pool.length<20_000,"copied every associative prefix");
	auto budget=new Budget(1,2048,1),before=pool.length;
	pool.from(t,Op.add,budget); assert(!budget.remaining&&pool.length==before);
	// Compare against independent DAG propagation on mixed grouping/sharing.
	Term[] trees=[x,y,zero,one,a.inv(x)]; uint seed=41;
	foreach(i;0..256){
		seed=seed*1664525+1013904223; auto l=trees[seed%trees.length];
		seed=seed*1664525+1013904223; auto r=trees[seed%trees.length];
		auto op=i%3?Op.add:Op.mul,v=op==Op.add?a.add(l,r):a.mul(l,r); trees~=v;
		auto expected=operands(a,v,op);
		sort!((x,y)=>x.term.id<y.term.id)(expected);
		assert(pool.terms(v,op)==expected);
	}
	auto other=Session.open(); assertThrown(pool.from(other.arena.real_(0),Op.add));
	assertThrown(pool.from(x,Op.inv));
	session.close(); assertThrown(pool.from(x,Op.add));
}
