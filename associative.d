module qsym.associative;
import qsym.ir;
import qsym.table:Table;
import qsym.budget;
import std.algorithm:sort;
import core.bitop:bsr;
import std.exception:enforce;
@safe:

package struct Operand{ Term term; uint count; }

// Canonical counted multisets, shared by all AC steps in a derivation. A
// compressed binary trie shares unchanged branches when a region grows. Its
// depth is at most 32, independent of expression depth and multiplicities.
// Binary terms remain the rule/proof interface; no cancellation is implicit.
package final class Regions{
	private Arena a;
	private struct Node{ uint key,mask,left,right,length; }
	private Node[] nodes=[Node.init];
	private Table!(Node,uint) interned;
	private Table!(ulong,uint) unions;
	private uint[2][] roots;
	this(Arena a){ this.a=a; }
	size_t length()const{ return nodes.length-1; }
	private void spend(Budget budget){ if(budget !is null) budget.spend(); }
	private uint intern(Node n){
		auto old=interned.get(n,uint.max); if(old!=uint.max) return old;
		enforce(nodes.length<uint.max,"associative pool exceeds 32-bit limit");
		auto id=cast(uint)nodes.length; nodes~=n; interned.set(n,id); return id;
	}
	private uint leaf(uint atom,uint count){ return intern(Node(atom,0,atom,count,1)); }
	private uint branch(uint mask,uint left,uint right){
		auto l=nodes[left],r=nodes[right];
		return intern(Node(l.key,mask,left,right,l.length+r.length));
	}
	private bool contains(Node x,Node y){ return x.mask>y.mask&&!((x.key^y.key)&~(x.mask|(x.mask-1))); }
	private uint merge(uint x,uint y,Budget budget){
		spend(budget); if(!x) return y; if(!y) return x;
		if(x>y){ auto t=x; x=y; y=t; }
		auto key=(cast(ulong)x<<32)|y,old=unions.get(key,uint.max);
		if(old!=uint.max) return old;
		auto l=nodes[x],r=nodes[y]; uint result;
		if(!l.mask&&!r.mask&&l.key==r.key){
			if(r.right>uint.max-l.right) throw new Limit;
			result=leaf(l.key,l.right+r.right);
		}else if(l.mask==r.mask&&l.mask&&!((l.key^r.key)&~(l.mask|(l.mask-1))))
			result=branch(l.mask,merge(l.left,r.left,budget),merge(l.right,r.right,budget));
		else if(contains(l,r)) result=r.key&l.mask?
			branch(l.mask,l.left,merge(l.right,y,budget)):branch(l.mask,merge(l.left,y,budget),l.right);
		else if(contains(r,l)) result=l.key&r.mask?
			branch(r.mask,r.left,merge(x,r.right,budget)):branch(r.mask,merge(x,r.left,budget),r.right);
		else{
			auto mask=1u<<bsr(l.key^r.key);
			result=l.key&mask?branch(mask,y,x):branch(mask,x,y);
		}
		if(budget !is null&&nodes[result].length>budget.maxTerms) throw new Limit;
		unions.set(key,result); return result;
	}
	uint from(Term t,Op op,Budget budget=null){
		a.check(t); enforce(op==Op.add||op==Op.mul,"associative operation expected");
		auto kind=op==Op.mul?1:0;
		if(t.id<roots.length&&roots[t.id][kind]){
			spend(budget); auto cached=roots[t.id][kind]-1;
			if(budget !is null&&nodes[cached].length>budget.maxTerms) throw new Limit;
			return cached;
		}
		if(roots.length<a.length) roots.length=a.length;
		uint[] pending=[t.id];
		while(pending.length){
			spend(budget); auto id=pending[$-1];
			if(roots[id][kind]){ --pending.length; continue; }
			auto atom=a.at(id),n=a.node(atom); uint result;
			if(n.op==op){
				auto l=roots[n.a][kind],r=roots[n.b][kind];
				if(!l){ pending~=n.a; continue; }
				if(!r){ pending~=n.b; continue; }
				result=merge(l-1,r-1,budget);
			}else if(!a.isNumber(atom)||!(op==Op.add?a.number(atom).zero:a.number(atom).one)) result=leaf(id,1);
			roots[id][kind]=result+1; --pending.length;
		}
		auto result=roots[t.id][kind]-1;
		if(budget !is null&&nodes[result].length>budget.maxTerms) throw new Limit;
		return result;
	}
	Operand[] terms(Term t,Op op,Budget budget=null){
		enforce(op==Op.add||op==Op.mul,"associative operation expected");
		if(a.node(t).op!=op){
			spend(budget);
			if(a.isNumber(t)&&(op==Op.add?a.number(t).zero:a.number(t).one)) return [];
			if(budget !is null&&!budget.maxTerms) throw new Limit;
			return [Operand(t,1)];
		}
		auto root=from(t,op,budget); Operand[] result; uint[] pending;
		if(root) pending~=root;
		while(pending.length){
			spend(budget); auto n=nodes[pending[$-1]]; --pending.length;
			if(n.mask) pending~=[n.right,n.left]; else result~=Operand(a.at(n.left),n.right);
		}
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
		seen.set(t.id,true); auto n=a.node(t); nodes~=t.id;
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
		auto n=a.node(a.at(id)),count=counts.get(id,0);
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
		assertThrown!Limit(pool.from(join(t,t),op));
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
