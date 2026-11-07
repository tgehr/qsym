module qsym.associative;
import qsym.ir;
import qsym.table:Table;
import qsym.budget;
import std.algorithm:sort;
import std.exception:enforce;
@safe:

package struct Operand{ Term term; uint count; }

// An associative region is a multiset of operands, not all its binary prefixes.
// Propagate multiplicities through the DAG once, including shared subexpressions.
package Operand[] operands(Arena a,Term root,Op op,Budget budget=null){
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
