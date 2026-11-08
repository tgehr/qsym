module qsym.matching;
import qsym.ir;
import qsym.order:compare;
import std.algorithm:sort;
@safe:

final class MatchWork{
	uint remaining=4096;
	bool spend(){ if(!remaining) return false; --remaining; return true; }
}
alias MatchFunction=bool delegate(Term,ref Term[]) @safe;
struct MatchOperand{ MatchFunction test; int variable=-1; uint head=uint.max; bool literal,bounded; }

// Match fixed operands first, then bound groups, then remainder variables.
// There is no unrestricted enumeration of partitions of the operand multiset.
bool matchRegion(Arena a,Term input,Op op,MatchOperand[] patterns,ref Term[] bindings,MatchWork work){
	auto remaining=a.multisetTerms(a.multiset(input,op));
	MatchOperand[] fixed;
	struct Variable{ uint index,count; bool literal,bounded; }
	Variable[] variables;
	foreach(p;patterns){
		if(p.variable<0){ fixed~=p; continue; }
		bool found;
		foreach(ref v;variables) if(v.index==p.variable){ ++v.count; found=true; break; }
		if(!found) variables~=Variable(cast(uint)p.variable,1,p.literal,p.bounded);
	}
	sort!((x,y)=>x.literal!=y.literal?x.literal:x.index<y.index)(variables);
	uint head(Term t){ auto n=a.view(t); return cast(uint)n.op|(cast(uint)n.sort<<8)|(n.op==Op.builtin?cast(uint)n.value<<16:0); }
	auto unit=a.number(Number(op==Op.add?0:1),a.sort(input));
	bool ordered=variables.length>1;
	foreach(p;fixed){
		if(p.head==uint.max){ ordered=true; continue; }
		uint matches;
		foreach(e;remaining){ if(!work.spend()) return false; matches+=head(e.term)==p.head; }
		if(!matches&&head(unit)!=p.head) return false;
		ordered|=matches>1;
	}
	if(ordered) sort!((x,y)=>compare(a,x.term,y.term)<0)(remaining);
	bool remove(Term t,uint count,ref Operand[] from){
		foreach(e;a.multisetTerms(a.multiset(t,op))){
			bool found;
			foreach(ref f;from) if(f.term==e.term){
				auto n=cast(ulong)e.count*count; if(n>f.count) return false;
				f.count-=cast(uint)n; found=true; break;
			}
			if(!found) return false;
		}
		return true;
	}
	bool groups(size_t at,Operand[] rest,ref Term[] slots){
		if(!work.spend()) return false;
		if(at==variables.length){ foreach(e;rest) if(e.count) return false; return true; }
		auto v=variables[at],bound=slots[v.index];
		if(bound.id!=uint.max){ auto next=rest.dup; return remove(bound,v.count,next)&&groups(at+1,next,slots); }
		bool last=true;
		foreach(w;variables[at+1..$]) if(slots[w.index].id==uint.max){ last=false; break; }
		if(last){
			auto next=rest.dup;
			foreach(w;variables[at+1..$]) if(!remove(slots[w.index],w.count,next)) return false;
			bool nonempty;
			foreach(ref e;next){ if(e.count%v.count) return false; e.count/=v.count; nonempty|=e.count!=0; }
			// Do not split an atom as x+0 or x*1 just to enable a general
			// distributive rewrite. A fixed factor may still expose its unit.
			if(!nonempty&&(!fixed.length||variables.length>1)) return false;
			if(v.bounded){
				// Automatic outer rewrites must not hoist a guard around a
				// growing product and repeatedly explore all its contexts.
				uint size;
				foreach(e;next){ if(e.count>8-size) return false; size+=e.count; }
			}
			auto group=a.region(op,a.sort(input),next);
			if(v.literal&&!a.isNumber(group)) return false;
			slots[v.index]=group; return true;
		}
		foreach(e;rest) if(e.count>=v.count){
			if(!work.spend()) return false;
			if(v.literal&&!a.isNumber(e.term)) continue;
			auto next=rest.dup,bs=slots.dup; bs[v.index]=e.term;
			if(remove(e.term,v.count,next)&&groups(at+1,next,bs)){ slots=bs; return true; }
		}
		return false;
	}
	bool select(size_t at,Operand[] rest,ref Term[] slots){
		if(!work.spend()) return false;
		if(at==fixed.length) return groups(0,rest,slots);
		auto p=fixed[at];
		foreach(i,e;rest) if(e.count){
			if(!work.spend()) return false;
			if(p.head!=uint.max&&p.head!=head(e.term)) continue;
			auto bs=slots.dup;
			if(!p.test(e.term,bs)) continue;
			auto next=rest.dup; --next[i].count;
			if(select(at+1,next,bs)){ slots=bs; return true; }
		}
		// Neutral operands are absent from canonical storage.
		auto bs=slots.dup;
		if(p.test(unit,bs)&&select(at+1,rest,bs)){ slots=bs; return true; }
		return false;
	}
	auto bs=bindings.dup;
	if(!select(0,remaining,bs)) return false;
	bindings=bs; return true;
}
