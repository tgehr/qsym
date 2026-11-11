module qsym.subtypes;
import qsym.ir;
import qsym.derive;
import qsym.budget;
import qsym.engine;
import qsym.embeddings;
@safe:

// Give arithmetic inside fixed-signature functions the same embedded normal
// form as arithmetic parsed directly in its smallest scalar type. All proofs
// remain homogeneous; only the public result drops the outer cast chain.
package final class Subtypes{
	private Arena a;
	private Derivation d;
	private Engine engine;
	private Embeddings embeddings;
	private Budget budget;
	private Proof[ulong] memo;
	private bool[ulong] active;
	this(Arena a,Derivation d,Engine engine,Embeddings embeddings,Budget budget){
		this.a=a; this.d=d; this.engine=engine; this.embeddings=embeddings; this.budget=budget;
	}
	Proof run(Term t,uint ctx,uint depth=0){
		auto key=(cast(ulong)ctx<<32)|t.id;
		if(auto p=key in memo) return *p;
		if(active.get(key,false)) return d.refl(t,ctx);
		if(depth>=128) throw new Limit;
		budget.spend(); active[key]=true; scope(exit) active.remove(key);
		auto n=a.view(t);
		// Keep ordinary coefficients in arithmetic and function arguments.
		// Embeddings.narrow introduces literal witnesses only when an entire
		// operation can descend; simplify handles a literal public result.
		if(a.isNumber(t)||!n.arity) return d.refl(t,ctx);
		Proof[] children;
		foreach(i;0..n.arity) children~=run(a.viewChild(t,i),ctx,depth+1);
		auto p=d.congr(t,children,ctx);
		if(p.after!=t){
			auto q=engine.go(p.after,ctx);
			if(q.after!=p.after&&q.after!=t){
				p=d.trans(p,d.trans(q,run(q.after,ctx,depth+1),ctx),ctx);
				memo[key]=p; return p;
			}
		}
		if(numeric(n.sort)&&!a.isNumber(p.after)){
			auto q=embeddings.narrow(p.after,ctx),lower=embeddings.source(q.after);
			if(a.sort(lower)!=n.sort){
				auto normalized=engine.go(lower,ctx);
				normalized=d.trans(normalized,run(normalized.after,ctx,depth+1),ctx);
				p=d.trans(p,d.trans(q,embeddings.lift(normalized,n.sort,ctx),ctx),ctx);
			}
		}
		memo[key]=p; return p;
	}
}
