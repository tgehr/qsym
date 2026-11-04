module qsym.engine;
import qsym.ir;
import qsym.derive;
import qsym.budget;
import qsym.field:Field;
import qsym.generated.rules;
import qsym.table:Table;
@safe:

package final class Engine{
	private Arena a;
	private Derivation d;
	private Budget budget;
	private Field field;
	private size_t rewritesLeft;
	private uint depth;
	private Table!(ulong,uint) memo,truths;
	private Proof[] proofs;
	private uint[] roots;
	private Table!(ulong,bool) active,proving;
	private Proof[][] facts=[[]];
	this(Arena a,Derivation d,Budget budget,size_t rewrites){
		this.a=a; this.d=d; this.budget=budget; rewritesLeft=rewrites;
		field=new Field(a,d,budget,&normalize);
	}
	private void remember(ref Table!(ulong,uint) index,ulong key,Proof p){
		index.set(key,cast(uint)proofs.length); proofs~=p;
	}
	private void memoize(ulong key,Proof p){
		if(key>uint.max){ remember(memo,key,p); return; }
		if(key>=roots.length) roots.length=cast(size_t)key+1;
		roots[cast(uint)key]=cast(uint)proofs.length+1; proofs~=p;
	}
	private ulong key(Term t,uint ctx,bool probe=false){ return (cast(ulong)ctx<<33)|(cast(ulong)probe<<32)|t.id; }
	private Proof normalize(Term t,uint ctx){ return go(t,ctx); }
	private Proof[] known(uint ctx){
		Proof[] result;
		while(ctx){ result~=facts[ctx]; ctx=d.contexts[ctx].parent; }
		return result;
	}
	private uint enter(uint parent,Term guard,bool value){
		budget.spend();
		auto ctx=d.enter(parent,guard,value);
		facts.length=d.contexts.length;
		struct Item{ Term term; bool value; uint[] path; }
		Item[] pending=[Item(guard,value)];
		while(pending.length){
			budget.spend(); auto item=pending[$-1]; --pending.length;
			auto p=d.assumption(ctx,item.path,ctx);
			facts[ctx]~=p; remember(truths,key(p.before,ctx),p);
			auto n=a.node(item.term);
			if(n.op==Op.not_) pending~=Item(a.at(n.a),!item.value,item.path~0u);
			else if(n.op==Op.and_&&item.value||n.op==Op.or_&&!item.value)
				pending~=[Item(a.at(n.b),item.value,item.path~1u),Item(a.at(n.a),item.value,item.path~0u)];
		}
		// Normalize strong assumptions and retain their proofs. This matters
		// for a false disjunct, e.g. ¬(x<0) becoming 0≤x.
		auto original=facts[ctx].dup;
		foreach(p;original){
			auto q=go(p.before,ctx,true);
			if(q.after!=p.before){ auto f=d.transport(p,q,ctx); facts[ctx]~=f; remember(truths,key(f.before,ctx),f); }
		}
		return ctx;
	}
	private bool instanceProof(Instance i,uint ctx,out Proof result){
		Proof[] premises;
		foreach(c;i.conditions){
			budget.spend();
			if(c.literal){ if(!a.isNumber(c.term)) return false; }
			else if(c.defined){ if(!d.domain(i.before,c.term).found) return false; }
			else{
				Proof p; if(!prove(c.term,ctx,p)) return false;
				premises~=p;
			}
		}
		if(!rewritesLeft) throw new Limit;
		--rewritesLeft;
		result=d.rule(i,premises,ctx); return true;
	}
	private bool complete(Law law,Term[] bindings,uint ctx,out Proof result,uint nesting=0){
		budget.spend(); if(nesting>=128) return false;
		size_t missing; foreach(b;bindings) if(b.id==uint.max) ++missing;
		if(!missing) return instanceProof(instantiate(a,law,bindings),ctx,result);
		auto available=known(ctx);
		foreach(i;0..conditionCount(law)) foreach(f;available){
			budget.spend(); auto bs=bindings.dup;
			if(!match(a,law,cast(int)i,f.before,bs)) continue;
			size_t rest; foreach(b;bs) if(b.id==uint.max) ++rest;
			if(rest>=missing) continue;
			if(complete(law,bs,ctx,result,nesting+1)) return true;
		}
		return false;
	}
	private bool attempt(Law law,Term t,uint ctx,out Proof result){
		budget.spend(); Term[] bindings;
		return match(a,law,-1,t,bindings)&&complete(law,bindings,ctx,result);
	}
	private bool prove(Term t,uint ctx,out Proof result){
		budget.spend();
		auto k=key(t,ctx);
		if(truths.contains(k)){ result=proofs[truths.get(k,uint.max)]; return true; }
		foreach(f;known(ctx)) if(f.before==t){ result=f; return true; }
		if(t==a.boolean(true)){ result=d.refl(t,ctx); return true; }
		if(proving.get(k,false)) return false;
		proving.set(k,true); scope(exit) proving.set(k,false);
		foreach(law;inferences(a.node(t).op)) if(attempt(law,t,ctx,result)){
			remember(truths,k,result); return true;
		}
		auto p=go(t,ctx,true);
		if(p.after==a.boolean(true)){ result=p; remember(truths,k,result); return true; }
		if(p.after!=t){
			Proof q;
			if(prove(p.after,ctx,q)){ result=d.trans(p,q,ctx); remember(truths,k,result); return true; }
		}
		return false;
	}
	Proof go(Term t,uint ctx=0,bool probe=false){
		auto k=key(t,ctx,probe);
		auto cached=k<=uint.max?(t.id<roots.length?roots[t.id]:0):memo.get(k,uint.max)+1;
		if(cached) return proofs[cached-1];
		if(active.get(k,false)) return d.refl(t,ctx);
		if(!rewritesLeft){ budget.exhausted=true; return d.refl(t,ctx); }
		try{
			if(depth>=128) throw new Limit;
			++depth; scope(exit) --depth;
			budget.spend(); active.set(k,true); scope(exit) active.set(k,false);
			auto n=a.node(t); Proof[] cs;
			foreach(i;0..n.arity) cs~=go(a.child(t,i),ctx,probe);
			auto p=d.congr(t,cs,ctx);
			auto current=p.after; n=a.node(current);
			if(ctx&&!probe&&n.sort==Sort.real_&&!a.isNumber(current)){
				auto i=instantiate(a,Law.real_known_zero,[current]); Proof q;
				if(instanceProof(i,ctx,q)){ p=d.trans(p,q,ctx); memoize(k,p); return p; }
			}
			if(!probe&&n.sort==Sort.boolean){
				Proof q;
				if(prove(current,ctx,q)){ p=d.trans(p,q,ctx); memoize(k,p); return p; }
				if(prove(a.not_(current),ctx,q)){
					auto f=d.rule(instantiate(a,Law.bool_false,[current]),[q],ctx);
					p=d.trans(p,f,ctx); memoize(k,p); return p;
				}
			}
			auto numeric=field.literal(current,ctx);
			if(numeric.after!=current){ p=d.trans(p,numeric,ctx); memoize(k,p); return p; }
			foreach(law;rewrites(n.op)){
				Proof q;
				if(attempt(law,current,ctx,q)&&q.after!=current){
					p=d.trans(p,q,ctx); p=d.trans(p,go(p.after,ctx,probe),ctx);
					memoize(k,p); return p;
				}
			}
			if(n.op==Op.mask||n.op==Op.and_||n.op==Op.or_){
				auto c=enter(ctx,a.at(n.a),n.op!=Op.or_);
				auto q=go(a.at(n.b),c,probe);
				if(q.after!=q.before){
					p=d.trans(p,d.scoped(current,q,ctx),ctx);
					p=d.trans(p,go(p.after,ctx,probe),ctx); memoize(k,p); return p;
				}
			}
			auto q=field.run(current,ctx);
			p=d.trans(p,q,ctx);
			if(q.after!=current) p=d.trans(p,go(p.after,ctx,probe),ctx);
			memoize(k,p); return p;
		}catch(Limit e){ budget.exhausted=true; return d.refl(t,ctx); }
	}
}
