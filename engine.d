module qsym.engine;
import qsym.ir;
import qsym.derive;
import qsym.budget;
import qsym.field:Field,compare;
import qsym.elementary:Elementary;
import qsym.predicates:Predicates;
import std.algorithm:sort;
import qsym.generated.rules;
import qsym.table:Table;
@safe:

package final class Engine{
	private Arena a;
	private Derivation d;
	private Budget budget;
	private Field field;
	private Elementary elementary;
	private Predicates predicates;
	private size_t rewritesLeft;
	private uint depth,epoch;
	private struct MemoKey{ ulong term; uint revision; }
	private Table!(MemoKey,uint) memo;
	private struct ContextKey{ uint parent,guard,revision; bool value; }
	private Table!(ContextKey,uint) branches;
	private Table!(ulong,uint) truths;
	private uint[] revisions=[0];
	private Proof[] proofs;
	private uint[] roots;
	private Table!(ulong,bool) active,proving;
	private Proof[][] facts=[[]];
	this(Arena a,Derivation d,Budget budget,size_t rewrites){
		this.a=a; this.d=d; this.budget=budget; rewritesLeft=rewrites;
		field=new Field(a,d,budget,&normalize);
		elementary=new Elementary(a,budget);
		predicates=new Predicates(a,budget,field,elementary);
	}
	private void remember(K)(ref Table!(K,uint) index,K key,Proof p){
		index.set(key,cast(uint)proofs.length); proofs~=p;
	}
	private void memoize(ulong key,Proof p){
		if(key>uint.max){ remember(memo,MemoKey(key,revision(cast(uint)(key>>33))),p); return; }
		if(key>=roots.length) roots.length=cast(size_t)key+1;
		roots[cast(uint)key]=cast(uint)proofs.length+1; proofs~=p;
	}
	private ulong key(Term t,uint ctx,bool probe=false){ return (cast(ulong)ctx<<33)|(cast(ulong)probe<<32)|t.id; }
	private Proof normalize(Term t,uint ctx){ return go(t,ctx); }
	// Invalidate child caches when inherited facts change during seeding.
	private uint revision(uint ctx){
		uint result;
		while(ctx){
			if(revisions[ctx]>result) result=revisions[ctx];
			ctx=d.contexts[ctx].parent;
		}
		return result;
	}
	private Proof[] known(uint ctx){
		Proof[] result;
		while(ctx){ result~=facts[ctx]; ctx=d.contexts[ctx].parent; }
		return result;
	}
	private uint enter(uint parent,Term guard,bool value){
		budget.spend();
		auto k=ContextKey(parent,guard.id,revision(parent),value);
		auto cached=branches.get(k,uint.max);
		if(cached!=uint.max) return cached;
		auto ctx=d.enter(parent,guard,value);
		facts.length=d.contexts.length;
		revisions.length=d.contexts.length;
		// Recursive visits during seeding must share the same assumptions.
		branches.set(k,ctx);
		seed(ctx); resolve(ctx); return ctx;
	}
	private void seed(uint ctx){
		auto guard=d.contexts[ctx].guard,value=d.contexts[ctx].value;
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
		// Normalization may have memoized terms before learning these equalities.
		revisions[ctx]=++epoch;
	}
	private void resolve(uint ctx){
		for(bool changed=true;changed;){
			changed=false;
			foreach(f;known(ctx)){
				budget.spend(); auto n=a.node(f.before);
				if(!f.known||n.op!=Op.or_) continue;
				foreach(law;[Law.bool_or_prune_left,Law.bool_or_prune_right]){
					auto i=instantiate(a,law,[a.at(n.a),a.at(n.b)]); bool found;
					foreach(old;known(ctx)) if(old.known&&old.before==i.result){ found=true; break; }
					if(found) continue;
					Proof p; if(!instanceProof(i,ctx,p)) continue;
					auto q=d.transport(f,p,ctx); facts[ctx]~=q; remember(truths,key(q.before,ctx),q);
					revisions[ctx]=++epoch; changed=true;
				}
			}
		}
	}
	uint assume(Term[] conditions){
		uint ctx;
		foreach(f;conditions) ctx=d.enter(ctx,f,true);
		facts.length=d.contexts.length;
		revisions.length=d.contexts.length;
		try{ foreach(i;1..ctx+1) seed(i); resolve(ctx); }
		catch(Limit e){ budget.exhausted=true; }
		return ctx;
	}
	private bool instanceProof(Instance i,uint ctx,out Proof result){
		// Reject inadmissible bindings before recursively searching for premises.
		foreach(c;i.conditions){
			budget.spend();
			if(c.literal&&!a.isNumber(c.term)) return false;
			if(c.defined&&!d.domain(i.before,c.term,ctx).found) return false;
		}
		Proof[] premises;
		foreach(c;i.conditions) if(!c.literal&&!c.defined){
			Proof p; if(!prove(c.term,ctx,p)) return false;
			premises~=p;
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
		auto numeric=field.literal(t,ctx);
		if(numeric.after!=t){
			if(numeric.after!=a.boolean(true)) return false;
			result=numeric; remember(truths,k,result); return true;
		}
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
	private Proof pairs(Term t,uint ctx){
		auto n=a.node(t);
		if((n.op!=Op.add&&n.op!=Op.mul)||(n.sort!=Sort.real_&&n.sort!=Sort.complex)) return d.refl(t,ctx);
		auto laws=pairRewrites(n.op); if(!laws.length) return d.refl(t,ctx);
		Term[] leaves,pending=[t];
		while(pending.length){
			budget.spend(); auto u=pending[$-1]; --pending.length; auto v=a.node(u);
			if(v.op==n.op) pending~=[a.at(v.b),a.at(v.a)]; else leaves~=u;
			if(leaves.length+pending.length>budget.maxTerms) return d.refl(t,ctx);
		}
		Term join(Term x,Term y){ return n.op==Op.add?a.add(x,y):a.mul(x,y); }
		foreach(i,x;leaves) foreach(j; i+1..leaves.length) foreach(reverse;[false,true]){
			auto left=reverse?leaves[j]:x,right=reverse?x:leaves[j];
			foreach(law;laws){
				budget.spend();
				if(!pairCandidate(law,a.node(left),a.node(right))) continue;
				auto pair=join(left,right);
				Proof q; if(!attempt(law,pair,ctx,q)||q.after==pair) continue;
				Term[] rest; foreach(k,y;leaves) if(k!=i&&k!=j) rest~=y;
				if(!rest.length) return d.trans(d.ac(t,pair,n.op,ctx),q,ctx);
				auto r=rest[0]; foreach(y;rest[1..$]) r=join(r,y);
				auto grouped=join(pair,r);
				return d.trans(d.ac(t,grouped,n.op,ctx),d.congr(grouped,[q,d.refl(r,ctx)],ctx),ctx);
			}
		}
		return d.refl(t,ctx);
	}
	private bool substitute(Term t,uint ctx,out Proof result){
		auto n=a.node(t);
		if((n.op!=Op.variable&&n.op!=Op.builtin&&n.op!=Op.abs&&n.op!=Op.conj)||(n.sort!=Sort.real_&&n.sort!=Sort.complex)) return false;
		struct Candidate{ Term coefficient,remainder,value; size_t variables; }
		Candidate[] candidates;
		foreach(f;known(ctx)){
			auto q=a.node(f.before);
			if(!f.known||q.op!=Op.not_) continue;
			q=a.node(a.at(q.a)); if(q.op!=Op.nonzero||a.sort(a.at(q.a))!=n.sort) continue;
			Term coefficient,remainder;
			if(!field.affine(a.at(q.a),t,coefficient,remainder)) continue;
			auto value=a.div(a.neg(remainder),coefficient); size_t count;
			foreach(id;a.postorder(value)) if(a.node(a.at(id)).op==Op.variable) ++count;
			candidates~=Candidate(coefficient,remainder,value,count);
		}
		sort!((x,y)=>x.variables!=y.variables?x.variables<y.variables:compare(a,x.value,y.value)<0)(candidates);
		foreach(c;candidates){
			auto changed=go(c.value,ctx); bool ordered=changed.after!=t;
			foreach(id;a.postorder(changed.after)){
				auto v=a.at(id);
				if(a.node(v).op==Op.variable&&compare(a,v,t)<=0){ ordered=false; break; }
			}
			if(!ordered) continue;
			auto law=n.sort==Sort.real_?Law.real_solve_affine:Law.complex_solve_affine;
			Proof p; if(!instanceProof(instantiate(a,law,[t,c.coefficient,c.remainder]),ctx,p)) continue;
			result=d.trans(p,changed,ctx); return true;
		}
		return false;
	}
	private bool strictBound(Term t,uint ctx,out Proof result){
		auto n=a.node(t);
		if(n.op!=Op.le||!ctx) return false;
		bool excluded;
		foreach(f;known(ctx)) if(f.known&&a.node(f.before).op==Op.nonzero){ excluded=true; break; }
		if(!excluded) return false;
		auto i=instantiate(a,Law.real_le_strict,[a.at(n.a),a.at(n.b)]);
		// Tighten only from an established exclusion, avoiding cyclic sign search.
		auto p=go(i.conditions[0].term,0,true);
		foreach(f;known(ctx)) if(f.known&&f.before==p.after){
			if(!rewritesLeft) throw new Limit;
			--rewritesLeft; result=d.rule(i,[d.trans(p,f,ctx)],ctx); return true;
		}
		return false;
	}
	private size_t guardCost(Term t){
		size_t cost; Term[] pending=[t];
		while(pending.length){
			budget.spend(); auto u=pending[$-1]; --pending.length; auto n=a.node(u);
			cost+=n.op==Op.le?2:1;
			if(cost>budget.maxTerms) return size_t.max;
			foreach(i;0..n.arity) pending~=a.child(u,i);
		}
		return cost;
	}
	Proof go(Term t,uint ctx=0,bool probe=false){
		auto k=key(t,ctx,probe);
		auto cached=k<=uint.max?(t.id<roots.length?roots[t.id]:0):memo.get(MemoKey(k,revision(ctx)),uint.max)+1;
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
			auto numeric=field.literal(current,ctx);
			if(numeric.after!=current){ p=d.trans(p,numeric,ctx); memoize(k,p); return p; }
			if(ctx&&!probe){
				Proof q;
				if(substitute(current,ctx,q)){ p=d.trans(p,q,ctx); memoize(k,p); return p; }
			}
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
			Proof strict;
			if(!probe&&strictBound(current,ctx,strict)){
				p=d.trans(p,strict,ctx); p=d.trans(p,go(p.after,ctx,probe),ctx); memoize(k,p); return p;
			}
			foreach(law;rewrites(n.op)){
				Proof q;
				if(attempt(law,current,ctx,q)&&q.after!=current){
					p=d.trans(p,q,ctx); p=d.trans(p,go(p.after,ctx,probe),ctx);
					memoize(k,p); return p;
				}
			}
			Instance proposal; Proof proposed;
			if(elementary.propose(current,proposal)&&instanceProof(proposal,ctx,proposed)&&proposed.after!=current){
				p=d.trans(p,proposed,ctx); p=d.trans(p,go(p.after,ctx,probe),ctx); memoize(k,p); return p;
			}
			if(n.op==Op.nonzero||n.op==Op.lt||n.op==Op.le){
				auto residual=n.op==Op.nonzero?a.at(n.a):go(a.sub(a.at(n.a),a.at(n.b)),ctx,true).after;
				if(predicates.propose(current,residual,proposal)&&instanceProof(proposal,ctx,proposed)&&proposed.after!=current){
					p=d.trans(p,proposed,ctx); p=d.trans(p,go(p.after,ctx,probe),ctx); memoize(k,p); return p;
				}
			}
			// Premise normalization must not start another guarded search.
			if(!probe&&(n.op==Op.mask||n.op==Op.and_||n.op==Op.or_)){
				auto c=enter(ctx,a.at(n.a),n.op!=Op.or_);
				auto q=go(a.at(n.b),c,probe);
				if(q.after!=q.before){
					p=d.trans(p,d.scoped(current,q,ctx),ctx);
					p=d.trans(p,go(p.after,ctx,probe),ctx); memoize(k,p); return p;
				}
			}
			if(!probe&&(n.op==Op.and_||n.op==Op.or_)&&d.domain(current,a.at(n.b),ctx).found){
				auto c=enter(ctx,a.at(n.b),n.op==Op.and_),q=go(a.at(n.a),c,probe);
				// Only commute to make progress; partial guards still require definedness.
				if(q.after!=q.before&&guardCost(q.after)<guardCost(q.before)){
					Proof swap;
					auto law=n.op==Op.and_?Law.bool_and_swap:Law.bool_or_swap;
					if(instanceProof(instantiate(a,law,[a.at(n.a),a.at(n.b)]),ctx,swap)){
						p=d.trans(p,swap,ctx); p=d.trans(p,d.scoped(p.after,q,ctx),ctx);
						// Restore the original guard order when the reduced guard is defined.
						if(instanceProof(instantiate(a,law,[a.child(p.after,0),a.child(p.after,1)]),ctx,swap)) p=d.trans(p,swap,ctx);
						p=d.trans(p,go(p.after,ctx,probe),ctx); memoize(k,p); return p;
					}
				}
			}
			auto q=pairs(current,ctx);
			if(q.after==current) q=field.run(current,ctx);
			p=d.trans(p,q,ctx);
			if(q.after!=current) p=d.trans(p,go(p.after,ctx,probe),ctx);
			memoize(k,p); return p;
		}catch(Limit e){ budget.exhausted=true; return d.refl(t,ctx); }
	}
}
