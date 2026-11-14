module qsym.embeddings;
import qsym.ir;
import qsym.derive;
import qsym.budget;
import qsym.generated.rules;
@safe:

// Pull exact embeddings out of arithmetic, then compare in the source type.
// Literal witnesses are checked by numeric replay; all other steps use laws.
package final class Embeddings{
	private Arena a;
	private Derivation d;
	private Budget budget;
	private Proof[ulong] narrowed,expanded;
	this(Arena a,Derivation d,Budget budget){ this.a=a; this.d=d; this.budget=budget; }
	static bool conversion(Node n){ return n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castRC; }
	Term source(Term t){ while(conversion(a.view(t))) t=a.viewChild(t,0); return t; }
	/// A homogeneous proof whose endpoint embeds the smallest available scalar
	/// expression. This runs outside the rewrite loop: expansion of embeddings
	/// remains useful inside real/complex algebra.
	Proof narrow(Term t,uint ctx,uint depth=0){
		auto key=(cast(ulong)ctx<<32)|t.id;
		if(auto p=key in narrowed) return *p;
		auto p=narrowUncached(t,ctx,depth); narrowed[key]=p; return p;
	}
	private Proof narrowUncached(Term t,uint ctx,uint depth){
		budget.spend();
		auto n=a.view(t);
		if(!numeric(n.sort)||n.sort==Sort.natural) return d.refl(t,ctx);
		if(depth>=128) throw new Limit;
		if(a.isNumber(t)){
			auto v=a.number(t);
			auto s=!v.im.zero?Sort.complex:!v.re.integral?Sort.rational:v.re<Rational(0)?Sort.integer:Sort.natural;
			return s==n.sort?d.refl(t,ctx):d.numeric(t,a.castTo(a.number(v,s),n.sort),ctx);
		}
		bool candidate=conversion(n)||n.op==Op.add||n.op==Op.mul||n.op==Op.inv||n.op==Op.pow||n.op==Op.mask;
		if(n.op==Op.builtin) switch(cast(Builtin)n.value){
			case Builtin.addZ,Builtin.addQ,Builtin.mulZ,Builtin.mulQ,
				Builtin.powZN,Builtin.powQN,Builtin.powRN,Builtin.powCN,Builtin.powRZ,Builtin.powCZ:candidate=true; break;
			default:break;
		}
		if(!candidate) return d.refl(t,ctx);
		Proof[] children;
		foreach(i;0..n.arity) children~=narrow(a.viewChild(t,i),ctx,depth+1);
		auto p=d.congr(t,children,ctx);
		if(!conversion(n)) p=d.trans(p,contract(p.after,ctx,true),ctx);
		if(!conversion(a.view(p.after))) return d.refl(t,ctx);
		// Each contraction descends one rank. Continue inside that embedding.
		if(conversion(n)) return p;
		auto lower=narrow(a.viewChild(p.after,0),ctx,depth+1);
		return d.trans(p,d.congr(p.after,[lower],ctx),ctx);
	}
	Proof lift(Proof p,Sort target,uint ctx){
		auto t=a.castTo(p.before,target);
		if(a.sort(p.before)==target) return p;
		return d.congr(t,[lift(p,a.sort(a.viewChild(t,0)),ctx)],ctx);
	}
	private Law law(string op)(Sort target){
		switch(target){
			case Sort.integer:return __traits(getMember,Law,"embed_NZ_"~op);
			case Sort.rational:return __traits(getMember,Law,"embed_ZQ_"~op);
			case Sort.real_:return __traits(getMember,Law,"embed_QR_"~op);
			case Sort.complex:
				static if(op=="lt"||op=="le") assert(0);
				else return __traits(getMember,Law,"embed_RC_"~op);
			default:assert(0);
		}
	}
	// This direction is opt-in and used before polynomial identity checking.
	Proof expand(Term t,uint ctx,uint depth=0){
		if(depth>=128) throw new Limit;
		auto key=(cast(ulong)ctx<<32)|t.id;
		if(auto p=key in expanded) return *p;
		auto p=expandUncached(t,ctx,depth); expanded[key]=p; return p;
	}
	private Proof expandUncached(Term t,uint ctx,uint depth){
		budget.spend(); auto n=a.view(t); Proof[] children;
		foreach(i;0..n.arity) children~=expand(a.viewChild(t,i),ctx,depth+1);
		auto p=d.congr(t,children,ctx),u=a.view(p.after);
		if(u.op==Op.builtin&&u.value>=Builtin.powNN&&u.value<=Builtin.powCN){
			auto exponent=a.viewChild(p.after,1),e=a.view(exponent);
			if(e.op==Op.builtin&&e.value==Builtin.addN){
				auto right=a.viewChild(exponent,1);
				if(a.isNumber(right)&&a.number(right).one){
					Law selected;
					static foreach(suffix;["NN","ZN","QN","RN","CN"]) if(u.value==__traits(getMember,Builtin,"pow"~suffix)) selected=__traits(getMember,Law,"sum_shift_power_"~suffix);
					auto step=d.rule(instantiate(a,selected,[a.viewChild(p.after,0),a.viewChild(exponent,0)]),[],ctx);
					return d.trans(p,step,ctx);
				}
			}
		}
		if(!conversion(u)) return p;
		auto child=a.viewChild(p.after,0),v=a.view(child);
		if(a.isNumber(child)) return d.trans(p,d.numeric(p.after,a.number(a.number(child),u.sort),ctx),ctx);
		string op;
		if(v.op==Op.add||v.op==Op.builtin&&(v.value==Builtin.addN||v.value==Builtin.addZ||v.value==Builtin.addQ)) op="add";
		if(v.op==Op.mul||v.op==Op.builtin&&(v.value==Builtin.mulN||v.value==Builtin.mulZ||v.value==Builtin.mulQ)) op="mul";
		if(v.op==Op.pow) op="pow";
		if(v.op==Op.builtin&&v.value>=Builtin.powNN&&v.value<=Builtin.powRN) op="powN";
		if(v.op==Op.builtin&&v.value==Builtin.invQ&&u.sort==Sort.real_) op="inv";
		if(!op.length) return p;
		Law selected;
		static foreach(pair;["NZ","ZQ","QR","RC"]){
			if(cast(Builtin)u.value==__traits(getMember,Builtin,"cast"~pair)){
				static foreach(kind;["add","mul","pow","powN"])
					if(op==kind) selected=__traits(getMember,Law,"sum_expand_"~pair~"_"~kind);
			}
		}
		if(op=="inv") selected=Law.sum_expand_QR_inv;
		Term[] args=[a.viewChild(child,0)];
		if(op=="pow") args~=a.real_(v.value); else if(v.arity==2) args~=a.viewChild(child,1);
		auto step=d.rule(instantiate(a,selected,args),[],ctx);
		if(step.before!=p.after) return p;
		return d.trans(p,d.trans(step,expand(step.after,ctx,depth+1),ctx),ctx);
	}
	Proof run(Term t,uint ctx){
		auto n=a.view(t);
		bool integrality=n.op==Op.builtin&&n.value==Builtin.isIntR;
		auto comparison=n.op==Op.nonzero||n.op==Op.lt||n.op==Op.le;
		if(n.op==Op.builtin) switch(cast(Builtin)n.value){
			case Builtin.nonzeroZ,Builtin.nonzeroQ,Builtin.ltZ,Builtin.ltQ,Builtin.leZ,Builtin.leQ:comparison=true; break;
			default:break;
		}
		if(!comparison&&!integrality) return d.refl(t,ctx);
		// Contract the scalar operands together, and keep the result only when
		// the predicate can move to the source type. Ordinary arithmetic retains
		// its existing normal form, including trig period and radical factors.
		Proof[uint] normalized;
		foreach(id;a.viewPostorder(t)){
			budget.spend(); auto u=a.at(id),v=a.view(u);
			if(id!=t.id&&!numeric(v.sort)){ normalized[id]=d.refl(u,ctx); continue; }
			Proof[] children;
			foreach(i;0..v.arity) children~=normalized[a.viewChild(u,i).id];
			auto p=d.congr(u,children,ctx),q=contract(p.after,ctx);
			if(id==t.id){
				if(q.after!=p.after) return d.trans(p,q,ctx);
				auto operand=a.view(a.viewChild(p.after,0));
				// Integer differences may still be necessary for natural equality;
				// their natural embeddings have no reverse expansion to cycle with.
				if(operand.sort==Sort.integer) return p;
				if(integrality&&operand.op==Op.builtin&&operand.value==Builtin.castQR) return p;
				return d.refl(t,ctx);
			}
			normalized[id]=d.trans(p,q,ctx);
		}
		assert(0);
	}
	private Proof contract(Term t,uint ctx,bool narrowing=false){
		auto n=a.view(t),op=n.op,s=n.sort;
		bool indexedNatural,indexedInteger;
		if(op==Op.builtin){
			switch(cast(Builtin)n.value){
				case Builtin.powZN,Builtin.powQN,Builtin.powRN,Builtin.powCN:
					if(!narrowing) return d.refl(t,ctx);
					indexedNatural=true; op=Op.pow; break;
				case Builtin.powRZ,Builtin.powCZ:
					if(!narrowing) return d.refl(t,ctx);
					indexedInteger=true; op=Op.pow; break;
				case Builtin.addZ,Builtin.addQ:op=Op.add; break;
				case Builtin.mulZ,Builtin.mulQ:op=Op.mul; break;
				case Builtin.nonzeroZ,Builtin.nonzeroQ:op=Op.nonzero; break;
				case Builtin.ltZ,Builtin.ltQ:op=Op.lt; break;
				case Builtin.leZ,Builtin.leQ:op=Op.le; break;
				default:return d.refl(t,ctx);
			}
		}
		if(op==Op.nonzero||op==Op.lt||op==Op.le) s=a.sort(a.at(n.a));
		if(rank(s)<=rank(Sort.natural)) return d.refl(t,ctx);
		auto source=s==Sort.integer?Sort.natural:s==Sort.rational?Sort.integer:s==Sort.real_?Sort.rational:Sort.real_;
		auto castFunction=builtin("cast"~suffix(source)~suffix(s));
		Law selected;
		switch(op){
			case Op.add:selected=law!"add"(s); break;
			case Op.mul:selected=law!"mul"(s); break;
			case Op.pow:selected=law!"pow"(s); break;
			case Op.mask:selected=law!"mask"(s); break;
			case Op.nonzero:selected=law!"nonzero"(s); break;
			case Op.lt:selected=law!"lt"(s); break;
			case Op.le:selected=law!"le"(s); break;
			case Op.inv:
				if(s!=Sort.real_&&s!=Sort.complex) return d.refl(t,ctx);
				selected=s==Sort.real_?Law.embed_QR_inv:Law.embed_RC_inv; break;
			default:return d.refl(t,ctx);
		}
		if(indexedNatural) selected=law!"powN"(s);
		if(indexedInteger) selected=s==Sort.real_?Law.embed_QR_powZ:Law.embed_RC_powZ;
		Proof[] children; Term[] bindings; bool embedded;
		foreach(i;0..n.arity){
			budget.spend(); auto child=a.viewChild(t,i),c=a.view(child);
			if(op==Op.mask&&i==0||(indexedNatural||indexedInteger)&&i==1){ children~=d.refl(child,ctx); bindings~=child; continue; }
			if(c.op==Op.builtin&&c.value==castFunction){
				embedded=true; children~=d.refl(child,ctx); bindings~=a.at(c.a);
			}else if(a.isNumber(child)){
				auto v=a.number(child);
				if(!v.im.zero||rank(source)<rank(Sort.rational)&&!v.re.integral||source==Sort.natural&&v.re<Rational(0)) return d.refl(t,ctx);
				auto lower=a.number(v,source),lifted=a.call(castFunction,[lower]);
				children~=d.numeric(child,lifted,ctx); bindings~=lower;
			}else return d.refl(t,ctx);
		}
		if(!embedded&&!narrowing) return d.refl(t,ctx);
		if(op==Op.pow&&!indexedNatural&&!indexedInteger) bindings~=a.real_(n.value);
		auto p=d.congr(t,children,ctx),q=d.rule(instantiate(a,selected,bindings),[],ctx);
		return d.trans(p,q,ctx);
	}
}
