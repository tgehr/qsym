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
	this(Arena a,Derivation d,Budget budget){ this.a=a; this.d=d; this.budget=budget; }
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
	private Proof contract(Term t,uint ctx){
		auto n=a.view(t),op=n.op,s=n.sort;
		if(op==Op.builtin){
			switch(cast(Builtin)n.value){
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
		Proof[] children; Term[] bindings; bool embedded;
		foreach(i;0..n.arity){
			budget.spend(); auto child=a.viewChild(t,i),c=a.view(child);
			if(op==Op.mask&&i==0){ children~=d.refl(child,ctx); bindings~=child; continue; }
			if(c.op==Op.builtin&&c.value==castFunction){
				embedded=true; children~=d.refl(child,ctx); bindings~=a.at(c.a);
			}else if(a.isNumber(child)){
				auto v=a.number(child);
				if(!v.im.zero||rank(source)<rank(Sort.rational)&&!v.re.integral||source==Sort.natural&&v.re<Rational(0)) return d.refl(t,ctx);
				auto lower=a.number(v,source),lifted=a.call(castFunction,[lower]);
				children~=d.numeric(child,lifted,ctx); bindings~=lower;
			}else return d.refl(t,ctx);
		}
		if(!embedded) return d.refl(t,ctx);
		if(op==Op.pow) bindings~=a.real_(n.value);
		auto p=d.congr(t,children,ctx),q=d.rule(instantiate(a,selected,bindings),[],ctx);
		return d.trans(p,q,ctx);
	}
}
