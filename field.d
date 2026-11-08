module qsym.field;
import qsym.ir;
public import qsym.order:compare;
import qsym.derive;
import qsym.budget;
import qsym.generated.rules;
import qsym.table:Table;
import std.algorithm:sort;
import std.exception:enforce;
@safe:

package struct Factor{ Term atom; long exponent; }
package struct Mono{ Number coefficient; Factor[] factors; }

package Factor factor(Arena a,Term t){
	long sign=1; auto n=a.view(t);
	if(n.op==Op.inv){ sign=-1; t=a.at(n.a); n=a.view(t); }
	return n.op==Op.pow?Factor(a.at(n.a),sign*n.value):Factor(t,sign);
}

package Mono monomial(Arena a,Term t,Budget budget){
	Mono m; m.coefficient=Number(1);
	auto es=a.multisetTerms(a.multiset(t,Op.mul));
	if(es.length>budget.maxTerms) throw new Limit;
	budget.spend(1+es.length);
	foreach(e;es){
		if(a.isNumber(e.term)){
			auto v=a.number(e.term);
			for(auto count=e.count;count;count>>=1){
				if(count&1) m.coefficient=budget.calc!"*"(m.coefficient,v);
				if(count>1) v=budget.calc!"*"(v,v);
			}
		}else{
			auto f=factor(a,e.term);
			if((f.exponent<0?-f.exponent:f.exponent)>uint.max/e.count) throw new Limit;
			f.exponent*=e.count; m.factors~=f;
		}
	}
	sort!((x,y)=>compare(a,x.atom,y.atom)<0)(m.factors);
	return m;
}

package int monomialOrder(Arena a,Mono x,Mono y){
	long dx,dy; foreach(f;x.factors) dx+=f.exponent; foreach(f;y.factors) dy+=f.exponent;
	if(dx!=dy) return dx<dy?-1:1;
	size_t i,j;
	while(i<x.factors.length||j<y.factors.length){
		if(i==x.factors.length) return y.factors[j].exponent>0?-1:1;
		if(j==y.factors.length) return x.factors[i].exponent>0?1:-1;
		auto c=compare(a,x.factors[i].atom,y.factors[j].atom);
		if(c) return c<0?(x.factors[i].exponent>0?1:-1):(y.factors[j].exponent>0?-1:1);
		auto ex=x.factors[i++].exponent,ey=y.factors[j++].exponent;
		if(ex!=ey) return ex<ey?-1:1;
	}
	return 0;
}

// The algorithms choose normal forms. Every changed expression is accompanied
// by applications of generated laws, congruence, AC permutations or arithmetic.
package final class Field{
	private Arena a;
	private Derivation d;
	private Budget budget;
	private Proof delegate(Term,uint) @safe norm;
	private uint divisions;
	bool expandPowers;
	this(Arena a,Derivation d,Budget budget,Proof delegate(Term,uint) @safe norm){
		this.a=a; this.d=d; this.budget=budget; this.norm=norm;
	}
	private Proof law(string name)(Sort s,Term[] args,uint ctx){
		budget.spend();
		auto id=s==Sort.real_?__traits(getMember,Law,"real_"~name):__traits(getMember,Law,"complex_"~name);
		return d.rule(instantiate(a,id,args),[],ctx);
	}
	private Proof then(Proof p,Proof q,uint ctx){ return d.trans(p,q,ctx); }
	private Term number(long x,Sort s){ return a.number(Number(x),s); }
	private Term balanced(Term[] ts,Op op,Sort s){
		if(!ts.length) return number(op==Op.add?0:1,s);
		while(ts.length>1){
			Term[] next;
			for(size_t i;i<ts.length;i+=2) next~=i+1==ts.length?ts[i]:op==Op.add?a.add(ts[i],ts[i+1]):a.mul(ts[i],ts[i+1]);
			ts=next;
		}
		return ts[0];
	}
	private Term[] leaves(Term t,Op op){
		if(a.view(t).op!=op){ budget.spend(); return [t]; }
		Term[] result;
		foreach(e;d.regions.terms(t,op,budget)){
			if(e.count>budget.maxTerms-result.length) throw new Limit;
			budget.spend(e.count);
			auto start=result.length; result.length+=e.count; result[start..$]=e.term;
		}
		if(!result.length) result~=number(op==Op.add?0:1,a.sort(t));
		return result;
	}
	private Term factorTerm(Factor f,Sort s){
		auto e=f.exponent<0?-f.exponent:f.exponent;
		if(e>uint.max) throw new Limit;
		auto t=e==1?f.atom:a.pow(f.atom,cast(uint)e);
		return f.exponent<0?a.inv(t):t;
	}
	private Factor factor(Term t){ return qsym.field.factor(a,t); }
	private Term base(Mono m,Sort s){
		Term[] fs; foreach(f;m.factors) fs~=factorTerm(f,s);
		return balanced(fs,Op.mul,s);
	}
	private Term emit(Mono m,Sort s){
		if(m.coefficient.zero) return number(0,s);
		Term[] fs;
		if(!m.coefficient.one||!m.factors.length) fs~=a.number(m.coefficient,s);
		foreach(f;m.factors) fs~=factorTerm(f,s);
		return balanced(fs,Op.mul,s);
	}
	private Mono mono(Term t){ return monomial(a,t,budget); }
	private Mono weighted(Operand e){
		auto m=mono(e.term);
		if(e.count!=1) m.coefficient=budget.calc!"*"(m.coefficient,Number(e.count));
		return m;
	}
	private Mono[] polynomial(Term t){
		Mono[] result; foreach(e;d.regions.terms(t,Op.add,budget)) result~=weighted(e); return result;
	}
	bool affine(Term expression,Term variable,out Term coefficient,out Term remainder){
		Number c; Operand[] rest;
		foreach(e;d.regions.terms(expression,Op.add,budget)){
			auto m=weighted(e);
			if(m.factors.length==1&&m.factors[0].atom==variable&&m.factors[0].exponent==1)
				c=budget.calc!"+"(c,m.coefficient);
			else{
				foreach(id;a.postorder(e.term)){ budget.spend(); if(id==variable.id) return false; }
				rest~=e;
			}
		}
		if(c.zero) return false;
		coefficient=a.number(c,a.sort(variable)); remainder=a.region(Op.add,a.sort(variable),rest); return true;
	}
	bool quadratic(Term expression,out Term atom,out Number[3] coefficients){
		if(a.sort(expression)!=Sort.real_&&a.sort(expression)!=Sort.complex) return false;
		bool found;
		foreach(m;polynomial(expression)){
			size_t degree;
			if(m.factors.length){
				if(m.factors.length!=1) return false;
				auto f=m.factors[0]; if(f.exponent<1||f.exponent>2) return false;
				if(found&&f.atom!=atom) return false;
				atom=f.atom; found=true; degree=cast(size_t)f.exponent;
			}
			coefficients[degree]=budget.calc!"+"(coefficients[degree],m.coefficient);
		}
		return found;
	}
	private int order(Mono x,Mono y){ return monomialOrder(a,x,y); }
	Proof literal(Term t,uint ctx){
		auto n=a.view(t);
		if(n.op==Op.builtin&&n.value==Builtin.eqB&&a.view(a.at(n.a)).op==Op.boolLit&&a.view(a.at(n.b)).op==Op.boolLit)
			return d.numeric(t,a.boolean(a.view(a.at(n.a)).value==a.view(a.at(n.b)).value),ctx);
		if(!n.arity) return d.refl(t,ctx);
		auto x=a.at(n.a); if(!a.isNumber(x)) return d.refl(t,ctx);
		auto v=a.number(x); Number w;
		if(n.arity==2){ if(!a.isNumber(a.at(n.b))) return d.refl(t,ctx); w=a.number(a.at(n.b)); }
		Term result;
		switch(n.op){
			case Op.add:result=a.number(budget.calc!"+"(v,w),n.sort); break;
			case Op.mul:result=a.number(budget.calc!"*"(v,w),n.sort); break;
			case Op.inv:if(v.zero) return d.refl(t,ctx); result=a.number(budget.calc!"/"(Number(1),v),n.sort); break;
			case Op.builtin:
				auto f=cast(Builtin)n.value;
				switch(f){
					case Builtin.gcdZ:
						auto l=v.re.numerator,r=w.re.numerator;
						if(l<0) l=-l; if(r<0) r=-r;
						while(r!=0){ budget.spend(1+l.uintLength+r.uintLength); auto rem=l%r; l=r; r=rem; }
						result=a.number(Number(Rational(l,BigInt(1))),Sort.natural); break;
					case Builtin.castNZ,Builtin.castZQ,Builtin.castQR,Builtin.castRC:result=a.number(v,n.sort); break;
					case Builtin.addN,Builtin.addZ,Builtin.addQ:result=a.number(budget.calc!"+"(v,w),n.sort); break;
					case Builtin.mulN,Builtin.mulZ,Builtin.mulQ:result=a.number(budget.calc!"*"(v,w),n.sort); break;
					case Builtin.invQ:if(v.zero) return d.refl(t,ctx); result=a.number(budget.calc!"/"(Number(1),v),n.sort); break;
					case Builtin.nonzeroN,Builtin.nonzeroZ,Builtin.nonzeroQ:result=a.boolean(!v.zero); break;
					case Builtin.ltN,Builtin.ltZ,Builtin.ltQ:result=a.boolean(v.re<w.re); break;
					case Builtin.leN,Builtin.leZ,Builtin.leQ:result=a.boolean(v.re<=w.re); break;
					case Builtin.reC:result=a.real_(v.re); break;
					case Builtin.imC:result=a.real_(v.im); break;
					case Builtin.makeC:result=a.complex(v.re,w.re); break;
					case Builtin.makeQ:if(w.zero) return d.refl(t,ctx); result=a.number(budget.calc!"/"(v,w),Sort.rational); break;
					case Builtin.numQ:result=a.number(Number(Rational(v.re.numerator,BigInt(1))),Sort.integer); break;
					case Builtin.denQ:result=a.number(Number(Rational(v.re.denominator,BigInt(1))),Sort.natural); break;
					default:return d.refl(t,ctx);
				}
				break;
			case Op.pow:
				if(n.sort!=Sort.real_&&n.sort!=Sort.complex){
					auto power=Number(1),base=v; auto exponent=cast(uint)n.value;
					while(exponent){
						if(exponent&1) power=budget.calc!"*"(power,base);
						exponent>>=1; if(exponent) base=budget.calc!"*"(base,base);
					}
					result=a.number(power,n.sort); break;
				}
				if(!n.value) return law!"pow_zero"(n.sort,[x],ctx);
				if(n.value==1) return law!"pow_one"(n.sort,[x],ctx);
				auto m=n.value/2;
				auto p=law!"pow_split"(n.sort,[x,a.real_(m),a.real_(n.value-m)],ctx);
				auto l=norm(a.viewChild(p.after,0),ctx),r=norm(a.viewChild(p.after,1),ctx);
				if(budget.exhausted) throw new Limit;
				p=then(p,d.congr(p.after,[l,r],ctx),ctx);
				return then(p,literal(p.after,ctx),ctx);
			case Op.conj:result=a.number(v.conjugate,n.sort); break;
			case Op.abs:result=a.number(v.re<Rational(0)?-v:v,n.sort); break;
			case Op.nonzero:result=a.boolean(!v.zero); break;
			case Op.lt:result=a.boolean(v.re<w.re); break;
			case Op.le:result=a.boolean(v.re<=w.re); break;
			default:return d.refl(t,ctx);
		}
		return d.numeric(t,result,ctx);
	}
	private Proof powerView(Term t,uint ctx){
		auto f=factor(t),s=a.sort(t);
		auto e=f.exponent<0?-f.exponent:f.exponent;
		auto p=d.refl(f.atom,ctx);
		if(e==1){
			auto i=instantiate(a,s==Sort.real_?Law.real_power_one:Law.complex_power_one,[f.atom]);
			auto old=i.before; i.before=i.result; i.result=old; i.reversed=true;
			p=d.rule(i,[],ctx);
		}else p=d.refl(a.pow(f.atom,cast(uint)e),ctx);
		return f.exponent<0?d.congr(t,[p],ctx):p;
	}
	private Proof joinFactors(Term x,Term y,uint ctx){
		auto s=a.sort(x),u=factor(x),v=factor(y);
		enforce(u.atom==v.atom,"different factor bases");
		if(u.exponent+v.exponent>uint.max||u.exponent+v.exponent<-(cast(long)uint.max)) throw new Limit;
		auto t=a.mul(x,y),p=d.congr(t,[powerView(x,ctx),powerView(y,ctx)],ctx);
		auto m=u.exponent<0?-u.exponent:u.exponent,n=v.exponent<0?-v.exponent:v.exponent;
		auto pm=a.pow(u.atom,cast(uint)m),pn=a.pow(u.atom,cast(uint)n);
		if(u.exponent>=0&&v.exponent>=0){
			p=then(p,law!"pow_join"(s,[u.atom,a.real_(m),a.real_(n)],ctx),ctx);
		}else if(u.exponent<0&&v.exponent<0){
			p=then(p,law!"mul_inv"(s,[pm,pn],ctx),ctx);
			p=then(p,d.congr(p.after,[law!"pow_join"(s,[u.atom,a.real_(m),a.real_(n)],ctx)],ctx),ctx);
		}else{
			if(u.exponent<0){
				auto swap=a.mul(pn,a.inv(pm)); p=then(p,d.ac(p.after,swap,Op.mul,ctx),ctx);
				auto k=m; m=n; n=k;
			}
			auto positive=a.pow(u.atom,cast(uint)m),negative=a.pow(u.atom,cast(uint)n);
			if(m>=n){
				auto split=law!"pow_split"(s,[u.atom,a.real_(n),a.real_(m-n)],ctx);
				p=then(p,d.congr(p.after,[split,d.refl(a.inv(negative),ctx)],ctx),ctx);
				auto rest=a.pow(u.atom,cast(uint)(m-n));
				auto grouped=a.mul(a.mul(negative,a.inv(negative)),rest);
				p=then(p,d.ac(p.after,grouped,Op.mul,ctx),ctx);
				p=then(p,d.congr(grouped,[law!"div_self"(s,[negative],ctx),d.refl(rest,ctx)],ctx),ctx);
				p=then(p,d.ac(p.after,rest,Op.mul,ctx),ctx);
			}else{
				auto split=law!"pow_split"(s,[u.atom,a.real_(m),a.real_(n-m)],ctx);
				p=then(p,d.congr(p.after,[d.refl(positive,ctx),d.congr(a.inv(negative),[split],ctx)],ctx),ctx);
				auto rest=a.pow(u.atom,cast(uint)(n-m));
				p=then(p,d.congr(p.after,[d.refl(positive,ctx),law!"inv_mul"(s,[positive,rest],ctx)],ctx),ctx);
				auto grouped=a.mul(a.mul(positive,a.inv(positive)),a.inv(rest));
				p=then(p,d.ac(p.after,grouped,Op.mul,ctx),ctx);
				p=then(p,d.congr(grouped,[law!"div_self"(s,[positive],ctx),d.refl(a.inv(rest),ctx)],ctx),ctx);
				p=then(p,d.ac(p.after,a.inv(rest),Op.mul,ctx),ctx);
			}
		}
		// Only powers zero and one are removed here; re-entering polynomial
		// normalization would undo the factor grouping just constructed.
		auto outNode=a.view(p.after);
		if(outNode.op==Op.pow&&(outNode.value==0||outNode.value==1))
			p=then(p,outNode.value==0?law!"pow_zero"(s,[a.at(outNode.a)],ctx):law!"pow_one"(s,[a.at(outNode.a)],ctx),ctx);
		else if(outNode.op==Op.inv){
			auto inner=a.view(a.at(outNode.a));
			if(inner.op==Op.pow&&inner.value==1) p=then(p,d.congr(p.after,[law!"pow_one"(s,[a.at(inner.a)],ctx)],ctx),ctx);
		}
		return p;
	}
	private Proof product(Term t,uint ctx){
		auto s=a.sort(t); auto fs=leaves(t,Op.mul);
		Term[] constants,atoms;
		foreach(f;fs) if(a.isNumber(f)) constants~=f; else atoms~=f;
		sort!((x,y)=>compare(a,factor(x).atom,factor(y).atom)<0)(atoms);
		Term[] groups; Proof[] changes;
		if(constants.length){
			auto c=balanced(constants,Op.mul,s),v=Number(1);
			foreach(x;constants) v=budget.calc!"*"(v,a.number(x));
			groups~=c; changes~=d.numeric(c,a.number(v,s),ctx);
		}
		for(size_t i;i<atoms.length;){
			auto start=i++; while(i<atoms.length&&factor(atoms[i]).atom==factor(atoms[start]).atom) ++i;
			auto g=atoms[start],p=d.refl(g,ctx);
			foreach(x;atoms[start+1..i]){
				auto pair=a.mul(g,x),previous=p.after;
				p=d.congr(pair,[p,d.refl(x,ctx)],ctx);
				p=then(p,a.isNumber(previous)&&a.number(previous).one?d.ac(p.after,x,Op.mul,ctx):joinFactors(previous,x,ctx),ctx);
				g=pair;
			}
			groups~=g; changes~=p;
		}
		auto grouped=balanced(groups,Op.mul,s),p=d.ac(t,grouped,Op.mul,ctx);
		p=then(p,d.join(changes,Op.mul,s,ctx),ctx);
		Term[] output; foreach(q;changes) output~=q.after;
		auto m=mono(balanced(output,Op.mul,s));
		if(m.coefficient.zero){
			auto rest=base(m,s),zero=number(0,s),withZero=a.mul(zero,rest);
			p=then(p,d.ac(p.after,withZero,Op.mul,ctx),ctx);
			return then(p,law!"zero_mul"(s,[rest],ctx),ctx);
		}
		return then(p,d.ac(p.after,emit(m,s),Op.mul,ctx),ctx);
	}
	private Proof sum(Term t,uint ctx){
		auto s=a.sort(t),ts=leaves(t,Op.add);
		if(ts.length>budget.maxTerms) throw new Limit;
		// A recursive normalization may leave an active product unchanged.
		// Fold its coefficients explicitly before using AC to collect terms.
		auto prefix=d.refl(t,ctx);
		Proof[] products; foreach(x;ts) products~=product(x,ctx);
		auto tree=balanced(ts,Op.add,s);
		prefix=d.ac(t,tree,Op.add,ctx);
		prefix=then(prefix,d.join(products,Op.add,s,ctx),ctx);
		t=prefix.after; ts=leaves(t,Op.add);
		struct Entry{ Term term; Mono m; }
		Entry[] entries; foreach(x;ts) entries~=Entry(x,mono(x));
		sort!((x,y)=>order(x.m,y.m)>0)(entries);
		Term[] groups; Proof[] changes;
		for(size_t i;i<entries.length;){
			auto start=i++; while(i<entries.length&&order(entries[start].m,entries[i].m)==0) ++i;
			if(i==start+1){
				groups~=entries[start].term; changes~=d.refl(entries[start].term,ctx); continue;
			}
			if(!entries[start].m.factors.length){
				Term[] constants; Number value;
				foreach(e;entries[start..i]){
					constants~=e.term; value=budget.calc!"+"(value,e.m.coefficient);
				}
				auto g=balanced(constants,Op.add,s);
				groups~=g; changes~=d.numeric(g,a.number(value,s),ctx); continue;
			}
			auto b=base(entries[start].m,s),g=entries[start].term;
			auto c=a.number(entries[start].m.coefficient,s);
			auto p=d.ac(g,a.mul(c,b),Op.mul,ctx);
			foreach(e;entries[start+1..i]){
				auto z=a.number(e.m.coefficient,s),pair=a.add(g,e.term);
				p=d.congr(pair,[p,d.ac(e.term,a.mul(z,b),Op.mul,ctx)],ctx);
				p=then(p,law!"collect"(s,[c,z,b],ctx),ctx);
				auto coefficient=literal(a.add(c,z),ctx);
				p=then(p,d.congr(p.after,[coefficient,d.refl(b,ctx)],ctx),ctx);
				c=coefficient.after; g=pair;
			}
			if(a.number(c).zero) p=then(p,law!"zero_mul"(s,[b],ctx),ctx);
			else p=then(p,d.ac(p.after,emit(Mono(a.number(c),entries[start].m.factors),s),Op.mul,ctx),ctx);
			groups~=g; changes~=p;
		}
		auto grouped=balanced(groups,Op.add,s),p=d.ac(t,grouped,Op.add,ctx);
		Term[] output;
		foreach(q;changes) if(!a.isNumber(q.after)||!a.number(q.after).zero) output~=q.after;
		p=then(p,d.join(changes,Op.add,s,ctx),ctx);
		return then(prefix,then(p,d.ac(p.after,balanced(output,Op.add,s),Op.add,ctx),ctx),ctx);
	}
	private Proof multiply(Term t,uint ctx){
		auto p=expandPowers?d.refl(t,ctx):product(t,ctx); t=p.after;
		if(a.view(t).op!=Op.mul) return p;
		if(!divisions){ auto q=divide(t,ctx); if(q.after!=t) return then(p,q,ctx); }
		auto fs=leaves(t,Op.mul); size_t at=fs.length;
		foreach(i,f;fs) if(a.view(f).op==Op.add){ at=i; break; }
		if(at==fs.length) return expandPowers?product(t,ctx):p;
		Term[] rest;
		foreach(i,f;fs) if(i!=at){
			if(!expandPowers&&!a.isNumber(f)) return p;
			rest~=f;
		}
		auto s=a.sort(t),x=balanced(rest,Op.mul,s),y=fs[at],v=a.view(y);
		p=then(p,d.ac(t,a.mul(x,y),Op.mul,ctx),ctx);
		p=then(p,law!"distribute"(s,[x,a.at(v.a),a.at(v.b)],ctx),ctx);
		auto output=a.view(p.after);
		p=then(p,d.congr(p.after,[norm(a.at(output.a),ctx),norm(a.at(output.b),ctx)],ctx),ctx);
		return then(p,sum(p.after,ctx),ctx);
	}
	Proof repeated(Proof atom,uint count,Op op,uint ctx){
		if(count==1) return atom;
		budget.spend(); enforce(count>1,"positive multiplicity expected");
		auto p=d.repeated(atom,count,op,ctx);
		return then(p,norm(p.after,ctx),ctx);
	}
	private Proof power(Term t,uint ctx){
		auto n=a.view(t),x=a.at(n.a),v=a.view(x);
		if(v.op==Op.pow){
			if(cast(ulong)v.value*n.value>uint.max) throw new Limit;
			return law!"pow_power"(n.sort,[a.at(v.a),a.real_(v.value),a.real_(n.value)],ctx);
		}
		if(v.op==Op.inv) return law!"power_inv"(n.sort,[a.at(v.a),a.real_(n.value)],ctx);
		if(v.op==Op.mul){
			auto p=law!"pow_product"(n.sort,[a.at(v.a),a.at(v.b),a.real_(n.value)],ctx);
			auto output=a.view(p.after);
			p=then(p,d.congr(p.after,[norm(a.at(output.a),ctx),norm(a.at(output.b),ctx)],ctx),ctx);
			return then(p,multiply(p.after,ctx),ctx);
		}
		if(expandPowers&&v.op==Op.add&&n.value>1){
			auto m=n.value/2;
			auto p=law!"pow_split"(n.sort,[x,a.real_(m),a.real_(n.value-m)],ctx);
			auto output=a.view(p.after);
			p=then(p,d.congr(p.after,[norm(a.at(output.a),ctx),norm(a.at(output.b),ctx)],ctx),ctx);
			return then(p,multiply(p.after,ctx),ctx);
		}
		return d.refl(t,ctx);
	}
	// Bound speculative expansion before allocating its terms or certificates.
	// Count uncollected monomials, saturating at the configured term limit.
	bool expandable(Term t){
		Table!(uint,size_t) widths;
		bool found;
		size_t multiply(size_t x,size_t y){
			return !x||!y?0:x>budget.maxTerms/y?size_t.max:x*y;
		}
		foreach(id;a.viewPostorder(t)){
			budget.spend(); auto n=a.view(a.at(id)); size_t width=1;
			if(n.op==Op.add){
				auto x=widths.get(n.a,1),y=widths.get(n.b,1);
				if(y>budget.maxTerms||x>budget.maxTerms-y) return false;
				width=x+y;
			}else if(n.op==Op.mul){
				auto x=widths.get(n.a,1),y=widths.get(n.b,1);
				width=multiply(x,y); found=found||x>1||y>1;
			}
			else if(n.op==Op.pow){
				auto base=widths.get(n.a,1);
				found=found||(base>1&&n.value>1);
				for(auto k=n.value;k;k>>=1){
					if(k&1) width=multiply(width,base);
					if(width>budget.maxTerms) return false;
					if(k>1) base=multiply(base,base);
				}
			}
			if(width>budget.maxTerms) return false;
			widths.set(id,width);
		}
		return found;
	}
	bool commonFactor(Term t,out Term x,out Term y){
		auto es=d.regions.terms(t,Op.add,budget);
		if(!es.length||es.length==1&&es[0].count==1) return false;
		Mono[] terms; foreach(e;es) terms~=weighted(e);
		Factor[] common;
		foreach(f;terms[0].factors){
			if(f.exponent<=0) continue;
			auto minimum=f.exponent;
			foreach(m;terms[1..$]){
				long exponent;
				foreach(g;m.factors){ budget.spend(); if(g.atom==f.atom){ exponent=g.exponent; break; } }
				if(exponent<minimum) minimum=exponent;
				if(minimum<=0) break;
			}
			if(minimum>0) common~=Factor(f.atom,minimum);
		}
		if(!common.length) return false;
		auto s=a.sort(t); Term[] quotients;
		foreach(m;terms){
			Factor[] rest;
			foreach(f;m.factors){
				foreach(g;common){ budget.spend(); if(g.atom==f.atom) f.exponent-=g.exponent; }
				if(f.exponent) rest~=f;
			}
			quotients~=emit(Mono(m.coefficient,rest),s);
		}
		x=base(Mono(Number(1),common),s); y=balanced(quotients,Op.add,s); return true;
	}
	private Mono[] collect(Mono[] p){
		sort!((x,y)=>order(x,y)>0)(p);
		Mono[] result;
		foreach(m;p){
			budget.spend(1+m.factors.length);
			if(m.coefficient.zero) continue;
			if(result.length&&order(result[$-1],m)==0) result[$-1].coefficient=budget.calc!"+"(result[$-1].coefficient,m.coefficient);
			else result~=m;
		}
		Mono[] output; foreach(m;result) if(!m.coefficient.zero) output~=m;
		if(output.length>budget.maxTerms) throw new Limit;
		return output;
	}
	private Factor[] factors(Factor[] x,Factor[] y){
		Factor[] result; auto fs=x~y;
		sort!((a,b)=>compare(this.a,a.atom,b.atom)<0)(fs);
		foreach(f;fs){
			budget.spend();
			if(result.length&&result[$-1].atom==f.atom) result[$-1].exponent+=f.exponent;
			else result~=f;
		}
		Factor[] output; foreach(f;result){ if(f.exponent>uint.max||f.exponent<-(cast(long)uint.max)) throw new Limit; if(f.exponent) output~=f; }
		return output;
	}
	private Proof divide(Term t,uint ctx){
		auto n=a.view(t),p=a.at(n.a),inv=a.at(n.b);
		if(a.view(inv).op!=Op.inv){ if(a.view(p).op!=Op.inv) return d.refl(t,ctx); auto z=p; p=inv; inv=z; }
		auto denominator=a.viewChild(inv,0);
		if(a.view(denominator).op!=Op.add) return d.refl(t,ctx);
		auto num=collect(polynomial(p)),den=collect(polynomial(denominator));
		foreach(m;num~den) foreach(f;m.factors) if(f.exponent<0) return d.refl(t,ctx);
		if(!den.length) return d.refl(t,ctx);
		Mono[] quotient; auto remainder=num;
		while(remainder.length){
			budget.spend();
			auto m=remainder[0]; m.coefficient=budget.calc!"/"(m.coefficient,den[0].coefficient);
			auto negative=den[0].factors.dup; foreach(ref f;negative) f.exponent=-f.exponent;
			m.factors=factors(m.factors,negative);
			foreach(f;m.factors) if(f.exponent<0) return d.refl(t,ctx);
			quotient=collect(quotient~m);
			Mono[] next=remainder;
			foreach(q;den) next~=Mono(-budget.calc!"*"(m.coefficient,q.coefficient),factors(m.factors,q.factors));
			next=collect(next);
			if(next.length&&order(next[0],remainder[0])>=0) throw new Limit;
			remainder=next;
		}
		Term[] terms; foreach(m;quotient) terms~=emit(m,n.sort);
		auto q=balanced(terms,Op.add,n.sort),grouped=a.mul(p,inv);
		if(!d.domain(grouped,q).found) return d.refl(t,ctx);
		auto result=d.ac(t,grouped,Op.mul,ctx);
		result=then(result,law!"divide_step"(n.sort,[p,denominator,q],ctx),ctx);
		++divisions; scope(exit) --divisions;
		auto previous=expandPowers; expandPowers=true; scope(exit) expandPowers=previous;
		return then(result,norm(result.after,ctx),ctx);
	}
	bool clearDenominator(Term t,uint ctx,out Proof result){
		auto n=a.view(t);
		if(n.op!=Op.nonzero) return false;
		auto residual=a.at(n.a),s=a.sort(residual);
		if(s!=Sort.real_&&s!=Sort.complex||a.view(residual).op!=Op.add) return false;
		auto terms=leaves(residual,Op.add);
		foreach(i,term;terms){
			auto factors=leaves(term,Op.mul);
			foreach(j,f;factors) if(a.view(f).op==Op.inv){
				auto denominator=a.viewChild(f,0);
				auto numerator=balanced(factors[0..j]~factors[j+1..$],Op.mul,s);
				auto rest=balanced(terms[0..i]~terms[i+1..$],Op.add,s);
				auto quotient=a.mul(numerator,f),grouped=a.add(term,rest);
				auto collect=d.ac(residual,grouped,Op.add,ctx);
				auto factor=d.ac(term,quotient,Op.mul,ctx);
				auto regroup=d.congr(grouped,[factor,d.refl(rest,ctx)],ctx);
				auto prepare=d.congr(t,[then(collect,regroup,ctx)],ctx);
				result=then(prepare,law!"quotient_add_nonzero"(s,[numerator,denominator,rest],ctx),ctx);
				return true;
			}
		}
		return false;
	}

	Proof run(Term t,uint ctx){
		budget.spend();
		auto p=literal(t,ctx); if(p.after!=t) return p;
		auto n=a.view(t);
		if(n.sort!=Sort.real_&&n.sort!=Sort.complex) return d.refl(t,ctx);
		switch(n.op){
			case Op.add:return sum(t,ctx);
			case Op.mul:return multiply(t,ctx);
			case Op.pow:return power(t,ctx);
			case Op.inv:
				auto x=a.viewChild(t,0),v=a.view(x);
				if(v.op==Op.mul){
					auto r=law!"inv_mul"(n.sort,[a.at(v.a),a.at(v.b)],ctx);
					return then(r,norm(r.after,ctx),ctx);
				}
				return d.refl(t,ctx);
			default:return d.refl(t,ctx);
		}
	}
}
