module qsym.algebra;
import qsym.ir;
import qsym.table:Table;
import qsym.order:Order,Limit;
import std.algorithm:sort;
import std.conv:to;
@safe:

// Hash tables only find entries. Structural order determines every emitted term.
int compare(Arena a,Term x,Term y){
	Term[] left=[x],right=[y];
	while(left.length){
		x=left[$-1]; y=right[$-1]; left.length--; right.length--;
		if(x==y) continue;
		auto l=a.node(x),r=a.node(y);
		if(l.sort!=r.sort) return l.sort<r.sort?-1:1;
		if(l.op!=r.op) return l.op<r.op?-1:1;
		if(a.isNumber(x)){
			auto u=a.number(x),v=a.number(y);
			auto c=u.re.opCmp(v.re); if(c) return c;
			return u.im.opCmp(v.im);
		}
		if(l.value!=r.value) return l.value<r.value?-1:1;
		if(l.arity==2){ left~=a.at(l.b); right~=a.at(r.b); }
		if(l.arity>=1){ left~=a.at(l.a); right~=a.at(r.a); }
	}
	return 0;
}

private struct Factor{ Term atom; long exponent; }
private struct Monomial{ Number coefficient; Factor[] factors; }
private alias Polynomial=Monomial[];

final class Algebra{
	private Arena a;
	private size_t maxTerms,remaining,maxWords;
	private Table!(uint,uint) index;
	private Polynomial[] forms;
	private uint depth;
	private Order orderAnalysis;
	bool exhausted;
	this(Arena a,size_t maxTerms,size_t work,size_t maxWords){
		this.a=a; this.maxTerms=maxTerms; remaining=work; this.maxWords=maxWords;
		orderAnalysis=new Order(a,&spend,maxWords);
	}
	private void spend(size_t n=1){
		if(n>remaining) throw new Limit;
		remaining-=n;
	}
	private Number arithmetic(string op)(Number x,Number y){
		if(x.words>maxWords||y.words>maxWords) throw new Limit;
		spend(x.words+y.words);
		auto r=x.opBinary!op(y);
		if(r.words>maxWords) throw new Limit;
		return r;
	}
	private void remember(Term t,Polynomial p){
		auto i=index.get(t.id,uint.max);
		if(i==uint.max){ index.set(t.id,cast(uint)forms.length); forms~=p; }
	}
	private Polynomial constant(Number c){ return c.zero?null:[Monomial(c)]; }
	private Polynomial atom(Term t,long exponent=1){ return [Monomial(Number(1),[Factor(t,exponent)])]; }
	private Polynomial form(Term t){
		if(a.isNumber(t)) return constant(a.number(t));
		auto i=index.get(t.id,uint.max);
		return i==uint.max?atom(t):forms[i];
	}
	private int order(Monomial x,Monomial y){
		long dx,dy;
		foreach(f;x.factors) dx+=f.exponent;
		foreach(f;y.factors) dy+=f.exponent;
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
	private Polynomial collect(Polynomial p){
		Table!(string,uint) positions;
		Polynomial result;
		foreach(m;p){
			spend(1+m.factors.length);
			if(m.coefficient.zero) continue;
			string key;
			foreach(f;m.factors) key~=to!string(f.atom.id)~":"~to!string(f.exponent)~",";
			auto pos=positions.get(key,uint.max);
			if(pos==uint.max){ positions.set(key,cast(uint)result.length); result~=m; }
			else result[pos].coefficient=arithmetic!"+"(result[pos].coefficient,m.coefficient);
		}
		Polynomial nonzero;
		foreach(m;result) if(!m.coefficient.zero) nonzero~=m;
		if(nonzero.length>maxTerms) throw new Limit;
		sort!((x,y)=>order(x,y)>0)(nonzero);
		return nonzero;
	}
	private Factor[] product(Factor[] x,Factor[] y){
		spend(x.length+y.length);
		Factor[] r;
		size_t i,j;
		while(i<x.length||j<y.length){
			if(i==x.length){ r~=y[j++]; continue; }
			if(j==y.length){ r~=x[i++]; continue; }
			auto c=compare(a,x[i].atom,y[j].atom);
			if(c<0) r~=x[i++];
			else if(c>0) r~=y[j++];
			else{
				auto p=x[i++],q=y[j++];
				if(p.exponent>0&&q.exponent>long.max-p.exponent||
					p.exponent<0&&q.exponent<long.min-p.exponent) throw new Limit;
				p.exponent+=q.exponent;
				if(p.exponent>uint.max||p.exponent<-(cast(long)uint.max)) throw new Limit;
				if(p.exponent) r~=p;
			}
		}
		return r;
	}
	private Polynomial add(Polynomial x,Polynomial y){ return collect(x~y); }
	private Polynomial multiply(Polynomial x,Polynomial y){
		if(!x.length||!y.length) return null;
		if(x.length>remaining/y.length) throw new Limit;
		spend(x.length*y.length);
		Polynomial p;
		foreach(u;x) foreach(v;y)
			p~=Monomial(arithmetic!"*"(u.coefficient,v.coefficient),product(u.factors,v.factors));
		return collect(p);
	}
	private Polynomial power(Polynomial p,uint n){
		auto r=constant(Number(1));
		while(n){
			if(n&1) r=multiply(r,p);
			n>>=1;
			if(n) p=multiply(p,p);
		}
		return r;
	}
	private Polynomial inverse(Polynomial p,Term t){
		if(p.length!=1) return atom(t,-1);
		auto m=p[0]; m.coefficient=arithmetic!"/"(Number(1),m.coefficient);
		m.factors=m.factors.dup;
		foreach(ref f;m.factors){ if(f.exponent==long.min) throw new Limit; f.exponent=-f.exponent; }
		return [m];
	}
	private Polynomial conjugate(Polynomial p){
		Polynomial r;
		foreach(m;p){
			m.coefficient=m.coefficient.conjugate;
			m.factors=m.factors.dup;
			foreach(ref f;m.factors){
				auto n=a.node(f.atom);
				f.atom=n.op==Op.conj?a.at(n.a):a.conj(f.atom);
			}
			sort!((x,y)=>compare(a,x.atom,y.atom)<0)(m.factors);
			r~=m;
		}
		return collect(r);
	}
	private Polynomial negative(Polynomial p){
		auto r=p.dup; foreach(ref m;r) m.coefficient=-m.coefficient; return r;
	}
	private bool polynomial(Polynomial p){
		foreach(m;p) foreach(f;m.factors) if(f.exponent<0) return false;
		return true;
	}
	private bool divide(Polynomial numerator,Polynomial denominator,out Polynomial quotient){
		if(!denominator.length||!polynomial(numerator)||!polynomial(denominator)) return false;
		auto r=numerator;
		while(r.length){
			spend();
			auto m=r[0]; m.coefficient=arithmetic!"/"(m.coefficient,denominator[0].coefficient);
			auto inverse=denominator[0].factors.dup;
			foreach(ref f;inverse) f.exponent=-f.exponent;
			m.factors=product(m.factors,inverse);
			foreach(f;m.factors) if(f.exponent<0) return false;
			quotient=add(quotient,[m]);
			auto next=add(r,negative(multiply([m],denominator)));
			if(next.length&&order(next[0],r[0])>=0) throw new Limit;
			r=next;
		}
		return true;
	}
	private Polynomial cancel(Polynomial p){
		if(!p.length) return p;
		foreach(f;p[0].factors) if(f.exponent==-1){
			auto denominator=form(f.atom);
			if(denominator.length<2) continue;
			Polynomial numerator;
			bool common=true;
			foreach(m;p){
				bool found; Factor[] fs;
				foreach(g;m.factors){
					if(g.atom==f.atom&&g.exponent==-1) found=true;
					else fs~=g;
				}
				if(!found){ common=false; break; }
				numerator~=Monomial(m.coefficient,fs);
			}
			if(common){
				Polynomial quotient;
				if(divide(collect(numerator),denominator,quotient)) return quotient;
			}
		}
		return p;
	}
	private bool opposite(Term p,Term q){
		auto x=a.node(p),y=a.node(q);
		return x.op==Op.not_&&x.a==q.id||y.op==Op.not_&&y.a==p.id;
	}
	private Term emit(Polynomial p,Sort s){
		if(!p.length) return a.number(Number(0),s);
		Term[] terms;
		foreach(m;p){
			spend(1+m.factors.length);
			Term[] factors;
			if(!m.coefficient.one||!m.factors.length) factors~=a.number(m.coefficient,s);
			foreach(f;m.factors){
				auto t=f.atom;
				auto n=f.exponent<0?-f.exponent:f.exponent;
				if(n>uint.max) throw new Limit;
				if(n!=1) t=a.pow(t,cast(uint)n);
				if(f.exponent<0) t=a.inv(t);
				factors~=t;
			}
			terms~=balanced(factors,false);
		}
		auto t=balanced(terms,true);
		remember(t,p);
		return t;
	}
	private Term balanced(Term[] ts,bool sum){
		while(ts.length>1){
			Term[] next;
			for(size_t i=0;i<ts.length;i+=2)
				next~=i+1==ts.length?ts[i]:sum?a.add(ts[i],ts[i+1]):a.mul(ts[i],ts[i+1]);
			ts=next;
		}
		return ts[0];
	}
	Term normalize(Term t){
		try{
			if(depth>=128) throw new Limit;
			++depth; scope(exit) --depth;
			auto n=a.node(t);
			if(a.isNumber(t)){ remember(t,constant(a.number(t))); return t; }
			auto reduced=orderAnalysis.reduce(t);
			if(reduced!=t) return normalize(reduced);
			Polynomial p;
			switch(n.op){
				case Op.add,Op.mul:
					auto x=a.at(n.a),y=a.at(n.b),u=a.node(x),v=a.node(y);
					if(u.op==Op.mask&&v.op==Op.mask&&n.op==Op.add){
						if(u.a==v.a) return normalize(a.mask(a.at(u.a),normalize(a.add(a.at(u.b),a.at(v.b)))));
						if(u.b==v.b&&opposite(a.at(u.a),a.at(v.a))) return a.at(u.b);
					}
					if(n.op==Op.mul&&(u.op==Op.mask||v.op==Op.mask)){
						auto guard=u.op==Op.mask?a.at(u.a):a.at(v.a);
						if(u.op==Op.mask&&v.op==Op.mask) guard=normalize(a.and_(guard,a.at(v.a)));
						auto body=normalize(a.mul(u.op==Op.mask?a.at(u.b):x,v.op==Op.mask?a.at(v.b):y));
						return normalize(a.mask(guard,body));
					}
					p=n.op==Op.add?add(form(x),form(y)):multiply(form(x),form(y)); break;
				case Op.pow:p=power(form(a.at(n.a)),cast(uint)n.value); break;
				case Op.inv:
					if(a.isNumber(a.at(n.a))&&a.number(a.at(n.a)).zero) return t;
					p=inverse(form(a.at(n.a)),a.at(n.a)); break;
				case Op.conj:p=conjugate(form(a.at(n.a))); break;
				case Op.abs:
					auto child=a.node(a.at(n.a));
					if(child.op==Op.mul) return normalize(a.mul(normalize(a.abs(a.at(child.a))),normalize(a.abs(a.at(child.b)))));
					if(child.op==Op.inv) return normalize(a.inv(normalize(a.abs(a.at(child.a)))));
					if(child.op==Op.pow) return normalize(a.pow(normalize(a.abs(a.at(child.a))),cast(uint)child.value));
					if(child.op==Op.mask) return normalize(a.mask(a.at(child.a),normalize(a.abs(a.at(child.b)))));
					return t;
				case Op.nonzero:
					if(a.isNumber(a.at(n.a))) return a.boolean(!a.number(a.at(n.a)).zero);
					auto child=a.node(a.at(n.a));
					if(child.op==Op.inv) return a.boolean(true);
					if(child.op==Op.pow&&child.value>0||child.op==Op.conj||child.op==Op.abs) return normalize(a.nonzero(a.at(child.a)));
					if(child.op==Op.mul) return normalize(a.and_(normalize(a.nonzero(a.at(child.a))),normalize(a.nonzero(a.at(child.b)))));
					return t;
				case Op.mask:
					auto guard=a.node(a.at(n.a)),body=a.node(a.at(n.b));
					if(guard.op==Op.boolLit) return guard.value?a.at(n.b):a.number(Number(0),n.sort);
					if(a.isNumber(a.at(n.b))&&a.number(a.at(n.b)).zero) return a.at(n.b);
					if(body.op==Op.mask){
						if(body.a==n.a) return a.at(n.b);
						return normalize(a.mask(normalize(a.and_(a.at(n.a),a.at(body.a))),a.at(body.b)));
					}
					auto value=orderAnalysis.under(a.at(n.b),a.at(n.a),&normalize);
					if(value!=a.at(n.b)) return normalize(a.mask(a.at(n.a),value));
					return t;
				case Op.not_:
					auto child=a.node(a.at(n.a));
					if(child.op==Op.boolLit) return a.boolean(!child.value);
					if(child.op==Op.not_) return a.at(child.a);
					return t;
				case Op.and_,Op.or_:
					auto x=a.at(n.a),y=a.at(n.b),u=a.node(x),v=a.node(y);
					auto stop=n.op==Op.and_?0:1;
					if(u.op==Op.boolLit) return u.value==stop?x:y;
					if(v.op==Op.boolLit) return v.value==stop?y:x;
					if(x==y) return x;
					if(opposite(x,y)) return a.boolean(stop!=0);
					return t;
				case Op.lt,Op.le:
					auto difference=add(form(a.at(n.a)),negative(form(a.at(n.b))));
					if(!difference.length) return a.boolean(n.op==Op.le);
					if(difference.length==1&&!difference[0].factors.length){
						auto c=difference[0].coefficient.re.opCmp(Rational(0));
						return a.boolean(n.op==Op.lt?c<0:c<=0);
					}
					return t;
				default:return t;
			}
			p=cancel(p);
			auto r=emit(p,n.sort); remember(t,p); return r;
		}catch(Limit e){ exhausted=true; return t; }
	}
}
