module qsym.order;
import qsym.ir;
import qsym.table:Table;
@safe:

package class Limit:Exception{ this(){ super("algebra budget exhausted"); } }
private enum uint neg=1,zero=2,pos=4,any=7;
private uint flip(uint s){ return (s&neg)<<2|(s&zero)|(s&pos)>>2; }
private uint signOf(Rational q){ return q.zero?zero:q<Rational(0)?neg:pos; }
private uint combine(uint x,uint y,bool product){
	uint result;
	foreach(i;[neg,zero,pos]) if(x&i) foreach(j;[neg,zero,pos]) if(y&j){
		if(product) result|=i==zero||j==zero?zero:i==j?pos:neg;
		else result|=i==zero?j:j==zero||i==j?i:any;
	}
	return result;
}
private struct Affine{ Term atom; Rational scale=Rational(1),offset; }
private struct Constraint{ Term atom; Rational bound; uint allowed; }
private class Facts{
	Table!(uint,uint) known,signs;
	Constraint[] bounds;
	bool impossible;
}

// Every fact is conditional on definedness. Context caches never escape their
// guard; only unconditional facts about a term are shared between contexts.
package final class Order{
	private Arena a;
	private void delegate(size_t) @safe spend;
	private size_t maxWords;
	private Table!(uint,uint) affineIndex,signs;
	private Affine[] affines;
	this(Arena a,void delegate(size_t) @safe spend,size_t maxWords){
		this.a=a; this.spend=spend; this.maxWords=maxWords;
	}
	private Rational calc(string op)(Rational x,Rational y){
		if(x.words>maxWords||y.words>maxWords) throw new Limit;
		spend(x.words+y.words);
		auto r=x.opBinary!op(y);
		if(r.words>maxWords) throw new Limit;
		return r;
	}
	private bool add(Affine x,Affine y,out Affine r){
		if(!x.scale.zero&&!y.scale.zero&&x.atom!=y.atom) return false;
		r.atom=x.scale.zero?y.atom:x.atom;
		r.scale=calc!"+"(x.scale,y.scale); r.offset=calc!"+"(x.offset,y.offset);
		if(r.scale.zero) r.atom=Term.init;
		return true;
	}
	private Affine scale(Affine f,Rational c){
		f.scale=calc!"*"(f.scale,c); f.offset=calc!"*"(f.offset,c);
		if(f.scale.zero) f.atom=Term.init;
		return f;
	}
	private Affine affine(Term t,uint depth=0){
		spend(1);
		auto index=affineIndex.get(t.id,uint.max);
		if(index!=uint.max) return affines[index];
		auto r=Affine(t),n=a.node(t);
		if(a.isNumber(t)) r=Affine(Term.init,Rational(0),a.number(t).re);
		else if(depth<128){
			if(n.op==Op.add){
				Affine sum;
				if(add(affine(a.at(n.a),depth+1),affine(a.at(n.b),depth+1),sum)) r=sum;
			}else if(n.op==Op.mul){
				auto x=a.at(n.a),y=a.at(n.b);
				if(a.isNumber(x)) r=scale(affine(y,depth+1),a.number(x).re);
				else if(a.isNumber(y)) r=scale(affine(x,depth+1),a.number(y).re);
			}
		}
		affineIndex.set(t.id,cast(uint)affines.length); affines~=r;
		return r;
	}
	private Constraint constraint(Affine f,uint allowed){
		if(f.scale.zero) return Constraint(Term.init,Rational(0),signOf(f.offset)&allowed?any:0);
		return Constraint(f.atom,calc!"/"(-f.offset,f.scale),f.scale<Rational(0)?flip(allowed):allowed);
	}
	private bool condition(Term t,out Constraint c,uint depth=0){
		spend(1);
		if(depth>=128) return false;
		auto n=a.node(t);
		if(n.op==Op.boolLit){ c=Constraint(Term.init,Rational(0),n.value?any:0); return true; }
		if(n.op==Op.not_){
			if(!condition(a.at(n.a),c,depth+1)) return false;
			c.allowed^=any; return true;
		}
		if(n.op==Op.nonzero&&a.sort(a.at(n.a))==Sort.real_){
			c=constraint(affine(a.at(n.a)),neg|pos); return true;
		}
		if(n.op==Op.lt||n.op==Op.le){
			Affine difference;
			if(!add(affine(a.at(n.a)),scale(affine(a.at(n.b)),Rational(-1)),difference)) return false;
			c=constraint(difference,n.op==Op.lt?neg:neg|zero); return true;
		}
		return false;
	}
	private bool compatible(Constraint p,Constraint q){
		spend(1+p.bound.words+q.bound.words);
		if(!p.allowed||!q.allowed) return false;
		if(p.atom==Term.init) return p.allowed!=0;
		if(q.atom==Term.init) return q.allowed!=0;
		if(p.atom!=q.atom) return true;
		auto c=p.bound.opCmp(q.bound);
		if(c==0) return (p.allowed&q.allowed)!=0;
		if(c>0){ auto t=p; p=q; q=t; }
		return (p.allowed&neg)&&(q.allowed&neg)||
			(p.allowed&zero)&&(q.allowed&neg)||
			(p.allowed&pos)&&(q.allowed&neg)||
			(p.allowed&pos)&&(q.allowed&zero)||
			(p.allowed&pos)&&(q.allowed&pos);
	}
	private bool implies(Constraint p,Constraint q){ q.allowed^=any; return !compatible(p,q); }
	private Term predicate(Constraint c){
		auto b=a.real_(c.bound);
		switch(c.allowed){
			case 0:return a.boolean(false);
			case any:return a.boolean(true);
			case neg:return a.lt(c.atom,b);
			case neg|zero:return a.le(c.atom,b);
			case pos:return a.lt(b,c.atom);
			case pos|zero:return a.le(b,c.atom);
			default:
				auto d=c.bound.zero?c.atom:a.add(c.atom,a.real_(-c.bound));
				auto p=a.nonzero(d);
				return c.allowed==zero?a.not_(p):p;
		}
	}
	private Facts assume(Term p,bool value){
		auto f=new Facts;
		struct Entry{ Term term; bool value; }
		Entry[] pending=[Entry(p,value)];
		while(pending.length){
			spend(1);
			auto e=pending[$-1]; --pending.length;
			auto old=f.known.get(e.term.id,2);
			if(old<2){ if(old!=e.value) f.impossible=true; continue; }
			f.known.set(e.term.id,e.value);
			auto n=a.node(e.term);
			if(n.op==Op.not_) pending~=Entry(a.at(n.a),!e.value);
			else if(n.op==Op.and_&&e.value||n.op==Op.or_&&!e.value)
				pending~=[Entry(a.at(n.b),e.value),Entry(a.at(n.a),e.value)];
			else{
				Constraint c;
				if(condition(e.term,c)){
					if(!e.value) c.allowed^=any;
					if(c.atom==Term.init){ if(!c.allowed) f.impossible=true; }
					else{
						foreach(b;f.bounds) if(!compatible(b,c)) f.impossible=true;
						f.bounds~=c;
					}
				}
			}
		}
		return f;
	}
	private uint sign(Term t,Facts f=null,uint depth=0){
		spend(1);
		if(f !is null&&f.impossible) return 0;
		auto cached=f is null?signs.get(t.id,8):f.signs.get(t.id,8);
		if(cached<8) return cached;
		if(depth>=128) return any;
		auto n=a.node(t);
		uint s=any;
		if(a.isNumber(t)) s=signOf(a.number(t).re);
		else switch(n.op){
			case Op.add,Op.mul:
				s=combine(sign(a.at(n.a),f,depth+1),sign(a.at(n.b),f,depth+1),n.op==Op.mul); break;
			case Op.inv:s=sign(a.at(n.a),f,depth+1)&~zero; break;
			case Op.abs,Op.pow:
				s=sign(a.at(n.a),f,depth+1);
				if(n.op==Op.pow&&n.value==0) s=pos;
				else if(n.op==Op.abs||n.value%2==0) s=(s&zero)|(s&(neg|pos)?pos:0);
				break;
			case Op.mask:s=zero|sign(a.at(n.b),f,depth+1); break;
			default:break;
		}
		if(f !is null&&f.bounds.length){
			auto v=affine(t);
			foreach(bit;[neg,zero,pos]) if(s&bit){
				auto c=constraint(v,bit);
				foreach(b;f.bounds) if(!compatible(b,c)){ s&=~bit; break; }
			}
		}
		if(f is null) signs.set(t.id,s); else f.signs.set(t.id,s);
		return s;
	}
	private int truth(Term t,Facts f=null,uint depth=0){
		spend(1);
		if(f !is null){
			if(f.impossible) return 0;
			auto known=f.known.get(t.id,2); if(known<2) return cast(int)known;
		}
		if(depth>=128) return -1;
		auto n=a.node(t);
		Constraint c;
		if(condition(t,c)){
			if(c.atom==Term.init) return c.allowed?1:0;
			auto d=c.bound.zero?c.atom:a.add(c.atom,a.real_(-c.bound));
			auto s=sign(d,f);
			if(!(s&~c.allowed)) return 1;
			if(!(s&c.allowed)) return 0;
		}
		if(n.op==Op.not_){ auto p=truth(a.at(n.a),f,depth+1); return p<0?p:1-p; }
		if(n.op==Op.and_||n.op==Op.or_){
			auto stop=n.op==Op.and_?0:1;
			auto p=truth(a.at(n.a),f,depth+1);
			if(p==stop) return stop;
			auto q=truth(a.at(n.b),f,depth+1);
			return p>=0?q:q==stop?stop:-1;
		}
		return -1;
	}
	private Term local(Term t,Facts f=null){
		auto n=a.node(t);
		if(f !is null&&n.sort==Sort.real_&&sign(t,f)==zero) return a.real_(0);
		if(n.op==Op.abs){
			auto x=a.at(n.a),s=sign(x,f);
			if(!(s&neg)) return x;
			if(!(s&pos)) return a.neg(x);
		}else if(n.sort==Sort.boolean){
			auto value=truth(t,f); if(value>=0) return a.boolean(value!=0);
		}
		return t;
	}
	Term reduce(Term t){
		auto r=local(t); if(r!=t) return r;
		auto n=a.node(t);
		if(n.op==Op.and_||n.op==Op.or_){
			auto p=a.at(n.a),q=a.at(n.b);
			Constraint x,y;
			if(condition(p,x)&&condition(q,y)&&x.atom==y.atom&&x.atom!=Term.init){
				if(x.bound==y.bound){ x.allowed=n.op==Op.and_?x.allowed&y.allowed:x.allowed|y.allowed; return predicate(x); }
				if(implies(x,y)) return predicate(n.op==Op.and_?x:y);
				if(implies(y,x)) return predicate(n.op==Op.and_?y:x);
			}
			auto stop=n.op==Op.and_?0:1;
			auto value=truth(q,assume(p,stop==0));
			if(value>=0) return value==stop?a.boolean(stop!=0):p;
		}
		if(n.op==Op.lt||n.op==Op.le){
			Constraint c; if(condition(t,c)) return predicate(c);
		}
		return t;
	}
	Term under(Term body,Term guard,Term delegate(Term) @safe normalize){
		auto f=assume(guard,true);
		if(f.impossible) return a.number(Number(0),a.sort(body));
		Table!(uint,uint) memo;
		uint[] stack=[body.id];
		while(stack.length){
			spend(1);
			auto id=stack[$-1],n=a.node(a.at(id));
			if(n.arity>=1&&!memo.contains(n.a)){ stack~=n.a; continue; }
			if(n.arity==2&&!memo.contains(n.b)){ stack~=n.b; continue; }
			Term[] cs;
			if(n.arity>=1) cs~=a.at(memo.get(n.a,uint.max));
			if(n.arity==2) cs~=a.at(memo.get(n.b,uint.max));
			auto t=local(a.rebuild(a.at(id),cs),f);
			if(t!=a.at(id)) t=normalize(t);
			memo.set(id,t.id); --stack.length;
		}
		return a.at(memo.get(body.id,uint.max));
	}
}
