module qsym.radical;
import qsym.ir;
import qsym.budget;
import qsym.elementary:Elementary;
import qsym.generated.rules;
import qsym.table:Table;
@safe:

package final class Radical{
	private Arena a;
	private Budget budget;
	private Elementary elementary;
	private Rational[] roots;
	private struct Polynomial{ Number[8] c; }
	private Table!(uint,uint) cache;
	private Polynomial[] values;
	this(Arena a,Budget budget,Elementary elementary){ this.a=a; this.budget=budget; this.elementary=elementary; }
	private Number calc(string op)(Number x,Number y){ return budget.calc!op(x,y); }
	private bool rootTerm(Term t,out Rational r){
		auto n=a.view(t);
		if(n.op!=Op.builtin||n.value!=Builtin.sqrtR||!a.isNumber(a.at(n.a))) return false;
		r=a.number(a.at(n.a)).re; return r>Rational(0);
	}
	private Rational product(uint mask){
		auto r=Number(1);
		foreach(i,q;roots) if(mask&(1u<<i)) r=calc!"*"(r,Number(q));
		return r.re;
	}
	private bool coordinates(Rational r,out uint mask,out Rational scale){
		foreach(m;0..1u<<roots.length){
			budget.spend();
			if(elementary.root(calc!"/"(Number(r),Number(product(m))).re,2,scale)){ mask=m; return true; }
		}
		return false;
	}
	private bool prepare(Term t){
		roots=null; values=null; cache=typeof(cache).init;
		foreach(id;a.viewPostorder(t)){
			budget.spend(); auto u=a.at(id),n=a.view(u);
			if(a.isNumber(u)) continue;
			Rational r,scale; uint mask;
			if(rootTerm(u,r)){
				if(!coordinates(r,mask,scale)){
					if(roots.length==3) return false;
					roots~=r;
				}
				continue;
			}
			if(n.op==Op.add||n.op==Op.mul||n.op==Op.inv) continue;
			if(n.op==Op.pow&&n.value<=256) continue;
			if(n.op==Op.builtin&&n.value==Builtin.castRC) continue;
			return false;
		}
		return roots.length!=0;
	}
	bool expandable(Term t){ return prepare(t); }
	private Polynomial mul(Polynomial x,Polynomial y){
		Polynomial r;
		foreach(i;0..1u<<roots.length) if(!x.c[i].zero)
			foreach(j;0..1u<<roots.length) if(!y.c[j].zero){
				auto c=calc!"*"(calc!"*"(x.c[i],y.c[j]),Number(product(i&j)));
				r.c[i^j]=calc!"+"(r.c[i^j],c);
			}
		return r;
	}
	private bool inverse(Polynomial x,out Polynomial y){
		Number[9][8] rows; auto size=1u<<roots.length;
		foreach(j;0..size){
			Polynomial unit; unit.c[j]=Number(1); auto column=mul(x,unit);
			foreach(i;0..size) rows[i][j]=column.c[i];
		}
		rows[0][size]=Number(1);
		foreach(j;0..size){
			auto pivot=j; while(pivot<size&&rows[pivot][j].zero) ++pivot;
			if(pivot==size) return false;
			auto row=rows[j]; rows[j]=rows[pivot]; rows[pivot]=row;
			auto divisor=rows[j][j];
			foreach(k;j..size+1) rows[j][k]=calc!"/"(rows[j][k],divisor);
			foreach(i;0..size) if(i!=j&&!rows[i][j].zero){
				auto scale=rows[i][j];
				foreach(k;j..size+1) rows[i][k]=calc!"-"(rows[i][k],calc!"*"(scale,rows[j][k]));
			}
		}
		foreach(i;0..size) y.c[i]=rows[i][size]; return true;
	}
	private bool read(Term t,out Polynomial r){
		if(cache.contains(t.id)){ r=values[cache.get(t.id,0)]; return true; }
		budget.spend(); auto n=a.view(t); Rational q,scale; uint mask;
		if(a.isNumber(t)) r.c[0]=a.number(t);
		else if(rootTerm(t,q)){
			if(!coordinates(q,mask,scale)) return false;
			r.c[mask]=Number(scale);
		}else{
			Polynomial x,y;
			if(!read(a.at(n.a),x)) return false;
			if(n.op==Op.add||n.op==Op.mul){
				if(!read(a.at(n.b),y)) return false;
				if(n.op==Op.mul) r=mul(x,y);
				else foreach(i;0..8) r.c[i]=calc!"+"(x.c[i],y.c[i]);
			}else if(n.op==Op.inv){ if(!inverse(x,r)) return false; }
			else if(n.op==Op.pow){
				r.c[0]=Number(1);
				for(auto e=n.value;e;e>>=1){ if(e&1) r=mul(r,x); if(e>1) x=mul(x,x); }
			}else if(n.op==Op.builtin&&n.value==Builtin.castRC) r=x;
			else return false;
		}
		cache.set(t.id,cast(uint)values.length); values~=r; return true;
	}
	private Term emit(Polynomial p,Sort s){
		Term[] terms;
		foreach(i;0..1u<<roots.length) if(!p.c[i].zero){
			auto t=a.number(p.c[i],s);
			if(i){
				foreach(j,q;roots) if(i&(1u<<j)){
					auto root=a.call(Builtin.sqrtR,[a.real_(q)]);
					if(s==Sort.complex) root=a.call(Builtin.castRC,[root]);
					t=a.isNumber(t)&&a.number(t).one?root:a.mul(t,root);
				}
			}
			terms~=t;
		}
		if(!terms.length) return a.number(Number(0),s);
		auto t=terms[0]; foreach(u;terms[1..$]) t=a.add(t,u); return t;
	}
	bool propose(Term t,out Instance result){
		auto n=a.view(t);
		if(n.op!=Op.inv||(n.sort!=Sort.real_&&n.sort!=Sort.complex)) return false;
		auto x=a.at(n.a); if(!prepare(x)) return false;
		Polynomial value,inverted;
		if(!read(x,value)||!inverse(value,inverted)) return false;
		auto y=emit(inverted,n.sort);
		result=instantiate(a,n.sort==Sort.real_?Law.real_radical_inverse:Law.complex_radical_inverse,[x,y]);
		return true;
	}
}
