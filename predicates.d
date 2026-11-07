module qsym.predicates;
import qsym.ir;
import qsym.budget;
import qsym.field:Field;
import qsym.elementary:Elementary;
import qsym.generated.rules;
@safe:

// Witness search only: the engine checks every factorization and sign premise.
package final class Predicates{
	private Arena a;
	private Budget budget;
	private Field field;
	private Elementary elementary;
	this(Arena a,Budget budget,Field field,Elementary elementary){
		this.a=a; this.budget=budget; this.field=field; this.elementary=elementary;
	}
	bool propose(Term t,Term residual,out Instance result,bool factor=true){
		auto n=a.node(t); Term atom; Number[3] c;
		auto s=a.sort(residual),complex=s==Sort.complex;
		auto nz=n.op==Op.nonzero; auto l=a.at(n.a),r=nz?a.number(Number(0),s):a.at(n.b);
		if(!field.quadratic(residual,atom,c)){
			// Do not recursively factor goals generated to check a factorization.
			if(!factor) return false;
			Term x,y; if(!field.commonFactor(residual,x,y)) return false;
			result=nz?instantiate(a,complex?Law.complex_nonzero_factor:Law.real_nonzero_factor,[l,x,y]):
				instantiate(a,n.op==Op.lt?Law.real_lt_factor:Law.real_le_factor,[l,r,x,y]);
			return true;
		}
		if(c[2].zero){
			if(c[1].zero||nz&&c[1].one) return false;
			if(!nz&&(l==atom&&a.isNumber(r)||r==atom&&a.isNumber(l))) return false;
			auto root=budget.calc!"/"(-c[0],c[1]),x=a.sub(atom,a.number(root,s)),scale=a.number(c[1],s);
			if(nz) result=instantiate(a,complex?Law.complex_nonzero_scale:Law.real_nonzero_scale,[l,x,scale]);
			else{
				auto positive=c[1].re>Rational(0);
				auto law=n.op==Op.lt?(positive?Law.real_lt_affine_pos:Law.real_lt_affine_neg):
					(positive?Law.real_le_affine_pos:Law.real_le_affine_neg);
				result=instantiate(a,law,[l,r,scale,x]);
			}
			return true;
		}
		auto discriminant=budget.calc!"-"(budget.calc!"*"(c[1],c[1]),budget.calc!"*"(Number(4),budget.calc!"*"(c[2],c[0])));
		auto scale=a.number(c[2],s),twoA=budget.calc!"*"(Number(2),c[2]);
		if(!complex&&discriminant.re<Rational(0)){
			auto u=a.add(atom,a.number(budget.calc!"/"(c[1],twoA),Sort.real_));
			auto v=a.number(budget.calc!"/"(-discriminant,budget.calc!"*"(twoA,twoA)),Sort.real_);
			result=nz?instantiate(a,Law.real_nonzero_definite,[l,scale,u,v]):
				instantiate(a,n.op==Op.lt?Law.real_lt_definite:Law.real_le_definite,[l,r,scale,u,v]);
			return true;
		}
		Rational squareRoot;
		if(complex||!elementary.root(discriminant.re,2,squareRoot)){
			auto center=a.number(budget.calc!"/"(c[1],twoA),s);
			auto radicand=a.number(budget.calc!"/"(discriminant,budget.calc!"*"(twoA,twoA)),s);
			if(nz) result=instantiate(a,complex?Law.complex_nonzero_quadratic:Law.real_nonzero_quadratic,[l,atom,scale,center,radicand]);
			else{
				auto positive=c[2].re>Rational(0);
				auto law=n.op==Op.lt?(positive?Law.real_lt_quadratic_pos:Law.real_lt_quadratic_neg):
					(positive?Law.real_le_quadratic_pos:Law.real_le_quadratic_neg);
				result=instantiate(a,law,[l,r,atom,scale,center,radicand]);
			}
			return true;
		}
		auto first=budget.calc!"/"(budget.calc!"-"(-c[1],Number(squareRoot)),twoA);
		auto second=budget.calc!"/"(budget.calc!"+"(-c[1],Number(squareRoot)),twoA);
		if(first.re>second.re){ auto tmp=first; first=second; second=tmp; }
		auto x=a.sub(atom,a.number(first,Sort.real_)),y=a.mul(scale,a.sub(atom,a.number(second,Sort.real_)));
		result=nz?instantiate(a,Law.real_nonzero_factor,[l,x,y]):
			instantiate(a,n.op==Op.lt?Law.real_lt_factor:Law.real_le_factor,[l,r,x,y]);
		return true;
	}
}
