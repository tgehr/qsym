module qsym.elementary;
import qsym.ir;
import qsym.budget;
import qsym.generated.rules;
@safe:

// Propose exact roots and period reductions; Engine checks each generated law's premises.
package final class Elementary{
	private Arena a;
	private Budget budget;
	this(Arena a,Budget budget){ this.a=a; this.budget=budget; }
	private BigInt power(BigInt x,uint n,BigInt limit){
		auto result=BigInt(1);
		while(n){
			budget.spend(1+x.uintLength+result.uintLength);
			if(n&1){ result*=x; if(result>limit) return limit+1; }
			n>>=1;
			if(n){ x*=x; if(x>limit) x=limit+1; }
		}
		return result;
	}
	private bool root(BigInt x,uint n,out BigInt result){
		if(x<0||!n) return false;
		if(x.uintLength>budget.maxWords) throw new Limit;
		if(x<=1){ result=x; return true; }
		auto bits=x.uintLength*32;
		auto lo=BigInt(0),hi=BigInt(1)<<((bits+n-1)/n);
		while(hi-lo>1){
			auto mid=(lo+hi)/2,p=power(mid,n,x);
			if(p==x){ result=mid; return true; }
			if(p<x) lo=mid; else hi=mid;
		}
		if(power(lo,n,x)==x){ result=lo; return true; }
		return false;
	}
	bool root(Rational x,uint n,out Rational result){
		BigInt numerator,denominator;
		if(!root(x.numerator,n,numerator)||!root(x.denominator,n,denominator)) return false;
		result=Rational(numerator,denominator); return true;
	}
	private bool pi(Term t){ auto n=a.node(t); return n.op==Op.builtin&&n.value==Builtin.pi; }
	private Rational angle(Term t){
		Term[] pending=[t]; Rational result;
		while(pending.length){
			budget.spend(); auto u=pending[$-1]; --pending.length; auto n=a.node(u);
			if(n.op==Op.add) pending~=[a.at(n.a),a.at(n.b)];
			else if(pi(u)) result=result+Rational(1);
			else if(n.op==Op.mul){
				if(a.isNumber(a.at(n.a))&&pi(a.at(n.b))) result=result+a.number(a.at(n.a)).re;
				else if(a.isNumber(a.at(n.b))&&pi(a.at(n.a))) result=result+a.number(a.at(n.b)).re;
			}
		}
		return result;
	}
	bool propose(Term t,out Instance result){
		auto n=a.node(t); if(n.op!=Op.builtin) return false;
		auto f=cast(Builtin)n.value;
		if((f==Builtin.floorR||f==Builtin.ceilR)&&a.isNumber(a.at(n.a))){
			auto q=a.number(a.at(n.a)).re,m=q.numerator/q.denominator,r=q.numerator%q.denominator;
			budget.spend(q.words);
			if(f==Builtin.floorR&&r<0) --m;
			if(f==Builtin.ceilR&&r>0) ++m;
			result=instantiate(a,f==Builtin.floorR?Law.real_floor_exact:Law.real_ceil_exact,
				[a.at(n.a),a.number(Number(Rational(m,BigInt(1))),Sort.integer)]); return true;
		}
		if((f==Builtin.log2R||f==Builtin.log10R)&&a.isNumber(a.at(n.a))){
			auto q=a.number(a.at(n.a)).re; if(q<=Rational(0)) return false;
			long exponent; auto base=f==Builtin.log2R?2:10;
			foreach(i,v;[q.numerator,q.denominator]){
				while(v!=1){
					budget.spend(1+v.uintLength);
					if(v%base!=0) return false;
					v/=base; exponent+=i?-1:1;
				}
			}
			result=instantiate(a,f==Builtin.log2R?Law.real_log2_exact:Law.real_log10_exact,[a.at(n.a),a.real_(exponent)]); return true;
		}
		if((f==Builtin.gammaR||f==Builtin.gammaC)&&a.isNumber(a.at(n.a))){
			auto q=a.number(a.at(n.a));
			if(!q.im.zero||!q.re.integral||q.re<Rational(2)||q.re>Rational(cast(long)budget.maxTerms)) return false;
			result=instantiate(a,f==Builtin.gammaR?Law.real_gamma_next:Law.complex_gamma_next,[a.at(n.a),a.real_(q.re.integer-2)]); return true;
		}
		if((f==Builtin.powQZ||f==Builtin.powRZ||f==Builtin.powCZ||f==Builtin.powerC)&&a.isNumber(a.at(n.b))){
			auto q=a.number(a.at(n.b));
			if(!q.im.zero||!q.re.integral||q.re>=Rational(0)||q.re<Rational(-cast(long)uint.max)) return false;
			auto law=f==Builtin.powQZ?Law.rational_indexed_negative_power:f==Builtin.powRZ?Law.real_indexed_negative_power:
				f==Builtin.powCZ?Law.complex_indexed_negative_power:Law.complex_general_negative_power;
			result=instantiate(a,law,[a.at(n.a),a.at(n.b),a.real_(-q.re.integer-1)]); return true;
		}
		if(f==Builtin.sqrtC&&a.isNumber(a.at(n.a))){
			auto z=a.number(a.at(n.a)); Rational magnitude,re,im;
			auto norm=budget.calc!"+"(budget.calc!"*"(Number(z.re),Number(z.re)),budget.calc!"*"(Number(z.im),Number(z.im)));
			if(!root(norm.re,2,magnitude)) return false;
			auto rr=budget.calc!"/"(budget.calc!"+"(Number(magnitude),Number(z.re)),Number(2));
			auto ii=budget.calc!"/"(budget.calc!"-"(Number(magnitude),Number(z.re)),Number(2));
			if(!root(rr.re,2,re)||!root(ii.re,2,im)) return false;
			if(z.im<Rational(0)) im=-im;
			result=re.zero?instantiate(a,Law.complex_sqrt_imaginary,[a.at(n.a),a.real_(im)]):
				instantiate(a,Law.complex_sqrt_exact,[a.at(n.a),a.complex(re,im)]); return true;
		}
		if(f==Builtin.sqrtR&&a.isNumber(a.at(n.a))){
			Rational value; if(!root(a.number(a.at(n.a)).re,2,value)) return false;
			result=instantiate(a,Law.real_sqrt_exact,[a.at(n.a),a.real_(value)]); return true;
		}
		if(f==Builtin.powerR&&a.isNumber(a.at(n.a))&&a.isNumber(a.at(n.b))){
			auto exponent=a.number(a.at(n.b)).re;
			if(exponent.numerator<0||exponent.numerator>uint.max||exponent.denominator>64) return false;
			auto degree=cast(uint)exponent.denominator.toLong();
			Rational value; if(!root(a.number(a.at(n.a)).re,degree,value)) return false;
			result=instantiate(a,Law.real_power_exact,[a.at(n.a),a.real_(value),a.at(n.b),
				a.real_(exponent.numerator.toLong()),a.real_(degree-1)]); return true;
		}
		if(f==Builtin.sinR||f==Builtin.cosR||f==Builtin.cisR){
			auto q=angle(a.at(n.a)),den=q.denominator*2,k=q.numerator/den;
			if(q.numerator<0&&q.numerator%den!=0) --k;
			if(k==0) return false;
			auto law=f==Builtin.sinR?Law.real_sin_period:f==Builtin.cosR?Law.real_cos_period:Law.complex_phase_period;
			result=instantiate(a,law,[a.at(n.a),a.number(Number(Rational(k,BigInt(1))),Sort.integer)]); return true;
		}
		return false;
	}
}
