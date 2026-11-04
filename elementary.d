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
	private bool root(Rational x,uint n,out Rational result){
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
