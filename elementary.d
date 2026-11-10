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
	private void extract(BigInt x,uint degree,out BigInt factor,out BigInt remainder){
		factor=BigInt(1); remainder=BigInt(1);
		auto limit=x; BigInt r;
		if(root(x,degree,r)){ factor=r; return; }
		// A fixed search bound avoids factoring large irreducible inputs.
		// Test perfect-power cofactors after each successful small division.
		for(uint p=2;p<=1024&&BigInt(p)*p<=x;p=p==2?3:p+2){
			budget.spend(1+x.uintLength);
			uint count;
			while(x%p==0){ budget.spend(1+x.uintLength); x/=p; ++count; }
			if(!count) continue;
			factor*=power(BigInt(p),count/degree,limit);
			remainder*=power(BigInt(p),count%degree,limit);
			if(root(x,degree,r)){ factor*=r; x=BigInt(1); break; }
		}
		remainder*=x;
	}
	private bool extract(Rational x,uint degree,out Rational scale,out Rational radicand){
		if(x<=Rational(0)||degree<2) return false;
		BigInt nf,nr,df,dr;
		extract(x.numerator,degree,nf,nr); extract(x.denominator,degree,df,dr);
		scale=Rational(nf,df*dr);
		auto d=Number(Rational(dr,BigInt(1))),r=Number(Rational(nr,BigInt(1)));
		foreach(i;1..degree) r=budget.calc!"*"(r,d);
		radicand=r.re;
		return scale!=Rational(1);
	}
	private bool pi(Term t){ auto n=a.view(t); return n.op==Op.builtin&&n.value==Builtin.pi; }
	private bool cartesian(Term t){
		foreach(id;a.postorder(t)){
			budget.spend(); auto u=a.at(id),n=a.view(u);
			if(n.sort!=Sort.complex||a.isNumber(u)) continue;
			switch(n.op){
				case Op.add,Op.mul,Op.inv,Op.pow,Op.conj:break;
				case Op.builtin:if(n.value==Builtin.castRC) break; goto default;
				default:return false;
			}
		}
		return true;
	}
	private Rational angle(Term t,out bool exact){
		exact=true;
		Term[] pending=[t]; Rational result;
		while(pending.length){
			budget.spend(); auto u=pending[$-1]; --pending.length; auto n=a.view(u);
			if(n.op==Op.add) pending~=[a.at(n.a),a.at(n.b)];
			else if(pi(u)) result=result+Rational(1);
			else if(n.op==Op.mul){
				if(a.isNumber(a.at(n.a))&&pi(a.at(n.b))) result=result+a.number(a.at(n.a)).re;
				else if(a.isNumber(a.at(n.b))&&pi(a.at(n.a))) result=result+a.number(a.at(n.b)).re;
				else exact=false;
			}
			else exact=false;
		}
		return result;
	}
	private bool symbolicPeriod(Term t,uint period,out Term result){
		Term[] pending=[t];
		while(pending.length){
			budget.spend(); auto u=pending[$-1]; --pending.length; auto n=a.view(u);
			if(n.op==Op.add){ pending~=[a.at(n.a),a.at(n.b)]; continue; }
			if(n.op!=Op.mul) continue;
			auto factors=a.multisetTerms(a.multiset(u,Op.mul));
			Rational scale=Rational(1); Term index; bool foundPi,valid=true;
			foreach(e;factors){
				budget.spend(); auto v=a.view(e.term);
				if(a.isNumber(e.term)){
					foreach(i;0..e.count) scale=budget.calc!"*"(Number(scale),a.number(e.term)).re;
				}else if(pi(e.term)&&e.count==1&&!foundPi) foundPi=true;
				else{
					uint exponent=1;
					if(v.op==Op.pow){ exponent=cast(uint)v.value; v=a.view(a.at(v.a)); }
					if(v.op!=Op.builtin||v.value!=Builtin.castQR){ valid=false; break; }
					auto q=a.view(a.at(v.a));
					if(q.op!=Op.builtin||q.value!=Builtin.castZQ){ valid=false; break; }
					auto factor=a.at(q.a);
					if(exponent!=1) factor=a.pow(factor,exponent);
					if(e.count!=1) factor=a.pow(factor,e.count);
					index=index==Term.init?factor:a.mul(index,factor);
				}
			}
			scale=budget.calc!"/"(Number(scale),Number(period)).re;
			if(!valid||!foundPi||index==Term.init||!scale.integral||scale==Rational(0)) continue;
			result=scale==Rational(1)?index:a.mul(a.number(Number(scale),Sort.integer),index); return true;
		}
		return false;
	}
	bool propose(Term t,out Instance result){
		auto n=a.view(t); if(n.op!=Op.builtin) return false;
		auto f=cast(Builtin)n.value;
		if(f==Builtin.absC&&cartesian(a.at(n.a))){
			result=instantiate(a,Law.complex_norm_components,[a.at(n.a)]); return true;
		}
		if(f==Builtin.floorR||f==Builtin.ceilR){
			auto x=a.at(n.a);
			if(a.view(x).op==Op.add){
				auto operands=a.multisetTerms(a.multiset(x,Op.add));
				foreach(i,e;operands){
					budget.spend(); if(!a.isNumber(e.term)) continue;
					auto value=a.number(e.term); if(!value.re.integral||value.zero) continue;
					--operands[i].count;
					result=instantiate(a,f==Builtin.floorR?Law.real_floor_shift_literal:Law.real_ceil_shift_literal,
						[a.region(Op.add,Sort.real_,operands),e.term,a.number(value,Sort.integer)]); return true;
				}
			}
		}
		if(f==Builtin.logR&&a.isNumber(a.at(n.a))){
			auto q=a.number(a.at(n.a)).re;
			if(q>Rational(0)&&!q.integral){
				result=instantiate(a,Law.real_log_rational,[a.at(n.a),
					a.real_(Rational(q.numerator,BigInt(1))),a.real_(Rational(q.denominator,BigInt(1)))]); return true;
			}
			if(q>Rational(1)){
				// Perfect powers suffice; factoring the integer is unnecessary.
				// Repeated extraction also handles composite exponents.
				auto words=q.numerator.uintLength;
				if(words>budget.maxWords) throw new Limit;
				auto bits=(words-1)*32,high=q.numerator.getDigit!uint(words-1); BigInt base;
				while(high){ ++bits; high>>=1; }
				foreach(degree;2..bits){
					budget.spend();
					if(root(q.numerator,cast(uint)degree,base)){
						result=instantiate(a,Law.real_log_exact_power,[a.at(n.a),
							a.real_(Rational(base,BigInt(1))),a.real_(degree-2)]); return true;
					}
				}
			}
		}
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
			auto x=a.number(a.at(n.a)).re; Rational value;
			if(root(x,2,value)){
				result=instantiate(a,Law.real_sqrt_exact,[a.at(n.a),a.real_(value)]); return true;
			}
			Rational scale,radicand;
			if(!extract(x,2,scale,radicand)) return false;
			result=instantiate(a,Law.real_sqrt_scale,[a.at(n.a),a.real_(scale),a.real_(radicand)]); return true;
		}
		if(f==Builtin.powerR&&a.isNumber(a.at(n.a))&&a.isNumber(a.at(n.b))){
			auto exponent=a.number(a.at(n.b)).re;
			if(exponent.numerator<0||exponent.numerator>uint.max||exponent.denominator>64) return false;
			auto degree=cast(uint)exponent.denominator.toLong();
			auto x=a.number(a.at(n.a)).re; Rational value;
			if(root(x,degree,value)){
				result=instantiate(a,Law.real_power_exact,[a.at(n.a),a.real_(value),a.at(n.b),
					a.real_(exponent.numerator.toLong()),a.real_(degree-1)]); return true;
			}
			Rational scale,radicand;
			if(!extract(x,degree,scale,radicand)) return false;
			result=instantiate(a,Law.real_power_scale,[a.at(n.a),a.real_(scale),a.real_(radicand),a.at(n.b),
				a.real_(exponent.numerator.toLong()),a.real_(degree-2)]); return true;
		}
		if(f==Builtin.sinR||f==Builtin.cosR||f==Builtin.tanR||f==Builtin.cisR){
			Term turns;
			if(symbolicPeriod(a.at(n.a),f==Builtin.tanR?1:2,turns)){
				auto law=f==Builtin.sinR?Law.real_sin_period:f==Builtin.cosR?Law.real_cos_period:
					f==Builtin.tanR?Law.real_tan_period:Law.complex_phase_period;
				result=instantiate(a,law,[a.at(n.a),turns]); return true;
			}
			bool exact;
			auto q=angle(a.at(n.a),exact),den=q.denominator*(f==Builtin.tanR?1:2),k=q.numerator/den;
			if(q.numerator<0&&q.numerator%den!=0) --k;
			if(k!=0){
				auto law=f==Builtin.sinR?Law.real_sin_period:f==Builtin.cosR?Law.real_cos_period:
					f==Builtin.tanR?Law.real_tan_period:Law.complex_phase_period;
				result=instantiate(a,law,[a.at(n.a),a.number(Number(Rational(k,BigInt(1))),Sort.integer)]); return true;
			}
			if(f!=Builtin.tanR&&q>=Rational(BigInt(1),BigInt(2))){
				auto law=f==Builtin.sinR?Law.real_sin_quarter_turn:f==Builtin.cosR?Law.real_cos_quarter_turn:Law.complex_phase_quarter_turn;
				result=instantiate(a,law,[a.at(n.a)]); return true;
			}
			// Expand only phases whose components have exact elementary values.
			// In particular, leave symbolic phases compact and tangent poles alone.
			auto degree=q.denominator;
			if(exact&&(degree==1||degree==3||degree==4||degree==6)){
				if(f==Builtin.cisR){ result=instantiate(a,Law.complex_phase_cartesian,[a.at(n.a)]); return true; }
				if(f==Builtin.tanR){ result=instantiate(a,Law.real_tan_ratio,[a.at(n.a)]); return true; }
			}
		}
		return false;
	}
}
