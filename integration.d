// Untrusted candidates for finite, constant-weight linear-guard integrals.
// Bounds, exceptional points, and the result are checked by Lean at extraction.
module qsym.integration;
import qsym.ir;
@safe:

struct IntegralBounds{
	Rational coefficient=Rational(1),lower,upper;
	bool hasLower,hasUpper,zero;
	Rational[] exceptions,nulls;
}

// Candidate cell boundaries for arbitrary Boolean combinations of affine
// comparisons. This does not assert bounded support or an integral value.
bool integralCutPoints(Arena a,Term predicate,Term x,out Rational[] points){
	Rational[] cuts;
	bool visit(Term t,uint depth=0){
		if(depth>64||cuts.length>64) return false;
		auto n=a.view(t);
		if(n.op==Op.boolLit) return true;
		if(n.op==Op.not_) return visit(a.viewChild(t,0),depth+1);
		if(n.op==Op.and_||n.op==Op.or_) return visit(a.viewChild(t,0),depth+1)&&visit(a.viewChild(t,1),depth+1);
		bool nz=n.op==Op.nonzero||n.op==Op.builtin&&(n.value==Builtin.nonzeroN||n.value==Builtin.nonzeroZ||n.value==Builtin.nonzeroQ);
		bool order=n.op==Op.lt||n.op==Op.le||n.op==Op.builtin&&(n.value==Builtin.ltN||n.value==Builtin.leN||
			n.value==Builtin.ltZ||n.value==Builtin.leZ||n.value==Builtin.ltQ||n.value==Builtin.leQ);
		if(!nz&&!order) return false;
		Rational sa,oa,sb,ob;
		if(!affine(a,a.viewChild(t,0),x,sa,oa)) return false;
		if(!nz&&!affine(a,a.viewChild(t,1),x,sb,ob)) return false;
		auto slope=sa-sb;
		if(!slope.zero){
			auto cut=-(oa-ob)/slope; if(cut.words>128) return false;
			cuts~=cut;
		}
		return true;
	}
	if(!visit(predicate)) return false;
	points=cuts; return true;
}

bool integralAffine(Arena a,Term t,Term x,out Rational slope,out Rational offset){
	return affine(a,t,x,slope,offset);
}

private bool affine(Arena a,Term t,Term x,out Rational slope,out Rational offset,uint depth=0){
	if(depth>64) return false;
	if(t==x){ slope=Rational(1); return true; }
	if(a.isNumber(t)){ offset=a.number(t).re; return a.number(t).im.zero; }
	auto n=a.view(t);
	if(n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castQR) return affine(a,a.viewChild(t,0),x,slope,offset,depth+1);
	bool add=n.op==Op.add||n.op==Op.builtin&&(n.value==Builtin.addN||n.value==Builtin.addZ||n.value==Builtin.addQ);
	bool mul=n.op==Op.mul||n.op==Op.builtin&&(n.value==Builtin.mulN||n.value==Builtin.mulZ||n.value==Builtin.mulQ);
	if(!add&&!mul) return false;
	Rational sa,oa,sb,ob;
	if(!affine(a,a.viewChild(t,0),x,sa,oa,depth+1)||!affine(a,a.viewChild(t,1),x,sb,ob,depth+1)) return false;
	if(add){ slope=sa+sb; offset=oa+ob; return true; }
	if(!sa.zero&&!sb.zero) return false;
	slope=sa*ob+sb*oa; offset=oa*ob; return true;
}

bool integralBounds(Arena a,Term input,Term x,out IntegralBounds result){
	IntegralBounds r;
	bool predicate(Term p,bool negated=false,uint depth=0) @safe {
		if(depth>64||r.exceptions.length>64) return false;
		auto n=a.view(p);
		if(n.op==Op.boolLit){ if(cast(bool)n.value==negated) r.zero=true; return true; }
		if(n.op==Op.not_) return predicate(a.viewChild(p,0),!negated,depth+1);
		if(n.op==Op.and_&&!negated||n.op==Op.or_&&negated)
			return predicate(a.viewChild(p,0),negated,depth+1)&&predicate(a.viewChild(p,1),negated,depth+1);
		Rational sa,oa,sb,ob;
		if(n.op!=Op.nonzero&&n.op!=Op.lt&&n.op!=Op.le) return false;
		if(!affine(a,a.viewChild(p,0),x,sa,oa)) return false;
		if(n.op!=Op.nonzero&&!affine(a,a.viewChild(p,1),x,sb,ob)) return false;
		auto s=sa-sb,o=oa-ob;
		if(s.zero){
			bool truth=n.op==Op.nonzero?!o.zero:n.op==Op.lt?o<Rational(0):o<=Rational(0);
			if(truth==negated) r.zero=true;
			return true;
		}
		auto cut=-o/s; if(cut.words>128) return false;
		r.exceptions~=cut;
		if(n.op==Op.nonzero){ r.nulls~=cut; if(negated) r.zero=true; return true; }
		if(negated) s=-s;
		if(s>Rational(0)){ if(!r.hasUpper||cut<r.upper) r.upper=cut; r.hasUpper=true; }
		else{ if(!r.hasLower||cut>r.lower) r.lower=cut; r.hasLower=true; }
		return true;
	}
	bool product(Term t,uint depth=0) @safe {
		if(depth>128) return false;
		if(a.isNumber(t)){ auto n=a.number(t); if(!n.im.zero) return false; r.coefficient=r.coefficient*n.re; return r.coefficient.words<=128; }
		auto n=a.view(t);
		if(n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castQR) return product(a.viewChild(t,0),depth+1);
		if(n.op==Op.mul) return product(a.viewChild(t,0),depth+1)&&product(a.viewChild(t,1),depth+1);
		return n.op==Op.mask&&predicate(a.viewChild(t,0))&&product(a.viewChild(t,1),depth+1);
	}
	if(!product(input)) return false;
	if(r.coefficient.zero||r.hasLower&&r.hasUpper&&r.upper<r.lower) r.zero=true;
	result=r; return true;
}

Term removeIntegralNullGuards(Arena a,Term input,Term x){
	Term visit(Term t){
		auto n=a.view(t);
		if(n.op==Op.nonzero){ Rational s,o; if(affine(a,a.viewChild(t,0),x,s,o)&&!s.zero) return a.boolean(true); }
		Term[] args; foreach(i;0..n.arity) args~=visit(a.viewChild(t,i));
		return n.arity?a.viewRebuild(t,args,true):t;
	}
	return visit(input);
}
