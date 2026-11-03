module scalar_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:replace;

struct Case{ string name; Term input,expected; }
@safe Case[] examples(Arena a){
	auto x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1),p=a.variable(Sort.boolean,0);
	auto q=a.variable(Sort.boolean,1);
	auto z=a.variable(Sort.complex,0),w=a.variable(Sort.complex,1);
	auto zero=a.real_(0),one=a.real_(1),two=a.real_(2);
	auto sum=a.add(x,y);
	auto expanded=a.add(a.add(a.pow(x,2),a.mul(two,a.mul(x,y))),a.pow(y,2));
	auto half=Rational(BigInt(1),BigInt(2));
	auto nonnegative=a.le(zero,x),negative=a.lt(x,zero),positive=a.lt(zero,x);
	auto interval=a.and_(nonnegative,a.lt(x,one));
	return [
		Case("Polynomial",a.sub(a.pow(sum,2),expanded),zero),
		Case("Collect",a.add(a.mul(two,x),a.mul(a.real_(3),x)),a.mul(a.real_(5),x)),
		Case("Rational",a.add(a.inv(two),a.inv(a.real_(3))),a.real_(Rational(BigInt(5),BigInt(6)))),
		Case("Large",a.pow(a.real_(long.max),2),a.real_(Rational("85070591730234615847396907784232501249"))),
		Case("Cancel",a.div(x,x),one),
		Case("DoubleInverse",a.inv(a.inv(x)),x),
		Case("Factors",a.mul(x,a.inv(a.mul(x,y))),a.inv(y)),
		Case("PolynomialDivision",a.div(a.sub(a.pow(x,2),one),a.sub(x,one)),a.add(x,one)),
		Case("ComplexConstant",a.pow(a.complex(1,1),2),a.complex(0,2)),
		Case("ComplexPower",a.pow(a.complex(1,1),5),a.complex(-4,-4)),
		Case("ComplexInverse",a.inv(a.complex(1,1)),a.complex(half,-half)),
		Case("ComplexCancel",a.div(z,z),a.complex(1)),
		Case("ComplexPolynomial",a.sub(a.pow(a.add(z,w),2),
			a.add(a.add(a.pow(z,2),a.mul(a.complex(2),a.mul(z,w))),a.pow(w,2))),a.complex(0)),
		Case("Conjugate",a.conj(a.mul(a.complex(1,1),z)),a.mul(a.complex(1,-1),a.conj(z))),
		Case("GuardedCancellation",a.mask(a.nonzero(x),a.div(x,x)),a.mask(a.nonzero(x),one)),
		Case("SameGuard",a.add(a.mask(p,x),a.mask(p,y)),a.mask(p,sum)),
		Case("Complement",a.add(a.mask(p,x),a.mask(a.not_(p),x)),x),
		Case("MaskedProduct",a.mul(a.mask(p,x),a.mask(q,y)),a.mask(a.and_(p,q),a.mul(x,y))),
		Case("NestedMasks",a.mask(p,a.mask(q,x)),a.mask(a.and_(p,q),x)),
		Case("Contradiction",a.mask(a.and_(p,a.not_(p)),a.inv(zero)),zero),
		Case("GuardedUndefined",a.mask(p,a.inv(zero)),a.mask(p,a.inv(zero))),
		Case("MaskedZero",a.mask(p,zero),zero),
		Case("ExtendedZero",a.mul(zero,a.inv(x)),zero),
		Case("Comparison",a.lt(a.add(x,one),a.add(x,two)),a.boolean(true)),
		Case("ShortCircuit",a.or_(a.lt(a.inv(x),one),a.boolean(true)),a.boolean(true)),
		Case("NonzeroPower",a.nonzero(a.pow(x,3)),a.nonzero(x)),
		Case("NonzeroProduct",a.nonzero(a.mul(x,y)),a.and_(a.nonzero(x),a.nonzero(y))),
		Case("NonzeroInverse",a.nonzero(a.inv(x)),a.boolean(true)),
		Case("AbsConstant",a.abs(a.real_(long.min)),a.real_(Rational("9223372036854775808"))),
		Case("AbsSquare",a.abs(a.pow(x,2)),a.pow(x,2)),
		Case("AbsQuartic",a.abs(a.pow(x,4)),a.pow(x,4)),
		Case("AbsProduct",a.abs(a.mul(x,y)),a.mul(a.abs(x),a.abs(y))),
		Case("AbsInverse",a.abs(a.inv(x)),a.inv(a.abs(x))),
		Case("AbsOddPower",a.abs(a.pow(x,3)),a.pow(a.abs(x),3)),
		Case("AbsMask",a.abs(a.mask(p,x)),a.mask(p,a.abs(x))),
		Case("SquareNonnegative",a.le(zero,a.pow(x,2)),a.boolean(true)),
		Case("EvenPowerNonnegative",a.le(zero,a.pow(x,6)),a.boolean(true)),
		Case("PositiveQuadratic",a.lt(zero,a.add(a.pow(x,2),one)),a.boolean(true)),
		Case("NegativeSquare",a.lt(a.pow(x,2),zero),a.boolean(false)),
		Case("PositiveInverse",a.lt(zero,a.inv(a.add(a.pow(x,2),one))),a.boolean(true)),
		Case("IntervalEmpty",a.and_(negative,nonnegative),a.boolean(false)),
		Case("ClosedPoint",a.and_(a.le(x,zero),nonnegative),a.not_(a.nonzero(x))),
		Case("IntervalUnion",a.or_(negative,nonnegative),a.boolean(true)),
		Case("PuncturedUnion",a.or_(negative,positive),a.nonzero(x)),
		Case("StrongerUpper",a.and_(a.lt(x,one),a.lt(x,two)),a.lt(x,one)),
		Case("WeakerUpper",a.or_(a.lt(x,one),a.lt(x,two)),a.lt(x,two)),
		Case("ScaledBound",a.lt(a.mul(a.real_(-2),x),two),a.lt(a.real_(-1),x)),
		Case("FractionalBound",a.lt(a.mul(a.real_(half),x),a.real_(half)),a.lt(x,one)),
		Case("ShiftedBound",a.lt(a.add(x,one),two),a.lt(x,one)),
		Case("MaskedAbs",a.mask(nonnegative,a.abs(x)),a.mask(nonnegative,x)),
		Case("MaskedNegativeAbs",a.mask(negative,a.abs(x)),a.mask(negative,a.neg(x))),
		Case("GuardedReciprocal",a.mask(positive,a.abs(a.inv(x))),a.mask(positive,a.inv(x))),
		Case("GuardedNonzero",a.mask(positive,a.mask(a.nonzero(x),x)),a.mask(positive,x)),
		Case("GuardDoesNotLeak",a.add(a.mask(nonnegative,a.abs(x)),a.abs(x)),a.add(a.mask(nonnegative,x),a.abs(x))),
		Case("GuardEquality",a.mask(a.equal(x,zero),a.abs(x)),zero),
		Case("GuardNonAdjacent",a.and_(a.and_(negative,a.lt(zero,y)),nonnegative),a.boolean(false)),
		Case("IntervalAbs",a.mask(interval,a.abs(a.sub(x,two))),a.mask(interval,a.add(a.neg(x),two))),
		Case("GuardedCube",a.mask(nonnegative,a.mask(a.le(zero,a.pow(x,3)),x)),a.mask(nonnegative,x))
	];
}

private struct Value{ bool defined; Number number; bool boolean; }
@safe private Value evaluate(Arena a,uint[] order,Value[] memo,Rational x,Rational y,uint flags){
	foreach(id;order){
		auto t=a.at(id),n=a.node(t);
		Value v,l,r;
		if(n.arity>=1) l=memo[n.a];
		if(n.arity==2) r=memo[n.b];
		if(a.isNumber(t)) v=Value(true,a.number(t));
		else switch(n.op){
			case Op.variable:
				v.defined=true;
				if(n.sort==Sort.boolean) v.boolean=(flags>>n.value&1)!=0;
				else if(n.sort==Sort.real_) v.number=Number(n.value?y:x);
				else v.number=n.value?Number(y,-x):Number(x,y);
				break;
			case Op.boolLit:v=Value(true,Number.init,n.value!=0); break;
			case Op.add,Op.mul:
				if(l.defined&&r.defined) v=Value(true,n.op==Op.add?l.number+r.number:l.number*r.number);
				break;
			case Op.inv:if(l.defined&&!l.number.zero) v=Value(true,l.number.inverse); break;
			case Op.pow:
				if(l.defined){
					v=Value(true,Number(1)); auto b=l.number;
					for(auto k=n.value;k;k>>=1){ if(k&1) v.number=v.number*b; if(k>1) b=b*b; }
				}
				break;
			case Op.conj:if(l.defined) v=Value(true,l.number.conjugate); break;
			case Op.abs:if(l.defined) v=Value(true,l.number.re<Rational(0)?-l.number:l.number); break;
			case Op.mask:if(l.defined) v=l.boolean?r:Value(true,Number(0)); break;
			case Op.nonzero:if(l.defined) v=Value(true,Number.init,!l.number.zero); break;
			case Op.not_:if(l.defined) v=Value(true,Number.init,!l.boolean); break;
			case Op.and_:if(l.defined) v=l.boolean?r:l; break;
			case Op.or_:if(l.defined) v=l.boolean?l:r; break;
			case Op.lt,Op.le:
				if(l.defined&&r.defined) v=Value(true,Number.init,n.op==Op.lt?l.number.re<r.number.re:l.number.re<=r.number.re);
				break;
			default:assert(0,"unexpected evaluator operation");
		}
		memo[id]=v;
	}
	return memo[order[$-1]];
}
@safe private void checkValues(Arena a,Term input,Term output){
	auto left=a.postorder(input),right=a.postorder(output);
	auto memo=new Value[a.length];
	foreach(i;-4..5) foreach(j;-2..3) foreach(flags;0u..4u){
		auto x=Rational(BigInt(i),BigInt(2)),y=Rational(j);
		auto l=evaluate(a,left,memo,x,y,flags),r=evaluate(a,right,memo,x,y,flags);
		assert(!l.defined||r.defined&&(a.sort(input)==Sort.boolean?l.boolean==r.boolean:l.number==r.number),
			"value changed at "~x.toString~","~y.toString~"\n"~dump(a,input)~"result:\n"~dump(a,output));
	}
}

@safe unittest{
	auto session=Session.open(); auto a=session.arena;
	foreach(c;examples(a)){
		auto fast=simplify(a,c.input),traced=simplify(a,c.input,Options(DensityMode.preserve,true));
		assert(fast.output==c.expected,c.name~"\n"~dump(a,fast.output)~"expected:\n"~dump(a,c.expected));
		assert(fast.output==traced.output&&fast.exhausted==traced.exhausted,c.name);
		assert(!fast.exhausted&&simplify(a,fast.output).output==fast.output,c.name~" is not idempotent");
		checkValues(a,c.input,fast.output);
	}
	auto x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1);
	auto limited=simplify(a,a.pow(a.add(x,y),100),Options(DensityMode.preserve,true,100_000,8,1000));
	assert(limited.exhausted);
	auto guarded=a.mask(a.le(a.real_(0),x),a.abs(a.add(x,a.real_(1))));
	auto exhausted=simplify(a,guarded,Options(DensityMode.preserve,true,100_000,256,1));
	assert(exhausted.exhausted);
	checkValues(a,guarded,exhausted.output);
	auto enormous=a.pow(a.real_(2),uint.max);
	auto bounded=simplify(a,enormous);
	assert(bounded.exhausted&&bounded.output==enormous);
	auto product=x;
	foreach(i;2..5000) product=a.mul(product,a.variable(Sort.real_,i));
	assert(simplify(a,product,Options(DensityMode.preserve,false,100_000,256,10000)).exhausted);
	assert(!domain(a,a.div(x,x)).everywhere&&domain(a,simplify(a,a.div(x,x)).output).everywhere);
	assert(equivalent(a,a.div(x,x),a.real_(1))==Equivalence.agreeOnCommonDomain);
}

@safe unittest{
	auto session=Session.open(); auto a=session.arena;
	struct Item{ Term term; uint depth; }
	Item[] scalars=[Item(a.real_(0)),Item(a.real_(1)),Item(a.variable(Sort.real_,0)),Item(a.variable(Sort.real_,1))];
	Item[] predicates=[Item(a.boolean(false)),Item(a.boolean(true)),Item(a.variable(Sort.boolean,0))];
	uint seed=0x715a;
	uint random(){ seed=1664525*seed+1013904223; return seed; }
	Item pick(Item[] items){
		auto i=random()%items.length;
		while(items[i].depth>=4) i=(i+1)%items.length;
		return items[i];
	}
	foreach(i;0..128){
		auto l=pick(scalars),r=pick(scalars),p=pick(predicates);
		auto depth=1+(l.depth>r.depth?l.depth:r.depth);
		Term t;
		switch(random()%7){
			case 0:t=a.add(l.term,r.term); break;
			case 1:t=a.mul(l.term,r.term); break;
			case 2:t=a.inv(l.term); break;
			case 3:t=a.pow(l.term,random()%4); break;
			case 4:t=a.abs(l.term); break;
			case 5:t=a.mask(p.term,l.term); if(p.depth>=depth) depth=p.depth+1; break;
			default:t=a.sub(l.term,r.term); break;
		}
		scalars~=Item(t,depth);
		auto q=i%3==0?a.lt(l.term,r.term):i%3==1?a.le(l.term,r.term):a.nonzero(t);
		predicates~=Item(q,depth+1);
		checkValues(a,t,simplify(a,t).output);
		checkValues(a,q,simplify(a,q).output);
	}
}

@safe unittest{
	bool sameTree(Arena a,Term x,Arena b,Term y){
		Term[] xs=[x],ys=[y];
		for(size_t i=0;i<xs.length;++i){
			auto n=a.node(xs[i]),m=b.node(ys[i]);
			if(n.op!=m.op||n.sort!=m.sort||n.arity!=m.arity) return false;
			if(a.isNumber(xs[i])){ if(a.number(xs[i])!=b.number(ys[i])) return false; }
			else if(n.value!=m.value) return false;
			if(n.arity>=1){ xs~=a.at(n.a); ys~=b.at(m.a); }
			if(n.arity==2){ xs~=a.at(n.b); ys~=b.at(m.b); }
		}
		return true;
	}
	auto sa=Session.open(),sb=Session.open();
	auto a=sa.arena,b=sb.arena;
	auto x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1);
	b.real_(Rational("1000000000000000000000000"));
	auto v=b.variable(Sort.real_,1),u=b.variable(Sort.real_,0);
	auto left=a.pow(a.add(x,y),8),right=b.pow(b.add(u,v),8);
	foreach(work;[100,100000]){
		auto opt=Options(DensityMode.preserve,false,100000,256,work);
		auto l=simplify(a,left,opt),r=simplify(b,right,opt);
		assert(l.exhausted==r.exhausted&&sameTree(a,l.output,b,r.output));
	}
}

void main(string[] args){
	enforce(args.length==2,"usage: scalar-tests DIRECTORY");
	auto session=Session.open(); auto a=session.arena;
	mkdirRecurse(args[1]);
	foreach(c;examples(a)){
		auto result=simplify(a,c.input,Options(DensityMode.preserve,true));
		enforce(result.output==c.expected,c.name);
		write(buildPath(args[1],c.name~".lean"),exportLean(a,result).replace("QSym.Certificate","QSym.ScalarTests."~c.name));
	}
	writeln("Wrote scalar certificates.");
}
