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
		Case("NonzeroInverse",a.nonzero(a.inv(x)),a.boolean(true))
	];
}

@safe unittest{
	auto session=Session.open(); auto a=session.arena;
	foreach(c;examples(a)){
		auto fast=simplify(a,c.input),traced=simplify(a,c.input,Options(DensityMode.preserve,true));
		assert(fast.output==c.expected,c.name~"\n"~dump(a,fast.output)~"expected:\n"~dump(a,c.expected));
		assert(fast.output==traced.output&&fast.exhausted==traced.exhausted,c.name);
		assert(!fast.exhausted&&simplify(a,fast.output).output==fast.output,c.name~" is not idempotent");
	}
	auto x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1);
	auto limited=simplify(a,a.pow(a.add(x,y),100),Options(DensityMode.preserve,true,100_000,8,1000));
	assert(limited.exhausted);
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
