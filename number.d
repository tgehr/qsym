module qsym.number;
public import std.bigint:BigInt;
import std.conv:to;
import std.exception:enforce;
@safe:

private BigInt gcd(BigInt a,BigInt b){
	if(a<0) a=-a;
	if(b<0) b=-b;
	while(b!=0){ auto r=a%b; a=b; b=r; }
	return a;
}

struct Rational{
	private BigInt n;
	private BigInt d=BigInt(1);
	this(long n){ this.n=BigInt(n); }
	this(string n){ this.n=BigInt(n); }
	this(BigInt n,BigInt d){
		enforce(d!=0,"zero rational denominator");
		if(d<0){ n=-n; d=-d; }
		auto g=gcd(n,d);
		this.n=n/g; this.d=d/g;
	}
	BigInt numerator()const{ return n; }
	BigInt denominator()const{ return d; }
	bool integral()const{ return d==1; }
	bool small()const{ return integral&&n>=long.min&&n<=long.max; }
	long integer()const{ enforce(small,"integer does not fit in long"); return n.toLong(); }
	bool zero()const{ return n==0; }
	bool one()const{ return n==1&&d==1; }
	size_t words()const{ return n.uintLength+d.uintLength; }
	Rational inverse()const{ enforce(!zero,"inverse of zero"); return Rational(d,n); }
	Rational opUnary(string op)()const if(op=="-"){ return Rational(-n,d); }
	Rational opBinary(string op)(Rational b)const if(op=="+"||op=="-"||op=="*"||op=="/"){
		static if(op=="+") return Rational(n*b.d+b.n*d,d*b.d);
		else static if(op=="-") return this+-b;
		else static if(op=="*") return Rational(n*b.n,d*b.d);
		else return this*b.inverse;
	}
	bool opEquals(Rational b)const{ return n==b.n&&d==b.d; }
	int opCmp(Rational b)const{ return (n*b.d).opCmp(b.n*d); }
	string toString()const{ return to!string(n)~(d==1?"":"/"~to!string(d)); }
}

struct Number{
	Rational re,im;
	this(long r,long i=0){ re=Rational(r); im=Rational(i); }
	this(Rational r,Rational i=Rational.init){ re=r; im=i; }
	bool zero()const{ return re.zero&&im.zero; }
	bool one()const{ return re.one&&im.zero; }
	size_t words()const{ return re.words+im.words; }
	Number conjugate()const{ return Number(re,-im); }
	Number inverse()const{
		enforce(!zero,"inverse of zero");
		auto d=re*re+im*im;
		return Number(re/d,-im/d);
	}
	Number opUnary(string op)()const if(op=="-"){ return Number(-re,-im); }
	Number opBinary(string op)(Number b)const if(op=="+"||op=="-"||op=="*"||op=="/"){
		static if(op=="+") return Number(re+b.re,im+b.im);
		else static if(op=="-") return this+-b;
		else static if(op=="*") return Number(re*b.re-im*b.im,re*b.im+im*b.re);
		else return this*b.inverse;
	}
	bool opEquals(Number b)const{ return re==b.re&&im==b.im; }
	string toString()const{ return re.toString~","~im.toString; }
}

unittest{
	import std.exception:assertThrown;
	auto half=Rational(BigInt(2),BigInt(4));
	assert(half.toString=="1/2");
	assert(half+half==Rational(1));
	assert(Rational(BigInt(0),BigInt(-8)).toString=="0");
	auto large=Rational("9223372036854775808");
	assert(!large.small&&(-large).integer==long.min);
	assert((large*large).toString=="85070591730234615865843651857942052864");
	assert(Number(1,1)*Number(1,1)==Number(0,2));
	assert(Number(1,1)*Number(1,1).inverse==Number(1));
	assertThrown(Number(0).inverse);
}
