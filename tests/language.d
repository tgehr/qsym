module language;
import qsym;
import qsym.derive:Derivation;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.string:replace;
import std.conv:to;
import std.stdio:writeln;
import std.exception:enforce,assertThrown;
@safe:

private Syntax syntax(){
	Syntax s; s.declare("n:ℕ,k:ℤ,q:ℚ,x:ℝ,z:ℂ,w:ℂ,p:𝔹"); return s;
}
private struct Example{ string name,source; Sort sort; }
private Example[] examples(){
	return [
		Example("Root","2^(1/2)",Sort.real_),
		Example("RealPower","x^(sin(x)+1/2)",Sort.real_),
		Example("ComplexPower","z^w",Sort.complex),
		Example("PowerAssociation","2^3^2",Sort.real_),
		Example("NaturalPower","n^(n+1)",Sort.natural),
		Example("IntegerPower","n^k",Sort.rational),
		Example("LargeNaturalExponent","n^4294967296",Sort.natural),
		Example("LargeNegativeExponent","q^(-4294967296)",Sort.rational),
		Example("RealNaturalPower","x^n",Sort.real_),
		Example("RationalInverse","q^(-2)",Sort.rational),
		Example("ExactNatural","nat(2)^20+nat(7)",Sort.natural),
		Example("ExactInteger","int(-5)*int(7)+int(2)",Sort.integer),
		Example("ExactRational","rat(1,3)+rat(1,6)",Sort.rational),
		Example("NaturalDifference","n-1",Sort.integer),
		Example("RationalDivision","n/(n+1)",Sort.rational),
		Example("MixedScalars","n+q+x+z",Sort.complex),
		Example("ComplexConstruction","cfromri(1/2,1/3)",Sort.complex),
		Example("ComplexProjections","creal(cfromri(x,x+1))+cimag(cfromri(x,2))",Sort.real_),
		Example("RationalConstruction","qfromnd(int(4),int(6))",Sort.rational),
		Example("Numerator","numerator(rat(-6,8))",Sort.integer),
		Example("Denominator","denominator(rat(-6,8))",Sort.natural),
		Example("RealExpLog","exp(log(x+1))",Sort.real_),
		Example("ComplexExpLog","cexp(clog(z+1))",Sort.complex),
		Example("ComplexBranch","clog(cexp(z))",Sort.complex),
		Example("ComplexTrig","sin(z+0)+cos(z)+tan(z)",Sort.complex),
		Example("ComplexInverseTrig","asin(z)+acos(z)+atan(z)",Sort.complex),
		Example("ComplexHyperbolic","sinh(z)+cosh(z)+tanh(z)",Sort.complex),
		Example("ComplexInverseHyperbolic","asinh(z)+acosh(z)+atanh(z)",Sort.complex),
		Example("ComplexCoshZero","ccosh(0)",Sort.complex),
		Example("Phase","cexp(2*π*𝑖*x)",Sort.complex),
		Example("PartialCongruence","log(x+0)",Sort.real_),
		Example("GuardedFunction","[x>0]*log(x+0)",Sort.real_),
		Example("MaskedUndefined","[false]*log(0)",Sort.real_),
		Example("UndefinedRealPower","(-2)^(1/2)",Sort.real_),
		Example("UndefinedComplexPower","cpow(0,ⅈ)",Sort.complex),
		Example("NaturalGuard","[p]*n",Sort.natural),
		Example("RationalGuard","[q≠0]*q⁻¹",Sort.rational),
		Example("TypedBrackets","([p]:ℕ)",Sort.natural),
		Example("ComplexBrackets","maskC(p,1)",Sort.complex),
		Example("BooleanEquality","p=true",Sort.boolean),
		Example("NaturalNonnegative","0≤n",Sort.boolean),
		Example("RealSqrtSquare","sqrt(x^2)",Sort.real_),
		Example("ComplexSqrtSquare","csqrt(z^2)",Sort.complex),
		Example("SpecialFunctions","erf(x)+erfc(x)+tgamma(x)+lgamma(x)",Sort.real_),
		Example("VariadicFunctions","min(x,1,2)+max(x,1,2)+hypot(x,1,2)",Sort.real_),
		Example("Rounding","floor(x)+ceil(x)+round(x)+sign(x)",Sort.integer)
	];
}

unittest{
	auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
	foreach(c;examples()){
		auto input=s.parse(a,c.source);
		assert(a.sort(input)==c.sort,c.name);
		auto fast=simplify(a,input),checked=simplify(a,input,Options(DensityMode.preserve,true));
		assert(!fast.exhausted&&!checked.exhausted&&fast.output==checked.output,c.name);
		auto printed=s.format(a,fast.output);
		assert(a.sort(s.parse(a,printed))==c.sort,c.name~": "~printed);
		exportLean(a,checked);
	}
	string result(string source){ return s.format(a,simplify(a,s.parse(a,source)).output); }
	assert(result("[x<2]")=="[x<2]");
	assert(result("([p]:ℕ)")=="([p]:ℕ)");
	assert(result("[q≠0]*q⁻¹")=="[q≠0]·q⁻¹");
	assert(result("2^(1/2)")=="sqrt(2)");
	assert(result("2^3^2")=="512");
	assert(result("q^0")=="rat(1,1)");
	assert(result("ccosh(0)")=="toℂ(1)");
	assert(result("clog(cexp(z))")=="clog(cexp(z))");
	assert(result("[false]*log(0)")=="0");
	assert(result("sqrt(x^2)")=="abs(x)");
	assert(result("csqrt(z^2)")!="z");
	assert(result("n*0")=="nat(0)");
	assert(result("min(x)")=="x");
	assert(result("max(x)")=="x");
	assert(result("hypot(x)")=="abs(x)");
	assert(result("hypot()")=="0");
	foreach(source;["mulR([p],x⁻¹)","mulC([p],z⁻¹)","mulQ([p],q⁻¹)"]){
		auto t=s.parse(a,source);
		assert(s.parse(a,s.format(a,t))==t,source);
	}
	assert(a.node(s.parse(a,"([false]:ℝ)*log(0)")).op==Op.mask);
	foreach(source;["n+true","z<x","x+lebesgue()","log()","cpow(z)","nat(-1)","rat(1,0)","sin(p)","toℝ(z)"])
		assertThrown(s.parse(a,source),source);
	assertThrown(a.number(Number(Rational(BigInt(1),BigInt(2))),Sort.natural));
	assertThrown(a.number(Number(-1),Sort.natural));
	assertThrown(a.call(Builtin.expR,[a.complex(0)]));
	assertThrown(a.castTo(a.real_(0),Sort.rational));
	assert(!domain(a,s.parse(a,"log(0)")).everywhere);
	assert(!domain(a,s.parse(a,"(-2)^(1/2)")).everywhere);
	assert(domain(a,s.parse(a,"exp(x)")).everywhere);
	// Defined arguments alone do not discharge a partial function's domain.
	auto d=new Derivation(a,true),x=s.parse(a,"x"),logx=s.parse(a,"log(x)");
	assert(!d.domain(x,logx).found);
	assert(d.domain(logx,x).found);
	assert(d.domain(x,s.parse(a,"exp(x)")).found);
}

@system void main(string[] args){
	enforce(args.length==2,"usage: language-tests DIRECTORY");
	mkdirRecurse(args[1]);
	foreach(c;examples()){
		auto owner=Session.open(); auto a=owner.arena; auto s=syntax();
		auto result=simplify(a,s.parse(a,c.source),Options(DensityMode.preserve,true));
		write(buildPath(args[1],c.name~".lean"),exportLean(a,result));
	}
	string all="import QSym\n";
	foreach(i;0..cast(uint)Builtin.invalid){
		auto owner=Session.open(); auto a=owner.arena;
		auto f=cast(Builtin)i,info=builtinInfo(f); Term[] operands;
		foreach(j,sort;info.args) operands~=a.variable(sort,cast(uint)j);
		auto result=simplify(a,a.call(f,operands),Options(DensityMode.preserve,true));
		all~=exportLean(a,result).replace("import QSym\n","").replace("QSym.Certificate","QSym.Builtin_"~info.code);
	}
	write(buildPath(args[1],"Builtins.lean"),all);
	writeln("Wrote language and built-in certificates.");
}
