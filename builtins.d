module qsym.builtins;
public import qsym.types:Sort;
import std.exception:enforce;
@safe:

enum Builtin{
	castNZ,castZQ,castQR,castRC,addN,mulN,
	ltN,leN,nonzeroN,addZ,mulZ,ltZ,
	leZ,nonzeroZ,addQ,mulQ,ltQ,leQ,
	nonzeroQ,invQ,eqB,powNN,powZN,powQN,
	powRN,powCN,powQZ,powRZ,powCZ,powerR,
	powerC,sqrtR,sqrtC,cbrtR,expR,expC,
	sinR,sinC,cosR,cosC,sinhR,sinhC,
	coshR,coshC,tanhR,tanhC,logR,logC,
	tanR,tanC,asinR,acosR,atanR,asinC,
	acosC,atanC,asinhR,acoshR,atanhR,asinhC,
	acoshC,atanhC,exp2R,log2R,log10R,makeC,
	reC,imC,absC,argC,cisR,expiC,
	polarC,atan2R,floorR,ceilR,roundR,signR,
	isIntR,minR,maxR,hypotR,gcdZ,makeQ,
	numQ,denQ,erfR,erfcR,gammaR,lgammaR,
	gammaC,pi,e,subN,floorN,invalid,
}
struct BuiltinInfo{ string code,name; Sort result; immutable(Sort)[] args; bool total; }
private immutable BuiltinInfo[] definitions=[
	BuiltinInfo("castNZ","toℤ",Sort.integer,[Sort.natural],true),
	BuiltinInfo("castZQ","toℚ",Sort.rational,[Sort.integer],true),
	BuiltinInfo("castQR","toℝ",Sort.real_,[Sort.rational],true),
	BuiltinInfo("castRC","toℂ",Sort.complex,[Sort.real_],true),
	BuiltinInfo("addN","addN",Sort.natural,[Sort.natural,Sort.natural],true),
	BuiltinInfo("mulN","mulN",Sort.natural,[Sort.natural,Sort.natural],true),
	BuiltinInfo("ltN","ltN",Sort.boolean,[Sort.natural,Sort.natural],true),
	BuiltinInfo("leN","leN",Sort.boolean,[Sort.natural,Sort.natural],true),
	BuiltinInfo("nonzeroN","nonzeroN",Sort.boolean,[Sort.natural],true),
	BuiltinInfo("addZ","addZ",Sort.integer,[Sort.integer,Sort.integer],true),
	BuiltinInfo("mulZ","mulZ",Sort.integer,[Sort.integer,Sort.integer],true),
	BuiltinInfo("ltZ","ltZ",Sort.boolean,[Sort.integer,Sort.integer],true),
	BuiltinInfo("leZ","leZ",Sort.boolean,[Sort.integer,Sort.integer],true),
	BuiltinInfo("nonzeroZ","nonzeroZ",Sort.boolean,[Sort.integer],true),
	BuiltinInfo("addQ","addQ",Sort.rational,[Sort.rational,Sort.rational],true),
	BuiltinInfo("mulQ","mulQ",Sort.rational,[Sort.rational,Sort.rational],true),
	BuiltinInfo("ltQ","ltQ",Sort.boolean,[Sort.rational,Sort.rational],true),
	BuiltinInfo("leQ","leQ",Sort.boolean,[Sort.rational,Sort.rational],true),
	BuiltinInfo("nonzeroQ","nonzeroQ",Sort.boolean,[Sort.rational],true),
	BuiltinInfo("invQ","invQ",Sort.rational,[Sort.rational],false),
	BuiltinInfo("eqB","eqB",Sort.boolean,[Sort.boolean,Sort.boolean],true),
	BuiltinInfo("powNN","powNN",Sort.natural,[Sort.natural,Sort.natural],true),
	BuiltinInfo("powZN","powZN",Sort.integer,[Sort.integer,Sort.natural],true),
	BuiltinInfo("powQN","powQN",Sort.rational,[Sort.rational,Sort.natural],true),
	BuiltinInfo("powRN","powRN",Sort.real_,[Sort.real_,Sort.natural],true),
	BuiltinInfo("powCN","powCN",Sort.complex,[Sort.complex,Sort.natural],true),
	BuiltinInfo("powQZ","powQZ",Sort.rational,[Sort.rational,Sort.integer],false),
	BuiltinInfo("powRZ","powRZ",Sort.real_,[Sort.real_,Sort.integer],false),
	BuiltinInfo("powCZ","powCZ",Sort.complex,[Sort.complex,Sort.integer],false),
	BuiltinInfo("powerR","pow",Sort.real_,[Sort.real_,Sort.real_],false),
	BuiltinInfo("powerC","cpow",Sort.complex,[Sort.complex,Sort.complex],false),
	BuiltinInfo("sqrtR","sqrt",Sort.real_,[Sort.real_],false),
	BuiltinInfo("sqrtC","csqrt",Sort.complex,[Sort.complex],true),
	BuiltinInfo("cbrtR","cbrt",Sort.real_,[Sort.real_],true),
	BuiltinInfo("expR","exp",Sort.real_,[Sort.real_],true),
	BuiltinInfo("expC","cexp",Sort.complex,[Sort.complex],true),
	BuiltinInfo("sinR","sin",Sort.real_,[Sort.real_],true),
	BuiltinInfo("sinC","csin",Sort.complex,[Sort.complex],true),
	BuiltinInfo("cosR","cos",Sort.real_,[Sort.real_],true),
	BuiltinInfo("cosC","ccos",Sort.complex,[Sort.complex],true),
	BuiltinInfo("sinhR","sinh",Sort.real_,[Sort.real_],true),
	BuiltinInfo("sinhC","csinh",Sort.complex,[Sort.complex],true),
	BuiltinInfo("coshR","cosh",Sort.real_,[Sort.real_],true),
	BuiltinInfo("coshC","ccosh",Sort.complex,[Sort.complex],true),
	BuiltinInfo("tanhR","tanh",Sort.real_,[Sort.real_],true),
	BuiltinInfo("tanhC","ctanh",Sort.complex,[Sort.complex],false),
	BuiltinInfo("logR","log",Sort.real_,[Sort.real_],false),
	BuiltinInfo("logC","clog",Sort.complex,[Sort.complex],false),
	BuiltinInfo("tanR","tan",Sort.real_,[Sort.real_],false),
	BuiltinInfo("tanC","ctan",Sort.complex,[Sort.complex],false),
	BuiltinInfo("asinR","asin",Sort.real_,[Sort.real_],false),
	BuiltinInfo("acosR","acos",Sort.real_,[Sort.real_],false),
	BuiltinInfo("atanR","atan",Sort.real_,[Sort.real_],true),
	BuiltinInfo("asinC","casin",Sort.complex,[Sort.complex],true),
	BuiltinInfo("acosC","cacos",Sort.complex,[Sort.complex],true),
	BuiltinInfo("atanC","catan",Sort.complex,[Sort.complex],false),
	BuiltinInfo("asinhR","asinh",Sort.real_,[Sort.real_],true),
	BuiltinInfo("acoshR","acosh",Sort.real_,[Sort.real_],false),
	BuiltinInfo("atanhR","atanh",Sort.real_,[Sort.real_],false),
	BuiltinInfo("asinhC","casinh",Sort.complex,[Sort.complex],true),
	BuiltinInfo("acoshC","cacosh",Sort.complex,[Sort.complex],true),
	BuiltinInfo("atanhC","catanh",Sort.complex,[Sort.complex],false),
	BuiltinInfo("exp2R","exp2",Sort.real_,[Sort.real_],true),
	BuiltinInfo("log2R","log2",Sort.real_,[Sort.real_],false),
	BuiltinInfo("log10R","log10",Sort.real_,[Sort.real_],false),
	BuiltinInfo("makeC","cfromri",Sort.complex,[Sort.real_,Sort.real_],true),
	BuiltinInfo("reC","creal",Sort.real_,[Sort.complex],true),
	BuiltinInfo("imC","cimag",Sort.real_,[Sort.complex],true),
	BuiltinInfo("absC","cabs",Sort.real_,[Sort.complex],true),
	BuiltinInfo("argC","carg",Sort.real_,[Sort.complex],false),
	BuiltinInfo("cisR","cis",Sort.complex,[Sort.real_],true),
	BuiltinInfo("expiC","cexpi",Sort.complex,[Sort.complex],true),
	BuiltinInfo("polarC","cfromrt",Sort.complex,[Sort.real_,Sort.real_],true),
	BuiltinInfo("atan2R","atan2",Sort.real_,[Sort.real_,Sort.real_],false),
	BuiltinInfo("floorR","floor",Sort.integer,[Sort.real_],true),
	BuiltinInfo("ceilR","ceil",Sort.integer,[Sort.real_],true),
	BuiltinInfo("roundR","round",Sort.integer,[Sort.real_],true),
	BuiltinInfo("signR","sign",Sort.integer,[Sort.real_],true),
	BuiltinInfo("isIntR","inZ",Sort.boolean,[Sort.real_],true),
	BuiltinInfo("minR","min",Sort.real_,[Sort.real_,Sort.real_],true),
	BuiltinInfo("maxR","max",Sort.real_,[Sort.real_,Sort.real_],true),
	BuiltinInfo("hypotR","hypot",Sort.real_,[Sort.real_,Sort.real_],true),
	BuiltinInfo("gcdZ","gcd",Sort.natural,[Sort.integer,Sort.integer],true),
	BuiltinInfo("makeQ","qfromnd",Sort.rational,[Sort.integer,Sort.integer],false),
	BuiltinInfo("numQ","numerator",Sort.integer,[Sort.rational],true),
	BuiltinInfo("denQ","denominator",Sort.natural,[Sort.rational],true),
	BuiltinInfo("erfR","erf",Sort.real_,[Sort.real_],true),
	BuiltinInfo("erfcR","erfc",Sort.real_,[Sort.real_],true),
	BuiltinInfo("gammaR","tgamma",Sort.real_,[Sort.real_],false),
	BuiltinInfo("lgammaR","lgamma",Sort.real_,[Sort.real_],false),
	BuiltinInfo("gammaC","cgamma",Sort.complex,[Sort.complex],false),
	BuiltinInfo("pi","pi",Sort.real_,[],true),
	BuiltinInfo("e","e",Sort.real_,[],true),
	BuiltinInfo("subN","sub",Sort.natural,[Sort.natural,Sort.natural],false),
	BuiltinInfo("floorN","floorN",Sort.natural,[Sort.real_],true),
];
const(BuiltinInfo) builtinInfo(Builtin f){
	enforce(cast(uint)f<cast(uint)Builtin.invalid,"invalid built-in function"); return definitions[f];
}
Builtin builtin(string code){
	foreach(i,d;definitions) if(d.code==code) return cast(Builtin)i;
	return Builtin.invalid;
}
bool numeric(Sort s){ return s==Sort.natural||s==Sort.integer||s==Sort.rational||s==Sort.real_||s==Sort.complex; }
int rank(Sort s){
	foreach(i,t;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(t==s) return cast(int)i;
	return -1;
}
bool promotes(Sort from,Sort to){ return from==to||numeric(from)&&numeric(to)&&rank(from)<rank(to); }
string suffix(Sort s){
	switch(s){
		case Sort.natural:return "N";
		case Sort.integer:return "Z";
		case Sort.rational:return "Q";
		case Sort.real_:return "R";
		case Sort.complex:return "C";
		case Sort.boolean:return "B";
		default:throw new Exception("scalar sort expected");
	}
}
bool builtinName(Builtin f,string name){
	auto d=builtinInfo(f);
	if(name==d.code||name==d.name) return true;
	if(name=="π") return f==Builtin.pi;
	if(name=="re"||name=="realPart") return f==Builtin.reC;
	if(name=="im"||name=="imagPart") return f==Builtin.imC;
	if(name=="arg") return f==Builtin.argC;
	if(name=="expi") return f==Builtin.cisR;
	if(name=="inℤ") return f==Builtin.isIntR;
	if(name=="log₂") return f==Builtin.log2R;
	if(name=="abs") return f==Builtin.absC;
	if(d.name.length>1&&d.name[0]=='c'&&d.name[1..$]==name) return true;
	return false;
}

unittest{
	import std.conv:to;
	assert(definitions.length==Builtin.invalid);
	foreach(i,d;definitions) assert(d.code==to!string(cast(Builtin)i));
}
