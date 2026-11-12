module functional_tests;
import qsym;
import qsym.binding;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,expected,variables; bool domain; }
private Case[] cases(){
	return [
		Case("Curried","(λ(a:ℕ). λ(b:ℕ). a+b)(1)(2)","3"),
		Case("Ascii","(lambda(a:Nat).lambda(b:Nat).a+b)(1)(2)","3"),
		Case("Shadow","(λ(n:ℕ). λ(n:ℕ). n)(1)(2)","2"),
		Case("Capture","(λ(y:ℝ). λ(x:ℝ). y+x)(x)(2)","x+2"),
		Case("HigherOrder","(λ(f:ℕ→ℕ). f(2))(λ(n:ℕ). n+1)","3"),
		Case("ArrowAscription","((λ(n:ℕ). n):ℕ→ℝ)(2)","2"),
		Case("BoolArgument","(λ(p:𝔹). if p then 1 else 2)(false)","2"),
		Case("DecimalBody","(λ(x:ℝ).2.5)(0)","5/2"),
		Case("LeadingDecimal","(λ(x:ℝ). .5)(0)","1/2"),
		Case("PartialApplication","(λ(a:ℕ). λ(b:ℕ). a+b)(1)"),
		Case("FunctionBody","λ(x:ℝ). x/x"),
		Case("GlobalBodyDomain","λ(x:ℝ). y/y","","y:ℝ"),
		Case("FunctionValueDefined","defined(λ(x:ℝ). 1/x)","true"),
		Case("LambdaDomain","λ(x:ℝ). 1/x","","",true),
		Case("LambdaDomainZero","0∈domain(λ(x:ℝ). 1/x)","false"),
		Case("LambdaDomainOne","1∈domain(λ(x:ℝ). 1/x)","true"),
		Case("QuotientDomainZero","0∈domain(λ(x:ℝ). x/x)","false"),
		Case("QuotientDomainOne","1∈domain(λ(x:ℝ). x/x)","true"),
		Case("UndefinedArgument","(λ(x:ℝ).0)(1/0)","guard(false,0)"),
		Case("UndefinedArgumentDomain","(λ(x:ℝ).0)(1/0)","false","",true),
		Case("MaskedArgument","(λ(x:ℝ).0)([false]*(1/0))","0"),
		Case("NaturalPartiality","(λ(n:ℕ). n sub 1)(0)","false","",true),
		Case("NaturalSubtraction","(λ(n:ℕ). n sub 1)(2)","1"),
		Case("Subset","{n:ℕ | n<3}"),
		Case("SubsetInside","2∈{n:ℕ | n<3}","true"),
		Case("SubsetOutside","3∈{n:ℕ | n<3}","false"),
		Case("SubsetPartialPredicate","0∈{x:ℝ | 1/x>0}","false"),
		Case("SubsetUndefinedElement","(1/0)∈{x:ℝ | true}","false","",true),
		Case("SubsetArgument","(λ(S:Set(ℕ)).2∈S)({i:ℕ | i<3})","true"),
		Case("SubsetOfFunctions","(λ(n:ℕ).n)∈{f:ℕ→ℕ | f(0)=0}","true"),
		Case("RestrictedInside","(λ(x:ℝ | x>0).log(x))(1)","0"),
		Case("RestrictedOutside","(λ(x:ℝ | x>0).log(x))(-1)","false","",true),
		Case("RestrictedLambda","λ(x:ℝ | x>0).log(x)"),
		Case("CurriedDomain","(λ(a:ℕ).λ(b:ℕ).a sub b)(3)","","",true),
		Case("CurriedDomainInside","2∈domain((λ(a:ℕ).λ(b:ℕ).a sub b)(3))","true"),
		Case("CurriedDomainOutside","4∈domain((λ(a:ℕ).λ(b:ℕ).a sub b)(3))","false"),
		Case("SymbolicFunction","f(1)","","f:ℝ→ℝ"),
		Case("SymbolicDomain","domain(f)","domain(f)","f:ℝ→ℝ"),
		Case("SymbolicApplicationDomain","f(1)","","f:ℝ→ℝ",true),
		Case("SymbolicSubset","1∈S","","S:Set(ℝ)"),
		Case("SymbolicSubsetBeta","0∈{n:ℕ | predicate(n)}","","predicate:ℕ→𝔹"),
		Case("CaptureSubset","(λ(n:ℕ).{m:ℕ | predicate(n)(m)})(1)","","predicate:ℕ→ℕ→𝔹"),
		Case("DefinedFunctionVariable","defined(f)","true","f:ℕ→ℕ"),
		Case("DefinedDomain","defined(domain(f))","true","f:ℕ→ℕ"),
		Case("ComplexDomainZero","0∈domain(λ(z:ℂ).log(z))","false"),
		Case("ComplexDomainOne","1∈domain(λ(z:ℂ).log(z))","true")
	];
}
private string[] run(string directory=""){
	string[] names;
	foreach(c;cases()){
		auto session=Session.open(),a=session.arena; FunctionSyntax s;
		if(c.variables.length) s.declare(c.variables);
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true),c.domain),output=s.format(a,r);
		enforce(!r.exhausted,c.name~" exhausted");
		if(c.expected.length) enforce(output==c.expected,c.name~": "~output);
		if(!r.scalarOnly){
			auto normalized=r.bindings.normalize(r.reduction.output,4096,true);
			enforce(normalized.output==r.reduction.output,c.name~" not a normal form");
			enforce(r.bindings.type(r.reduction.input)==r.bindings.type(r.reduction.output),c.name~" changed type");
		}
		auto again=s.run(a,output,[],Options(DensityMode.preserve,true));
		enforce(s.format(a,again)==output,c.name~" round trip: "~output~" -> "~s.format(a,again));
		auto code=s.exportCertificate(a,r);
		if(directory.length) write(buildPath(directory,c.name~".lean"),code);
		names~=c.name;
	}
	return names;
}
unittest{
	run(); auto session=Session.open(),a=session.arena; FunctionSyntax s;
	foreach(source;["λ(x:ℕ).missing(0)","(λ(x:ℕ).x)(true)","0∈{p:𝔹 | p}","λ(x:ℕ).x(0)","domain(2)",
		"{x:ℕ | x+1}","λ(x:ℕ).(λ(x:ℕ).x)(0,1)","λ(exp:ℝ).exp", "((λ(x:ℕ).x):ℝ→ℝ)"])
		assertThrown(s.run(a,source));
	assertThrown(s.declare("f:ℕ→ℕ,f:ℝ→ℝ"));
	assertThrown(s.declare("domain:ℕ→ℕ"));
	s.declare("f:ℕ→ℕ,S:Set(ℝ)");
	assertThrown(s.declare("f:ℕ"));
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/functional"; mkdirRecurse(directory);
	writeln(run(directory).length," functional certificates"); return 0;
}
