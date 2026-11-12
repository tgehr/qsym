module higher_equality_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,expected; bool domain; }
private Case[] cases(){
	return [
		Case("Predicates","{x:ℕ|p(x)}={x:ℕ|q(x)}","({x:ℕ | p(x)}={x:ℕ | q(x)})"),
		Case("Reflexive","{x:ℕ|p(x)}={x:ℕ|p(x)}","true"),
		Case("Alpha","{x:ℕ|p(x)}={y:ℕ|p(y)}","true"),
		Case("NotReflexive","{x:ℕ|p(x)}≠{y:ℕ|p(y)}","false"),
		Case("UnknownDifferent","{x:ℕ|p(x)}≠{y:ℕ|q(y)}"),
		Case("EqualDefined","defined({x:ℕ|p(x)}={y:ℕ|q(y)})","true"),
		Case("SetVariables","S=T","(S=T)"),Case("SetVariableSelf","S=S","true"),
		Case("EmptyUniversal","{x:ℕ|false}={y:ℕ|true}","false"),
		Case("UniversalEmpty","{x:ℕ|true}={y:ℕ|false}","false"),
		Case("FunctionSets","{f:ℕ→ℕ|true}={g:ℕ→ℕ|false}","false"),
		Case("SetSets","{U:Set(ℕ)|false}={V:Set(ℕ)|true}","false"),
		Case("TypeSets","{A:Type|true}={B:Type|false}","false"),
		Case("BooleanSets","{b:𝔹|true}={c:𝔹|false}","false"),
		Case("LambdaSelf","(λ(n:ℕ).n)=(λ(m:ℕ).m)","true"),
		Case("LambdaDistinct","(λ(n:ℕ).n)=(λ(m:ℕ).m+1)","((λ(n:ℕ). n)=(λ(m:ℕ). m+1))"),
		Case("FunctionVariables","p=q","(p=q)"),Case("FunctionSelf","p=p","true"),
		Case("HigherOrderBeta","(λ(f:ℕ→𝔹).f=f)(p)","true"),
		Case("SetBeta","(λ(U:Set(ℕ)).U=U)(S)","true"),
		Case("SetPartialPredicate","{x:ℝ|1/x>0}={y:ℝ|1/y>0}","true"),
		Case("FunctionPartialBody","(λ(x:ℝ).1/x)=(λ(y:ℝ).1/y)","true"),
		Case("BottomLeft","undefined(Set(ℕ))=S","undefined(𝔹)"),
		Case("BottomRight","S=undefined(Set(ℕ))","undefined(𝔹)"),
		Case("BottomSelf","undefined(Set(ℕ))=undefined(Set(ℕ))","undefined(𝔹)"),
		Case("BottomDifferent","undefined(Set(ℕ))≠S","undefined(𝔹)"),
		Case("BottomDomain","undefined(Set(ℕ))=S","false",true),
		Case("GuardedSelf","guard(b,S)=guard(b,S)"),
		Case("GuardedDomain","guard(b,S)=T","b",true),
		Case("FunctionBottom","undefined(ℕ→𝔹)=p","undefined(𝔹)"),
		Case("TypeAlias","Real=ℝ","true"),
		Case("AssumedScalar","(λ(U:Set(ℕ)).defined(U=U))(S)","true")
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s; s.declare("p:ℕ→𝔹,q:ℕ→𝔹,S:Set(ℕ),T:Set(ℕ),b:𝔹");
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true),c.domain),output=s.format(a,r);
		enforce(!r.exhausted,c.name~" exhausted"); if(c.expected.length) enforce(output==c.expected,c.name~": "~output);
		if(!r.scalarOnly) enforce(r.bindings.normalize(r.reduction.output,4096,true).output==r.reduction.output,c.name~" not normalized");
		auto again=s.run(a,output); enforce(s.format(a,again)==output,c.name~" round trip: "~output~" -> "~s.format(a,again));
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
}
unittest{
	run(); auto owner=Session.open(),a=owner.arena; FunctionSyntax s; s.declare("p:ℕ→𝔹,S:Set(ℕ)");
	foreach(source;["S=p","S=Real","p=0","{n:ℕ|true}={x:ℝ|true}"])
		assertThrown(s.run(a,source));
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/higher-equality"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," higher-order equality certificates"); return 0;
}
