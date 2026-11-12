module refinement_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,expected; bool domain; }
private Case[] cases(){
	return [
		Case("ZeroQuotient","λ(t:ℝ).0/(2*t-1)","λ(x:{x1:ℝ | x1≠1/2}). (0:Real)"),
		Case("ExplicitRefinement","λ(t:{t:ℝ|t≠1/2}).0/(2*t-1)","λ(x:{x1:ℝ | x1≠1/2}). (0:Real)"),
		Case("RenamedRestriction","λ(t:{u:ℝ|u≠1/2}).0/(2*t-1)","λ(x:{x1:ℝ | x1≠1/2}). (0:Real)"),
		Case("ZeroQuotientDomain","domain(λ(t:ℝ).0/(2*t-1))","{x:ℝ | x≠1/2}"),
		Case("CommandDomain","λ(t:ℝ).0/(2*t-1)","{x:ℝ | x≠1/2}",true),
		Case("ExcludedPoint","(λ(t:ℝ).0/(2*t-1))(1/2)","false",true),
		Case("IncludedPoint","(λ(t:ℝ).0/(2*t-1))(1)","0"),
		Case("RestrictedOutside","(λ(t:{u:ℝ|u≠1/2}).0)(1/2)","false",true),
		Case("RestrictedInside","(λ(t:{u:ℝ|u≠1/2}).0)(1)","0"),
		Case("SimplePointwise","λ(x:ℝ).x*0","λ(x:ℝ). (0:Real)"),
		Case("DomainPartial","domain(λ(x:ℝ).1/x)","{x:ℝ | x≠0}"),
		Case("BooleanPointwise","λ(p:𝔹).p∧true","λ(x:𝔹). x"),
		Case("NaturalPointwise","λ(n:ℕ).n+0","λ(x:ℕ). x"),
		Case("ComplexPointwise","λ(z:ℂ).z/z","λ(x:{x1:ℂ | x1≠0}). (1:Complex)"),
		Case("FreeVariable","λ(t:ℝ).x/(2*t-1)"),
		Case("FreeParameterDomain","domain(λ(t:ℝ).x/(2*t-1))","{x1:ℝ | x1≠1/2}"),
		Case("CurriedRefinement","λ(a:ℝ).λ(t:{u:ℝ|u≠a}).0/(t-a)"),
		Case("CaptureRefinement","(λ(a:ℝ).λ(t:{u:ℝ|u≠a}).0/(t-a))(1/2)","λ(x:{x1:ℝ | x1≠1/2}). (0:Real)"),
		Case("NestedRefinement","λ(t:{u:{v:ℝ|v≠0}|u≠1}).t/t","λ(x:{x1:ℝ | x1≠0∧x1≠1}). (1:Real)"),
		Case("PartialPredicate","domain(λ(t:{u:ℝ|1/u>0}).t)","{x:ℝ | 0<x}"),
		Case("BoolDomain","domain(λ(p:𝔹).p∧true)","{x:𝔹 | true}"),
		Case("NaturalIdentityDomain","domain(λ(x:ℕ).x)","{x:ℕ | true}"),
		Case("IntegerIdentityDomain","domain(λ(x:ℤ).x)","{x:ℤ | true}"),
		Case("RationalIdentityDomain","domain(λ(x:ℚ).x)","{x:ℚ | true}"),
		Case("RealIdentityDomain","domain(λ(x:ℝ).x)","{x:ℝ | true}"),
		Case("ComplexIdentityDomain","domain(λ(x:ℂ).x)","{x:ℂ | true}"),
		Case("BooleanIdentityDomain","domain(λ(x:𝔹).x)","{x:𝔹 | true}"),
		Case("SetRefinement","{t:{u:ℝ|u≠0}|t<1}","{x:ℝ | x≠0∧x<1}"),
		Case("EmptyRestriction","domain(λ(t:{u:ℝ|false}).t)","{x:ℝ | false}"),
		Case("UndefinedPredicate","(λ(t:{u:ℝ|1/u>0}).0)(0)","false",true),
		Case("UnknownRestriction","λ(t:{u:ℝ|predicate(u)}).t"),
		Case("BinderShadow","(λ(t:ℝ).(λ(t:{u:ℝ|u≠t}).t)(1))(0)","1")
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
		s.declare("predicate:ℝ→𝔹");
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true),c.domain),output=s.format(a,r);
		enforce(!r.exhausted,c.name~" exhausted");
		if(c.expected.length) enforce(output==c.expected,c.name~": "~output);
		if(!r.scalarOnly){
			auto again=r.bindings.normalize(r.reduction.output,4096,true);
			enforce(again.output==r.reduction.output,c.name~" not a normal form");
			enforce(r.bindings.type(r.reduction.input)==r.bindings.type(r.reduction.output),c.name~" changed type");
		}
		auto again=s.run(a,output); enforce(s.format(a,again)==output,c.name~" round trip: "~s.format(a,again));
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
}
unittest{
	run(); auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
	foreach(source;["λ(t:{u:ℝ|1}).t","λ(t:{u:ℝ|u}).t","λ(t:{exp:ℝ|true}).t"])
		assertThrown(s.run(a,source));
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/refinements"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," refinement certificates"); return 0;
}
