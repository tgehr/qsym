module distribution_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,type,expected; }
private Case[] cases(){ return [
	Case("Dirac","δ(2)","Distribution(ℕ)"),
	Case("NaturalDirac","(δ(2):Distribution(ℕ))","Distribution(ℕ)"),
	Case("FunctionDirac","δ(λ(n:ℕ).n)","Distribution(ℕ→ℕ)"),
	Case("TypeDirac","δ(Distribution(ℝ))","Distribution(Type)"),
	Case("NestedDirac","δ(δ(2))","Distribution(Distribution(ℕ))"),
	Case("SetDirac","δ({x:ℝ|x≠0})","Distribution(Set(ℝ))"),
	Case("DistributionIdentity","λ(d:Distribution(ℝ)).Λ(x:ℝ).d[x]","Distribution(ℝ)→Distribution(ℝ)"),
	Case("DistributionFunction","λ(p:Distribution(ℝ)).δ(p)","Distribution(ℝ)→Distribution(Distribution(ℝ))"),
	Case("Lebesgue","Λ(x:ℝ).λ[x]","Distribution(ℝ)"),
	Case("UntypedLebesgue","Λx.λ[x]","Distribution(ℝ)"),
	Case("UntypedIntegral","∫dx x*δ(2)[x]","ℝ"),
	Case("Marginal","Λ(x:ℝ).∫(y:ℝ).δ(y)[x]*λ[y]","Distribution(ℝ)"),
	Case("BarePuncture","[x≠0]·λ[x]","Distribution(ℝ)"),
	Case("BareLebesgue","λ[x]","Distribution(ℝ)"),
	Case("Interval","∫dx [-1≤x≤1]·λ[x]","ℝ"),
	Case("PuncturedInterval","∫dx [x≠0]·λ[x]·[-1≤x≤1]","ℝ"),
	Case("UnboundedPuncture","∫dx [x≠0]·λ[x]","ℝ"),
	Case("ZeroIntegral","∫dx 0","ℝ","0"),
	Case("StrictInterval","∫dx [-1<x<1]·λ[x]","ℝ","2"),
	Case("EmptyInterval","∫dx [2≤x≤1]·λ[x]","ℝ","0"),
	Case("SingletonIntegral","∫dx [x=0]·λ[x]","ℝ","0"),
	Case("ShiftedPuncture","∫dx [2*x≠1]·[-1≤x≤1]·λ[x]","ℝ","2"),
	Case("IntersectedIntervals","∫dx [0≤x≤3]·λ[x]·[-1≤x≤1]","ℝ","1"),
	Case("SignedInterval","∫dx (-3)*[-1≤x≤1]·λ[x]","ℝ","-6"),
	Case("LinearInterval","∫dx [0≤2*x+1]·[3*x≤6]·λ[x]","ℝ","5/2"),
	Case("MixedIntegral","∫dx δ(0)[x]+[-1≤x≤1]·λ[x]","ℝ","3"),
	Case("BoundRectangle","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).weightD(λ(y:ℝ).[0≤y≤2],lebesgueD())))","ℝ","2"),
	Case("SignedRectangle","massD(bindD(weightD(λ(x:ℝ).(-3)*[0≤x≤1],lebesgueD()),λ(x:ℝ).weightD(λ(y:ℝ).[0≤y≤2],lebesgueD())))","ℝ","-6"),
	Case("IntegralRectangle","massD(integralD(λ(x:ℝ).scaleD([0≤x≤1],weightD(λ(y:ℝ).[0≤y≤2],lebesgueD()))))","ℝ","2"),
	Case("ParametricWeight","λ(a:ℝ).massD(weightD(λ(y:ℝ).a,weightD(λ(y:ℝ).[0≤y≤2],lebesgueD())))","ℝ→ℝ"),
	Case("ParametricPartialWeight","λ(a:ℝ).massD(weightD(λ(y:ℝ).1/a,weightD(λ(y:ℝ).[0≤y≤2],lebesgueD())))","ℝ→ℝ"),
	Case("ParametricNestedWeights","λ(a:ℝ).λ(b:ℝ).massD(weightD(λ(y:ℝ).a,weightD(λ(y:ℝ).[0≤y≤2],weightD(λ(y:ℝ).b,lebesgueD()))))","ℝ→ℝ→ℝ"),
	Case("WeightedRows","massD(integralD(λ(x:ℝ).weightD(λ(y:ℝ).[0≤x≤1],weightD(λ(y:ℝ).[0≤y≤2],lebesgueD()))))","ℝ","2"),
	Case("TripleBind","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).bindD(weightD(λ(y:ℝ).[0≤y≤2],lebesgueD()),λ(y:ℝ).weightD(λ(z:ℝ).[0≤z≤3],lebesgueD()))))","ℝ","6"),
	Case("BoundFunction","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).δ(λ(n:ℕ).n)))","ℝ","1"),
	Case("BoundDistribution","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).δ(δ(x))))","ℝ","1"),
	Case("BoundType","massD(bindD(weightD(λ(x:ℝ).[0≤x≤1],lebesgueD()),λ(x:ℝ).δ(Distribution(ℝ))))","ℝ","1"),
	Case("UnboundedParameter","λ(a:ℝ).massD(weightD(λ(y:ℝ).a,lebesgueD()))","ℝ→ℝ"),
	Case("ZeroInfiniteRow","massD(bindD(weightD(λ(x:ℝ).0,lebesgueD()),λ(x:ℝ).lebesgueD()))","ℝ"),
	Case("NestedMaskedRectangle","∫dx ∫dy [0≤x≤1]*[0≤y≤2]*λ[y]*λ[x]","ℝ","2"),
	Case("ReversedMaskedRectangle","∫dx ∫dy [0≤y≤2]*[0≤x≤1]*λ[y]*λ[x]","ℝ","2"),
	Case("SignedMaskedRectangle","∫dx ∫dy (-3)*[0≤x≤1]*[0≤y≤2]*λ[y]*λ[x]","ℝ","-6"),
	Case("PuncturedMaskedRectangle","∫dx ∫dy [x≠0]*[-1≤x≤1]*[0≤y≤2]*λ[y]*λ[x]","ℝ","4"),
	Case("MaskedParameter","λ(a:ℝ).∫dx [0≤x≤2]*a*λ[x]","ℝ→ℝ"),
	Case("MaskedPartialParameter","λ(a:ℝ).∫dx [0≤x≤2]*(1/a)*λ[x]","ℝ→ℝ"),
	Case("OuterParameterMask","λ(p:𝔹).∫dx [p]*[0≤x≤2]*λ[x]","𝔹→ℝ"),
	Case("InnerParameterMask","λ(p:𝔹).∫dx [0≤x≤2]*[p]*λ[x]","𝔹→ℝ"),
	Case("MaskedPartialBranch","λ(p:𝔹).λ(a:ℝ).∫dx [p]*[0≤x≤2]*(1/a)*λ[x]","𝔹→ℝ→ℝ"),
	Case("MixedParameterMasks","λ(p:𝔹).λ(q:𝔹).∫dx [p]*[0≤x≤2]*[q]*λ[x]","𝔹→𝔹→ℝ"),
	Case("NullPointParameter","λ(a:ℝ).∫dx [x=0]*(1/a)*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("ClosedSingletonParameter","λ(a:ℝ).∫dx [0≤x≤0]*(1/a)*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("OpenEmptyParameter","λ(a:ℝ).∫dx [0<x<0]*(1/a)*λ[x]","ℝ→ℝ","λ(a:ℝ). (0:ℝ)"),
	Case("EmptyMaskedParameter","λ(a:ℝ).∫dx [x<0]*[1<x]*(1/a)*λ[x]","ℝ→ℝ","λ(a:ℝ). (0:ℝ)"),
	Case("DisjointPartialWeights","λ(a:ℝ).massD(weightD(λ(x:ℝ).[x=0]*(1/a),weightD(λ(x:ℝ).[x=1],lebesgueD())))","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("DisjointOpenSupports","λ(a:ℝ).massD(weightD(λ(x:ℝ).[0<x<1]*(1/a),weightD(λ(x:ℝ).[2<x<3],lebesgueD())))","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("DisjointTwoParameters","λ(a:ℝ).λ(b:ℝ).massD(weightD(λ(x:ℝ).[x=0]*(1/a),weightD(λ(x:ℝ).[x=1]*(1/b),lebesgueD())))","ℝ→ℝ→ℝ"),
	Case("MaskedNullPoint","λ(p:𝔹).λ(a:ℝ).∫dx [p]*[x=0]*(1/a)*λ[x]","𝔹→ℝ→ℝ"),
	Case("ShiftedNullPoint","λ(a:ℝ).∫dx [2*x=1]*(1/a)*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (0:ℝ)"),
	Case("NullPointDensity","λ(a:ℝ).densityAtD(weightD(λ(x:ℝ).[x=0]*a,lebesgueD()),0)","ℝ→ℝ"),
	Case("StepSum","∫dx ([0≤x≤1]+2*[1≤x≤3])*λ[x]","ℝ","5"),
	Case("StepUnion","∫dx [(0<x<1)∨(2<x<3)]*λ[x]","ℝ","2"),
	Case("StepOverlap","∫dx ([0≤x≤2]+[1≤x≤3])*λ[x]","ℝ","4"),
	Case("StepSigned","∫dx ((-3)*[0<x<1]+2*[1<x<2])*λ[x]","ℝ","-1"),
	Case("StepPartialParameter","λ(a:ℝ).∫dx ([0≤x≤1]*a+[2≤x≤3]*(1/a))*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). a+a⁻¹"),
	Case("StepTwoParameters","λ(a:ℝ).λ(b:ℝ).∫dx ([0<x<1]*a+[1<x<2]*b)*λ[x]","ℝ→ℝ→ℝ"),
	Case("StepBoundaryParameter","λ(a:ℝ).∫dx ([0<x<1]+[1<x<2]+[x=1]*(1/a))*λ[x]","ℝ→ℝ","λ(a:{a:ℝ | a≠0}). (2:ℝ)"),
	Case("StepProduct","∫dx ([0<x<1]+[1<x<3])*λ[x]*[0≤x≤2]","ℝ","2"),
	Case("StepUnbounded","∫dx [x<0∨1<x]*λ[x]","ℝ"),
	Case("StepNonconstant","∫dx x*[0≤x≤1]*λ[x]","ℝ"),
	Case("Puncture","Λ(x:ℝ).[x≠0]*λ[x]","Distribution(ℝ)"),
	Case("WeightedDirac","Λ(x:ℝ).x*δ(2)[x]","Distribution(ℝ)"),
	Case("Mixture","Λ(x:ℝ).δ(0)[x]+[x≠0]*λ[x]","Distribution(ℝ)"),
	Case("Signed","Λ(x:ℝ).-δ(0)[x]","Distribution(ℝ)"),
	Case("Integral","∫(x:ℝ).x*δ(2)[x]","ℝ"),
	Case("DensityRecovery","([x≠0]*λ[x])//λ[x]","ℝ"),
	Case("DensityOne","λ[x]//λ[x]","ℝ","1"),
	Case("Capture","(λ(a:ℝ).Λ(x:ℝ).(a+x)*λ[x])(2)","Distribution(ℝ)"),
	Case("Shadow","λ(x:ℝ).Λ(x:ℝ).x*λ[x]","ℝ→Distribution(ℝ)"),
	Case("FormalIntegral","integralD(λ(x:ℝ).δ(x))","Distribution(ℝ)"),
	Case("RecursiveAtom","(μ(f:ℕ→ℝ).λ(n:ℕ).if n=0 then 0 else massD(δ(f(n sub 1))))(2)","ℝ"),
	Case("RecursiveConstant","μ(f:ℕ→ℝ).λ(n:ℕ).massD(δ(1))","ℕ→ℝ")
]; }

private void run(string directory){
	foreach(c;cases()){
		scope(failure) writeln("Failed distribution case: ",c.name);
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
		enforce(s.inspectType(a,c.source)==c.type,c.name~" type: "~s.inspectType(a,c.source));
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true));
		enforce(!r.exhausted,c.name~" exhausted");
		auto text=s.format(a,r);
		if(c.expected.length) enforce(text==c.expected,c.name~": "~text);
		if(c.name=="DensityRecovery") enforce(text=="[x≠0]",c.name~": "~text);
		if(c.name=="Interval"||c.name=="PuncturedInterval") enforce(text=="2",c.name~": "~text);
		if(c.name=="UnboundedPuncture") enforce(text=="∫dx λ[x]",c.name~": "~text);
		if(c.name=="Integral") enforce(text=="2",c.name~": "~text);
		if(c.name=="RecursiveAtom") enforce(text=="1",c.name~": "~text);
		auto again=s.run(a,text,[],Options(DensityMode.preserve,true));
		enforce(s.format(a,again)==text,c.name~" round trip: "~text);
		auto certificate=s.exportCertificate(a,r);
		// These existing rules now cross a proved bridge to the reference-aware
		// model. Keep their proof dependencies from silently reverting to the
		// presentation-only lemmas while the remaining backend is migrated.
		import std.string:indexOf;
		if(c.name=="DensityRecovery") enforce(certificate.indexOf("Distribution.model_density_weight_lebesgueValue")>=0);
		if(c.name=="DensityOne") enforce(certificate.indexOf("Distribution.model_density_lebesgueValue")>=0);
		if(c.name=="Integral") enforce(certificate.indexOf("Distribution.model_mass_weight_diracValue")>=0);
		if(c.name=="RecursiveAtom") enforce(certificate.indexOf("Distribution.model_mass_diracValue")>=0);
		if(c.name=="Interval"||c.name=="PuncturedInterval"||c.name=="SignedInterval"||c.name=="MixedIntegral"){
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0);
			enforce(certificate.indexOf("Distribution.DensityProgram.weight")>=0);
		}
		if(c.name=="UnboundedPuncture") enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid_null_edit")>=0);
		if(c.name=="BoundRectangle"||c.name=="TripleBind"||c.name=="BoundFunction"||c.name=="BoundDistribution"||c.name=="BoundType")
			enforce(certificate.indexOf("Distribution.model_mass_bind_density")>=0);
		if(c.name=="IntegralRectangle"||c.name=="WeightedRows") enforce(certificate.indexOf("Distribution.model_mass_integralValue")>=0);
		if(c.name=="ParametricWeight"||c.name=="ParametricPartialWeight"||c.name=="ParametricNestedWeights"||c.name=="WeightedRows")
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0);
		if(c.name=="UnboundedParameter"||c.name=="ZeroInfiniteRow"){
			if(c.name=="UnboundedParameter") enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")<0);
			enforce(text.indexOf("∫")>=0,c.name~" must retain its unsupported integral");
		}
		if(c.name=="NestedMaskedRectangle"||c.name=="ReversedMaskedRectangle"||c.name=="SignedMaskedRectangle"||
			c.name=="PuncturedMaskedRectangle"||c.name=="MaskedParameter"||c.name=="MaskedPartialParameter"||
			c.name=="OuterParameterMask"||c.name=="InnerParameterMask"||c.name=="MaskedPartialBranch"||c.name=="MixedParameterMasks")
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0,c.name~" must use a domain-checked parameter certificate");
		if(c.name=="NullPointParameter"||c.name=="ClosedSingletonParameter"||c.name=="EmptyMaskedParameter"||
			c.name=="DisjointPartialWeights"||c.name=="DisjointOpenSupports"||c.name=="DisjointTwoParameters"||c.name=="MaskedNullPoint"||c.name=="ShiftedNullPoint")
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0,c.name~" must check pointwise definedness on null supports");
		if(c.name=="NullPointDensity") enforce(certificate.indexOf("Distribution.model_density_weight_lebesgueValue")>=0);
		if(c.name=="StepSum"||c.name=="StepUnion"||c.name=="StepOverlap"||c.name=="StepSigned"||
			c.name=="StepPartialParameter"||c.name=="StepTwoParameters"||c.name=="StepBoundaryParameter"||c.name=="StepProduct")
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")>=0,c.name~" must use a checked step certificate");
		if(c.name=="StepUnbounded"||c.name=="StepNonconstant"){
			enforce(certificate.indexOf("Distribution.DensityProgram.presentation_mass_grid")<0,c.name~" must not invent a step certificate");
			enforce(text.indexOf("∫")>=0,c.name~" must retain its unsupported integral");
		}
		write(buildPath(directory,c.name~".lean"),certificate);
	}
	auto owner=Session.open(),a=owner.arena; FunctionSyntax s;
	foreach(source;[
		"Λ(x:ℕ).λ[x]", "Λ(x:ℝ).δ(x)[x]", "Λ(x:ℝ).λ[x]*λ[x]",
		"Λ(x:ℝ).δ(2)[y]", "δ(2)=δ(2)", "(δ(2):Distribution(𝔹))",
		"μ(f:ℕ→ℝ).λ(n:ℕ).massD(Λ(x:ℝ).f(n)*λ[x])",
		"μ(f:ℕ→ℝ).λ(n:ℕ).densityAtD(Λ(x:ℝ).f(n)*λ[x],0)"
	]) assertThrown(s.run(a,source),source);
	s.declare("n:ℕ");
	assertThrown(s.run(a,"Λ(n:ℕ).δ(λ(n:ℝ^n).0)[n]"),"output-axis dependency in a shadowing binder annotation");
}

int main(string[] args){
	auto dir=args.length>1?args[1]:"build/distributions"; mkdirRecurse(dir); run(dir);
	writeln(cases().length," distribution syntax certificates and rejection tests"); return 0;
}
