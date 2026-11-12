module dependent_tests;
import qsym;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:

private struct Case{ string name,source,expected,type,vars; }
private Case[] cases(){
	return [
		Case("Family","λ(n:ℕ).ℝ^n","λ(n:ℕ). ℝ^n","ℕ→Type"),
		Case("FamilyApply","(λ(n:ℕ).ℝ^n)(3)","ℝ^3","Type"),
		Case("Pi","Π(n:ℕ).ℝ^n","Π(n:ℕ). ℝ^n","Type"),
		Case("PiAscii","Pi(k:Nat).Real^k","Π(n:ℕ). ℝ^n","Type"),
		Case("Global","f","f","Π(n:ℕ). ℝ^n","f:Π(n:ℕ).ℝ^n"),
		Case("Apply","f(3)","f(3)","ℝ^3","f:Π(n:ℕ).ℝ^n"),
		Case("ApplyParameter","f(k)","f(k)","ℝ^k","k:ℕ,f:Π(n:ℕ).ℝ^n"),
		Case("ApplySum","f(k+1)","f(k+1)","ℝ^(k+1)","k:ℕ,f:Π(n:ℕ).ℝ^n"),
		Case("Identity","λ(n:ℕ).λ(x:ℝ^n).x","λ(n:ℕ). λ(x:ℝ^n). x","Π(n:ℕ). ℝ^n→ℝ^n"),
		Case("Specialize","(λ(n:ℕ).λ(x:ℝ^n).x)(3)","λ(x:ℝ^3). x","ℝ^3→ℝ^3"),
		Case("Zero","(λ(n:ℕ).λ(x:ℝ^n).x)(0)","λ(x:ℝ^0). x","ℝ^0→ℝ^0"),
		Case("VectorBeta","(λ(n:ℕ).λ(x:ℕ^n).x)(2)((1,2))","(1,2)","ℕ^2"),
		Case("Nested","λ(n:ℕ).λ(m:ℕ).ℝ^(m×n)","λ(n:ℕ). λ(m:ℕ). ℝ^(m×n)","ℕ→ℕ→Type"),
		Case("NestedApply","(λ(n:ℕ).λ(m:ℕ).ℝ^(m×n))(2)(3)","ℝ^(3×2)","Type"),
		Case("Shadow","(λ(n:ℕ).λ(n:ℕ).ℝ^n)(2)","λ(n:ℕ). ℝ^n","ℕ→Type"),
		Case("Capture","(λ(n:ℕ).λ(m:ℕ).ℝ^(m×n))(m)","λ(m1:ℕ). ℝ^(m1×m)","ℕ→Type","m:ℕ"),
		Case("Dot","λ(n:ℕ).λ(x:ℝ^n).dot(x,x)","λ(n:ℕ). λ(x:ℝ^n). dot(x,x)","Π(n:ℕ). ℝ^n→ℝ"),
		Case("MatVec","λ(m:ℕ).λ(n:ℕ).λ(A:ℝ^(m×n)).λ(x:ℝ^n).A@x","λ(m:ℕ). λ(n:ℕ). λ(A:ℝ^(m×n)). λ(x:ℝ^n). (A@x)","Π(n:ℕ). Π(n1:ℕ). ℝ^(n×n1)→ℝ^n1→ℝ^n"),
		Case("PiDomain","domain(f)","domain(f)","Set(ℕ)","f:Π(n:ℕ).ℝ^n"),
		Case("NestedPi","f(2)(3)","(f(2))(3)","ℝ^(2×3)","f:Π(m:ℕ).Π(n:ℕ).ℝ^(m×n)"),
		Case("OuterParameter","λ(n:ℕ).ℝ^(n+k)","λ(n:ℕ). ℝ^(n+k)","ℕ→Type","k:ℕ"),
		Case("HigherOrder","λ(f:Π(n:ℕ).ℝ^n).f(2)","λ(f:Π(n:ℕ). ℝ^n). f(2)","(Π(n:ℕ). ℝ^n)→ℝ^2"),
		Case("Undefined","undefined(Π(n:ℕ).ℝ^n)(2)","(undefined(Π(n:ℕ). ℝ^n))(2)","ℝ^2"),
		Case("PartialFamily","(λ(n:ℕ).ℝ^n)(0 sub 1)","(λ(n:ℕ). ℝ^n)(0 sub 1)","Type"),
		Case("NestedScope","λ(n:ℕ).λ(x:ℝ).λ(v:ℝ^n).v","λ(n:ℕ). λ(x:ℝ). λ(v:ℝ^n). v","Π(n:ℕ). ℝ→ℝ^n→ℝ^n"),
		Case("UnusedPi","Π(n:ℕ).ℝ","ℕ→ℝ","Type")
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s; if(c.vars.length) s.declare(c.vars);
		auto ty=s.inspectType(a,c.source); enforce(ty==c.type,c.name~" type: "~ty);
		auto r=s.run(a,c.source,[],Options(DensityMode.preserve,true)),text=s.format(a,r);
		enforce(!r.exhausted&&text==c.expected,c.name~": "~text);
		auto again=s.run(a,text); enforce(s.format(a,again)==text,c.name~" round trip");
		enforce(s.inspectType(a,text)==ty,c.name~" type changed");
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
}
unittest{
	run(); auto owner=Session.open(); FunctionSyntax s; s.declare("f:Π(n:ℕ).ℝ^n");
	foreach(source;["f(1/2)","f(0 sub 1)","λ(n:ℝ).ℝ^n","Π(n:ℝ).ℝ^n","(λ(n:ℕ).λ(x:ℝ^n).x)(2)((1,2,3))",
		"(λ(n:ℕ).λ(m:ℕ).λ(x:ℝ^n).λ(y:ℝ^m).(x,y))(2)(2)","Π(n:ℕ).ℝ^n×ℝ^2"])
		assertThrown(s.run(owner.arena,source));
	enforce(s.inspectType(owner.arena,"1/0")=="ℚ","type inspection evaluated a partial expression");
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/dependent"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," dependent certificates"); return 0;
}
