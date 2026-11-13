module binder_name_tests;
import qsym;
import qsym.binding;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:startsWith;
@safe:

private struct Case{ string name,source,expected,variables; bool prefix; }
private Case[] cases(){
	return [
		Case("Identity","λ(n:ℕ).n","λ(n:ℕ). n"),
		Case("Curried","λ(a:ℕ).λ(b:ℕ).a+b","λ(a:ℕ). λ(b:ℕ). a+b"),
		Case("PartialApplication","(λ(a:ℕ).λ(b:ℕ).a+b)(1)","λ(b:ℕ). b+1"),
		Case("Shadow","λ(n:ℕ).λ(n:ℕ).n","λ(n:ℕ). λ(n1:ℕ). n1"),
		Case("ScalarCapture","(λ(x:ℝ).λ(y:ℝ).x)(y)","λ(y1:ℝ). y"),
		Case("FunctionCapture","(λ(g:ℕ→ℕ).λ(f:ℕ→ℕ).g)(f)","λ(f1:ℕ→ℕ). f","f:ℕ→ℕ"),
		Case("UnusedGlobal","λ(f:ℕ).f","λ(f:ℕ). f","f:ℕ→ℕ"),
		Case("Pointwise","λ(n:ℕ).n+0","λ(n:ℕ). n"),
		Case("Refined","λ(t:{u:ℝ|u≠1/2}).0/(2*t-1)","λ(t:{u:ℝ | u≠1/2}). (0:ℝ)"),
		Case("InferredRefinement","λ(t:ℝ).0/(2*t-1)","λ(t:{t:ℝ | t≠1/2}). (0:ℝ)"),
		Case("Domain","domain(λ(t:ℝ).0/(2*t-1))","{t:ℝ | t≠1/2}"),
		Case("Subset","{n:ℕ|p(n)}","{n:ℕ | p(n)}","p:ℕ→𝔹"),
		Case("Recursive","μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)","λ(n:ℕ). floorN(","",true),
		Case("FixedConstant","μ(f:ℕ→ℕ).λ(n:ℕ).7","λ(n:ℕ). 7"),
		Case("FixedIdentity","μ(f:ℕ→ℕ).λ(n:ℕ).f(n)","λ(n:ℕ). undefined(ℕ)"),
		Case("FixedDomain","domain(μ(f:ℕ→ℕ).λ(n:ℕ).f(n))","{n:ℕ | false}"),
		Case("NestedTypes","λ(A:Type).λ(n:ℕ).A","λ(A:Type). λ(n:ℕ). A"),
		Case("GlobalArgument","λ(n:ℕ).p(n)","λ(n:ℕ). p(n)","p:ℕ→𝔹")
	];
}
private void run(string directory=""){
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena; FunctionSyntax s; if(c.variables.length) s.declare(c.variables);
		auto r=s.run(a,c.source),output=s.format(a,r); enforce(!r.exhausted,c.name~" exhausted");
		enforce(c.prefix?output.startsWith(c.expected):output==c.expected,c.name~": "~output);
		auto again=s.run(a,output); enforce(s.format(a,again)==output,c.name~" round trip: "~s.format(a,again));
		if(directory.length) write(buildPath(directory,c.name~".lean"),s.exportCertificate(a,r));
	}
}
unittest{
	run(); auto owner=Session.open(),a=owner.arena,b=new Bindings(a),nat=b.scalarType(Sort.natural);
	auto ctx=b.push(b.empty(),nat),t=b.lambda(b.variable(ctx,0)),r=b.normalize(t),code=b.exportLean(r);
	enforce(b.hint(t,"n")==t&&b.lambda(b.variable(ctx,0))==t,"name changed canonical identity");
	b.hint(t,"m"); enforce(b.binderHint(t).name=="n","shared canonical binder must retain its first hint");
	enforce(b.exportLean(b.normalize(t))==code,"name changed certificate");
	string certificate;
	foreach(source;["λ(a:ℕ).λ(b:ℕ).a+b","λ(u:ℕ).λ(v:ℕ).u+v"]){
		auto session=Session.open(); FunctionSyntax s; auto value=s.run(session.arena,source),next=s.exportCertificate(session.arena,value);
		if(certificate.length) enforce(next==certificate,"alpha renaming changed certificate"); else certificate=next;
	}
}
int main(string[] args){
	auto directory=args.length>1?args[1]:"build/binder-names"; mkdirRecurse(directory); run(directory);
	writeln(cases().length," binder-name certificates"); return 0;
}
