module polymorphic_conditional_tests;
import qsym;
import qsym.binding;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:

private struct Case { string name,source,expected,variables; }
private Case[] cases(){ return [
 Case("UserShadow","if x=0 then λ(x:ℕ).x else λ(x:ℕ).x+1","","x:ℕ"),
 Case("UserTrue","(λ(x:ℕ).(if x=0 then λ(x:ℕ).x else λ(x:ℕ).x+1)(4))(0)","4"),
 Case("UserFalse","(λ(x:ℕ).(if x=0 then λ(x:ℕ).x else λ(x:ℕ).x+1)(4))(2)","5"),
 Case("PointwiseElse","λ(n:ℕ).if p then (0,1) else (n+0,n*1)","λ(n:ℕ).if p then (0,1) else (n,n)","p:𝔹"),
 Case("FunctionTrue","(if true then λ(x:ℕ).x else λ(x:ℕ).x+1)(4)","4"),
 Case("FunctionFalse","(if false then λ(x:ℕ).x else λ(x:ℕ).x+1)(4)","5"),
 Case("FunctionSymbolic","(if p then f else g)(4)","","p:𝔹,f:ℕ→ℕ,g:ℕ→ℕ"),
 Case("FunctionUndefined","if undefined(𝔹) then λ(x:ℕ).x else λ(x:ℕ).x+1","undefined(ℕ→ℕ)"),
 Case("PartialPredicate","defined(if 1/0>0 then λ(x:ℕ).x else λ(x:ℕ).x+1)","false"),
 Case("SamePartial","defined(if 1/0>0 then λ(x:ℕ).x else λ(x:ℕ).x)","false"),
 Case("SameSymbolic","if p then f else f","f","p:𝔹,f:ℕ→ℕ"),
 Case("SamePartialSymbolic","defined(if p(0) then f else f)","","p:ℕ→𝔹,f:ℕ→ℕ"),
 Case("DefinedSymbolic","defined(if p then f else undefined(ℕ→ℕ))","p","p:𝔹,f:ℕ→ℕ"),
 Case("InactiveUndefined","if false then undefined(ℕ→ℕ) else λ(x:ℕ).x","λ(x:ℕ).x"),
 Case("InactiveDivergence","if true then (1,2) else (μ(f:ℕ→ℕ^2).λ(n:ℕ).f(n+1))(0)","(1,2)"),
 Case("InactiveDivergenceFalse","if false then (μ(f:ℕ→ℕ^2).λ(n:ℕ).f(n+1))(0) else (3,4)","(3,4)"),
 Case("SetTrue","if true then {n:ℕ | n<3} else {n:ℕ | n>5}","{n:ℕ | n<3}"),
 Case("SetMember","2∈(if false then {n:ℕ | n>5} else {n:ℕ | n<3})","true"),
 Case("SetSymbolic","if p then S else T","","p:𝔹,S:Set(ℕ),T:Set(ℕ)"),
 Case("Unit","if p then () else ()","()","p:𝔹"),
 Case("UnitPartial","defined(if undefined(𝔹) then () else ())","false"),
 Case("EmptyVector","if true then (():ℕ^0) else undefined(ℕ^0)","(():ℕ^0)"),
 Case("EmptyVectorSymbolic","if p then x else y","","p:𝔹,x:ℕ^0,y:ℕ^0"),
 Case("TypeTrue","if true then ℕ else ℤ","ℕ"),
 Case("TypeFalse","if false then ℕ else ℤ","ℤ"),
 Case("TypeSymbolic","if p then ℕ else ℤ","","p:𝔹"),
 Case("VectorDimension","if p then x else y","","n:ℕ,p:𝔹,x:ℕ^n,y:ℕ^n"),
 Case("DependentFunction","if p then f else g","","p:𝔹,f:Π(n:ℕ).ℝ^n,g:Π(n:ℕ).ℝ^n"),
 Case("DependentFalse","(if false then f else g)(2)","g(2)","f:Π(n:ℕ).ℝ^n,g:Π(n:ℕ).ℝ^n"),
 Case("DependentBinder","λ(n:ℕ).λ(p:𝔹).λ(x:ℝ^n).λ(y:ℝ^n).if p then x else y",""),
 Case("CaptureElse","(λ(y:ℕ).if p then λ(x:ℕ).x else λ(x:ℕ).y)(x)","","p:𝔹,x:ℕ"),
 Case("SubstituteElse","(λ(y:ℕ).if false then λ(x:ℕ).x else λ(x:ℕ).y)(7)(2)","7"),
 Case("NestedElse","(λ(y:ℕ).if p then λ(x:ℕ).x else if q then λ(x:ℕ).y else λ(x:ℕ).y+1)(7)","","p:𝔹,q:𝔹"),
 Case("FunctionPair","if true then (λ(x:ℕ).x,false) else (λ(x:ℕ).x+1,true)","(λ(x:ℕ).x,false)")
]; }
int main(string[] args){
 auto directory=args.length>1?args[1]:"build/polymorphic-conditionals"; mkdirRecurse(directory);
 foreach(c;cases()){
  writeln(c.name);
  auto owner=Session.open(); FunctionSyntax s; if(c.variables.length) s.declare(c.variables);
  auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
  enforce(!r.exhausted,c.name~" exhausted: "~text);
  if(c.expected.length) enforce(text==s.format(owner.arena,s.run(owner.arena,c.expected)),c.name~": "~text);
  auto again=s.run(owner.arena,text); enforce(!again.exhausted&&s.format(owner.arena,again)==text,c.name~" round trip: "~text);
  enforce(s.inspectType(owner.arena,c.source)==s.inspectType(owner.arena,text),c.name~" type changed");
  if(c.name=="UserShadow") enforce(text.indexOf("if x=0 then")>=0,"free predicate variable was captured: "~text);
  if(c.name=="CaptureElse") enforce(text.indexOf("x1")>=0,"conditional else branch lost capture avoidance: "~text);
  write(buildPath(directory,c.name~".lean"),s.exportCertificate(owner.arena,r));
  if(c.name=="InactiveDivergence"||c.name=="InactiveDivergenceFalse"){
   auto plain=r.bindings.normalize(r.original,64,false);
   enforce(!plain.exhausted&&plain.output==r.reduction.output,"inactive branch evaluated without domain normalization");
  }
 }
 auto owner=Session.open(); FunctionSyntax s;
 foreach(source;["if true then λ(x:ℕ).x else 1","if true then ℕ else ()","if true then (1,2) else (3,4,5)"])
  assertThrown(s.run(owner.arena,source));
 writeln(cases().length," polymorphic conditional certificates; 3 type mismatches rejected"); return 0;
}
