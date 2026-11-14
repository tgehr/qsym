module conditional_consumer_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
@safe:
private struct Case { string name,source,expected,vars; }
private Case[] cases(){ return [
 Case("Application","(if x=0 then (λ(y:ℕ).y) else (λ(y:ℕ).y+1))(2)","if x=0 then 2 else 3"),
 Case("Projection","get((if x=0 then (1,0) else (0,1)),0)","[x=0]"),
 Case("PairFirst","get(if p then (1,true) else (2,false),0)","if p then 1 else 2","p:𝔹"),
 Case("PairRest","get(if p then (1,true) else (2,false),1)","p","p:𝔹"),
 Case("FunctionArgument","(λ(v:ℕ^2).get(v,0))(if p then (1,0) else (0,1))","[p]","p:𝔹"),
 Case("GlobalArgument","f(if p then (1,0) else (0,1))","if p then f((1,0)) else f((0,1))","p:𝔹,f:ℕ^2→ℕ"),
 Case("HigherOrder","(if p then λ(n:ℕ).λ(m:ℕ).n+m else λ(n:ℕ).λ(m:ℕ).n*m)(2)(3)","if p then 5 else 6","p:𝔹"),
 Case("MemberLeft","2∈(if p then {n:ℕ | n<3} else {n:ℕ | n>3})","p","p:𝔹"),
 Case("MemberRight","(if p then (1,0) else (0,1))∈{v:ℕ^2 | get(v,0)=1}","p","p:𝔹"),
 Case("TypeEquality","(if p then ℕ else ℤ)=ℕ","p","p:𝔹"),
 Case("TypeEqualityRight","ℕ=(if p then ℕ else ℤ)","p","p:𝔹"),
 Case("SetEquality","(if p then {n:ℕ | true} else {n:ℕ | false})={n:ℕ | true}","p","p:𝔹"),
 Case("Subset","{n:ℕ | true}⊆(if p then {n:ℕ | true} else {n:ℕ | false})","p","p:𝔹"),
 Case("DotLeft","dot(if p then (1,0) else (0,1),(2,3))","if p then 2 else 3","p:𝔹"),
 Case("DotRight","dot((2,3),if p then (1,0) else (0,1))","if p then 2 else 3","p:𝔹"),
 Case("VectorAdd","(if p then (1,0) else (0,1))+(2,3)","if p then (3,3) else (2,4)","p:𝔹"),
 Case("Hadamard","(2,3)·(if p then (1,0) else (0,1))","if p then (2,0) else (0,3)","p:𝔹"),
 Case("MatrixVector","((2,0),(0,3))@(if p then (1,0) else (0,1))","if p then (2,0) else (0,3)","p:𝔹"),
 Case("MatrixPower","(if p then ((2,0),(0,3)) else ((1,0),(0,1)))^2","if p then ((4,0),(0,9)) else ((1,0),(0,1))","p:𝔹"),
 Case("SymbolicDimension","dot(if p then x else y,z)","if p then dot(x,z) else dot(y,z)","n:ℕ,p:𝔹,x:ℝ^n,y:ℝ^n,z:ℝ^n"),
 Case("StrictTuple","defined(get(if p then (1,1/0) else (2,3),0))","¬p","p:𝔹"),
 Case("UndefinedCondition","defined((if 1/0>0 then λ(n:ℕ).1 else λ(n:ℕ).2)(0))","false"),
 Case("SameBranchesPartial","defined(get(if 1/0>0 then (1,0) else (1,1),0))","false"),
 Case("DefinedNonStrict","defined(if p then undefined(ℕ→ℕ) else λ(n:ℕ).n)","¬p","p:𝔹"),
 Case("DomainNonStrict","defined(domain(if 1/0>0 then λ(n:ℕ).n else λ(n:ℕ).n+1))","true"),
 Case("DeadBoolean","false∧get(if 1/0>0 then (true,1) else (false,2),0)","false"),
 Case("DeadMask","[false]*get(if 1/0>0 then (1,0) else (0,1),0)","0"),
 Case("RationalResult","(if p then λ(n:ℕ).(1/2) else λ(n:ℕ).(1/3))(0)","if p then 1/2 else 1/3","p:𝔹"),
 Case("IntegerResult","(if p then λ(n:ℕ).(-1) else λ(n:ℕ).(-2))(0)","if p then -1 else -2","p:𝔹"),
 Case("RealResult","(if p then λ(n:ℕ).(1:ℝ) else λ(n:ℕ).(2:ℝ))(0)","if p then (1:ℝ) else (2:ℝ)","p:𝔹"),
 Case("ComplexResult","(if p then λ(n:ℕ).ⅈ else λ(n:ℕ).(2*ⅈ))(0)","if p then ⅈ else 2*ⅈ","p:𝔹")
]; }
int main(string[] args){
 auto directory=args.length>1?args[1]:"build/conditional-consumers"; mkdirRecurse(directory);
 foreach(c;cases()){
  auto owner=Session.open(); FunctionSyntax s; if(c.vars.length) s.declare(c.vars);
  auto r=s.run(owner.arena,c.source,[],Options(DensityMode.preserve,true)),text=s.format(owner.arena,r);
  writeln(c.name,": ",text);
  enforce(!r.exhausted,c.name~" exhausted");
  auto expected=s.format(owner.arena,s.run(owner.arena,c.expected));
  enforce(text==expected,c.name~": expected "~expected);
  auto again=s.run(owner.arena,text); enforce(!again.exhausted&&s.format(owner.arena,again)==text,c.name~" round trip");
  write(buildPath(directory,c.name~".lean"),s.exportCertificate(owner.arena,r));
 }
 writeln(cases().length," conditional consumer certificates"); return 0;
}
