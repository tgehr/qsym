module algebra_certificate_tests;
import qsym;
import qsym.rational_identity:rationalIdentityZero;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.conv:to;
@safe:
int main(string[] args){
 enforce(args.length==2);mkdirRecurse(args[1]);
 auto owner=Session.open(),a=owner.arena;Syntax s;s.declare("x:ℝ,y:ℝ,n:ℕ");
 string[] identities=[
  "exp(x)-exp(x)",
  "[exp(x)≠1]*((exp(x)-1)/(exp(x)-1)-1)",
  "x^(n+n)-(x^2)^n",
  "x^(2*(n+1))-x^2*(x^2)^n",
  "x^(n*2)-(x^2)^n",
  "[x≠0∧y≠0]*(x*y/(x*y)-1)",
  "[x=0∨y=0]*x*y",
  "[x=0]*x+[x≠0]*(x/x-1)",
  "creal(cis(x))-creal(cis(x))",
  "[x^2≠1]*((x^2-1)/(x^2-1)-1)",
  "[x^n≠1]*((x^n-1)/(x^n-1)-1)",
  "[x^(n+n)≠1]*((x^(n+n)-1)/(x^(n+n)-1)-1)",
  "[(x^n)^n≠1]*(((x^n)^n-1)/((x^n)^n-1)-1)"
 ];
 foreach(i,source;identities){
  auto input=s.parse(a,source,Sort.real_);Term[] conditions;
  enforce(rationalIdentityZero(a,input,conditions),source);
  write(buildPath(args[1],"Identity"~to!string(i)~".lean"),exportRationalZeroLean(a,input,conditions));
 }
 foreach(source;["1/x-1/x","exp(1/x)-exp(1/x)","[x≠0]*(y/y-1)","x^n-x^(n+1)"]){
  Term[] conditions;enforce(!rationalIdentityZero(a,s.parse(a,source,Sort.real_),conditions),source);
 }
 writeln(identities.length," algebra certificates; 4 invalid or partial identities rejected");return 0;
}
