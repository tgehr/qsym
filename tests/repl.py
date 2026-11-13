#!/usr/bin/env python3
import pathlib
import subprocess

root=pathlib.Path(__file__).resolve().parents[1]
certificate=root/"build/Repl.lean"
source="\n".join([
	"# Expressions use the rule grammar.","x+x","[x≠0]·x⁻¹",":vars z:ℂ,p:𝔹",
	"conj(conj(z))","(1+ⅈ)^2","[p]·x+[¬p]·x","1+true","x+x",
	":vars x:ℂ",f":lean {certificate}",":quit","42"])+"\n"
result=subprocess.run([str(root/"build/qsym")],input=source,text=True,capture_output=True,timeout=30)
assert result.returncode==0,result.stderr
assert result.stdout.splitlines()==[
	"2·x","[x≠0]·x⁻¹","z","2·ⅈ","x","2·x",
	f"Wrote {certificate}"],result.stdout
assert "type mismatch" in result.stderr,result.stderr
# The last input retains its original real environment after a type declaration.
assert "Expr .real" in certificate.read_text()
result=subprocess.run([str(root/"build/qsym"),"repl"],input="1+2\n",text=True,capture_output=True,timeout=30)
assert result.returncode==0 and result.stdout=="3\n",result
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"[x<2]","2^(1/2)",":vars n:ℕ,q:ℚ,z:ℂ,p:𝔹","n*0","rat(1,3)+rat(1,6)",
	"sin(z+0)","([p]:ℕ)",":functions cexp",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==[
	"[x<2]","sqrt(2)","0","1/2","csin(z)","[p]",
	"cexp(Complex): Complex","cexpi(Complex): Complex"],result.stdout
facts_certificate=root/"build/ReplFacts.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":assume x>0",":facts","abs(x)",":assume 2*y+1=7","y^2",":assume x+1",
	":vars x:ℂ",":vars z:ℂ",":facts","abs(x)",":clear",":vars x:ℂ",
	f":lean {facts_certificate}",":reset","abs(x)",":facts",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0,result.stderr
assert result.stdout.splitlines()==[
	"x>0","x","9","x>0","2*y+1=7","x",f"Wrote {facts_certificate}","abs(x)"],result.stdout
assert "assumptions must be Bool" in result.stderr,result.stderr
assert "use :clear before changing the type of x" in result.stderr,result.stderr
# Clearing facts and changing types cannot change the last result's certificate.
assert "(g1 :" in facts_certificate.read_text() and "(g2 :" in facts_certificate.read_text()
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"[3·x+1=7]","[x^2=1]·[x<1]","[x<1]·[x^2=1]","x-2","-x",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["[x=2]","[x=-1]","[x=-1]","x-2","-x"],result.stdout
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"[x^2<=1]·[x<1]","[x=-1∨x=1]·[x<1]","[x<0]·[y>0]·[1<x]","floor(-7/3)","log2(8)","cabs(3+4*ⅈ)",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["[-1≤x∧x<1]","[x=-1]","0","-3","3","5"],result.stdout
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars x:ℂ,t:ℝ","cpow(x,1/2)","cpow(x,t)","carg(cpow(x,1/2))","carg(csqrt(x))",
	"cimag(clog(x))","cabs(cexp(x))",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["x^(1/2)","x^t","1/2·carg(x)","1/2·carg(x)","carg(x)","exp(creal(x))"],result.stdout
expanded_certificate=root/"build/ReplExpand.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"(x+1)^10","(x+1)^10<2^10",":expand (x+1)^3",f":lean {expanded_certificate}",
	"(x+1)^3",":expand",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0,result.stderr
assert result.stdout.splitlines()==["(x+1)^10","-3<x∧x<1","x^3+3·x^2+3·x+1",
	f"Wrote {expanded_certificate}","(x+1)^3"],result.stdout
assert "expected an expression" in result.stderr,result.stderr
domain_certificate=root/"build/ReplDomain.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":domain 1/x",":domain [x≠0]/x",":domain 0*(1/0)",":domain [false]*(1/0)",
	":domain sqrt(x)",":domain log(1/x)",":domain tanh(atanh(x))",":domain",
	":assume x>0",":domain log(x)",":clear",":vars x:ℂ",f":lean {domain_certificate}",
	":reset",":domain clog(0)",":domain csqrt(-1)",":domain false∧1/0>0",
	":domain 1/0>0∧false",":help",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0,result.stderr
assert result.stdout.splitlines()[:13]==[
	"x≠0","true","false","true","0≤x","0<x","-1<x∧x<1","true",
	f"Wrote {domain_certificate}","false","true","true","false"],result.stdout
assert "expected an expression" in result.stderr,result.stderr
assert ":domain EXPR" in result.stdout,result.stdout
domain_source=domain_certificate.read_text()
assert "theorem domain_iff" in domain_source and "theorem domain_total" in domain_source
assert "(h0 :" in domain_source and "Expr .real" in domain_source

# Brackets guard either side of a surface product; explicit calls stay strict.
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars z:ℂ,x:ℝ",":domain clog(z)*[z≠0]",":domain [z≠0]*clog(z)",
	":domain log(x)*[0<x]/x",":domain mulC(clog(z),[z≠0])",
	"floor(x+1)-floor(x)","[x=0]+[x≠0]*[z=0]=[x=0∨z=0]",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0,result.stderr
assert result.stdout.splitlines()==["true","true","true","z≠0","1","true"],result.stdout
# Literal defaults, exact decimals, and comparisons in the source scalar type.
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars j:ℕ","x^j=1",":vars j:ℤ","x^j=1",":vars j:ℚ","x^j=1",
	":vars j:ℝ","j/2=toℝ(floor(j/2))",":vars q:ℚ,r:ℚ","toℝ(q)=toℝ(r)",
	"2^3^2","0.1+0.2","-.5x+1.5x","1.25e-2","3/2","-3/2",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==[
	"j=0∨x=1∨x=-1∧denominator(1/2·j)=1",
	"j=0∨x=1∨x=-1∧denominator(1/2·j)=1",
	"j=0∨x=1∨x=-1∧denominator(1/2·j)=1",
	"j·(1/2)=floor(j·(1/2))","q=r","512","3/10","x","1/80","3/2","-3/2"],result.stdout
print("REPL checks passed.")

# Exact discrete bounds, extrema, signs, and original domains.
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars n:ℕ,m:ℕ,k:ℤ,q:ℚ,x:ℝ,y:ℝ","¬(n<m)","2*q+1<4","toℝ(k)<3/2",
	"min(exp(x),exp(y))","max(acos(x),acos(y))","sign(x/y)","min(x+2,y+2)",
	":domain max(sqrt(-1),sqrt(4))",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["m≤n","q<3/2","k≤1","exp(min(x,y))","acos(min(x,y))",
	"sign(x)·sign(y)","min(x,y)+2","false"],result.stdout

# A printed result must not expose another round of rounding simplification.
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"2*floor(x)=2","floor(x)=1","2*ceil(x)=2","round(x)=1","floor(x)=0",
	"2*floor(ceil(x)/2)=2","cos(abs(x))","cosh(abs(x))","abs(sinh(x))",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["1≤x∧x<2","1≤x∧x<2","0<x∧x≤1","1/2≤x∧x<3/2",
	"0≤x∧x<1","1<x∧x≤3","cos(x)","cosh(x)","sinh(abs(x))"],result.stdout

result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars i:ℤ,n:ℕ","2*i+1=5","1+2*i=4","2*n+1=5","2*(n+1)=4",
	"2*floor(x)+1=5","2*floor(x)+1=4","2*ceil(x)+1=5","2*round(x)+1=5",
	"2*n-1=-1","0=-2*n","n^3+1=1","n+n+1≠1",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==[
	"i=2","false","n=2","n=1","2≤x∧x<3","false","1<x∧x≤2","3/2≤x∧x<5/2",
	"n=0","n=0","n=0","n≠0"],result.stdout
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars i:ℤ,j:ℤ,n:ℕ,r:ℚ","2*i+1=3",":assume 2*i+1=3",
	"[2*i+1=3]","[2*i+1=2]","[i=3]","i","[i≠1]",":clear",
	"[2*j+1=3]*j","j","[2*n+1=3]*n","n","[2*r+1=3]*r","r",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==[
	"i=1","1","0","0","1","0","[j=1]","j","[n=1]","n","[r=1]","r"],result.stdout

result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars a:ℕ,b:ℕ,p:𝔹",":domain a sub b","8 sub 3",":domain 2 sub 5",
	"if true then 3 else 1/0","if false then 1/0 else 3","if p then true else false",
	":domain if b≤a then a sub b else 0",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["b≤a","5","false","3","3","p","true"],result.stdout
function_certificate=root/"build/ReplFunction.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"(λ(a:ℕ).λ(b:ℕ).a+b)(1)(2)",f":lean {function_certificate}",
	":vars f:ℝ→ℝ,S:Set(ℝ)","domain(f)","defined(f)",
	"0∈domain(λ(x:ℝ).x/x)","1∈domain(λ(x:ℝ).x/x)",
	"(λ(x:ℝ).0)(1/0)",":domain (λ(x:ℝ).0)(1/0)",
	":domain (λ(x:ℝ | x>0).log(x))(-1)","(λ(x:ℝ).2.5)(0)",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["3",f"Wrote {function_certificate}","domain(f)","true",
	"false","true","undefined(ℕ)","false","false","5/2"],result.stdout
assert "theorem refinement" in function_certificate.read_text() and "BindingCertificate.lowered" in function_certificate.read_text()
print("Function and subset REPL checks passed.")
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars f:ℕ→ℕ",":assume f=0","domain(f)",":facts",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and result.stdout.splitlines()==["domain(f)"],result.stdout
assert "expected a function or set expression" in result.stderr,result.stderr
subset_certificate=root/"build/ReplSubsets.lean"
subset_snapshot=root/"build/ReplSubsetSnapshot.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":assume x∈{x:ℝ|x=1}","x","[x=1]","x∈{y:ℝ|y>0}",f":lean {subset_certificate}",":facts",":clear",
	":vars S:Set(ℝ),T:Set(ℝ)","S⊆S","S⊆T","S⊈S","1∉{x:ℝ|x=0}",":domain 1∉guard(false,S)",
	":assume S⊆S",":vars S:Set(ℕ)",":clear",":vars S:Set(ℕ)",f":lean {subset_snapshot}",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0,result.stderr
assert result.stdout.splitlines()==["1","1","true",f"Wrote {subset_certificate}","x∈{x:ℝ|x=1}",
	"true","(S⊆T)","false","true","false",f"Wrote {subset_snapshot}"],result.stdout
assert "use :clear before changing the type of S" in result.stderr,result.stderr
assert "AssumptionCertificate" in subset_certificate.read_text()
print("Subset assumption REPL checks passed.")
type_certificate=root/"build/ReplTypes.lean"
recursion_certificate=root/"build/ReplRecursion.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"Real","ℝ","Real=ℝ",f":lean {type_certificate}","Real=ℂ","λ(t:ℝ).(0:ℝ)",
	"(μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2))(5)",f":lean {recursion_certificate}",
	"domain(μ(f:ℕ→ℕ).f)","defined(μ(f:ℕ→ℕ).λ(n:ℕ).f(n+1))",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["ℝ","ℝ","true",f"Wrote {type_certificate}","false","λ(t:ℝ). (0:ℝ)",
	"5",f"Wrote {recursion_certificate}","{x:ℕ | false}","true"],result.stdout
assert "Recursion.program_unfold" in recursion_certificate.read_text()
print("Type value and recursion REPL checks passed.")
equality_certificate=root/"build/ReplHigherEquality.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars p:ℕ→𝔹,q:ℕ→𝔹","{x:ℕ|p(x)}={x:ℕ|q(x)}",f":lean {equality_certificate}",
	"{x:ℕ|p(x)}={y:ℕ|p(y)}","p=p","{x:ℕ|false}={x:ℕ|true}",
	"μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)",
	"(λ(x:ℝ).λ(y:ℝ).x)(y)","λ(t:ℝ).0/(2*t-1)",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["({x:ℕ | p(x)}={x:ℕ | q(x)})",f"Wrote {equality_certificate}","true","true","false",
	"μ(f:ℕ→ℕ). λ(n:ℕ). ([n≤1]·n+[¬(n≤1)]·(f(n sub 1)+f(n sub 2)):ℕ)",
	"λ(y1:ℝ). y","λ(t:{t:ℝ | t≠1/2}). (0:ℝ)"],result.stdout
assert "Binding.equalValue" in equality_certificate.read_text()
print("Higher-order equality and binder-name REPL checks passed.")
solver_certificate=root/"build/ReplRecurrenceSolver.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars a:ℕ,d:ℕ,n:ℕ","μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else f(n sub 1)+2",
	"(μ(f:ℕ→ℕ).λ(k:ℕ).if k=0 then a else f(k sub 1)*d)(n)",f":lean {solver_certificate}",
	"domain(μ(f:ℕ→ℕ).λ(k:ℕ).if k=0 then a else f(k sub 1)+d)",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["λ(n:ℕ). 2·n+3","a·d^n",f"Wrote {solver_certificate}","{k:ℕ | true}"],result.stdout
assert "Recursion.solve_nat_step" in solver_certificate.read_text()
print("Recurrence solver REPL checks passed.")
tensor_certificate=root/"build/ReplTensors.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"ℕ×ℕ×ℕ","((1,2),(3,4))@(5,6)","dot((ⅈ,),(1,))",
	"(λ(v:ℝ^2).dot(v,v))((3,4))",f":lean {tensor_certificate}",
	":vars n:ℕ,m:ℕ,A:ℝ^(m×n),x:ℝ^n","A@x","ℝ^n=ℝ^m",
	":domain μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else if n≤10 then f(n sub 1) else f(n+1)",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["ℕ^3","(17,39)","-ⅈ","25",f"Wrote {tensor_certificate}",
	"(A@x)","(ℝ^n=ℝ^m)","{n:ℕ | n≤10}"],result.stdout
assert "Tensor.dotValue" in tensor_certificate.read_text()
print("Tensor and bounded-recursion REPL checks passed.")
dependent_certificate=root/"build/ReplDependent.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":vars f:Π(n:ℕ).ℝ^n",":type f",":type f(3)",":type λ(n:ℕ).ℝ^n",":type 1/0",
	"λ(n:ℕ).ℝ^n","(λ(n:ℕ).λ(x:ℝ^n).x)(2)","f(2)",":type f(4)",
	f":lean {dependent_certificate}",":type",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0,result.stderr
assert result.stdout.splitlines()==["Π(n:ℕ). ℝ^n","ℝ^3","ℕ→Type","ℚ","λ(n:ℕ). ℝ^n",
	"λ(x:ℝ^2). x","f(2)","ℝ^4",f"Wrote {dependent_certificate}"],result.stdout
assert "expected an expression" in result.stderr,result.stderr
assert "Dependent.apply" in dependent_certificate.read_text()
assert "(.scalar .real) 2" in dependent_certificate.read_text()
assert "(.scalar .real) 4" not in dependent_certificate.read_text()
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":domain μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 0 else if n<10 then f(n sub 1) else f(n+1)",
	":domain μ(f:ℕ→ℕ).λ(n:ℕ).if n<10 then f(n sub 1) else if n=10 then 0 else if n<20 then f(n sub 1) else f(n+1)",
	":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["{n:ℕ | n≤9}","{n:ℕ | 10≤n∧n≤19}"],result.stdout
print("Dependent types, type queries, and interval-domain REPL checks passed.")
fixed_domain_certificate=root/"build/ReplFixedDomain.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":domain μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)",
	f":lean {fixed_domain_certificate}",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["{n:ℕ | true}",f"Wrote {fixed_domain_certificate}"],result.stdout
assert "SetFixed.domain_univ" in fixed_domain_certificate.read_text()
print("Fixed-point set-domain REPL checks passed.")

partial_domain_certificate=root/"build/ReplPartialDomain.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"domain(μ(f:ℕ→ℕ).λ(n:ℕ).if n≤1 then n else f(n sub 1)+f(n sub 2)+f(n sub 3))",
	f":lean {partial_domain_certificate}",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["{n:ℕ | n≤1}",f"Wrote {partial_domain_certificate}"],result.stdout
assert "SetFixed.domain_set" in partial_domain_certificate.read_text()
print("Partial recursive domain REPL checks passed.")

real_countdown_certificate=root/"build/ReplRealCountdown.lean"
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	":domain μ(f:ℝ→ℝ).λ(x:ℝ).if x≤1 then x else 2*f(x-1)",
	f":lean {real_countdown_certificate}",":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["{x:ℝ | true}",f"Wrote {real_countdown_certificate}"],result.stdout
assert "SetFixed.Predicate.total_measure" in real_countdown_certificate.read_text()
print("Real countdown domain REPL checks passed.")
result=subprocess.run([str(root/"build/qsym")],input="\n".join([
	"(μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1)(10)",
	"(μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then -3 else -2*f(n sub 1)+1)(5)",
	":type μ(f:ℕ→ℤ).λ(n:ℕ).if n=0 then -3 else -2*f(n sub 1)+1",
	":domain μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1",
	"defined((μ(f:ℕ→ℕ).λ(n:ℕ).if n=0 then 3 else 2*f(n sub 1)+1)(0 sub 1))",
	":quit",""]),text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["4095","107","ℕ→ℤ","{n:ℕ | true}","false"],result.stdout
