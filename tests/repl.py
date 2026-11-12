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
