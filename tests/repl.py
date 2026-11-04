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
	"[x<2]","sqrt(2)","nat(0)","rat(1,2)","csin(z)","([p]:ℕ)",
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
	"[x^2<=1]·[x<1]","[x<0]·[y>0]·[1<x]","floor(-7/3)","log2(8)","cabs(3+4*ⅈ)",":quit",""]),
	text=True,capture_output=True,timeout=30)
assert result.returncode==0 and not result.stderr,result.stderr
assert result.stdout.splitlines()==["[-1≤x∧x<1]","0","int(-3)","3","5"],result.stdout
print("REPL checks passed.")
