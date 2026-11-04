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
	"[x<2]","2^(1/2)","nat(0)","rat(1,2)","csin(z)","([p]:ℕ)",
	"cexp(Complex): Complex","cexpi(Complex): Complex"],result.stdout
print("REPL checks passed.")
