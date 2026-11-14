module trig_magnitude_tests;
import qsym;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.stdio:writeln;
import std.string:indexOf;
@safe:

private struct Case{ string name,input,expected; string[] facts; string law; bool domain; }
private Case[] cases(){
	return [
		Case("Sin","cabs(csin(z))","sqrt(sin(creal(z))^2+sinh(cimag(z))^2)",[],"complex_norm_sin"),
		Case("Cos","cabs(ccos(z))","sqrt(cos(creal(z))^2+sinh(cimag(z))^2)",[],"complex_norm_cos"),
		Case("Sinh","cabs(csinh(z))","sqrt(sinh(creal(z))^2+sin(cimag(z))^2)",[],"complex_norm_sinh"),
		Case("Cosh","cabs(ccosh(z))","sqrt(sinh(creal(z))^2+cos(cimag(z))^2)",[],"complex_norm_cosh"),
		Case("Tan","cabs(ctan(z))","sqrt(sin(creal(z))^2+sinh(cimag(z))^2)/sqrt(cos(creal(z))^2+sinh(cimag(z))^2)",[],"complex_norm_tan"),
		Case("Tanh","cabs(ctanh(z))","sqrt(sinh(creal(z))^2+sin(cimag(z))^2)/sqrt(sinh(creal(z))^2+cos(cimag(z))^2)",[],"complex_norm_tanh"),
		Case("SinSquared","cabs(csin(z))^2","sin(creal(z))^2+sinh(cimag(z))^2",[]),
		Case("CosSquared","cabs(ccos(z))^2","cos(creal(z))^2+sinh(cimag(z))^2",[]),
		Case("SinhSquared","cabs(csinh(z))^2","sinh(creal(z))^2+sin(cimag(z))^2",[]),
		Case("CoshSquared","cabs(ccosh(z))^2","sinh(creal(z))^2+cos(cimag(z))^2",[]),
		Case("SinPartialDomain","cabs(csin(1/z))","z≠0",[],"",true),
		Case("CosPartialDomain","cabs(ccos(1/z))","z≠0",[],"",true),
		Case("SinhPartialDomain","cabs(csinh(1/z))","z≠0",[],"",true),
		Case("CoshPartialDomain","cabs(ccosh(1/z))","z≠0",[],"",true),
		Case("SinUndefined","cabs(csin(undefined(ℂ)))","false",[],"",true),
		Case("CosUndefined","cabs(ccos(undefined(ℂ)))","false",[],"",true),
		Case("SinhUndefined","cabs(csinh(undefined(ℂ)))","false",[],"",true),
		Case("CoshUndefined","cabs(ccosh(undefined(ℂ)))","false",[],"",true),
		Case("TanUndefined","cabs(ctan(undefined(ℂ)))","false",[],"",true),
		Case("TanhUndefined","cabs(ctanh(undefined(ℂ)))","false",[],"",true),
		Case("SinFalseMask","[false]*cabs(csin(undefined(ℂ)))","0",[]),
		Case("CosFalseMask","[false]*cabs(ccos(undefined(ℂ)))","0",[]),
		Case("SinhFalseMask","[false]*cabs(csinh(undefined(ℂ)))","0",[]),
		Case("CoshFalseMask","[false]*cabs(ccosh(undefined(ℂ)))","0",[]),
		Case("TanFalseMask","[false]*cabs(ctan(undefined(ℂ)))","0",[]),
		Case("TanhFalseMask","[false]*cabs(ctanh(undefined(ℂ)))","0",[]),
		Case("SinReal","cabs(csin(toℂ(x)))","abs(sin(x))",[]),
		Case("CosReal","cabs(ccos(toℂ(x)))","abs(cos(x))",[]),
		Case("SinhReal","cabs(csinh(toℂ(x)))","abs(sinh(x))",[]),
		Case("CoshReal","cabs(ccosh(toℂ(x)))","cosh(x)",[]),
		Case("SinImaginary","cabs(csin(ⅈ*toℂ(x)))","abs(sinh(x))",[]),
		Case("CosImaginary","cabs(ccos(ⅈ*toℂ(x)))","cosh(x)",[]),
		Case("SinhImaginary","cabs(csinh(ⅈ*toℂ(x)))","abs(sin(x))",[]),
		Case("CoshImaginary","cabs(ccosh(ⅈ*toℂ(x)))","abs(cos(x))",[]),
		Case("SinLog","cabs(csin(π/2+ⅈ*log(2)))","5/4",[]),
		Case("CosLog","cabs(ccos(π/2+ⅈ*log(2)))","3/4",[]),
		Case("SinhLog","cabs(csinh(log(2)+ⅈ*π/2))","5/4",[]),
		Case("CoshLog","cabs(ccosh(log(2)+ⅈ*π/2))","3/4",[]),
		Case("TanLog","cabs(ctan(ⅈ*log(2)))","3/5",[]),
		Case("TanhLog","cabs(ctanh(log(2)))","3/5",[]),
		Case("TanPole","cabs(ctan(toℂ(π/2)))","false",[],"",true),
		Case("TanhPole","cabs(ctanh(ⅈ*π/2))","false",[],"",true),
		Case("TanZero","cabs(ctan(0))","0",[]),
		Case("TanhZero","cabs(ctanh(0))","0",[]),
		Case("TanPoleFalseMask","[false]*cabs(ctan(toℂ(π/2)))","0",[]),
		Case("TanhPoleFalseMask","[false]*cabs(ctanh(ⅈ*π/2))","0",[]),
		Case("SinUnknownMask","[p]*cabs(csin(z))","[p]*sqrt(sin(creal(z))^2+sinh(cimag(z))^2)",[]),
		Case("TanUnknownMask","[p]*cabs(ctan(z))","[p]*(sqrt(sin(creal(z))^2+sinh(cimag(z))^2)/sqrt(cos(creal(z))^2+sinh(cimag(z))^2))",[]),
		Case("SinAssumedReal","cabs(csin(z))","abs(sin(creal(z)))",["cimag(z)=0"]),
		Case("SqrtUndefined","sqrt(undefined(ℝ))","false",[],"",true),
		Case("LogUndefined","clog(undefined(ℂ))","false",[],"",true),
		Case("GammaUndefined","cgamma(undefined(ℂ))","false",[],"",true),
		Case("CastUndefined","toℂ(undefined(ℝ))","false",[],"",true),
		Case("CoshAssumedImaginary","cabs(ccosh(z))","abs(cos(cimag(z)))",["creal(z)=0"])
	];
}
int main(string[] args){
	enforce(args.length==2);mkdirRecurse(args[1]);
	foreach(c;cases()){
		auto owner=Session.open(),a=owner.arena;Syntax s;s.declare("z:ℂ,x:ℝ,p:𝔹");
		Term[] facts;foreach(f;c.facts) facts~=s.parse(a,f);
		if(c.input.indexOf("undefined(")>=0){
			FunctionSyntax fs;fs.declare("z:ℂ,x:ℝ,p:𝔹");
			auto r=fs.run(a,c.input,facts,Options(DensityMode.preserve,true),c.domain),out_=fs.format(a,r);
			auto expected=fs.run(a,c.expected,facts),fast=fs.run(a,c.input,facts,Options.init,c.domain);
			enforce(!r.exhausted&&!expected.exhausted&&!fast.exhausted&&out_==fs.format(a,expected)&&out_==fs.format(a,fast),c.name~": "~out_);
			auto again=fs.run(a,out_,facts);enforce(!again.exhausted&&out_==fs.format(a,again),c.name~" round trip");
			write(buildPath(args[1],c.name~".lean"),fs.exportCertificate(a,r));writeln(c.name,": ",out_);continue;
		}
		auto input=s.parse(a,c.input);if(c.domain) input=definedness(a,input);
		auto expected=simplify(a,s.parse(a,c.expected,a.sort(input)),facts),r=simplify(a,input,facts,Options(DensityMode.preserve,true));
		enforce(!r.exhausted&&!expected.exhausted&&r.output==expected.output,c.name~": "~s.format(a,r.output)~"; expected "~s.format(a,expected.output));
		auto fast=simplify(a,input,facts);enforce(!fast.exhausted&&fast.output==r.output,c.name~" trace");
		auto again=simplify(a,r.output,facts);enforce(!again.exhausted&&again.output==r.output,c.name~" idempotence");
		auto roundtrip=simplify(a,s.parse(a,s.format(a,r.output),a.sort(r.output)),facts);enforce(!roundtrip.exhausted&&roundtrip.output==r.output,c.name~" round trip");
		auto proof=exportLean(a,r);if(c.law.length) enforce(proof.indexOf("r_"~c.law)>=0,c.name~" law path");
		write(buildPath(args[1],c.name~".lean"),proof);writeln(c.name,": ",s.format(a,r.output));
	}
	writeln(cases().length," trigonometric magnitude cases");return 0;
}
