module qsym.tests.counted;
import qsym;
import qsym.budget;
import qsym.field:Field;
import qsym.derive:Derivation;
import std.exception:enforce;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.conv:to;
import std.stdio:writeln;
@safe:

private Options options(){
	auto o=Options(DensityMode.preserve,true);
	o.maxTerms=8; o.maxAlgebraWork=512; return o;
}
private Result example(Arena a,Sort s,Op op,string kind){
	auto x=a.variable(s,0),y=a.variable(s,1),o=options(); o.maxAlgebraWork=100_000;
	uint n=kind=="Large"?uint.max:kind=="Partial"?65537:kind=="Mapped"?257:7;
	if(kind=="Fact"){
		auto sum=a.region(Op.add,s,[Operand(x,1_000_003)]);
		auto fact=a.not_(a.nonzero(a.sub(sum,a.number(Number(7_000_021),s))));
		auto r=simplify(a,x,[fact],o);
		enforce(!r.exhausted&&r.output==a.natural_(7),"counted affine fact failed"); return r;
	}
	if(kind=="Quadratic"){
		auto sum=a.region(Op.add,s,[Operand(a.pow(x,2),1_000_003)]);
		auto input=a.not_(a.nonzero(a.sub(sum,a.number(Number(1_000_003),s))));
		auto expected=a.or_(a.not_(a.nonzero(a.sub(x,a.number(Number(-1),s)))),a.not_(a.nonzero(a.sub(x,a.number(Number(1),s)))));
		auto r=simplify(a,input,o);
		enforce(!r.exhausted&&r.output==simplify(a,expected,o).output,"counted quadratic failed"); return r;
	}
	Term atom;
	switch(kind){
		case "Large":atom=x; break;
		case "Partial":atom=a.mask(a.variable(Sort.boolean,0),a.inv(x)); break;
		case "Mapped":atom=a.inv(a.inv(x)); break;
		case "Grouped":atom=op==Op.add?a.add(x,y):a.mul(x,y); break;
		case "Unit":atom=a.number(Number(op==Op.add?0:1),s); break;
		default:assert(0);
	}
	auto child=simplify(a,atom,o),d=child.derivation,p=d.repeated(child.certificate,n,op,0);
	Result r; r.input=r.proofInput=p.before; r.output=p.after; r.traced=true; r.derivation=d; r.certificate=p;
	return r;
}
unittest{
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]) foreach(n;[2u,3u,257u,1_000_003u,1u<<31,uint.max]){
		auto owner=Session.open(); auto a=owner.arena,x=a.variable(s,0);
		auto input=a.region(op,s,[Operand(x,n)]);
		auto expected=op==Op.add?a.mul(a.number(Number(n),s),x):a.pow(x,n);
		auto o=options(),checked=simplify(a,input,o); o.trace=false;
		auto fast=simplify(a,input,o);
		assert(!checked.exhausted&&!fast.exhausted&&checked.output==expected&&fast.output==expected,
			to!string(s)~" "~to!string(op)~" "~to!string(n));
		assert(checked.derivation.deductions.length<32,"repetition still constructs a chain of rule applications");
		assert(exportLean(a,checked).length<24_000,"repetition certificate expands its multiplicity");
	}
}
unittest{
	import std.exception:assertThrown;
	auto owner=Session.open(); auto a=owner.arena,d=new Derivation(a,true),x=a.variable(Sort.real_,0);
	assertThrown(d.repeated(d.refl(x),0,Op.add,0));
	assertThrown(d.repeated(d.refl(x),2,Op.inv,0));
	assertThrown(d.repeated(d.refl(a.boolean(true)),2,Op.add,0));
	auto ctx=d.enter(0,a.variable(Sort.boolean,0),true);
	assertThrown(d.repeated(d.refl(x,ctx),2,Op.add,0));
	foreach(s;[Sort.real_,Sort.complex]){
		foreach(op;[Op.add,Op.mul]) foreach(kind;["Partial","Mapped","Grouped","Unit"]){
			auto r=example(a,s,op,kind); assert(r.certificate.before==r.input&&r.certificate.after==r.output);
			assert(exportLean(a,r).length<100_000,"counted certificate expanded its operand");
		}
		foreach(kind;["Fact","Quadratic"]) example(a,s,Op.add,kind);
	}
}
unittest{
	foreach(s;[Sort.real_,Sort.complex]){
		auto owner=Session.open(); auto a=owner.arena,x=a.variable(s,0),y=a.variable(s,1);
		auto d=new Derivation(a,true),budget=new Budget(512,8,512);
		auto f=new Field(a,d,budget,(Term t,uint ctx)=>d.refl(t,ctx));
		auto n=1_000_003u,constant=a.number(Number(7),s);
		auto affine=a.region(Op.add,s,[Operand(x,n),Operand(constant,1)]);
		Term coefficient,remainder;
		assert(f.affine(affine,x,coefficient,remainder));
		assert(coefficient==a.number(Number(n),s)&&remainder==constant);
		auto quadratic=a.region(Op.add,s,[Operand(a.pow(x,2),n),Operand(x,3),Operand(constant,1)]);
		Term atom; Number[3] cs;
		assert(f.quadratic(quadratic,atom,cs)&&atom==x&&cs==[Number(7),Number(3),Number(n)]);
		auto expression=a.region(Op.add,s,[Operand(a.mul(x,y),n),Operand(x,1)]);
		Term factor,quotient;
		assert(f.commonFactor(expression,factor,quotient)&&factor==x);
		assert(quotient==a.add(a.mul(a.number(Number(n),s),y),a.number(Number(1),s)));
	}
}

@system void main(string[] args){
	enforce(args.length==2,"usage: counted-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]){
		foreach(kind;["Large","Partial","Mapped","Grouped","Unit"]){
			auto owner=Session.open(); auto a=owner.arena;
			auto name=(s==Sort.real_?"Real":"Complex")~(op==Op.add?"Sum":"Product")~kind;
			write(buildPath(args[1],name~".lean"),exportLean(a,example(a,s,op,kind)));
		}
	}
	foreach(s;[Sort.real_,Sort.complex]) foreach(kind;["Fact","Quadratic"]){
		auto owner=Session.open(); auto a=owner.arena;
		write(buildPath(args[1],(s==Sort.real_?"Real":"Complex")~kind~".lean"),exportLean(a,example(a,s,Op.add,kind)));
	}
	writeln("Wrote counted-fold certificates.");
}
