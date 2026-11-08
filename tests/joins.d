module qsym.tests.joins;
import qsym;
import qsym.derive:Derivation,Proof;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.conv:to;
import std.stdio:writeln;
@safe:

private Result mapped(Arena a,Sort s,Op op,uint count,bool trace){
	Operand[] inputs,outputs;
	foreach(i;0..count){
		auto x=a.variable(s,i);
		inputs~=Operand(a.inv(a.inv(x)),1); outputs~=Operand(x,1);
	}
	auto r=simplify(a,a.region(op,s,inputs),Options(DensityMode.preserve,trace));
	enforce(!r.exhausted&&r.output==a.region(op,s,outputs),"region mapping failed");
	return r;
}
private Result joined(Arena a,Sort s,Op op,string kind){
	auto d=new Derivation(a,true); Proof[] ps;
	foreach(i;0..7){
		auto x=a.variable(s,kind=="Merged"?0:i),y=a.variable(s,i+7),before=x;
		if(kind=="Grouped") before=op==Op.add?a.add(x,y):a.mul(x,y);
		if(kind=="Partial") before=a.mask(a.variable(Sort.boolean,i),a.inv(x));
		if(kind=="Unit"&&i%2) before=a.number(Number(op==Op.add?0:1),s);
		// Use one shared derivation so every premise belongs to this certificate.
		auto input=a.inv(a.inv(before));
		import qsym.generated.rules:Law,instantiate;
		auto law=s==Sort.real_?Law.real_inv_inv:Law.complex_inv_inv;
		auto p=d.rule(instantiate(a,law,[before]),[],0);
		enforce(p.before==input&&p.after==before,"inverse premise mismatch");
		ps~=kind=="Counted"?d.repeated(p,257,op,0):p;
	}
	auto p=d.join(ps,op,s,0);
	Result r; r.input=r.proofInput=p.before; r.output=p.after; r.traced=true; r.derivation=d; r.certificate=p;
	return r;
}
unittest{
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]) foreach(count;[3u,16u,64u]){
		auto owner=Session.open(); auto a=owner.arena;
		auto fast=mapped(a,s,op,count,false),checked=mapped(a,s,op,count,true);
		assert(fast.output==checked.output);
		assert(checked.derivation.deductions.length<=count+3,"rebuilt and certified every intermediate region");
		assert(exportLean(a,checked).length<4000*count,"region mapping certificate grew superlinearly");
		assert(simplify(a,checked.output).output==checked.output);
	}
}
unittest{
	auto owner=Session.open(); auto a=owner.arena,d=new Derivation(a,true),x=a.variable(Sort.real_,0);
	assert(d.join([],Op.add,Sort.real_,0).after==a.real_(0));
	assert(d.join([],Op.mul,Sort.complex,0).after==a.complex(1));
	assert(d.join([d.refl(x)],Op.add,Sort.real_,0).after==x);
	assert(d.join([d.refl(x),d.refl(x)],Op.add,Sort.real_,0).id==uint.max);
	assertThrown(d.join([d.refl(x)],Op.inv,Sort.real_,0));
	assertThrown(d.join([],Op.add,Sort.boolean,0));
	assertThrown(d.join([d.refl(x)],Op.mul,Sort.complex,0));
	auto other=Session.open(); assertThrown(d.join([d.refl(other.arena.real_(1))],Op.add,Sort.real_,0));
	auto raw=a.add(x,a.real_(1),true); assertThrown(d.join([d.refl(raw)],Op.add,Sort.real_,0));
	auto ctx=d.enter(0,a.variable(Sort.boolean,0),true);
	assertThrown(d.join([d.refl(x,ctx)],Op.add,Sort.real_,0));
	assert(d.join([d.refl(x)],Op.add,Sort.real_,ctx).context==ctx);
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]) foreach(kind;["Merged","Grouped","Partial","Unit","Counted"]){
		auto r=joined(a,s,op,kind);
		assert(simplify(a,r.input).output==simplify(a,r.output).output);
		exportLean(a,r);
	}
}
@system void main(string[] args){
	enforce(args.length==2,"usage: join-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]){
		auto prefix=(s==Sort.real_?"Real":"Complex")~(op==Op.add?"Sum":"Product");
		foreach(count;[3u,64u]){
			auto owner=Session.open(); auto a=owner.arena;
			write(buildPath(args[1],prefix~to!string(count)~".lean"),exportLean(a,mapped(a,s,op,count,true)));
		}
		foreach(kind;["Merged","Grouped","Partial","Unit","Counted"]){
			auto owner=Session.open(); auto a=owner.arena;
			write(buildPath(args[1],prefix~kind~".lean"),exportLean(a,joined(a,s,op,kind)));
		}
	}
	writeln("Wrote region mapping certificates.");
}
