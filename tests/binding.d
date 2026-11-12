module binding_tests;
import qsym;
import qsym.binding;
import qsym.types:TypeKind,TypePool;
import std.exception:enforce,assertThrown;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
@safe:

private struct Artifact{ string name,code; }
private Artifact[] run(){
	auto owner=Session.open(),a=owner.arena;
	auto b=new Bindings(a),s=b.empty(),nat=b.scalarType(Sort.natural),realType=b.scalarType(Sort.real_);
	auto sn=b.push(s,nat),snn=b.push(sn,nat);
	auto plus=a.add(a.variable(Sort.natural,0),a.variable(Sort.natural,1));
	auto x=b.variable(snn,1),y=b.variable(snn,0);
	auto add=b.lambda(b.lambda(b.primitive(plus,[x,y])));
	auto one=b.scalar(s,a.natural_(1)),two=b.scalar(s,a.natural_(2));
	Artifact[] artifacts;
	void check(string name,BoundTerm input,Term expected=Term.init){
		auto r=b.normalize(input);
		enforce(!r.exhausted,name~" exhausted");
		enforce(b.normalize(r.output).output==r.output,name~" not idempotent");
		enforce(b.type(input)==b.type(r.output)&&b.context(input)==b.context(r.output),name~" changed type or context");
		if(expected!=Term.init) enforce(simplify(a,b.lower(r.output)).output==simplify(a,expected).output,name~" wrong result");
		artifacts~=Artifact(name,b.exportLean(r,expected!=Term.init));
	}
	auto curried=b.apply(b.apply(add,one),two);
	check("Curried",curried,a.natural_(3));
	check("PartialApplication",b.apply(add,one));
	check("Lambda",add);
	check("Shadow",b.apply(b.apply(b.lambda(b.lambda(y)),one),two),a.natural_(2));
	check("Capture",b.apply(b.apply(b.lambda(b.lambda(x)),one),two),a.natural_(1));
	auto global=a.variable(Sort.natural,0);
	check("Global",b.apply(b.lambda(b.scalar(sn,global)),two),global);
	auto fty=b.typePool.function_(nat,nat),sf=b.push(s,fty),sfn=b.push(sf,nat);
	auto apply=b.lambda(b.lambda(b.apply(b.variable(sfn,1),b.variable(sfn,0))));
	auto identity=b.lambda(b.variable(sn,0));
	check("IdentityArithmetic",b.apply(identity,b.primitive(plus,[one,two])),a.natural_(3));
	auto sharedBody=b.variable(sn,0);
	foreach(i;0..8) sharedBody=b.primitive(plus,[sharedBody,sharedBody]);
	check("SharedBody",b.apply(b.lambda(sharedBody),two),a.natural_(512));
	enforce(artifacts[$-1].code.length<50_000,"expanded a shared binding proof");
	check("HigherOrder",b.apply(b.apply(apply,identity),two),a.natural_(2));
	auto self=b.lambda(b.variable(sf,0));
	check("FunctionArgument",b.apply(b.apply(self,identity),one),a.natural_(1));
	check("OpenApplication",b.apply(b.lambda(b.variable(snn,1)),b.variable(sn,0)));
	check("OpenFunction",b.apply(b.lambda(b.variable(b.push(sf,nat),1)),b.scalar(sf,a.natural_(0))));
	auto sr=b.push(s,realType),zr=b.scalar(s,a.real_(0)),zeroBody=b.scalar(sr,a.real_(0));
	auto undefined=a.inv(a.real_(0));
	check("IdentityPartial",b.apply(b.lambda(b.variable(sr,0)),b.scalar(s,undefined)),undefined);
	auto strict=b.apply(b.lambda(zeroBody),b.scalar(s,undefined));
	check("StrictUnused",strict);
	auto strictResult=b.normalize(strict).output;
	enforce(b.node(strictResult).op==BoundOp.sequence,"discarded undefined argument");
	assertThrown(b.lower(strictResult));
	auto badBody=b.scalar(sr,undefined);
	check("UndefinedBody",b.lambda(badBody));
	check("UndefinedApplication",b.apply(b.lambda(badBody),zr),undefined);
	auto hidden=a.mask(a.boolean(false),undefined);
	check("MaskedArgument",b.apply(b.lambda(zeroBody),b.scalar(s,hidden)));
	check("MaskedBody",b.apply(b.lambda(b.scalar(sr,hidden)),zr),a.real_(0));
	check("PrimitiveUnary",b.apply(b.lambda(b.primitive(a.inv(a.real_(1)),[b.variable(sr,0)])),b.scalar(s,a.real_(2))),a.inv(a.real_(2)));
	check("PrimitiveMask",b.apply(b.lambda(b.primitive(a.mask(a.boolean(false),a.real_(1)),[b.scalar(sr,a.boolean(false)),b.variable(sr,0)])),b.scalar(s,undefined)));
	foreach(sort;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean]){
		auto ctx=b.push(s,b.scalarType(sort));
		auto v=b.scalar(s,a.variable(sort,7));
		check("Identity"~sortName(sort),b.apply(b.lambda(b.variable(ctx,0)),v),a.variable(sort,7));
	}
	auto budget=b.normalize(curried,0);
	enforce(budget.exhausted&&budget.steps==0&&budget.output==curried,"zero budget changed term");
	artifacts~=Artifact("BudgetZero",b.exportLean(budget));
	budget=b.normalize(curried,1); enforce(budget.exhausted&&budget.steps==1,"one-step budget");
	artifacts~=Artifact("BudgetOne",b.exportLean(budget));
	assertThrown(b.variable(s,0));
	assertThrown(b.variable(sn,1));
	assertThrown(b.lambda(one));
	assertThrown(b.apply(one,two));
	assertThrown(b.apply(identity,zr));
	assertThrown(b.sequence(one,b.variable(sn,0)));
	assertThrown(b.primitive(plus,[one]));
	assertThrown(b.primitive(plus,[one,zr]));
	assertThrown(b.primitive(plus,[one,b.variable(sn,0)]));
	assertThrown(b.rename(b.variable(sn,0),s,[0]));
	assertThrown(b.rename(b.variable(sn,0),sr,[0]));
	assertThrown(b.substitute(b.variable(sn,0),s,[zr]));
	assertThrown(b.substitute(b.variable(sn,0),s,[]));
	assertThrown(b.beta(b.variable(sn,0),zr));
	assertThrown(b.lower(identity));
	auto foreign=new Bindings(a);
	assertThrown(b.type(foreign.scalar(foreign.empty(),a.natural_(1))));
	assertThrown(b.variable(foreign.empty(),0));
	assertThrown(b.push(s,(new TypePool).primitive(TypeKind.natural)));
	assertThrown(b.push(s,b.typePool.primitive(TypeKind.unit)));
	assertThrown(b.push(s,b.typePool.array(nat)));
	assertThrown(b.scalar(s,a.lebesgue()));
	return artifacts;
}

unittest{ run(); }

@system void main(string[] args){
	enforce(args.length==2,"usage: binding-tests DIRECTORY"); mkdirRecurse(args[1]);
	auto artifacts=run();
	foreach(a;artifacts) write(buildPath(args[1],a.name~".lean"),a.code);
	import std.stdio:writeln;
	writeln(artifacts.length," binding certificates");
}
