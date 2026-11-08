module region_tests;
import qsym;
import qsym.derive:Derivation;
import std.file:write,mkdirRecurse;
import std.path:buildPath;
import std.exception:enforce;
import std.stdio:writeln;
@safe:

private Result bridge(Arena a,Sort sort,Op op){
	auto raw=a.number(Number(op==Op.add?0:1),sort),native=raw;
	foreach(i;0..32){
		auto atom=a.mask(a.variable(Sort.boolean,i),a.inv(a.variable(sort,i)));
		raw=op==Op.add?a.add(atom,raw,true):a.mul(atom,raw,true);
		native=op==Op.add?a.add(native,atom):a.mul(native,atom);
	}
	auto d=new Derivation(a,true);
	Result r; r.input=r.proofInput=raw; r.output=native; r.traced=true;
	r.derivation=d; r.certificate=d.ac(raw,native,op,0);
	return r;
}

unittest{
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]){
		auto owner=Session.open(); auto a=owner.arena; auto r=bridge(a,s,op);
		assert(a.canonical(r.input)==r.output);
		assert(a.node(r.output).arity==32&&a.postorder(r.output).length==129);
		auto inputs=a.operands(r.output),size=a.length;
		foreach(i;0..64){
			auto reversed=inputs.dup;
			import std.algorithm:reverse;
			reverse(reversed);
			assert(a.region(op,s,reversed)==r.output);
		}
		assert(a.length==size,"permutations allocated new terms");
	}
}

@system void main(string[] args){
	enforce(args.length==2,"usage: region-tests DIRECTORY"); mkdirRecurse(args[1]);
	foreach(s;[Sort.real_,Sort.complex]) foreach(op;[Op.add,Op.mul]){
		auto owner=Session.open(); auto a=owner.arena;
		auto name="Raw"~(s==Sort.real_?"Real":"Complex")~(op==Op.add?"Sum":"Product");
		write(buildPath(args[1],name~".lean"),exportLean(a,bridge(a,s,op)));
	}
	foreach(op;[Op.add,Op.mul]){
		auto owner=Session.open(); auto a=owner.arena;
		auto atom=a.mask(a.variable(Sort.boolean,0),a.inv(a.variable(Sort.real_,0)));
		auto input=a.region(op,Sort.real_,[Operand(atom,257)]);
		auto r=simplify(a,input,Options(DensityMode.preserve,true));
		enforce(!r.exhausted,"counted normalization exhausted");
		write(buildPath(args[1],op==Op.add?"CountedSum.lean":"CountedProduct.lean"),exportLean(a,r));
	}
	writeln("Wrote counted-region certificates.");
}
