module qsym.simplify;
import qsym.ir;
import qsym.generated.rules;
import std.exception:enforce;
@safe:

enum DensityMode{ preserve,distributionOnly }
struct Options{
	DensityMode densityMode=DensityMode.preserve;
	bool trace=false;
	size_t maxRewrites=100_000;
}
struct Applied{ Term before; Rewrite rule; }
struct Step{ Term before,rebuilt,result; Applied[] applied; }
struct Result{
	Term input;
	/// In distributionOnly mode this is forget(input), with type Measure.
	Term proofInput;
	Term output;
	bool exhausted;
	bool traced;
	Step[] steps;
}

/// Proof search only. Generated Lean certificates are the trust boundary.
/// All child rewriting uses pointwise partial-value equality. Erasure happens
/// once, at the requested root, and cannot flow back to densityAt.
Result simplify(Arena a,Term input,Options options=Options.init){
	a.check(input);
	auto root=input;
	if(options.densityMode==DensityMode.distributionOnly){
		enforce(a.sort(input)==Sort.density,
			"distributionOnly requires a density-valued root; it is not a global congruence flag");
		root=a.forget(input);
	}
	Result result;
	result.input=input; result.proofInput=root; result.traced=options.trace;
	auto order=a.postorder(root);
	Term[] memo=new Term[a.length];
	size_t remaining=options.maxRewrites;
	foreach(i;order){
		auto original=a.at(i);
		auto n=a.node(original);
		if(n.arity>=1) enforce(memo[n.a].id!=uint.max,"postorder missing first child");
		if(n.arity==2) enforce(memo[n.b].id!=uint.max,"postorder missing second child");
		Term[] children;
		if(n.arity>=1) children~=memo[n.a];
		if(n.arity==2) children~=memo[n.b];
		auto rebuilt=a.rebuild(original,children);
		auto current=rebuilt;
		Applied[] applied;
		while(true){
			if(remaining==0){ result.exhausted=true; break; }
			auto r=rewrite(a,current,options.trace);
			if(!r.applied) break;
			if(options.trace) applied~=Applied(current,r);
			current=r.result; --remaining;
		}
		memo[i]=current;
		if(options.trace) result.steps~=Step(original,rebuilt,current,applied);
	}
	result.output=memo[root.id];
	return result;
}

enum Equivalence{ sameNormalForm,unknown }
/// Different normal forms do not prove inequivalence.
Equivalence equivalent(Arena a,Term left,Term right,Options options=Options.init){
	enforce(a.sort(left)==a.sort(right),"equivalence requires equal types");
	return simplify(a,left,options).output==simplify(a,right,options).output
		?Equivalence.sameNormalForm:Equivalence.unknown;
}

unittest{
	auto session=Session.open();
	auto a=session.arena;
	auto x=a.variable(Sort.real_,0);
	auto one=a.real_(1),zero=a.real_(0);
	auto r=simplify(a,a.add(a.mul(x,one),zero),Options(DensityMode.preserve,true));
	assert(r.output==x&&r.traced&&!r.exhausted);
	auto bad=a.mul(zero,a.inv(zero));
	assert(simplify(a,bad).output==bad); // strict 0*undefined is undefined
	assert(simplify(a,a.mask(a.boolean(false),a.inv(zero))).output==zero);
	auto d=a.puncture(a.lebesgue());
	assert(simplify(a,d).output==d);
	auto erased=simplify(a,d,Options(DensityMode.distributionOnly,true));
	assert(erased.output==a.forget(a.lebesgue()));
	assert(a.sort(erased.output)==Sort.measure);
	assert(equivalent(a,d,a.lebesgue())==Equivalence.unknown);
	assert(equivalent(a,d,a.lebesgue(),Options(DensityMode.distributionOnly))==Equivalence.sameNormalForm);
	auto limited=simplify(a,a.add(x,zero),Options(DensityMode.preserve,true,0));
	assert(limited.exhausted&&limited.output==a.add(x,zero));
	auto z=a.variable(Sort.complex,0);
	assert(simplify(a,a.conj(a.conj(z))).output==z);
}
