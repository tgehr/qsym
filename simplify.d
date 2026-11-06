module qsym.simplify;
import qsym.ir;
import qsym.derive:Derivation,Proof;
import qsym.budget:Budget;
import qsym.engine:Engine;
import std.exception:enforce;
@safe:

enum DensityMode{ preserve,distributionOnly }
struct Options{
	DensityMode densityMode=DensityMode.preserve;
	bool trace=false;
	size_t maxRewrites=100_000;
	size_t maxTerms=256;
	size_t maxAlgebraWork=1_000_000;
	size_t maxCoefficientWords=512;
}
struct Result{
	Term input;
	/// In distributionOnly mode this is forget(input), with type Measure.
	Term proofInput;
	Term output;
	bool exhausted;
	bool traced;
	Derivation derivation;
	Proof certificate;
	Term[] assumptions;
}

/// Proof search only. Generated Lean certificates are the trust boundary.
/// Results agree with the original wherever the original was defined; the
/// result may have a larger domain. Erasure remains an explicit root operation.
Result simplify(Arena a,Term input,Options options=Options.init){
	return simplify(a,input,[],options);
}

/// Facts are defined, true Boolean expressions. Certificates retain them as hypotheses.
Result simplify(Arena a,Term input,Term[] facts,Options options=Options.init){
	a.check(input);
	foreach(f;facts) enforce(a.sort(f)==Sort.boolean,"simplification facts must be Bool");
	auto root=input;
	if(options.densityMode==DensityMode.distributionOnly){
		enforce(a.sort(input)==Sort.density,
			"distributionOnly requires a density-valued root; it is not a global congruence flag");
		root=a.forget(input);
	}
	Result result;
	result.input=input; result.proofInput=root; result.traced=options.trace;
	result.assumptions=facts.dup;
	auto d=new Derivation(a,options.trace);
	auto budget=new Budget(options.maxAlgebraWork,options.maxTerms,options.maxCoefficientWords);
	auto engine=new Engine(a,d,budget,options.maxRewrites);
	auto context=engine.assume(facts);
	result.certificate=engine.go(root,context);
	result.derivation=d; result.output=result.certificate.after;
	result.exhausted=budget.exhausted;
	return result;
}

enum Equivalence{ agreeOnCommonDomain,unknown }
/// A shared normal form proves agreement where BOTH inputs are defined. It
/// does not prove equality of domains; different forms remain inconclusive.
Equivalence equivalent(Arena a,Term left,Term right,Options options=Options.init){
	return equivalent(a,left,right,[],options);
}
Equivalence equivalent(Arena a,Term left,Term right,Term[] facts,Options options=Options.init){
	enforce(a.sort(left)==a.sort(right),"equivalence requires equal types");
	return simplify(a,left,facts,options).output==simplify(a,right,facts,options).output
		?Equivalence.agreeOnCommonDomain:Equivalence.unknown;
}

unittest{
	auto session=Session.open();
	auto a=session.arena;
	auto x=a.variable(Sort.real_,0);
	auto one=a.real_(1),zero=a.real_(0);
	auto r=simplify(a,a.add(a.mul(x,one),zero),Options(DensityMode.preserve,true));
	assert(r.output==x&&r.traced&&!r.exhausted);
	auto bad=a.mul(zero,a.inv(zero));
	assert(simplify(a,bad).output==zero); // extends the empty original domain
	assert(simplify(a,a.mask(a.boolean(false),a.inv(zero))).output==zero);
	auto d=a.puncture(a.lebesgue());
	assert(simplify(a,d).output==d);
	auto erased=simplify(a,d,Options(DensityMode.distributionOnly,true));
	assert(erased.output==a.forget(a.lebesgue()));
	assert(a.sort(erased.output)==Sort.measure);
	assert(equivalent(a,d,a.lebesgue())==Equivalence.unknown);
	assert(equivalent(a,d,a.lebesgue(),Options(DensityMode.distributionOnly))==Equivalence.agreeOnCommonDomain);
	auto limited=simplify(a,a.add(x,zero),Options(DensityMode.preserve,true,0));
	assert(limited.exhausted&&limited.output==a.add(x,zero));
	auto z=a.variable(Sort.complex,0);
	assert(simplify(a,a.conj(a.conj(z))).output==z);
}
