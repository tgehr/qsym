module qsym.tests.rules;
import qsym.ir;
import qsym.spec;
import qsym.derive;
import qsym.generated.rules;
import std.exception:assertThrown;
@safe:

unittest{
	auto lemma=Parser("lemma distribute(x:ℝ,y:ℝ,z:ℝ):x·(y+z)⇒x·y+x·z;").parse()[0];
	assert(!lemma.automatic&&!lemma.equality&&!lemma.inference);
	assertThrown(Parser("rule distribute(x:ℝ,y:ℝ,z:ℝ):x·(y+z)⇒x·y+x·z;").parse());
	auto eq=Parser("equation associate(x:ℝ,y:ℝ,z:ℝ):(x+y)+z≡x+(y+z);").parse()[0];
	assert(eq.equality&&!eq.automatic);
	auto f=Parser("fact square(x:ℝ,n:ℕ):0≤x^(n+n);").parse()[0];
	assert(f.inference&&f.parameters[1].natural);
	assertThrown(Parser("rule bad(x:ℝ):|x|⇒x when x;").parse());
	assertThrown(Parser("lemma bad(x:ℝ,n:ℕ):x^n⇒x when defined(n);").parse());
	assertThrown(Parser("fact bad(x:ℝ):x;").parse());
}

unittest{
	auto owner=Session.open(); auto a=owner.arena;
	auto x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1);
	auto p=a.le(a.real_(0),x);
	Term[] args;
	assert(match(a,Law.real_nonnegative_square,-1,a.le(a.real_(0),a.pow(x,6)),args));
	assert(args==[x,a.real_(3)]);
	args=null;
	assert(!match(a,Law.real_nonnegative_square,-1,a.le(a.real_(0),a.pow(x,3)),args));
	args=null;
	assert(!match(a,Law.real_lt_upper,2,p,args));
	assertThrown(instantiate(a,Law.real_pow_join,[x,a.real_(uint.max),a.real_(1)]));
	auto d=new Derivation(a,true),rule=instantiate(a,Law.real_abs_nonnegative,[x]);
	assertThrown(d.rule(rule,[],0));
	assertThrown(d.rule(rule,[d.refl(a.boolean(true))],0));
	auto ctx=d.enter(0,p,true),premise=d.assumption(ctx,[],ctx);
	auto proof=d.rule(rule,[premise],ctx);
	assert(proof.before==a.abs(x)&&proof.after==x);
	assertThrown(d.rule(rule,[premise],0));
	assertThrown(d.numeric(a.add(x,a.real_(1)),a.real_(2),0));
	assertThrown(d.ac(a.add(x,y),a.add(x,x),Op.add,0));
}
