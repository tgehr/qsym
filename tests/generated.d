module generated_tests;
import qsym.ir;
import qsym.spec:ruleCode;
import qsym.generated.rules;

@safe unittest{
	auto session=Session.open(); auto a=session.arena;
	auto x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1);
	auto r=rewrite(a,a.add(a.add(x,y),a.real_(0)),true);
	assert(r.applied&&r.result==a.add(x,y));
	assert(r.rule==ruleCode("σύγκρουση")&&r.bindings==[x,y]);
	r=rewrite(a,a.add(x,a.real_(0)),true);
	assert(r.applied&&r.result==x&&r.rule==ruleCode("απλό"));
	auto z=a.variable(Sort.complex,0);
	r=rewrite(a,a.mul(a.complex(1),z),true);
	assert(r.applied&&r.result==z&&r.rule==ruleCode("theorem"));
	r=rewrite(a,a.mask(a.boolean(false),a.real_(1)),true);
	assert(r.applied&&r.result==a.real_(0)&&r.bindings.length==0);
	r=rewrite(a,a.mask(a.boolean(false),a.real_(long.min)),false);
	assert(r.applied&&r.result==a.real_(0));
	r=rewrite(a,a.mask(a.boolean(true),a.real_(long.min)),true);
	assert(r.applied&&r.result==a.real_(long.min));
	r=rewrite(a,a.mask(a.boolean(false),a.complex(0,1)),true);
	assert(r.applied&&r.result==a.complex(0));
}

void main(){}
