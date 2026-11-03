module qsym.domain;
import qsym.ir;
import std.conv:to;
@safe:

/// Both bounds coincide for the initial grammar. When incomplete analysis is
/// introduced, preserve must => Defined => may. Unknown must be (False, True).
struct DomainBounds{
	string must,may;
	bool exact;
	bool everywhere;
}

bool isGuardedInverse(Arena a,Term t){
	auto n=a.node(t);
	if(n.op!=Op.mask) return false;
	auto p=a.node(a.at(n.a)),v=a.node(a.at(n.b));
	return p.op==Op.nonzero&&v.op==Op.inv&&p.a==v.a;
}

/// Diagnostic formulas are not proof objects. exportLean also emits kernel-
/// checked theorems for these exact domains, including the guarded-inverse case.
DomainBounds domain(Arena a,Term root){
	string[] formulas=new string[a.length];
	bool[] top=new bool[a.length];
	foreach(i;a.postorder(root)){
		auto t=a.at(i),n=a.node(t);
		string f;
		bool total;
		final switch(n.op){
			case Op.realLit,Op.complexLit,Op.boolLit,Op.variable,Op.lebesgue:
				f="True"; total=true; break;
			case Op.add,Op.mul,Op.densityAt:
				total=top[n.a]&&top[n.b];
				f=total?"True":"(D(%"~to!string(n.a)~") and D(%"~to!string(n.b)~"))"; break;
			case Op.inv:
				f="defined(%"~to!string(n.a)~") and value(%"~to!string(n.a)~") != 0"; break;
			case Op.nonzero,Op.conj,Op.puncture,Op.forget:
				f=formulas[n.a]; total=top[n.a]; break;
			case Op.mask:
				if(isGuardedInverse(a,t)){
					auto child=a.node(a.at(n.b)).a;
					f=formulas[child]; total=top[child];
				}else{
					auto p=a.node(a.at(n.a));
					if(p.op==Op.boolLit&&p.value==0){ f="True"; total=true; }
					else if(p.op==Op.boolLit&&p.value==1){ f=formulas[n.b]; total=top[n.b]; }
					else f="(value(%"~to!string(n.a)~") = false or (value(%"~
						to!string(n.a)~") = true and D(%"~to!string(n.b)~")))";
				}
				break;
		}
		formulas[i]=f; top[i]=total;
	}
	return DomainBounds(formulas[root.id],formulas[root.id],true,top[root.id]);
}

unittest{
	auto session=Session.open();
	auto a=session.arena;
	auto x=a.variable(Sort.real_,0);
	assert(!domain(a,a.inv(x)).everywhere);
	assert(domain(a,a.mask(a.nonzero(x),a.inv(x))).everywhere);
	assert(domain(a,a.mask(a.boolean(false),a.inv(a.real_(0)))).everywhere);
	assert(!domain(a,a.mul(a.real_(0),a.inv(a.real_(0)))).everywhere);
}
