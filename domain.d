module qsym.domain;
import qsym.ir;
import std.conv:to;
@safe:

package Term domainPredicate(Arena a,Term t){
	auto n=a.view(t),f=cast(Builtin)n.value;
	if(builtinInfo(f).total) return a.boolean(true);
	auto x=a.at(n.a),y=n.arity==2?a.at(n.b):Term.init;
	auto zero=a.number(Number(0),a.sort(x));
	auto call(Builtin b,Term v){ return a.call(b,[v]); }
	auto nz(Term v){ return a.nonzero(v); }
	auto eq0(Term v){ return a.not_(nz(v)); }
	auto poles(Term v){ return a.or_(a.lt(a.real_(0),v),a.not_(call(Builtin.isIntR,v))); }
	switch(f){
		case Builtin.invQ,Builtin.logC,Builtin.argC:return nz(x);
		case Builtin.sqrtR:return a.le(zero,x);
		case Builtin.logR,Builtin.log2R,Builtin.log10R:return a.lt(zero,x);
		case Builtin.tanR:return nz(call(Builtin.cosR,x));
		case Builtin.tanC:return nz(call(Builtin.cosC,x));
		case Builtin.tanhC:return nz(call(Builtin.coshC,x));
		case Builtin.asinR,Builtin.acosR:return a.and_(a.le(a.real_(-1),x),a.le(x,a.real_(1)));
		case Builtin.acoshR:return a.le(a.real_(1),x);
		case Builtin.atanhR:return a.and_(a.lt(a.real_(-1),x),a.lt(x,a.real_(1)));
		case Builtin.atanC,Builtin.atanhC:
			auto c=f==Builtin.atanC?a.complex(0,1):a.complex(1);
			auto minus=f==Builtin.atanC?a.complex(0,-1):a.complex(-1);
			return a.and_(nz(a.add(x,minus,true)),nz(a.add(x,c,true)));
		case Builtin.powQZ,Builtin.powRZ,Builtin.powCZ:return a.or_(nz(x),a.le(a.integer(0),y));
		case Builtin.powerR:return a.and_(a.or_(a.le(zero,x),call(Builtin.isIntR,y)),
			a.or_(nz(x),a.le(zero,y)));
		case Builtin.powerC:return a.or_(nz(x),
			a.and_(a.le(a.real_(0),call(Builtin.reC,y)),eq0(call(Builtin.imC,y))));
		case Builtin.atan2R:return a.or_(nz(y),nz(x));
		case Builtin.makeQ:return nz(y);
		case Builtin.subN:return a.le(y,x);
		case Builtin.gammaR:return poles(x);
		case Builtin.lgammaR:return a.and_(poles(x),nz(call(Builtin.gammaR,x)));
		case Builtin.gammaC:return a.or_(nz(call(Builtin.imC,x)),poles(call(Builtin.reC,x)));
		default:assert(0,"missing built-in domain predicate");
	}
}

package Term[] domainConditions(Arena a,Term root){
	auto order=a.viewPostorder(root);
	Term[] conditions=new Term[a.length];
	Term both(Term x,Term y){ auto n=a.view(x); return n.op==Op.boolLit?(n.value?y:x):a.and_(x,y); }
	foreach(i;order){
		auto n=a.view(a.at(i)); Term d;
		final switch(n.op){
			case Op.realLit,Op.complexLit,Op.boolLit,Op.variable,Op.lebesgue,Op.numberLit:
				d=a.boolean(true); break;
			case Op.builtin:
				d=n.arity?conditions[n.a]:a.boolean(true);
				if(n.arity==2) d=both(d,conditions[n.b]);
				if(!builtinInfo(cast(Builtin)n.value).total) d=both(d,domainPredicate(a,a.at(i)));
				break;
			case Op.add,Op.mul,Op.densityAt,Op.lt,Op.le:
				d=both(conditions[n.a],conditions[n.b]); break;
			case Op.inv:d=both(conditions[n.a],a.nonzero(a.at(n.a))); break;
			case Op.nonzero,Op.conj,Op.puncture,Op.forget,Op.pow,Op.not_,Op.abs:
				d=conditions[n.a]; break;
			case Op.mask,Op.and_,Op.or_:
				auto guard=a.at(n.a);
				if(n.op!=Op.or_) guard=a.not_(guard);
				d=both(conditions[n.a],a.or_(guard,conditions[n.b])); break;
		}
		conditions[i]=d;
	}
	return conditions;
}

Term definedness(Arena a,Term root){ return domainConditions(a,root)[root.id]; }

import qsym.simplify:Result,Options,simplify;
Result simplifyDomain(Arena a,Term root,Term[] facts=[],Options options=Options.init){
	options.distributeLogic=false;
	return simplify(a,definedness(a,root),facts,options);
}

/// Both bounds coincide for the initial grammar. When incomplete analysis is
/// introduced, preserve must => Defined => may. Unknown must be (False, True).
struct DomainBounds{
	string must,may;
	bool exact;
	bool everywhere;
}

bool isGuardedInverse(Arena a,Term t){
	auto n=a.view(t);
	if(n.op!=Op.mask) return false;
	auto p=a.view(a.at(n.a)),v=a.view(a.at(n.b));
	return p.op==Op.nonzero&&v.op==Op.inv&&p.a==v.a;
}

/// Diagnostic formulas are not proof objects. exportLean also emits kernel-
/// checked theorems for these exact domains, including the guarded-inverse case.
DomainBounds domain(Arena a,Term root){
	string[] formulas=new string[a.length];
	bool[] top=new bool[a.length];
	foreach(i;a.viewPostorder(root)){
		auto t=a.at(i),n=a.view(t);
		string f;
		bool total;
		final switch(n.op){
			case Op.realLit,Op.complexLit,Op.boolLit,Op.variable,Op.lebesgue,Op.numberLit:
				f="True"; total=true; break;
			case Op.builtin:
				auto info=builtinInfo(cast(Builtin)n.value);
				total=info.total&&(!n.arity||top[n.a])&&(n.arity<2||top[n.b]);
				if(total) f="True";
				else f=(n.arity?"D(%"~to!string(n.a)~") and ":"")~
					(n.arity==2?"D(%"~to!string(n.b)~") and ":"")~info.code~".domain(values)";
				break;
			case Op.add,Op.mul,Op.densityAt,Op.lt,Op.le:
				total=top[n.a]&&top[n.b];
				f=total?"True":"(D(%"~to!string(n.a)~") and D(%"~to!string(n.b)~"))"; break;
			case Op.inv:
				f="defined(%"~to!string(n.a)~") and value(%"~to!string(n.a)~") != 0"; break;
			case Op.nonzero,Op.conj,Op.puncture,Op.forget,Op.pow,Op.not_,Op.abs:
				f=formulas[n.a]; total=top[n.a]; break;
			case Op.mask:
				if(isGuardedInverse(a,t)){
					auto child=a.view(a.at(n.b)).a;
					f=formulas[child]; total=top[child];
				}else{
					auto p=a.view(a.at(n.a));
					if(p.op==Op.boolLit&&p.value==0){ f="True"; total=true; }
					else if(p.op==Op.boolLit&&p.value==1){ f=formulas[n.b]; total=top[n.b]; }
					else f="(value(%"~to!string(n.a)~") = false or (value(%"~
						to!string(n.a)~") = true and D(%"~to!string(n.b)~")))";
				}
				break;
			case Op.and_,Op.or_:
				auto p=a.view(a.at(n.a));
				auto stop=n.op==Op.and_?0:1;
				total=top[n.a]&&(top[n.b]||p.op==Op.boolLit&&p.value==stop);
				f=total?"True":"(value(%"~to!string(n.a)~") = "~(stop?"true":"false")~
					" or (value(%"~to!string(n.a)~") = "~(stop?"false":"true")~" and D(%"~to!string(n.b)~")))";
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
