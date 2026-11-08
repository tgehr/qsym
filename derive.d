module qsym.derive;
import qsym.ir;
import qsym.generated.rules:Instance,instantiate;
import qsym.table:Table;
import qsym.associative:Regions;
import std.exception:enforce;
@safe:

struct Proof{ Term before,after; uint id=uint.max,context; bool known; }
struct Context{ uint parent; Term guard; bool value; }
enum Evidence{ rule,trans,congr,scoped,assumption,transport,numeric,ac }
struct DomainProof{ Term term; uint[] path; DomainProof[] children; bool found,total; uint assumption; uint fact=uint.max; }
struct Deduction{
	Evidence kind;
	Proof proof;
	Proof[] premises;
	Instance instance;
	DomainProof[] domains;
	uint assumptionScope;
	uint[] path;
	bool value;
}

// D records choices. The exporter must justify every choice with a theorem.
final class Derivation{
	Arena arena;
	bool tracing;
	Deduction[] deductions;
	Proof[] domainFacts;
	Context[] contexts=[Context.init];
	package Regions regions;
	this(Arena a,bool tracing){ arena=a; this.tracing=tracing; regions=new Regions(a); }
	Proof refl(Term t,uint context=0){ return Proof(t,t,uint.max,context); }
	private Proof record(Deduction d){
		if(tracing){ d.proof.id=cast(uint)deductions.length; deductions~=d; }
		return d.proof;
	}
	bool visible(uint outer,uint inner){
		while(inner!=outer&&inner) inner=contexts[inner].parent;
		return inner==outer;
	}
	Proof trans(Proof p,Proof q,uint context){
		enforce(p.after==q.before&&visible(p.context,context)&&visible(q.context,context),"invalid derivation composition");
		if(p.before==p.after){ q.context=context; return q; }
		if(q.before==q.after){ p.context=context; return p; }
		auto result=Proof(p.before,q.after,uint.max,context);
		return tracing?record(Deduction(Evidence.trans,result,[p,q])):result;
	}
	private Proof rawCongr(Term t,Proof[] children,uint context){
		auto n=arena.view(t);
		enforce(n.arity==children.length,"congruence arity mismatch");
		bool unchanged=true;
		foreach(i,p;children){
			enforce(arena.viewChild(t,cast(uint)i)==p.before&&visible(p.context,context),"invalid congruence premise");
			unchanged=unchanged&&p.before==p.after;
		}
		if(unchanged) return refl(t,context);
		Term[] cs; foreach(p;children) cs~=p.after;
		auto result=arena.viewRebuild(t,cs,true);
		if(t==result) return refl(t,context);
		return record(Deduction(Evidence.congr,Proof(t,result,uint.max,context),children));
	}
	private Proof canonical(Term t,uint context,bool reverse=false){
		auto target=arena.canonical(t); if(t==target) return refl(t,context);
		auto n=arena.view(t); Proof[] cs;
		foreach(i;0..n.arity) cs~=canonical(arena.viewChild(t,i),context,reverse);
		if(!reverse){
			auto p=rawCongr(t,cs,context);
			return p.after==target?p:trans(p,ac(p.after,target,n.op,context),context);
		}
		Term[] inputs; foreach(p;cs) inputs~=p.before;
		auto base=arena.viewRebuild(t,inputs,true),p=rawCongr(base,cs,context);
		return base==target?p:trans(ac(target,base,n.op,context),p,context);
	}
	Proof congr(Term t,Proof[] children,uint context){
		auto n=arena.view(t); enforce(n.arity==children.length,"congruence arity mismatch");
		if(n.op!=Op.add&&n.op!=Op.mul){
			auto p=rawCongr(t,children,context); return trans(p,canonical(p.after,context),context);
		}
		foreach(p;children) enforce(visible(p.context,context),"invisible congruence premise");
		auto before=n.op==Op.add?arena.add(children[0].before,children[1].before):arena.mul(children[0].before,children[1].before);
		enforce(before==arena.canonical(t),"invalid associative congruence premises");
		if(!tracing){
			auto after=n.op==Op.add?arena.add(children[0].after,children[1].after):arena.mul(children[0].after,children[1].after);
			return Proof(t,after,uint.max,context);
		}
		if(children[0].before==children[0].after&&children[1].before==children[1].after) return refl(t,context);
		auto raw=n.op==Op.add?arena.add(children[0].before,children[1].before,true):arena.mul(children[0].before,children[1].before,true);
		auto p=trans(ac(t,raw,n.op,context),rawCongr(raw,children,context),context);
		return trans(p,canonical(p.after,context),context);
	}
	Proof rule(Instance i,Proof[] premises,uint context){
		if(i.before==i.result) return refl(i.before,context);
		if(tracing&&!i.raw){
			auto r=instantiate(arena,i.law,i.bindings,true);
			if(i.reversed){ auto t=r.before; r.before=r.result; r.result=t; r.reversed=true; }
			Proof[] ps; size_t j;
			foreach(c;r.conditions) if(!c.defined&&!c.literal){
				enforce(j<premises.length,"missing rule premise");
				ps~=trans(canonical(c.term,context),premises[j++],context);
			}
			enforce(j==premises.length,"unexpected rule premises");
			return trans(trans(canonical(r.before,context,true),rule(r,ps,context),context),canonical(r.result,context),context);
		}
		size_t j; DomainProof[] domains;
		foreach(c;i.conditions){
			if(c.literal) enforce(arena.isNumber(c.term),"literal premise failed");
			else if(c.defined){
				auto d=domain(i.before,c.term,context);
				enforce(d.found,"missing definedness premise"); domains~=d;
			}else{
				enforce(j<premises.length&&premises[j].before==c.term&&premises[j].after==arena.boolean(true)&&visible(premises[j].context,context),"invalid rule premise");
				++j;
			}
		}
		enforce(j==premises.length,"unexpected rule premises");
		auto d=Deduction(Evidence.rule,Proof(i.before,i.result,uint.max,context),premises,i,domains);
		return record(d);
	}
	uint enter(uint parent,Term guard,bool value){
		enforce(arena.sort(guard)==Sort.boolean,"Boolean assumption expected");
		contexts~=Context(parent,guard,value);
		return cast(uint)contexts.length-1;
	}
	Proof scoped(Term t,Proof body,uint context){
		auto n=arena.view(t),s=contexts[body.context];
		enforce((n.op==Op.mask||n.op==Op.and_||n.op==Op.or_)&&s.parent==context&&s.guard==arena.at(n.a)&&s.value==(n.op!=Op.or_)&&body.before==arena.at(n.b),"invalid guarded derivation");
		auto result=arena.viewRebuild(t,[arena.at(n.a),body.after]);
		if(result==t) return refl(t,context);
		return record(Deduction(Evidence.scoped,Proof(t,result,uint.max,context),[body]));
	}
	Proof assumption(uint assumptionScope,uint[] path,uint context){
		enforce(assumptionScope&&visible(assumptionScope,context),"invisible assumption");
		auto t=contexts[assumptionScope].guard; bool value=contexts[assumptionScope].value;
		foreach(i;path){
			auto n=arena.view(t);
			if(n.op==Op.not_){ enforce(i==0,"bad assumption path"); value=!value; }
			else enforce((n.op==Op.and_&&value||n.op==Op.or_&&!value)&&i<2,"invalid assumption projection");
			t=arena.viewChild(t,i);
		}
		auto p=value?t:arena.not_(t);
		auto d=Deduction(Evidence.assumption,Proof(p,arena.boolean(true),uint.max,context,true));
		d.assumptionScope=assumptionScope; d.path=path; d.value=value;
		return record(d);
	}
	Proof transport(Proof known,Proof change,uint context){
		enforce(known.known&&known.before==change.before,"known value required");
		auto result=Proof(change.after,known.after,uint.max,context,true);
		if(tracing) result=record(Deduction(Evidence.transport,result,[known,change]));
		domainFacts~=result;
		return result;
	}
	Proof project(Proof source,uint[] path,uint context){
		enforce(source.known&&visible(source.context,context),"known value required");
		auto t=source.before; bool value=true;
		foreach(i;path){
			auto n=arena.view(t);
			if(n.op==Op.not_){ enforce(i==0,"bad fact path"); value=!value; }
			else enforce((n.op==Op.and_&&value||n.op==Op.or_&&!value)&&i<2,"invalid fact projection");
			t=arena.viewChild(t,i);
		}
		auto p=value?t:arena.not_(t);
		auto d=Deduction(Evidence.assumption,Proof(p,arena.boolean(true),uint.max,context,true),[source]);
		d.path=path; d.value=value;
		auto result=record(d); domainFacts~=result; return result;
	}
	Proof numeric(Term before,Term after,uint context){
		enforce(arena.sort(before)==arena.sort(after),"numeric type mismatch");
		foreach(t;[before,after]) foreach(id;arena.viewPostorder(t)){
			auto n=arena.view(arena.at(id));
			enforce(qsym.ir.numeric(n.sort)||n.sort==Sort.boolean,"non-scalar numeric certificate");
			enforce(n.op!=Op.variable&&n.op!=Op.densityAt,"symbolic numeric certificate");
		}
		if(before==after) return refl(before,context);
		return record(Deduction(Evidence.numeric,Proof(before,after,uint.max,context)));
	}
	Proof ac(Term before,Term after,Op op,uint context){
		enforce(op==Op.add||op==Op.mul,"AC operation expected");
		enforce(arena.sort(before)==arena.sort(after),"AC type mismatch");
		if(before==after) return refl(before,context);
		enforce(regions.from(before,op)==regions.from(after,op),"AC leaf mismatch");
		auto d=Deduction(Evidence.ac,Proof(before,after,uint.max,context)); d.value=op==Op.mul;
		return record(d);
	}
	DomainProof domain(Term source,Term target,uint context=0,bool learned=true){
		Table!(uint,uint) known;
		struct Entry{ Term term; uint[] path; }
		Entry[] pending=[Entry(source)]; uint[][] paths;
		while(pending.length){
			auto e=pending[$-1]; --pending.length;
			if(known.contains(e.term.id)) continue;
			known.set(e.term.id,cast(uint)paths.length); paths~=e.path;
			auto n=arena.view(e.term);
			if(n.arity>=1) pending~=Entry(arena.at(n.a),e.path~0u);
			if(n.arity==2&&n.op!=Op.mask&&n.op!=Op.and_&&n.op!=Op.or_) pending~=Entry(arena.at(n.b),e.path~1u);
		}
		DomainProof build(Term t,uint depth=0){
			DomainProof d; d.term=t;
			auto i=known.get(t.id,uint.max);
			if(i!=uint.max){ d.found=true; d.path=paths[i]; return d; }
			auto n=arena.view(t);
			if(n.arity==0){ d.found=d.total=true; return d; }
			for(auto c=context;c;c=contexts[c].parent){
				auto p=this.domain(contexts[c].guard,t,0,false);
				if(p.found){ p.assumption=c; return p; }
			}
			if(learned) foreach(j,f;domainFacts) if(visible(f.context,context)){
				auto p=this.domain(f.before,t,0,false);
				if(p.found){ p.fact=cast(uint)j; return p; }
			}
			if(depth>=128||n.op==Op.inv||n.op==Op.mask||n.op==Op.builtin&&!builtinInfo(cast(Builtin)n.value).total) return d;
			foreach(j;0..n.arity){
				auto child=build(arena.viewChild(t,j),depth+1);
				if(!child.found) return d;
				d.children~=child;
			}
			d.found=true; return d;
		}
		return build(target);
	}
}
