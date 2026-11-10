module qsym.proof;
import qsym.table:Table;
import qsym.ir;
import qsym.simplify;
import qsym.domain;
import qsym.derive;
import qsym.spec:leanSort;
import std.conv:to;
import std.exception:enforce;
@safe:

private string name(uint i){ return "n"~to!string(i); }
private string exprEval(uint i){ return "(Expr.eval ρ "~name(i)~")"; }
private string ev(uint i){ return "(v"~to!string(i)~" ρ)"; }
private string evalEq(uint i){ return "(eval_"~to!string(i)~" ρ)"; }
private string dc(uint i){ return "(d"~to!string(i)~" ρ)"; }
private string ds(uint i){ return "(domain_"~to!string(i)~" ρ)"; }
private string rat(Rational q){ return "(("~to!string(q.numerator)~") / ("~to!string(q.denominator)~") : ℚ)"; }

private string positive(uint n){
	enforce(n>0,"positive multiplicity expected");
	return n==1?".one":"(."~(n&1?"twicePlusOne":"twice")~" "~positive(n/2)~")";
}
private string positiveCount(uint n){
	if(n==1) return "Positive.toNat_one";
	return "(Positive.toNat_"~(n&1?"twicePlusOne":"twice")~" "~positive(n/2)~" "~to!string(n/2)~" "~positiveCount(n/2)~")";
}
private string syntaxCode(Arena a,Term t,bool expression=true){
	auto n=a.node(t),s=leanSort(n.sort); string code,body;
	if(n.region){
		string child(uint id){ auto v=a.node(a.at(id)); return v.region&&v.op==n.op?"b"~to!string(id):"(.item "~name(id)~" .one)"; }
		if(n.arity==1){ auto e=a.operands(t)[0]; body=".item "~name(e.term.id)~" "~positive(e.count); }
		else body=".join "~child(n.a)~" "~child(n.b);
		code="def b"~to!string(t.id)~" : Region (Expr ."~s~") := "~body~"\n";
		if(!expression) return code;
		body="Expr."~(n.op==Op.add?"sum":"product")~suffix(n.sort)~" b"~to!string(t.id);
	}else body=leanConstructor(a,n);
	return code~"def "~name(t.id)~" : Expr ."~s~" := "~body~"\n";
}

string leanConstructor(Arena a,Node n){
	string suf=numeric(n.sort)?suffix(n.sort):"";
	string op;
	final switch(n.op){
		case Op.realLit:return "(.real ("~to!string(n.value)~"))";
		case Op.complexLit:return "(.complex ("~to!string(n.value)~") ("~to!string(n.imaginary)~"))";
		case Op.numberLit:
			auto q=a.number(n);
			if(n.sort==Sort.natural||n.sort==Sort.integer) return "(."~(n.sort==Sort.natural?"nat":"int")~" ("~to!string(q.re.numerator)~"))";
			if(n.sort==Sort.rational) return "(.rat "~rat(q.re)~")";
			return n.sort==Sort.real_?"(.ratR "~rat(q.re)~")":"(.ratC "~rat(q.re)~" "~rat(q.im)~")";
		case Op.boolLit:return "(.bool "~(n.value?"true":"false")~")";
		case Op.variable:
			return "(.var"~(n.sort==Sort.boolean?"B":suf)~" "~to!string(n.value)~")";
		case Op.builtin:op=builtinInfo(cast(Builtin)n.value).code; break;
		case Op.add:op="add"~suf; break;
		case Op.mul:op="mul"~suf; break;
		case Op.inv:op="inv"~suf; break;
		case Op.pow:return "(.pow"~suf~" "~name(n.a)~" "~to!string(n.value)~")";
		case Op.abs:op="absR"; break;
		case Op.not_:op="not"; break;
		case Op.and_:op="and"; break;
		case Op.or_:op="or"; break;
		case Op.lt:op="ltR"; break;
		case Op.le:op="leR"; break;
		case Op.nonzero:op="nonzero"~(a.sort(a.at(n.a))==Sort.real_?"R":"C"); break;
		case Op.mask:op="mask"~suf; break;
		case Op.conj:op="conj"; break;
		case Op.lebesgue:op="lebesgue"; break;
		case Op.puncture:op="puncture"; break;
		case Op.densityAt:op="densityAt"; break;
		case Op.forget:op="forget"; break;
	}
	return "(."~op~(n.arity>=1?" "~name(n.a):"")~
		(n.arity==2?" "~name(n.b):"")~")";
}

// Share evaluated subterms as well as syntax. Connect only public endpoints
// and arithmetic replay to Expr.eval; intermediate steps use the values.
private string valueCode(Arena a,Term t){
	auto n=a.view(t); string op;
	switch(n.op){
		case Op.add:op="Value.add"; break;
		case Op.mul:op="Value.mul"; break;
		case Op.inv:op="Value.inv"; break;
		case Op.nonzero:op="Value.nonzero"; break;
		case Op.mask:op="Value.mask"; break;
		case Op.conj:op="Value.conj"; break;
		case Op.abs:op="Value.abs"; break;
		case Op.not_:op="Value.not"; break;
		case Op.and_:op="Value.and"; break;
		case Op.or_:op="Value.or"; break;
		case Op.lt:op="Value.lt"; break;
		case Op.le:op="Value.le"; break;
		case Op.densityAt:op="Value.densityAt"; break;
		case Op.pow:op="(Option.map (fun (x : Ty.denote ."~leanSort(n.sort)~") => x ^ "~to!string(n.value)~"))"; break;
		case Op.puncture:op="(Option.map Density.puncture)"; break;
		case Op.forget:op="(Option.map Density.forget)"; break;
		case Op.builtin:if(n.arity) op="Functions."~builtinInfo(cast(Builtin)n.value).code~".apply"; break;
		default:enforce(!n.arity,"missing value constructor"); break;
	}
	string value;
	if(n.arity) value=op~" "~ev(n.a)~(n.arity==2?" "~ev(n.b):"");
	else switch(n.op){
		case Op.realLit:value="some (("~to!string(n.value)~" : Int) : ℝ)"; break;
		case Op.complexLit:value="some ((("~to!string(n.value)~" : Int) : ℂ) + (("~to!string(n.imaginary)~" : Int) : ℂ) * Complex.I)"; break;
		case Op.boolLit:value="some "~(n.value?"true":"false"); break;
		case Op.variable:value="some (ρ."~leanSort(n.sort)~" "~to!string(n.value)~")"; break;
		case Op.lebesgue:value="some Density.lebesgue"; break;
		case Op.builtin:value="some Functions."~builtinInfo(cast(Builtin)n.value).code; break;
		case Op.numberLit:
			auto q=a.number(n);
			if(n.sort==Sort.natural||n.sort==Sort.integer) value="some ("~to!string(q.re.numerator)~")";
			else if(n.sort==Sort.rational) value="some "~rat(q.re);
			else if(n.sort==Sort.real_) value="some ("~rat(q.re)~" : ℝ)";
			else value="some (("~rat(q.re)~" : ℂ) + ("~rat(q.im)~" : ℂ) * Complex.I)";
			break;
		default:assert(0,"missing leaf value");
	}
	return "noncomputable def v"~to!string(t.id)~" (ρ : Env) : Option (Ty.denote ."~leanSort(n.sort)~") := "~value~"\n";
}

private string domainCode(Arena a,Term t){
	auto n=a.view(t);
	auto i=to!string(t.id);
	string cond,proof;
	final switch(n.op){
		case Op.realLit,Op.complexLit,Op.boolLit,Op.variable,Op.lebesgue,Op.numberLit:
			cond="True"; proof="iff_true_intro ⟨_, rfl⟩"; break;
		case Op.builtin:
			auto info=builtinInfo(cast(Builtin)n.value),f="Functions."~info.code;
			if(!n.arity){ cond="True"; proof="iff_true_intro ⟨_, rfl⟩"; }
			else if(n.arity==1){ cond="∃ x, "~ev(n.a)~" = some x ∧ "~f~".domain x"; proof=f~".defined "~ev(n.a); }
			else{ cond="∃ x y, "~ev(n.a)~" = some x ∧ "~ev(n.b)~" = some y ∧ "~f~".domain x y"; proof=f~".defined "~ev(n.a)~" "~ev(n.b); }
			break;
		case Op.add,Op.mul,Op.densityAt,Op.lt,Op.le:
			cond=dc(n.a)~" ∧ "~dc(n.b);
			auto lemma=n.op==Op.add?"defined_add":n.op==Op.mul?"defined_mul":n.op==Op.lt?"defined_lt":n.op==Op.le?"defined_le":"defined_densityAt";
			proof="(Value."~lemma~" "~ev(n.a)~" "~ev(n.b)~
				").trans (and_congr "~ds(n.a)~" "~ds(n.b)~")"; break;
		case Op.inv:
			cond="∃ v, "~ev(n.a)~" = some v ∧ v ≠ 0";
			proof="Value.defined_inv "~ev(n.a); break;
		case Op.nonzero,Op.conj,Op.not_:
			cond=dc(n.a);
			proof="(Value."~(n.op==Op.nonzero?"defined_nonzero":n.op==Op.not_?"defined_not":"defined_conj")~
				" "~ev(n.a)~").trans "~ds(n.a); break;
		case Op.pow,Op.abs:
			cond=dc(n.a);
			proof="(Value.defined_map _ "~ev(n.a)~").trans "~ds(n.a); break;
		case Op.puncture,Op.forget:
			cond=dc(n.a);
			proof="(Value.defined_map _ "~ev(n.a)~").trans "~ds(n.a); break;
		case Op.mask:
			if(isGuardedInverse(a,t)){
				auto child=a.view(a.at(n.b)).a;
				cond=dc(child);
				proof="(Value.defined_guarded_inv "~ev(child)~").trans "~ds(child);
			}else{
				cond=ev(n.a)~" = some false ∨ ("~ev(n.a)~" = some true ∧ "~dc(n.b)~")";
				proof="(Value.defined_mask "~ev(n.a)~" "~ev(n.b)~
					").trans (or_congr Iff.rfl (and_congr Iff.rfl "~ds(n.b)~"))";
			}
			break;
		case Op.and_,Op.or_:
			auto stop=n.op==Op.and_?"false":"true",go=n.op==Op.and_?"true":"false";
			cond=ev(n.a)~" = some "~stop~" ∨ ("~ev(n.a)~" = some "~go~" ∧ "~dc(n.b)~")";
			proof="(Value."~(n.op==Op.and_?"defined_and":"defined_or")~" "~ev(n.a)~" "~ev(n.b)~
				").trans (or_congr Iff.rfl (and_congr Iff.rfl "~ds(n.b)~"))"; break;
	}
	return "def d"~i~" (ρ : Env) : Prop := "~cond~"\n"~
		"theorem domain_"~i~" (ρ : Env) : Value.Defined "~ev(t.id)~" ↔ d"~i~" ρ :=\n  "~proof~"\n\n";
}

private string contexts(Derivation d,uint ctx,bool declarations){
	uint[] chain;
	for(auto i=ctx;i;i=d.contexts[i].parent) chain=i~chain;
	string s;
	foreach(i;chain){
		auto c=d.contexts[i]; auto g="g"~to!string(i);
		s~=declarations?" ("~g~" : "~ev(c.guard.id)~" = some "~(c.value?"true":"false")~")":" "~g;
	}
	return s;
}
private string reference(Derivation d,Proof p,bool raw=false){
	if(p.id==uint.max){ enforce(p.before==p.after,"missing derivation"); return "(Value.refines_refl "~ev(p.before.id)~")"; }
	enforce(p.id<d.deductions.length,"invalid proof reference");
	auto saved=d.deductions[p.id].proof;
	enforce(saved.before==p.before&&saved.after==p.after,"proof endpoints changed");
	auto s="(p"~to!string(p.id)~" ρ"~contexts(d,saved.context,false)~")";
	return saved.known&&!raw?"(Value.refines_of_eq "~s~")":s;
}
private string domainLemma(Node n){
	switch(n.op){
		case Op.add:return "defined_add";
		case Op.mul:return "defined_mul";
		case Op.lt:return "defined_lt";
		case Op.le:return "defined_le";
		case Op.densityAt:return "defined_densityAt";
		case Op.nonzero:return "defined_nonzero";
		case Op.not_:return "defined_not";
		case Op.conj:return "defined_conj";
		case Op.pow,Op.abs,Op.puncture,Op.forget:return "defined_map _";
		default:assert(0,"unsupported definedness operation");
	}
}
private string totalRef(uint i){ return "(total_"~to!string(i)~" ρ)"; }
private string totalCode(Arena a,Term t,bool[] total){
	if(a.node(t).region){
		foreach(e;a.operands(t)) if(!total[e.term.id]) return "";
		auto op=a.node(t).op,label=op==Op.add?"add":"mul";
		string build(Term u){
			auto n=a.node(u);
			if(!n.region||n.op!=op) return totalRef(u.id);
			if(n.arity==1){
				auto e=a.operands(u)[0];
				return "(Positive.defined_"~label~" "~positive(e.count)~" "~ev(e.term.id)~").mpr "~totalRef(e.term.id);
			}
			return "(Value.defined_"~label~" "~ev(n.a)~" "~ev(n.b)~").mpr ⟨"~build(a.at(n.a))~", "~build(a.at(n.b))~"⟩";
		}
		total[t.id]=true;
		return "theorem total_"~to!string(t.id)~" (ρ : Env) : Value.Defined "~ev(t.id)~" :=\n  "~build(t)~"\n";
	}
	auto n=a.view(t);
	string proof;
	final switch(n.op){
		case Op.realLit,Op.complexLit,Op.numberLit,Op.boolLit,Op.variable,Op.lebesgue:
			proof="⟨_, rfl⟩"; break;
		case Op.builtin:
			auto info=builtinInfo(cast(Builtin)n.value);
			if(!n.arity) proof="⟨_, rfl⟩";
			else if(info.total&&total[n.a]&&(n.arity==1||total[n.b])){
				proof="Functions."~info.code~".total (fun "~(n.arity==1?"_":"_ _")~" => True.intro) "~ev(n.a);
				if(n.arity==2) proof~=" "~ev(n.b);
				proof~=" "~totalRef(n.a)~(n.arity==2?" "~totalRef(n.b):"");
			}
			break;
		case Op.add,Op.mul,Op.lt,Op.le,Op.densityAt:
			if(total[n.a]&&total[n.b]) proof="(Value."~domainLemma(n)~" "~ev(n.a)~" "~ev(n.b)~
				").mpr ⟨"~totalRef(n.a)~", "~totalRef(n.b)~"⟩";
			break;
		case Op.nonzero,Op.conj,Op.not_,Op.pow,Op.abs,Op.puncture,Op.forget:
			if(total[n.a]) proof="(Value."~domainLemma(n)~" "~ev(n.a)~").mpr "~totalRef(n.a);
			break;
		case Op.inv:break;
		case Op.mask:
			if(isGuardedInverse(a,t)){
				auto child=a.view(a.at(n.b)).a;
				if(total[child]) proof="(Value.defined_guarded_inv "~ev(child)~").mpr "~totalRef(child);
			}else{
				auto p=a.view(a.at(n.a));
				if(p.op==Op.boolLit){
					if(!p.value) proof="⟨_, rfl⟩";
					else if(total[n.b]) proof=totalRef(n.b);
				}
			}
			break;
		case Op.and_,Op.or_:
			auto p=a.view(a.at(n.a));
			if(p.op==Op.boolLit&&p.value==(n.op==Op.or_)) proof="⟨_, rfl⟩";
			else if(total[n.a]&&total[n.b]) proof="Value.defined_"~(n.op==Op.and_?"and":"or")~
				"_total "~ev(n.a)~" "~ev(n.b)~" "~totalRef(n.a)~" "~totalRef(n.b);
			break;
	}
	total[t.id]=proof.length!=0;
	return proof.length?"theorem total_"~to!string(t.id)~" (ρ : Env) : Value.Defined "~ev(t.id)~" :=\n  "~proof~"\n":"";
}
private string domainEvidence(Arena a,Derivation d,Term source,DomainProof p,string h){
	if(p.fact!=uint.max){
		auto f=d.domainFacts[p.fact]; enforce(f.known,"strong domain fact required");
		source=f.before;
		h="(show Value.Defined "~ev(source.id)~" from ⟨_, "~reference(d,f,true)~"⟩)";
	}
	if(p.assumption){
		source=d.contexts[p.assumption].guard;
		h="(show Value.Defined "~ev(source.id)~" from ⟨_, g"~to!string(p.assumption)~"⟩)";
	}
	enforce(p.found,"missing domain evidence");
	if(p.total) return "(show Value.Defined "~ev(p.term.id)~" from ⟨_, rfl⟩)";
	if(p.children.length){
		auto n=a.view(p.term);
		if(n.op==Op.builtin){
			auto info=builtinInfo(cast(Builtin)n.value);
			enforce(info.total,"partial function is not total");
			string proof="(Functions."~info.code~".total (fun "~(n.arity==1?"_":"_ _")~" => True.intro) "~ev(n.a);
			if(n.arity==2) proof~=" "~ev(n.b);
			foreach(child;p.children) proof~=" "~domainEvidence(a,d,source,child,h);
			return proof~")";
		}
		if(n.op==Op.and_||n.op==Op.or_) return "(Value.defined_"~(n.op==Op.and_?"and":"or")~"_total "~ev(n.a)~" "~ev(n.b)~" "~
			domainEvidence(a,d,source,p.children[0],h)~" "~domainEvidence(a,d,source,p.children[1],h)~")";
		string args=ev(n.a),proof=domainEvidence(a,d,source,p.children[0],h);
		if(n.arity==2){ args~=" "~ev(n.b); proof="⟨"~proof~", "~domainEvidence(a,d,source,p.children[1],h)~"⟩"; }
		return "((Value."~domainLemma(n)~" "~args~").mpr "~proof~")";
	}
	auto t=source;
	foreach(i;p.path){
		auto n=a.view(t);
		switch(n.op){
			case Op.builtin:
				h="(Functions."~builtinInfo(cast(Builtin)n.value).code~(n.arity==1?".defined_arg ":i==0?".defined_left ":".defined_right ")~ev(n.a)~(n.arity==2?" "~ev(n.b):"")~" "~h~")";
				break;
			case Op.inv:h="(Value.defined_inv_arg "~ev(n.a)~" "~h~")"; break;
			case Op.mask:h="(Value.defined_mask_guard "~ev(n.a)~" "~ev(n.b)~" "~h~")"; break;
			case Op.and_:h="(Value.defined_and_guard "~ev(n.a)~" "~ev(n.b)~" "~h~")"; break;
			case Op.or_:h="(Value.defined_or_guard "~ev(n.a)~" "~ev(n.b)~" "~h~")"; break;
			default:
				auto args=ev(n.a)~(n.arity==2?" "~ev(n.b):"");
				h="((Value."~domainLemma(n)~" "~args~").mp "~h~")";
				if(n.arity==2) h~="."~to!string(i+1);
				break;
		}
		t=a.viewChild(t,i);
	}
	enforce(t==p.term,"bad domain projection");
	return h;
}
private struct ACCode{ string declarations,proof; }
private string lookupCode(Term[] atoms){
	string tree(size_t offset,size_t stride){
		if(offset>=atoms.length) return ".empty";
		if(stride>=atoms.length-offset) return "(.leaf v"~to!string(atoms[offset].id)~")";
		return "(.node "~tree(offset,stride*2)~" "~tree(offset+stride,stride*2)~")";
	}
	return tree(0,1);
}
private ACCode bagEvidence(Arena a,Deduction e,uint[] nodes,Term[] atoms,Table!(uint,uint) ids){
	auto op=e.value?Op.mul:Op.add;
	auto ac="Replay."~(e.value?"mul":"add")~(a.sort(e.proof.before)==Sort.real_?"R":"C");
	auto prefix="ac"~to!string(e.proof.id)~"_";
	auto type="Option (Ty.denote ."~leanSort(a.sort(e.proof.before))~")";
	// Select a value function before applying ρ; keep the lookup tree closed.
	string code="noncomputable def "~prefix~"values : Replay.Lookup (Env → "~type~") := "~lookupCode(atoms)~"\n"~
		"noncomputable def "~prefix~"env (ρ : Env) (i : Nat) : "~type~" := Replay.Lookup.get (fun _ => none) "~prefix~"values i ρ\n";
	auto env="("~prefix~"env ρ)";
	uint height;
	while((1UL<<height)<atoms.length) ++height;
	// Persistent count tries share unchanged branches between successive merges.
	struct BagNode{ uint height,left,right; }
	struct Pair{ uint left,right; }
	BagNode[] bags=[BagNode.init]; Table!(BagNode,uint) intern; Table!(Pair,uint) merges;
	string bagRef(uint id,uint h){ return id?prefix~"b"~to!string(id):"(Replay.Bag.zero : Replay.Bag "~to!string(h)~")"; }
	string proof(uint id){ return "("~prefix~"p"~to!string(id)~" ρ)"; }
	uint node(uint h,uint l,uint r=0){
		if(!l&&!r) return 0;
		auto key=BagNode(h,l,r),id=intern.get(key,0);
		if(id) return id;
		enforce(bags.length<uint.max,"AC bag overflow"); id=cast(uint)bags.length;
		bags~=key; intern.set(key,id);
		code~="def "~bagRef(id,h)~" : Replay.Bag "~to!string(h)~" := "~(h?".node "~bagRef(l,h-1)~" "~bagRef(r,h-1):".leaf "~to!string(l))~"\n";
		return id;
	}
	uint single(uint h,uint i){
		if(!h) return node(0,1);
		auto b=single(h-1,i/2);
		return i%2?node(h,0,b):node(h,b,0);
	}
	uint merge(uint l,uint r){
		if(!l) return r; if(!r) return l;
		if(l>r){ auto tmp=l; l=r; r=tmp; }
		auto key=Pair(l,r),cached=merges.get(key,0);
		if(cached) return cached;
		auto x=bags[l],y=bags[r]; enforce(x.height==y.height,"AC bag height mismatch");
		uint result;
		if(x.height) result=node(x.height,merge(x.left,y.left),merge(x.right,y.right));
		else{
			enforce(x.left<=uint.max-y.left,"AC multiplicity overflow");
			result=node(0,x.left+y.left);
		}
		merges.set(key,result); return result;
	}
	Table!(uint,uint) normal;
	foreach(id;nodes){
		auto n=a.view(a.at(id)); uint b; string p;
		if(n.op==op){
			auto l=normal.get(n.a,uint.max),r=normal.get(n.b,uint.max);
			enforce(l!=uint.max&&r!=uint.max,"AC node order mismatch");
			b=merge(l,r);
			p="Replay.Bag.node_sound "~ac~" "~env~" "~ev(n.a)~" "~ev(n.b)~" "~bagRef(l,height)~" "~bagRef(r,height)~" "~bagRef(b,height)~" "~proof(n.a)~" "~proof(n.b)~" rfl";
		}else if(ids.contains(id)){
			auto i=ids.get(id,0); b=single(height,i);
			p="Replay.Bag.atom_sound "~ac~" "~env~" "~to!string(height)~" "~to!string(i)~" "~ev(id)~" "~bagRef(b,height)~" (of_decide_eq_true rfl) rfl rfl";
		}else p="rfl";
		normal.set(id,b);
		code~="theorem "~prefix~"p"~to!string(id)~" (ρ : Env) : "~ev(id)~" = Replay.Bag.eval "~ac~" "~env~" "~bagRef(b,height)~" := "~p~"\n";
	}
	auto left=e.proof.before.id,right=e.proof.after.id;
	enforce(normal.get(left,uint.max)==normal.get(right,uint.max),"AC certificate mismatch");
	return ACCode(code,"  Value.refines_of_eq ("~proof(left)~".trans "~proof(right)~".symm)\n");
}
private ACCode acEvidence(Arena a,Deduction e){
	auto op=e.value?Op.mul:Op.add;
	if(a.view(e.proof.before)==a.view(e.proof.after))
		return ACCode("","  Value.refines_refl "~ev(e.proof.before.id)~"\n");
	Term[] atoms,pending=[e.proof.before,e.proof.after]; uint[] nodes;
	Table!(uint,uint) ids; Table!(uint,bool) seen;
	while(pending.length){
		auto t=pending[$-1]; --pending.length;
		if(seen.get(t.id,false)) continue;
		seen.set(t.id,true); nodes~=t.id;
		auto n=a.view(t);
		if(n.op==op) pending~=[a.at(n.b),a.at(n.a)];
		else if(!a.isNumber(t)||!(e.value?a.number(t).one:a.number(t).zero)){
			ids.set(t.id,cast(uint)atoms.length); atoms~=t;
		}
	}
	import std.algorithm:sort;
	sort(nodes);
	// Larger bridges check shared merges separately, avoiding costly reduction
	// of a whole tree against evaluated real or complex expressions.
	if(nodes.length>8) return bagEvidence(a,e,nodes,atoms,ids);
	auto ac="Replay."~(e.value?"mul":"add")~(a.sort(e.proof.before)==Sort.real_?"R":"C");
	string env="(fun i => ([";
	foreach(i,t;atoms) env~=(i?",":"")~ev(t.id);
	env~="] : List (Option (Ty.denote ."~leanSort(a.sort(e.proof.before))~"))).getD i none)";
	string tree(uint id){ return "ac"~to!string(id); }
	string code;
	foreach(id;nodes){
		auto n=a.view(a.at(id)); string value;
		if(n.op==op) value="(.node "~tree(n.a)~" "~tree(n.b)~")";
		else if(ids.contains(id)) value="(.leaf "~to!string(ids.get(id,0))~")";
		else value=".unit";
		code~="  let "~tree(id)~" : Replay.Tree := "~value~"\n";
	}
	return ACCode("",code~"  Value.refines_of_eq (Replay.AC.sound_counts "~ac~" "~env~" "~tree(e.proof.before.id)~" "~tree(e.proof.after.id)~" rfl)\n");
}

// The exporter replays named laws and their premises. It never asks an
// algebra tactic to guess why two symbolic endpoints might agree.
string exportLean(Arena a,Result result){
	enforce(result.traced&&result.derivation !is null&&result.derivation.tracing,"proof export requires a recorded derivation");
	auto d=result.derivation;
	enforce(d.arena is a,"invalid certificate arena");
	auto context=result.certificate.context;
	auto chain=context;
	foreach_reverse(f;result.assumptions){
		enforce(chain&&d.contexts[chain].guard==f&&d.contexts[chain].value,"invalid certificate assumptions");
		chain=d.contexts[chain].parent;
	}
	enforce(!chain,"undeclared certificate assumption");
	enforce(result.certificate.before==result.proofInput&&result.certificate.after==result.output,"certificate endpoints changed");
	bool[] needed=new bool[a.length],used=new bool[d.deductions.length],evaluated=new bool[a.length];
	foreach(t;[result.input,result.proofInput,result.output]) evaluated[t.id]=true;
	Term[] pending=[result.input,result.proofInput,result.output];
	pending~=result.assumptions;
	Proof[] proofs=[result.certificate];
	void domains(DomainProof p){
		if(p.fact!=uint.max) proofs~=d.domainFacts[p.fact];
		foreach(child;p.children) domains(child);
	}
	while(proofs.length){
		auto p=proofs[$-1]; --proofs.length;
		pending~=[p.before,p.after];
		if(p.id==uint.max) continue;
		enforce(p.id<used.length,"invalid proof index");
		if(used[p.id]) continue;
		used[p.id]=true; auto e=d.deductions[p.id]; proofs~=e.premises;
		if(e.kind==Evidence.numeric){ evaluated[p.before.id]=true; evaluated[p.after.id]=true; }
		foreach(domain;e.domains) domains(domain);
		pending~=e.instance.bindings;
		foreach(c;e.instance.conditions) pending~=c.term;
		for(auto c=e.proof.context;c;c=d.contexts[c].parent) pending~=d.contexts[c].guard;
	}
	while(pending.length){
		auto t=pending[$-1]; --pending.length;
		if(needed[t.id]) continue;
		needed[t.id]=true;
		foreach(i;0..a.view(t).arity) pending~=a.viewChild(t,i);
	}
	// Only evaluation endpoints and assumptions need expression syntax.
	// Region branches share bags; their binary value views need no Expr nodes.
	bool[] syntax=new bool[a.length],bags=new bool[a.length];
	foreach(i,yes;evaluated) if(yes) pending~=a.at(cast(uint)i);
	pending~=result.assumptions;
	while(pending.length){
		auto t=pending[$-1]; --pending.length;
		if(syntax[t.id]) continue;
		syntax[t.id]=true;
		foreach(i;0..a.node(t).arity) pending~=a.child(t,i);
	}
	foreach(i,yes;syntax) if(yes&&a.node(a.at(cast(uint)i)).region) pending~=a.at(cast(uint)i);
	while(pending.length){
		auto t=pending[$-1]; --pending.length;
		if(bags[t.id]) continue;
		bags[t.id]=true; auto n=a.node(t);
		if(n.arity>1) foreach(id;[n.a,n.b]){
			auto v=a.node(a.at(id)); if(v.region&&v.op==n.op) pending~=a.at(id);
		}
	}
	string s="-- Generated certificate. Check with: lake env lean FILE.lean\nimport QSym\nnamespace QSym.Certificate\nattribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv\nattribute [local irreducible] Value.add Value.mul\nset_option maxRecDepth 8192\n";
	foreach(i,n;syntax) if(n||bags[i]) s~=syntaxCode(a,a.at(cast(uint)i),n);
	foreach(i,n;needed) if(n) s~=valueCode(a,a.at(cast(uint)i));
	foreach(i,n;evaluated) if(n) s~="theorem eval_"~to!string(i)~" (ρ : Env) : "~exprEval(cast(uint)i)~" = "~ev(cast(uint)i)~" := rfl\n";
	s~="\n";
	foreach(i,yes;used) if(yes){
		auto e=d.deductions[i],p=e.proof;
		auto ac=e.kind==Evidence.ac?acEvidence(a,e):ACCode.init;
		s~=ac.declarations;
		auto claim=p.known?ev(p.before.id)~" = "~ev(p.after.id):"Value.Refines "~ev(p.before.id)~" "~ev(p.after.id);
		s~="theorem p"~to!string(i)~" (ρ : Env)"~contexts(d,p.context,true)~" : "~claim~" :=\n";
		string ref_(Proof q){ return reference(d,q); }
		final switch(e.kind){
			case Evidence.join:
				Table!(ulong,uint) leaves;
				ulong key(Term before,Term after){ return (cast(ulong)before.id<<32)|after.id; }
				foreach(j,q;e.premises) leaves.set(key(q.before,q.after),cast(uint)j);
				string join(Term before,Term after){
					auto j=leaves.get(key(before,after),uint.max);
					if(j!=uint.max) return ref_(e.premises[j]);
					if(before==after) return "(Value.refines_refl "~ev(before.id)~")";
					auto l=a.view(before),r=a.view(after);
					enforce(l.op==(e.value?Op.mul:Op.add)&&r.op==l.op,"invalid join skeleton");
					return "(Value.refines_"~(e.value?"mul":"add")~" (a := "~ev(l.a)~") (b := "~ev(l.b)~") (x := "~ev(r.a)~") (y := "~ev(r.b)~") "~
						join(a.at(l.a),a.at(r.a))~" "~join(a.at(l.b),a.at(r.b))~")";
				}
				s~="  "~join(p.before,p.after)~"\n"; break;
			case Evidence.repeated:
				auto atom=e.premises[0];
				s~="  Value.refines_repeat_"~(e.value?"mul":"add"~suffix(a.sort(p.before)))~" "~positive(e.count)~" "~to!string(e.count)~" "~positiveCount(e.count)~
					" (x := "~ev(atom.before.id)~") (y := "~ev(atom.after.id)~") "~ref_(atom)~"\n";
				break;
			case Evidence.rule:
				auto r=e.instance;
				string application="Generated."~r.rule;
				foreach(j,b;r.bindings) application~=" "~(r.naturals[j]?to!string(a.number(b).re.integer):ev(b.id));
				size_t premise,domain;
				if(e.domains.length) s~="  fun v hv =>\n  let hd : Value.Defined "~ev(p.before.id)~" := ⟨v, hv⟩\n";
				foreach(c;r.conditions){
					if(c.literal) continue;
					application~=" "~(c.defined?domainEvidence(a,d,p.before,e.domains[domain++],"hd"):ref_(e.premises[premise++]));
				}
				application="("~application~")";
				if(r.reversed){ enforce(r.equality,"cannot reverse a refinement"); application~=".symm"; }
				if(r.equality) application="(Value.refines_of_eq "~application~")";
				s~="  "~application~(e.domains.length?" v hv":"")~"\n";
				break;
			case Evidence.trans:s~="  "~ref_(e.premises[0])~".trans "~ref_(e.premises[1])~"\n"; break;
			case Evidence.congr:
				auto n=a.view(p.before);
				string lemma;
				switch(n.op){
					case Op.builtin:lemma="refines_function"~to!string(n.arity)~" Functions."~builtinInfo(cast(Builtin)n.value).code; break;
					case Op.add:lemma="refines_add"; break;
					case Op.mul:lemma="refines_mul"; break;
					case Op.inv:lemma="refines_inv"; break;
					case Op.nonzero:lemma="refines_nonzero"; break;
					case Op.conj:lemma="refines_conj"; break;
					case Op.not_:lemma="refines_not"; break;
					case Op.and_:lemma="refines_and"; break;
					case Op.or_:lemma="refines_or"; break;
					case Op.lt:lemma="refines_lt"; break;
					case Op.le:lemma="refines_le"; break;
					case Op.mask:lemma="refines_mask"; break;
					case Op.densityAt:lemma="refines_densityAt"; break;
					case Op.pow,Op.abs,Op.puncture,Op.forget:lemma="refines_map _"; break;
					default:assert(0,"invalid congruence");
				}
				s~="  Value."~lemma;
				foreach(q;e.premises) s~=" "~ref_(q);
				s~="\n"; break;
			case Evidence.scoped:
				auto n=a.view(p.before),body=e.premises[0];
				auto op=n.op==Op.mask?"mask":n.op==Op.and_?"and":"or";
				s~="  Value.refines_"~op~"_under "~ev(n.a)~" "~ev(body.before.id)~" "~ev(body.after.id)~
					" (fun g"~to!string(body.context)~" => "~ref_(body)~")\n";
				break;
			case Evidence.assumption:
				auto t=e.premises.length?e.premises[0].before:d.contexts[e.assumptionScope].guard;
				string h=e.premises.length?reference(d,e.premises[0],true):"g"~to!string(e.assumptionScope);
				foreach(j;e.path){
					auto n=a.view(t);
					auto lemma=n.op==Op.not_?"of_not":(n.op==Op.and_?"and_true_":"or_false_")~(j==0?"left":"right");
					h="(Value."~lemma~" "~h~")"; t=a.viewChild(t,j);
				}
				s~="  "~(e.value?h:"Value.not_eq "~h)~"\n"; break;
			case Evidence.transport:
				s~="  "~ref_(e.premises[1])~" true "~reference(d,e.premises[0],true)~"\n"; break;
			case Evidence.numeric:
				s~="  Eq.mp (congrArg₂ Value.Refines "~evalEq(p.before.id)~" "~evalEq(p.after.id)~") (Numeric.sound ρ "~name(p.before.id)~" "~name(p.after.id)~" rfl)\n";
				break;
			case Evidence.ac:s~=ac.proof; break;
		}
		s~="\n";
	}
	s~="theorem refinement (ρ : Env)"~contexts(d,context,true)~" : Value.Refines "~exprEval(result.proofInput.id)~" "~exprEval(result.output.id)~" :=\n  Eq.mpr (congrArg₂ Value.Refines "~evalEq(result.proofInput.id)~" "~evalEq(result.output.id)~") "~reference(d,result.certificate)~"\n#qsym_check_axioms refinement\n\n";
	s~="theorem simplification (ρ : Env)"~contexts(d,context,true)~" (h : Expr.Defined ρ "~name(result.proofInput.id)~") : "~
		exprEval(result.proofInput.id)~" = "~exprEval(result.output.id)~" := (refinement ρ"~contexts(d,context,false)~").eq_of_defined h\n#qsym_check_axioms simplification\n\n";
	auto inputOrder=a.viewPostorder(result.input);
	bool direct=true;
	foreach(id;inputOrder){
		auto n=a.view(a.at(id));
		if(n.op==Op.inv||n.op==Op.mask||n.op==Op.and_||n.op==Op.or_||n.op==Op.builtin&&n.arity) direct=false;
	}
	if(direct){
		auto id=result.input.id;
		bool[] total=new bool[a.length];
		foreach(i;a.postorder(result.input)) s~=totalCode(a,a.at(i),total);
		enforce(total[id],"missing totality proof");
		s~="theorem total_root (ρ : Env) : Value.Defined "~ev(id)~" := "~totalRef(id)~"\n";
		s~="def d"~to!string(id)~" (_ : Env) : Prop := True\n";
		s~="theorem definedness (ρ : Env) : Expr.Defined ρ "~name(id)~" ↔ "~dc(id)~" := (Iff.of_eq (congrArg Value.Defined "~evalEq(id)~")).trans (iff_true_intro (total_root ρ))\n#qsym_check_axioms definedness\n";
		s~="theorem everywhere_defined (ρ : Env) : Expr.Defined ρ "~name(id)~" := Eq.mpr (congrArg Value.Defined "~evalEq(id)~") (total_root ρ)\n#qsym_check_axioms everywhere_defined\n";
		return s~"end QSym.Certificate\n";
	}
	foreach(i;inputOrder) s~=domainCode(a,a.at(i));
	s~="theorem definedness (ρ : Env) : Expr.Defined ρ "~name(result.input.id)~" ↔ "~dc(result.input.id)~" := (Iff.of_eq (congrArg Value.Defined "~evalEq(result.input.id)~")).trans "~ds(result.input.id)~"\n#qsym_check_axioms definedness\n";
	if(domain(a,result.input).everywhere){
		bool[] total=new bool[a.length];
		foreach(i;a.postorder(result.input)) s~=totalCode(a,a.at(i),total);
		enforce(total[result.input.id],"missing totality proof");
		s~="theorem everywhere_defined (ρ : Env) : Expr.Defined ρ "~name(result.input.id)~" := "~
			"Eq.mpr (congrArg Value.Defined "~evalEq(result.input.id)~") "~totalRef(result.input.id)~"\n#qsym_check_axioms everywhere_defined\n";
	}
	return s~"end QSym.Certificate\n";
}

/// Join two checked simplification paths. Failure to find a shared result is
/// "unknown", not inequivalence. In erasure mode the theorem compares measures.
string exportEquivalence(Arena a,Result left,Result right){
	import std.string:replace;
	enforce(left.output==right.output,"no shared normal form; equivalence remains unknown");
	enforce(a.sort(left.proofInput)==a.sort(right.proofInput),"proof endpoint types differ");
	enforce(left.assumptions==right.assumptions,"equivalence requires the same assumptions");
	auto l=exportLean(a,left).replace("QSym.Certificate","QSym.LeftCertificate");
	auto r=exportLean(a,right).replace("QSym.Certificate","QSym.RightCertificate");
	r=r.replace("import QSym\n","");
	string hypotheses,arguments;
	foreach(i,f;left.assumptions){
		auto h="h"~to!string(i);
		hypotheses~="\n    ("~h~" : Expr.eval ρ LeftCertificate."~name(f.id)~" = some true)";
		arguments~=" "~h;
	}
	return l~"\n"~r~"\nnamespace QSym\n"~
		"theorem equivalence (ρ : Env)"~hypotheses~"\n"~
		"    (hl : Expr.Defined ρ LeftCertificate."~name(left.proofInput.id)~")\n"~
		"    (hr : Expr.Defined ρ RightCertificate."~name(right.proofInput.id)~") :\n"~
		"    Expr.eval ρ LeftCertificate."~name(left.proofInput.id)~
		" = Expr.eval ρ RightCertificate."~name(right.proofInput.id)~" :=\n"~
		"  (LeftCertificate.simplification ρ"~arguments~" hl).trans (RightCertificate.simplification ρ"~arguments~" hr).symm\n"~
		"#qsym_check_axioms equivalence\nend QSym\n";
}

string exportDomainLean(Arena a,Term source,Result result){
	auto conditions=domainConditions(a,source),condition=conditions[source.id];
	enforce(result.input==condition&&result.proofInput==condition,"domain certificate input changed");
	auto code=exportLean(a,result)~"\nnamespace QSym.DomainCertificate\n";
	bool[] needed=new bool[a.length];
	foreach(root;[source,condition]) foreach(id;a.viewPostorder(root)) needed[id]=true;
	foreach(id;a.viewPostorder(source)) foreach(j;a.viewPostorder(conditions[id])) needed[j]=true;
	foreach(i,yes;needed) if(yes){
		auto t=a.at(cast(uint)i);
		code~=syntaxCode(a,t)~valueCode(a,t);
	}
	string ref_(uint id){ return "(q"~to!string(id)~" ρ)"; }
	string arg(string label,uint id){ return " ("~label~" := "~ev(id)~")"; }
	foreach(id;a.viewPostorder(source)){
		auto n=a.view(a.at(id)); string p;
		final switch(n.op){
			case Op.realLit,Op.complexLit,Op.boolLit,Op.variable,Op.lebesgue,Op.numberLit:
				p="Domain.leaf _"; break;
			case Op.builtin:
				auto info=builtinInfo(cast(Builtin)n.value),f="Functions."~info.code;
				if(!n.arity) p="Domain.leaf _";
				else{
					p="Domain."~(info.total?"total":"partial")~to!string(n.arity)~" "~f~arg("x",n.a);
					p~=n.arity==1?arg("d",conditions[n.a].id):arg("y",n.b)~arg("dx",conditions[n.a].id)~arg("dy",conditions[n.b].id);
					if(!info.total) p~=arg("p",domainPredicate(a,a.at(id)).id);
					p~=" ";
					p~=info.total?(n.arity==1?"(fun _ => True.intro)":"(fun _ _ => True.intro)"):
						"(Domain.test_"~info.code~" "~ev(n.a)~(n.arity==2?" "~ev(n.b):"")~")";
					p~=" "~ref_(n.a)~(n.arity==2?" "~ref_(n.b):"");
				}
				break;
			case Op.add,Op.mul,Op.densityAt,Op.lt,Op.le:
				p="Domain.strict2"~arg("x",n.a)~arg("y",n.b)~arg("dx",conditions[n.a].id)~arg("dy",conditions[n.b].id)~
					" (Value."~domainLemma(n)~" "~ev(n.a)~" "~ev(n.b)~") "~ref_(n.a)~" "~ref_(n.b); break;
			case Op.inv:p="Domain.inverse"~arg("x",n.a)~arg("d",conditions[n.a].id)~" "~ref_(n.a); break;
			case Op.nonzero,Op.conj,Op.puncture,Op.forget,Op.pow,Op.not_,Op.abs:
				p="Domain.transport"~arg("x",n.a)~arg("d",conditions[n.a].id)~" (Value."~domainLemma(n)~" "~ev(n.a)~") "~ref_(n.a); break;
			case Op.mask,Op.and_,Op.or_:
				p="Domain."~(n.op==Op.mask?"mask":n.op==Op.and_?"and":"or")~arg("p",n.a)~arg(n.op==Op.mask?"x":"q",n.b)~
					arg("dp",conditions[n.a].id)~arg(n.op==Op.mask?"dx":"dq",conditions[n.b].id)~" "~ref_(n.a)~" "~ref_(n.b); break;
		}
		code~="theorem q"~to!string(id)~" (ρ : Env) : Domain.Correct "~ev(id)~" "~ev(conditions[id].id)~" :=\n  "~p~"\n";
	}
	string hypotheses,arguments;
	foreach(i,f;result.assumptions){
		auto h="h"~to!string(i);
		hypotheses~=" ("~h~" : Expr.eval ρ Certificate."~name(f.id)~" = some true)";
		arguments~=" "~h;
	}
	auto output="(Expr.eval ρ Certificate."~name(result.output.id)~")";
	code~="theorem domain_correct (ρ : Env)"~hypotheses~" : Domain.Correct "~exprEval(source.id)~" "~output~" :=\n  "~
		"Domain.simplify "~ref_(source.id)~" (Certificate.refinement ρ"~arguments~")\n#qsym_check_axioms domain_correct\n";
	code~="theorem domain_total (ρ : Env)"~hypotheses~" : Value.Defined "~output~" :=\n  "~
		"(domain_correct ρ"~arguments~").total\n#qsym_check_axioms domain_total\n";
	code~="theorem domain_iff (ρ : Env)"~hypotheses~" : Expr.Defined ρ "~name(source.id)~" ↔ "~output~" = some true :=\n  "~
		"(domain_correct ρ"~arguments~").iff\n#qsym_check_axioms domain_iff\nend QSym.DomainCertificate\n";
	return code;
}
