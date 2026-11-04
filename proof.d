module qsym.proof;
import qsym.ir;
import qsym.simplify;
import qsym.domain;
import qsym.derive;
import qsym.spec:leanSort;
import std.conv:to;
import std.exception:enforce;
@safe:

private string name(uint i){ return "n"~to!string(i); }
private string ev(uint i){ return "(Expr.eval ρ "~name(i)~")"; }
private string dc(uint i){ return "(d"~to!string(i)~" ρ)"; }
private string ds(uint i){ return "(domain_"~to!string(i)~" ρ)"; }
private string rat(Rational q){ return "(("~to!string(q.numerator)~") / ("~to!string(q.denominator)~") : ℚ)"; }

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

private string domainCode(Arena a,Term t){
	auto n=a.node(t);
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
				auto child=a.node(a.at(n.b)).a;
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
		"theorem domain_"~i~" (ρ : Env) : Expr.Defined ρ "~name(t.id)~" ↔ d"~i~" ρ :=\n  "~proof~"\n\n";
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
	auto n=a.node(t);
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
				auto child=a.node(a.at(n.b)).a;
				if(total[child]) proof="(Value.defined_guarded_inv "~ev(child)~").mpr "~totalRef(child);
			}else{
				auto p=a.node(a.at(n.a));
				if(p.op==Op.boolLit){
					if(!p.value) proof="⟨_, rfl⟩";
					else if(total[n.b]) proof=totalRef(n.b);
				}
			}
			break;
		case Op.and_,Op.or_:
			auto p=a.node(a.at(n.a));
			if(p.op==Op.boolLit&&p.value==(n.op==Op.or_)) proof="⟨_, rfl⟩";
			else if(total[n.a]&&total[n.b]) proof="Value.defined_"~(n.op==Op.and_?"and":"or")~
				"_total "~ev(n.a)~" "~ev(n.b)~" "~totalRef(n.a)~" "~totalRef(n.b);
			break;
	}
	total[t.id]=proof.length!=0;
	return proof.length?"theorem total_"~to!string(t.id)~" (ρ : Env) : Expr.Defined ρ "~name(t.id)~" :=\n  "~proof~"\n":"";
}
private string domainEvidence(Arena a,Derivation d,Term source,DomainProof p,string h){
	if(p.assumption){
		source=d.contexts[p.assumption].guard;
		h="(show Value.Defined "~ev(source.id)~" from ⟨_, g"~to!string(p.assumption)~"⟩)";
	}
	enforce(p.found,"missing domain evidence");
	if(p.total) return "(show Value.Defined "~ev(p.term.id)~" from ⟨_, rfl⟩)";
	if(p.children.length){
		auto n=a.node(p.term);
		if(n.op==Op.builtin){
			auto info=builtinInfo(cast(Builtin)n.value);
			enforce(info.total,"partial function is not total");
			string proof="(Functions."~info.code~".total (fun "~(n.arity==1?"_":"_ _")~" => True.intro) "~ev(n.a);
			if(n.arity==2) proof~=" "~ev(n.b);
			foreach(child;p.children) proof~=" "~domainEvidence(a,d,source,child,h);
			return proof~")";
		}
		string args=ev(n.a),proof=domainEvidence(a,d,source,p.children[0],h);
		if(n.arity==2){ args~=" "~ev(n.b); proof="⟨"~proof~", "~domainEvidence(a,d,source,p.children[1],h)~"⟩"; }
		return "((Value."~domainLemma(n)~" "~args~").mpr "~proof~")";
	}
	auto t=source;
	foreach(i;p.path){
		auto n=a.node(t);
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
		t=a.child(t,i);
	}
	enforce(t==p.term,"bad domain projection");
	return h;
}
private string acEvidence(Arena a,Deduction e){
	import qsym.table:Table;
	auto op=e.value?Op.mul:Op.add;
	Term[] atoms; Table!(uint,uint) ids;
	string tree(Term t){
		auto n=a.node(t);
		if(n.op==op) return "(.node "~tree(a.at(n.a))~" "~tree(a.at(n.b))~")";
		if(a.isNumber(t)&&(e.value?a.number(t).one:a.number(t).zero)) return ".unit";
		auto i=ids.get(t.id,uint.max);
		if(i==uint.max){ i=cast(uint)atoms.length; ids.set(t.id,i); atoms~=t; }
		return "(.leaf "~to!string(i)~")";
	}
	auto left=tree(e.proof.before),right=tree(e.proof.after);
	auto ac="Replay."~(e.value?"mul":"add")~(a.sort(e.proof.before)==Sort.real_?"R":"C");
	string env="(fun i => match i with";
	foreach(i,t;atoms) env~=" | "~to!string(i)~" => "~ev(t.id);
	env~=" | _ => none)";
	return "  Value.refines_of_eq (Replay.AC.sound "~ac~" "~env~" "~left~" "~right~
		" (of_decide_eq_true rfl))\n";
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
	bool[] needed=new bool[a.length],used=new bool[d.deductions.length];
	Term[] pending=[result.input,result.proofInput,result.output];
	pending~=result.assumptions;
	Proof[] proofs=[result.certificate];
	while(proofs.length){
		auto p=proofs[$-1]; --proofs.length;
		pending~=[p.before,p.after];
		if(p.id==uint.max) continue;
		enforce(p.id<used.length,"invalid proof index");
		if(used[p.id]) continue;
		used[p.id]=true; auto e=d.deductions[p.id]; proofs~=e.premises;
		pending~=e.instance.bindings;
		foreach(c;e.instance.conditions) pending~=c.term;
		for(auto c=e.proof.context;c;c=d.contexts[c].parent) pending~=d.contexts[c].guard;
	}
	foreach(t;pending) foreach(id;a.postorder(t)) needed[id]=true;
	string s="-- Generated certificate. Check with: lake env lean FILE.lean\nimport QSym\nnamespace QSym.Certificate\nattribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv\n";
	foreach(i,n;needed) if(n){ auto t=a.at(cast(uint)i); s~="def "~name(t.id)~" : Expr ."~leanSort(a.sort(t))~" := "~leanConstructor(a,a.node(t))~"\n"; }
	s~="\n";
	foreach(i,yes;used) if(yes){
		auto e=d.deductions[i],p=e.proof;
		auto claim=p.known?ev(p.before.id)~" = "~ev(p.after.id):"Value.Refines "~ev(p.before.id)~" "~ev(p.after.id);
		s~="theorem p"~to!string(i)~" (ρ : Env)"~contexts(d,p.context,true)~" : "~claim~" :=\n";
		string ref_(Proof q){ return reference(d,q); }
		final switch(e.kind){
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
				auto n=a.node(p.before);
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
				auto n=a.node(p.before),body=e.premises[0];
				auto op=n.op==Op.mask?"mask":n.op==Op.and_?"and":"or";
				s~="  Value.refines_"~op~"_under "~ev(n.a)~" "~ev(body.before.id)~" "~ev(body.after.id)~
					" (fun g"~to!string(body.context)~" => "~ref_(body)~")\n";
				break;
			case Evidence.assumption:
				auto t=d.contexts[e.assumptionScope].guard;
				string h="g"~to!string(e.assumptionScope);
				foreach(j;e.path){
					auto n=a.node(t);
					auto lemma=n.op==Op.not_?"of_not":(n.op==Op.and_?"and_true_":"or_false_")~(j==0?"left":"right");
					h="(Value."~lemma~" "~h~")"; t=a.child(t,j);
				}
				s~="  "~(e.value?h:"Value.not_eq "~h)~"\n"; break;
			case Evidence.transport:
				s~="  "~ref_(e.premises[1])~" true "~reference(d,e.premises[0],true)~"\n"; break;
			case Evidence.numeric:
				s~="  Numeric.sound ρ "~name(p.before.id)~" "~name(p.after.id)~" rfl\n";
				break;
			case Evidence.ac:s~=acEvidence(a,e); break;
		}
		s~="\n";
	}
	s~="theorem refinement (ρ : Env)"~contexts(d,context,true)~" : Value.Refines "~ev(result.proofInput.id)~" "~ev(result.output.id)~" :=\n  "~reference(d,result.certificate)~"\n#qsym_check_axioms refinement\n\n";
	s~="theorem simplification (ρ : Env)"~contexts(d,context,true)~" (h : Expr.Defined ρ "~name(result.proofInput.id)~") : "~
		ev(result.proofInput.id)~" = "~ev(result.output.id)~" := (refinement ρ"~contexts(d,context,false)~").eq_of_defined h\n#qsym_check_axioms simplification\n\n";
	auto inputOrder=a.postorder(result.input);
	foreach(i;inputOrder) s~=domainCode(a,a.at(i));
	s~="theorem definedness (ρ : Env) : Expr.Defined ρ "~name(result.input.id)~" ↔ "~dc(result.input.id)~" := "~ds(result.input.id)~"\n#qsym_check_axioms definedness\n";
	if(domain(a,result.input).everywhere){
		bool[] total=new bool[a.length];
		foreach(i;inputOrder) s~=totalCode(a,a.at(i),total);
		enforce(total[result.input.id],"missing totality proof");
		s~="theorem everywhere_defined (ρ : Env) : Expr.Defined ρ "~name(result.input.id)~" := "~
			totalRef(result.input.id)~"\n#qsym_check_axioms everywhere_defined\n";
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
