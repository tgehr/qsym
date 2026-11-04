module qsym.proof;
import qsym.ir;
import qsym.simplify;
import qsym.domain;
import qsym.derive;
import qsym.spec:leanSort;
import std.conv:to;
import std.exception:enforce;
import std.array:join;
@safe:

private string name(uint i){ return "n"~to!string(i); }
private string ev(uint i){ return "(Expr.eval ρ "~name(i)~")"; }
private string dc(uint i){ return "(d"~to!string(i)~" ρ)"; }
private string ds(uint i){ return "(domain_"~to!string(i)~" ρ)"; }
private string rat(Rational q){ return "(("~to!string(q.numerator)~") / ("~to!string(q.denominator)~") : ℚ)"; }

string leanConstructor(Arena a,Node n){
	string suffix=n.sort==Sort.real_?"R":"C";
	string op;
	final switch(n.op){
		case Op.realLit:return "(.real ("~to!string(n.value)~"))";
		case Op.complexLit:return "(.complex ("~to!string(n.value)~") ("~to!string(n.imaginary)~"))";
		case Op.numberLit:
			auto q=a.number(n);
			return n.sort==Sort.real_?"(.ratR "~rat(q.re)~")":"(.ratC "~rat(q.re)~" "~rat(q.im)~")";
		case Op.boolLit:return "(.bool "~(n.value?"true":"false")~")";
		case Op.variable:
			return "(.var"~(n.sort==Sort.boolean?"B":suffix)~" "~to!string(n.value)~")";
		case Op.add:op="add"~suffix; break;
		case Op.mul:op="mul"~suffix; break;
		case Op.inv:op="inv"~suffix; break;
		case Op.pow:return "(.pow"~suffix~" "~name(n.a)~" "~to!string(n.value)~")";
		case Op.abs:op="absR"; break;
		case Op.not_:op="not"; break;
		case Op.and_:op="and"; break;
		case Op.or_:op="or"; break;
		case Op.lt:op="ltR"; break;
		case Op.le:op="leR"; break;
		case Op.nonzero:op="nonzero"~(a.sort(a.at(n.a))==Sort.real_?"R":"C"); break;
		case Op.mask:op="mask"~suffix; break;
		case Op.conj:op="conj"; break;
		case Op.lebesgue:op="lebesgue"; break;
		case Op.puncture:op="puncture"; break;
		case Op.densityAt:op="densityAt"; break;
		case Op.forget:op="forget"; break;
	}
	return "(."~op~(n.arity>=1?" "~name(n.a):"")~
		(n.arity==2?" "~name(n.b):"")~")";
}

private string semantic(Arena a,Node n){
	final switch(n.op){
		case Op.realLit:return "some (("~to!string(n.value)~" : Int) : ℝ)";
		case Op.complexLit:
			return "some ((("~to!string(n.value)~" : Int) : ℂ) + (("~
				to!string(n.imaginary)~" : Int) : ℂ) * Complex.I)";
		case Op.numberLit:
			auto q=a.number(n);
			return n.sort==Sort.real_?"some ("~rat(q.re)~" : ℝ)":
				"some (("~rat(q.re)~" : ℂ) + ("~rat(q.im)~" : ℂ) * Complex.I)";
		case Op.boolLit:return "some "~(n.value?"true":"false");
		case Op.variable:
			return "some (ρ."~leanSort(n.sort)~" "~to!string(n.value)~")";
		case Op.add:return "Value.add "~ev(n.a)~" "~ev(n.b);
		case Op.mul:return "Value.mul "~ev(n.a)~" "~ev(n.b);
		case Op.inv:return "Value.inv "~ev(n.a);
		case Op.pow:return ev(n.a)~".map (fun x => x ^ "~to!string(n.value)~")";
		case Op.abs:return "Value.abs "~ev(n.a);
		case Op.not_:return "Value.not "~ev(n.a);
		case Op.and_:return "Value.and "~ev(n.a)~" "~ev(n.b);
		case Op.or_:return "Value.or "~ev(n.a)~" "~ev(n.b);
		case Op.lt:return "Value.lt "~ev(n.a)~" "~ev(n.b);
		case Op.le:return "Value.le "~ev(n.a)~" "~ev(n.b);
		case Op.nonzero:return "Value.nonzero "~ev(n.a);
		case Op.mask:return "Value.mask "~ev(n.a)~" "~ev(n.b);
		case Op.conj:return "Value.conj "~ev(n.a);
		case Op.lebesgue:return "some Density.lebesgue";
		case Op.puncture:return ev(n.a)~".map Density.puncture";
		case Op.densityAt:return "Value.densityAt "~ev(n.a)~" "~ev(n.b);
		case Op.forget:return ev(n.a)~".map Density.forget";
	}
}

private string domainCode(Arena a,Term t){
	auto n=a.node(t);
	auto i=to!string(t.id);
	string cond,proof;
	string sem=semantic(a,n);
	final switch(n.op){
		case Op.realLit,Op.complexLit,Op.boolLit,Op.variable,Op.lebesgue,Op.numberLit:
			cond="True"; proof="exact iff_true_intro ⟨_, rfl⟩"; break;
		case Op.add,Op.mul,Op.densityAt,Op.lt,Op.le:
			cond=dc(n.a)~" ∧ "~dc(n.b);
			auto lemma=n.op==Op.add?"defined_add":n.op==Op.mul?"defined_mul":n.op==Op.lt?"defined_lt":n.op==Op.le?"defined_le":"defined_densityAt";
			proof="exact (Value."~lemma~" "~ev(n.a)~" "~ev(n.b)~
				").trans (and_congr "~ds(n.a)~" "~ds(n.b)~")"; break;
		case Op.inv:
			cond="∃ v, "~ev(n.a)~" = some v ∧ v ≠ 0";
			proof="exact Value.defined_inv "~ev(n.a); break;
		case Op.nonzero,Op.conj,Op.not_:
			cond=dc(n.a);
			proof="exact (Value."~(n.op==Op.nonzero?"defined_nonzero":n.op==Op.not_?"defined_not":"defined_conj")~
				" "~ev(n.a)~").trans "~ds(n.a); break;
		case Op.pow,Op.abs:
			cond=dc(n.a);
			proof="exact (Value.defined_map _ "~ev(n.a)~").trans "~ds(n.a); break;
		case Op.puncture,Op.forget:
			cond=dc(n.a);
			proof="exact (Value.defined_map _ "~ev(n.a)~").trans "~ds(n.a); break;
		case Op.mask:
			if(isGuardedInverse(a,t)){
				auto child=a.node(a.at(n.b)).a;
				cond=dc(child);
				sem="Value.mask (Value.nonzero "~ev(child)~") (Value.inv "~ev(child)~")";
				proof="exact (Value.defined_guarded_inv "~ev(child)~").trans "~ds(child);
			}else{
				cond=ev(n.a)~" = some false ∨ ("~ev(n.a)~" = some true ∧ "~dc(n.b)~")";
				proof="exact (Value.defined_mask "~ev(n.a)~" "~ev(n.b)~
					").trans (or_congr Iff.rfl (and_congr Iff.rfl "~ds(n.b)~"))";
			}
			break;
		case Op.and_,Op.or_:
			auto stop=n.op==Op.and_?"false":"true",go=n.op==Op.and_?"true":"false";
			cond=ev(n.a)~" = some "~stop~" ∨ ("~ev(n.a)~" = some "~go~" ∧ "~dc(n.b)~")";
			proof="exact (Value."~(n.op==Op.and_?"defined_and":"defined_or")~" "~ev(n.a)~" "~ev(n.b)~
				").trans (or_congr Iff.rfl (and_congr Iff.rfl "~ds(n.b)~"))"; break;
	}
	return "def d"~i~" (ρ : Env) : Prop := "~cond~"\n"~
		"theorem domain_"~i~" (ρ : Env) : Expr.Defined ρ "~name(t.id)~" ↔ d"~i~" ρ := by\n"~
		"  change Value.Defined ("~sem~") ↔ ("~cond~")\n  "~proof~"\n\n";
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
private string domainEvidence(Arena a,Term source,DomainProof p,string h){
	enforce(p.found,"missing domain evidence");
	if(p.total) return "(show Value.Defined "~ev(p.term.id)~" from ⟨_, rfl⟩)";
	if(p.children.length){
		auto n=a.node(p.term);
		string args=ev(n.a),proof=domainEvidence(a,source,p.children[0],h);
		if(n.arity==2){ args~=" "~ev(n.b); proof="⟨"~proof~", "~domainEvidence(a,source,p.children[1],h)~"⟩"; }
		return "((Value."~domainLemma(n)~" "~args~").mpr "~proof~")";
	}
	auto t=source;
	foreach(i;p.path){
		auto n=a.node(t);
		switch(n.op){
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
private string nodeDefinitions(Arena a,Term[] roots){
	bool[] seen=new bool[a.length]; string[] names;
	foreach(root;roots) foreach(id;a.postorder(root)) if(!seen[id]){ seen[id]=true; names~=name(id); }
	return names.join(", ");
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
	return "  simpa only ["~nodeDefinitions(a,[e.proof.before,e.proof.after])~
		", Expr.eval, Replay.AC.eval, "~ac~", Int.cast_zero, Int.cast_one, zero_mul, add_zero] using\n"~
		"    (Value.refines_of_eq (Replay.AC.sound "~ac~" "~env~" "~left~" "~right~" (by decide)))\n";
}

// The exporter replays named laws and their premises. It never asks an
// algebra tactic to guess why two symbolic endpoints might agree.
string exportLean(Arena a,Result result){
	enforce(result.traced&&result.derivation !is null&&result.derivation.tracing,"proof export requires a recorded derivation");
	auto d=result.derivation;
	enforce(d.arena is a&&result.certificate.context==0,"invalid certificate context");
	enforce(result.certificate.before==result.proofInput&&result.certificate.after==result.output,"certificate endpoints changed");
	bool[] needed=new bool[a.length],used=new bool[d.deductions.length];
	Term[] pending=[result.input,result.proofInput,result.output];
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
	string s="-- Generated certificate. Check with: lake env lean FILE.lean\nimport QSym\nnamespace QSym.Certificate\n";
	foreach(i,n;needed) if(n){ auto t=a.at(cast(uint)i); s~="def "~name(t.id)~" : Expr ."~leanSort(a.sort(t))~" := "~leanConstructor(a,a.node(t))~"\n"; }
	s~="\n";
	foreach(i,yes;used) if(yes){
		auto e=d.deductions[i],p=e.proof;
		auto claim=p.known?ev(p.before.id)~" = "~ev(p.after.id):"Value.Refines "~ev(p.before.id)~" "~ev(p.after.id);
		s~="theorem p"~to!string(i)~" (ρ : Env)"~contexts(d,p.context,true)~" : "~claim~" := by\n";
		string ref_(Proof q){ return reference(d,q); }
		final switch(e.kind){
			case Evidence.rule:
				auto r=e.instance;
				string application="Generated."~r.rule;
				foreach(j,b;r.bindings) application~=" "~(r.naturals[j]?to!string(a.number(b).re.integer):ev(b.id));
				size_t premise,domain;
				if(e.domains.length) s~="  intro v hv\n  have hd : Value.Defined "~ev(p.before.id)~" := ⟨v, hv⟩\n";
				foreach(c;r.conditions){
					if(c.literal) continue;
					application~=" "~(c.defined?domainEvidence(a,p.before,e.domains[domain++],"hd"):ref_(e.premises[premise++]));
				}
				application="("~application~")";
				if(r.reversed){ enforce(r.equality,"cannot reverse a refinement"); application~=".symm"; }
				if(r.equality) application="(Value.refines_of_eq "~application~")";
				s~="  exact "~application~(e.domains.length?" v hv":"")~"\n";
				break;
			case Evidence.trans:s~="  exact "~ref_(e.premises[0])~".trans "~ref_(e.premises[1])~"\n"; break;
			case Evidence.congr:
				auto n=a.node(p.before),m=a.node(p.after);
				s~="  change Value.Refines ("~semantic(a,n)~") ("~semantic(a,m)~")\n";
				string lemma;
				switch(n.op){
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
				s~="  exact Value."~lemma;
				foreach(q;e.premises) s~=" "~ref_(q);
				s~="\n"; break;
			case Evidence.scoped:
				auto n=a.node(p.before),body=e.premises[0];
				auto op=n.op==Op.mask?"mask":n.op==Op.and_?"and":"or";
				s~="  exact Value.refines_"~op~"_under "~ev(n.a)~" "~ev(body.before.id)~" "~ev(body.after.id)~
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
				s~="  exact "~(e.value?h:"Value.not_eq "~h)~"\n"; break;
			case Evidence.transport:
				s~="  exact "~ref_(e.premises[1])~" true "~reference(d,e.premises[0],true)~"\n"; break;
			case Evidence.numeric:
				s~="  apply Value.refines_of_eq\n  norm_num ["~nodeDefinitions(a,[p.before,p.after])~
					", Expr.eval, Value.add, Value.mul, Value.inv, Value.conj, Value.abs, Value.nonzero, Value.lt, Value.le, Complex.ext_iff, Complex.normSq_apply]\n";
				break;
			case Evidence.ac:s~=acEvidence(a,e); break;
		}
		s~="\n";
	}
	s~="theorem refinement (ρ : Env) : Value.Refines "~ev(result.proofInput.id)~" "~ev(result.output.id)~" :=\n  "~reference(d,result.certificate)~"\n#print axioms refinement\n\n";
	s~="theorem simplification (ρ : Env) (h : Expr.Defined ρ "~name(result.proofInput.id)~") : "~
		ev(result.proofInput.id)~" = "~ev(result.output.id)~" := (refinement ρ).eq_of_defined h\n#print axioms simplification\n\n";
	foreach(i,yes;needed) if(yes) s~=domainCode(a,a.at(cast(uint)i));
	s~="theorem definedness (ρ : Env) : Expr.Defined ρ "~name(result.input.id)~" ↔ "~dc(result.input.id)~" := "~ds(result.input.id)~"\n#print axioms definedness\n";
	if(domain(a,result.input).everywhere){
		string[] defs;
		foreach(i,yes;needed) if(yes){ defs~="d"~to!string(i); defs~=name(cast(uint)i); }
		s~="theorem everywhere_defined (ρ : Env) : Expr.Defined ρ "~name(result.input.id)~" := by\n"~
			"  apply (definedness ρ).mpr\n  simp only ["~defs.join(", ")~", Expr.eval]\n  all_goals qsym_defined\n#print axioms everywhere_defined\n";
	}
	return s~"end QSym.Certificate\n";
}

/// Join two checked simplification paths. Failure to find a shared result is
/// "unknown", not inequivalence. In erasure mode the theorem compares measures.
string exportEquivalence(Arena a,Result left,Result right){
	import std.string:replace;
	enforce(left.output==right.output,"no shared normal form; equivalence remains unknown");
	enforce(a.sort(left.proofInput)==a.sort(right.proofInput),"proof endpoint types differ");
	auto l=exportLean(a,left).replace("QSym.Certificate","QSym.LeftCertificate");
	auto r=exportLean(a,right).replace("QSym.Certificate","QSym.RightCertificate");
	r=r.replace("import QSym\n","");
	return l~"\n"~r~"\nnamespace QSym\n"~
		"theorem equivalence (ρ : Env)\n"~
		"    (hl : Expr.Defined ρ LeftCertificate."~name(left.proofInput.id)~")\n"~
		"    (hr : Expr.Defined ρ RightCertificate."~name(right.proofInput.id)~") :\n"~
		"    Expr.eval ρ LeftCertificate."~name(left.proofInput.id)~
		" = Expr.eval ρ RightCertificate."~name(right.proofInput.id)~" := by\n"~
		"  calc\n    _ = Expr.eval ρ LeftCertificate."~name(left.output.id)~
		" := LeftCertificate.simplification ρ hl\n"~
		"    _ = Expr.eval ρ RightCertificate."~name(right.output.id)~" := by rfl\n"~
		"    _ = _ := (RightCertificate.simplification ρ hr).symm\n"~
		"#print axioms equivalence\nend QSym\n";
}
