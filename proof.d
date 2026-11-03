module qsym.proof;
import qsym.ir;
import qsym.simplify;
import qsym.domain;
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

/// Emits a closed statement about the ORIGINAL input and actual output, with
/// explicit congruence and instantiated rule proofs. D is not trusted by Lean.
/// Fast-mode results cannot accidentally be exported as checked results.
string exportLean(Arena a,Result result){
	enforce(result.traced,"proof export requires Options.trace = true");
	a.check(result.input); a.check(result.proofInput); a.check(result.output);
	string s="-- Generated certificate. Check with: lake env lean FILE.lean\n"~
		"import QSym\nnamespace QSym.Certificate\n";

	// Only export nodes referenced by the certificate, retaining DAG sharing.
	bool[] needed=new bool[a.length];
	Term[] pending=[result.input,result.proofInput,result.output];
	foreach(step;result.steps){
		pending~=[step.before,step.rebuilt,step.result,step.algebraInput];
		foreach(ap;step.applied){
			pending~=[ap.before,ap.rule.result]; pending~=ap.rule.bindings;
		}
	}
	size_t cursor;
	while(cursor<pending.length){
		auto t=pending[cursor++]; a.check(t);
		if(needed[t.id]) continue;
		needed[t.id]=true;
		auto n=a.node(t);
		if(n.arity>=1) pending~=a.at(n.a);
		if(n.arity==2) pending~=a.at(n.b);
	}
	foreach(i,used;needed) if(used){
		auto n=a.node(a.at(cast(uint) i));
		s~="def "~name(cast(uint) i)~" : Expr ."~leanSort(n.sort)~" := "~leanConstructor(a,n)~"\n";
	}
	s~="\n";

	foreach(step;result.steps){
		auto n=a.node(step.before),rebuilt=a.node(step.rebuilt);
		s~="theorem h"~to!string(step.before.id)~" (ρ : Env) : Value.Refines "~ev(step.before.id)~
			" "~ev(step.result.id)~" := by\n";
		s~="  have h0 : Value.Refines "~ev(step.before.id)~" "~ev(step.rebuilt.id)~" := by\n";
		if(step.before==step.rebuilt) s~="    exact Value.refines_refl _\n";
		else{
			s~="    change Value.Refines ("~semantic(a,n)~") ("~semantic(a,rebuilt)~")\n";
			auto h1="(h"~to!string(n.a)~" ρ)",h2="(h"~to!string(n.b)~" ρ)";
			string lemma;
			switch(n.op){
				case Op.add:lemma="refines_add "~h1~" "~h2; break;
				case Op.mul:lemma="refines_mul "~h1~" "~h2; break;
				case Op.inv:lemma="refines_inv "~h1; break;
				case Op.nonzero:lemma="refines_nonzero "~h1; break;
				case Op.conj:lemma="refines_conj "~h1; break;
				case Op.not_:lemma="refines_not "~h1; break;
				case Op.and_:lemma="refines_and "~h1~" "~h2; break;
				case Op.or_:lemma="refines_or "~h1~" "~h2; break;
				case Op.lt:lemma="refines_lt "~h1~" "~h2; break;
				case Op.le:lemma="refines_le "~h1~" "~h2; break;
				case Op.mask:lemma="refines_mask "~h1~" "~h2; break;
				case Op.densityAt:lemma="refines_densityAt "~h1~" "~h2; break;
				case Op.pow,Op.abs,Op.puncture,Op.forget:lemma="refines_map _ "~h1; break;
				default:assert(0,"unexpected congruence");
			}
			s~="    exact Value."~lemma~"\n";
		}
		string chain="h0";
		uint j;
		foreach(ap;step.applied){
			auto hn="h"~to!string(++j);
			s~="  have "~hn~" : Value.Refines "~ev(ap.before.id)~" "~ev(ap.rule.result.id)~
				" := Generated."~ap.rule.rule~" ρ";
			foreach(b;ap.rule.bindings) s~=" "~name(b.id);
			s~="\n"; chain="("~chain~").trans "~hn;
		}
		if(step.algebraInput!=step.result){
			auto hn="h"~to!string(++j);
			s~="  have "~hn~" : Value.Refines "~ev(step.algebraInput.id)~" "~ev(step.result.id)~" := by\n";
			string[] defs;
			foreach(id;a.postorder(step.algebraInput)) defs~=name(id);
			foreach(id;a.postorder(step.result)) defs~=name(id);
			s~="    simp only ["~defs.join(", ")~", Expr.eval]\n    qsym_scalar\n";
			chain="("~chain~").trans "~hn;
		}
		s~="  exact "~chain~"\n\n";
	}
	s~="theorem refinement (ρ : Env) : Value.Refines "~ev(result.proofInput.id)~" "~ev(result.output.id)~
		" := h"~to!string(result.proofInput.id)~" ρ\n#print axioms refinement\n\n";
	s~="theorem simplification (ρ : Env) (h : Expr.Defined ρ "~name(result.proofInput.id)~") : "~
		ev(result.proofInput.id)~" = "~ev(result.output.id)~" := (refinement ρ).eq_of_defined h\n"~
		"#print axioms simplification\n\n";

	foreach(i,used;needed) if(used) s~=domainCode(a,a.at(cast(uint) i));
	s~="theorem definedness (ρ : Env) : Expr.Defined ρ "~name(result.input.id)~
		" ↔ "~dc(result.input.id)~" := "~ds(result.input.id)~"\n";
	s~="#print axioms definedness\n";
	if(domain(a,result.input).everywhere){
		s~="theorem everywhere_defined (ρ : Env) : Expr.Defined ρ "~name(result.input.id)~" := by\n"~
			"  apply (definedness ρ).mpr\n  simp only [";
		string[] defs;
		foreach(i,used;needed) if(used){ defs~="d"~to!string(i); defs~=name(cast(uint) i); }
		s~=defs.join(", ")~", Expr.eval]\n  all_goals qsym_defined\n#print axioms everywhere_defined\n";
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
