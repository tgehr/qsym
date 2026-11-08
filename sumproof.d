module qsym.sumproof;
import qsym.sum;
import qsym.ir;
import qsym.proof:leanConstructor;
import qsym.spec:leanSort;
import qsym.table:Table;
import std.conv:to;
import std.exception:enforce;
@safe:

string exportSumLean(SumPool pool,Sum input,Sum output){
	enforce(pool.fold(input)==pool.fold(output),"sum normal forms differ");
	auto a=pool.arena(),scalar=pool.type();
	auto left=pool.terms(input),right=pool.terms(output);
	Term[] atoms; Table!(uint,uint) indices; bool[] needed=new bool[a.length];
	foreach(e;left~right) if(!a.isNumber(e.term)&&!indices.contains(e.term.id)){
		indices.set(e.term.id,cast(uint)atoms.length); atoms~=e.term;
		foreach(id;a.viewPostorder(e.term)) needed[id]=true;
	}
	string rat(Rational q){ return "(("~to!string(q.numerator)~")/("~to!string(q.denominator)~") : ℚ)"; }
	string literal(Number q){ return scalar==Sort.real_?rat(q.re):"("~rat(q.re)~","~rat(q.im)~")"; }
	string code(Summand[] sum){
		string result="[";
		foreach(i,e;sum){
			auto atom=a.isNumber(e.term)?".literal "~literal(a.number(e.term)):".term "~to!string(indices.get(e.term.id,uint.max));
			result~=(i?",":"")~"("~atom~","~to!string(e.count)~")";
		}
		return result~"]";
	}
	string s="import QSym.Sum\nimport QSym.AxiomCheck\nnamespace QSym.SumCertificate\nattribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv\nset_option maxRecDepth 8192\n";
	foreach(i,yes;needed) if(yes){
		auto t=a.at(cast(uint)i);
		s~="def n"~to!string(i)~" : Expr ."~leanSort(a.sort(t))~" := "~leanConstructor(a,a.view(t))~"\n";
	}
	auto coeff=scalar==Sort.real_?"ℚ":"(ℚ × ℚ)",model=scalar==Sort.real_?"Sum.real":"Sum.complex";
	auto value="Option (Ty.denote ."~leanSort(scalar)~")";
	s~="noncomputable def atoms (ρ : Env) (i : Nat) : "~value~" :=\n  ([";
	foreach(i,t;atoms) s~=(i?",":"")~"Expr.eval ρ n"~to!string(t.id);
	s~="] : List ("~value~")).getD i none\n";
	s~="def input : Sum.Expr "~coeff~" := "~code(left)~"\ndef output : Sum.Expr "~coeff~" := "~code(right)~"\n";
	s~="theorem simplification (ρ : Env) : Sum.eval "~model~" (atoms ρ) input = Sum.eval "~model~" (atoms ρ) output :=\n  Sum.sound "~model~" (atoms ρ) input output rfl\n#qsym_check_axioms simplification\n";
	s~="theorem definedness (ρ : Env) : Value.Defined (Sum.eval "~model~" (atoms ρ) input) ↔ Value.Defined (Sum.eval "~model~" (atoms ρ) output) := Iff.of_eq (congrArg Value.Defined (simplification ρ))\n#qsym_check_axioms definedness\nend QSym.SumCertificate\n";
	return s;
}
