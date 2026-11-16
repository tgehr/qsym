// Untrusted native proof construction for checked sparse arithmetic.
module qsym.algebra_proof;
import qsym.ir;
import qsym.budget:Budget;
import qsym.polynomial:Arithmetic,Polynomial,Powers;
import qsym.proof:leanSyntaxCode;
import qsym.spec:leanSort;
import std.algorithm:sort;
import std.conv:to;
import std.exception:enforce;
@safe:

package class AlgebraExporter {
	Arena a;
	Arithmetic arithmetic;
	Polynomial[uint] values;
	string[uint] proofs;
	string[string] polynomials;
	Polynomial[string] namedPolynomials;
	string code,namespace_;
	bool[uint] syntax;
	void expression(Term t){foreach(id;a.viewPostorder(t))if(!(id in syntax)){syntax[id]=true;code~=leanSyntaxCode(a,a.at(id));}}
	this(Arena arena,Term input,string ns){
		a=arena;arithmetic=new Arithmetic(a);
		// Certificate construction includes shared intermediate arithmetic checks.
		arithmetic.budget=new Budget(32_000_000,4096,512);namespace_=ns;
		code="import QSym\nnamespace "~ns~"\nopen AlgebraCertificate\nset_option maxRecDepth 8192\nset_option linter.unusedVariables false\nattribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv\n";
		auto ids=a.viewPostorder(input);
		expression(input);
		code~="noncomputable def atoms (ρ : Env) (i : ℕ) : ℂ := ";
		foreach(id;ids){auto n=a.view(a.at(id));if(n.op==Op.variable&&numeric(n.sort))
			code~="if i = "~to!string(id)~" then embed"~field(n.sort)~" (ρ."~leanSort(n.sort)~" "~to!string(n.value)~") else ";
			else if(numeric(n.sort)&&opaque(a.at(id)))code~="if i = "~to!string(id)~" then embed"~field(n.sort)~" ((n"~to!string(id)~".eval ρ).getD 0) else ";}
		code~="0\n";
	}
	bool opaque(Term t){
		auto n=a.view(t);
		return n.op==Op.conj||n.op==Op.abs||n.op==Op.builtin&&
			!(n.value>=Builtin.castNZ&&n.value<=Builtin.castRC||n.value==Builtin.invQ||
			 n.value==Builtin.addN||n.value==Builtin.addZ||n.value==Builtin.addQ||
			 n.value==Builtin.mulN||n.value==Builtin.mulZ||n.value==Builtin.mulQ||
			 n.value>=Builtin.powNN&&n.value<=Builtin.powCN);
	}
	string[uint] totals;
	string total(Term t){
		if(auto old=t.id in totals)return *old;
		auto n=a.view(t);string h;
		string ev(uint id){return "(n"~to!string(id)~".eval ρ)";}
		if(a.isNumber(t)||n.op==Op.variable||n.op==Op.boolLit)h="⟨_, rfl⟩";
		else if(n.op==Op.builtin){
			auto info=builtinInfo(cast(Builtin)n.value);enforce(info.total,"partial opaque scalar atom");
			if(!n.arity)h="⟨_, rfl⟩";
			else {
				auto left=total(a.viewChild(t,0));
				h="Functions."~info.code~".total (fun "~(n.arity==1?"_":"_ _")~" => True.intro) "~ev(n.a);
				if(n.arity==2)h~=" "~ev(n.b);
				h~=" "~left;if(n.arity==2)h~=" "~total(a.viewChild(t,1));
			}
		}else if(n.op==Op.add||n.op==Op.mul){
			auto x=total(a.viewChild(t,0)),y=total(a.viewChild(t,1));
			h="(Value.defined_"~(n.op==Op.add?"add":"mul")~" "~ev(n.a)~" "~ev(n.b)~").mpr ⟨"~x~", "~y~"⟩";
		}else{
			enforce(n.op==Op.pow||n.op==Op.conj||n.op==Op.abs,"partial opaque scalar argument");
			auto x=total(a.viewChild(t,0));
			h="(Value."~(n.op==Op.conj?"defined_conj":"defined_map _")~" "~ev(n.a)~").mpr "~x;
		}
		auto name="total"~to!string(t.id);
		code~="theorem "~name~" (ρ : Env) : Value.Defined "~ev(t.id)~" := "~h~"\n";
		auto result="("~name~" ρ)";totals[t.id]=result;return result;
	}
	static string field(Sort s){
		final switch(s){
		case Sort.natural:return "N";
		case Sort.integer:return "Z";
		case Sort.rational:return "Q";
		case Sort.real_:return "R";
		case Sort.complex:return "C";
		case Sort.boolean,Sort.density,Sort.measure:throw new Exception("nonnumeric algebra field");
		}
	}
	string[string] rationalNames;
	string rational(Rational q){
		if(q.denominator==1)return "("~to!string(q.numerator)~" : ℚ)";
		auto text="(Rat.mk' ("~to!string(q.numerator)~") "~to!string(q.denominator)~" (of_decide_eq_true rfl) (of_decide_eq_true rfl))";
		if(auto old=text in rationalNames)return *old;
		auto name="rat"~to!string(rationalNames.length);rationalNames[text]=name;
		code~="noncomputable def "~name~" : ℚ := "~text~"\n";return name;
	}
	Number[string] coefficients;
	string[string] coefficientNames;
	string coefficient(Number c){
		auto text="("~rational(c.re)~", "~rational(c.im)~")";
		if(auto old=text in coefficientNames)return *old;
		auto name="coef"~to!string(coefficientNames.length);coefficientNames[text]=name;coefficients[name]=c;
		code~="noncomputable def "~name~" : Coefficient := "~text~"\n";return name;
	}

	string poly(Polynomial p){
		auto keys=p.keys;sort!((x,y)=>x<y)(keys);string text="[";
		foreach(i,k;keys){if(i)text~=",";text~="([";for(size_t j;j<k.length;j+=2){if(j)text~=",";text~="("~to!string(k[j])~","~to!string(k[j+1])~")";}text~="],"~coefficient(p[k])~")";}text~="]";
		if(auto old=text in polynomials)return *old;
		auto name="poly"~to!string(polynomials.length);polynomials[text]=name;namedPolynomials[name]=p;
		code~="noncomputable def "~name~" : AlgebraCertificate.Polynomial := "~text~"\n";return name;
	}
	string[string] computations;
	string compute(string lhs,string rhs,string proof="rfl"){
		import std.string:startsWith;
		auto arithmetic=lhs.startsWith("AlgebraCertificate.add ","AlgebraCertificate.mul ","multiplyTerm ");
		auto claim=arithmetic?"ArithmeticEquality ("~lhs~") "~rhs:lhs~" = "~rhs;if(auto old=claim in computations)return *old;
		auto name="calc"~to!string(computations.length);computations[claim]=name;
		code~="theorem "~name~" : "~claim~" := "~proof~"\n";return name;
	}
	string monomial(Powers p){
		string result="[";for(size_t i;i<p.length;i+=2){if(i)result~=",";result~="("~to!string(p[i])~","~to!string(p[i+1])~")";}return result~"]";
	}
	string addCalculation(Polynomial p,Polynomial q){
		auto lhs="AlgebraCertificate.add "~poly(p)~" "~poly(q),rhs=poly(arithmetic.add(p,q));
		return compute(lhs,rhs,"Raw.addition_check "~poly(p)~" "~poly(q)~" "~rhs~" rfl");
	}
	uint rows;
	string termCalculation(Powers m,Number c,Polynomial p){
		Polynomial term;arithmetic.put(term,m,c);
		auto lhs="multiplyTerm "~monomial(m)~" "~coefficient(c)~" "~poly(p),rhs=poly(arithmetic.mul(term,p));
		string h;
		if(!m.length){
			h="Raw.Mapped.sound (m := []) (c := "~coefficient(c)~") (p := "~poly(p)~") (q := "~rhs~") (Raw.mappedSame_sound rfl)";
		}else{
			auto keys=p.keys;sort(keys);string text="[";
			Polynomial unit;arithmetic.put(unit,m,Number(1));
			foreach(k;keys){
				auto d=arithmetic.budget.calc!"*"(c,p[k]);
				if(d.zero)continue;
				Polynomial atom;arithmetic.put(atom,k,Number(1));auto outKey=arithmetic.mul(unit,atom).keys[0];
				if(text.length>1)text~=",";text~="("~monomial(outKey)~","~coefficient(d)~")";
			}
			text~="]";auto row="row"~to!string(rows++);
			code~="noncomputable def "~row~" : AlgebraCertificate.Polynomial := "~text~"\n";
			h="Raw.mapped_check "~monomial(m)~" "~coefficient(c)~" "~poly(p)~" "~row~" "~rhs~" (Raw.mappedSame_sound rfl) rfl";
		}
		return compute(lhs,rhs,h);
	}
	string mulCalculation(Polynomial p,Polynomial q){
		auto lhs="AlgebraCertificate.mul "~poly(p)~" "~poly(q),rhs=poly(arithmetic.mul(p,q));
		auto claim="ArithmeticEquality ("~lhs~") "~rhs;if(auto old=claim in computations)return *old;
		string h;
		if(p.length>q.length&&q.length&&p.length*q.length>16)h="Raw.mul_swap "~mulCalculation(q,p);
		else if(p.length&&p.length*q.length>16){
			auto keys=p.keys;sort(keys);auto m=keys[0],c=p[m],tail=p.dup;tail.remove(m);
			Polynomial term;arithmetic.put(term,m,c);auto a=arithmetic.mul(term,q),b=arithmetic.mul(tail,q);
			auto ht=termCalculation(m,c,q),hp=mulCalculation(tail,q),ha=addCalculation(a,b);
			h="Raw.mul_cons_check "~poly(p)~" (m := "~monomial(m)~") (c := "~coefficient(c)~") (p := "~poly(tail)~") (q := "~poly(q)~") (a := "~poly(a)~") (b := "~poly(b)~") "~ht~" "~hp~" "~ha~" rfl";
		}else h="Raw.mul_check "~poly(p)~" "~poly(q)~" "~rhs~" rfl";
		return compute(lhs,rhs,h);
	}
	// Expression trees here are built by this emitter, never parsed from source
	// programs. Composite arithmetic witnesses are split before elaboration.
	struct Calculated {Polynomial value;string proof;}
	Calculated calculation(string expression){
		import std.string:strip;
		expression=expression.strip;
		if(expression[0]=='('&&expression[$-1]==')')expression=expression[1..$-1];
		if(auto p=expression in namedPolynomials)return Calculated(*p,"rfl");
		string[] parts;size_t begin,depth;
		foreach(i,c;expression){if(c=='('||c=='[')++depth;else if(c==')'||c==']')--depth;else if(c==' '&&!depth){if(begin<i)parts~=expression[begin..i];begin=i+1;}}
		parts~=expression[begin..$];
		if(parts[0]=="multiplyTerm"){
			enforce(parts.length==4&&parts[1]=="[]"&&(parts[2] in coefficients) !is null,"unsupported scaled calculation");
			auto p=calculation(parts[3]);enforce(p.proof=="rfl");
			return Calculated(arithmetic.mul(arithmetic.constant(coefficients[parts[2]]),p.value),termCalculation(null,coefficients[parts[2]],p.value));
		}
		enforce(parts.length==3,"unsupported arithmetic calculation");
		auto p=calculation(parts[1]),q=calculation(parts[2]);
		auto add=parts[0]=="AlgebraCertificate.add";enforce(add||parts[0]=="AlgebraCertificate.mul");
		auto r=add?arithmetic.add(p.value,q.value):arithmetic.mul(p.value,q.value);
		auto h=add?addCalculation(p.value,q.value):mulCalculation(p.value,q.value);
		if(p.proof!="rfl"||q.proof!="rfl"){
			enforce(add,"nested multiplication certificate");
			h=compute(expression,poly(r),"add_computed (a := "~poly(p.value)~") (b := "~poly(q.value)~") ("~(p.proof=="rfl"?"ArithmeticEquality.refl _":p.proof)~") ("~(q.proof=="rfl"?"ArithmeticEquality.refl _":q.proof)~") "~h);
		}
		return Calculated(r,h);
	}
	string[string] powers;
	string powered(Polynomial p,uint n){
		auto base=poly(p),key=base~":"~to!string(n);if(auto old=key in powers)return *old;
		string h;
		if(!n)h="Powered.zero σ "~base;
		else if(n<=128||n&1){
			auto previous=powered(p,n-1);
			h="Powered.succ "~previous~" "~mulCalculation(arithmetic.power(p,n-1),p);
		}else{
			auto previous=powered(p,n/2);
			h="Powered.double "~previous~" "~mulCalculation(arithmetic.power(p,n/2),arithmetic.power(p,n/2));
		}
		auto target=poly(arithmetic.power(p,n)),name="power"~to!string(powers.length);
		code~="theorem "~name~" (σ : ℕ → ℂ) : Powered σ "~base~" "~to!string(n)~" "~target~" := "~h~"\n";
		auto result="("~name~" σ)";powers[key]=result;return result;
	}
	string prove(Term t){
		if(auto old=t.id in proofs)return *old;
		auto n=a.view(t);Polynomial p;string h;
		if(a.isNumber(t)){
			auto v=a.number(t);p=arithmetic.constant(v);
			auto literal=n.sort==Sort.natural||n.sort==Sort.integer?"("~to!string(v.re.numerator)~")":n.sort==Sort.complex?coefficient(v):rational(v.re);
			h="numeric"~field(n.sort)~" (atoms ρ) ρ n"~to!string(t.id)~" "~literal~" rfl";
		}else if(n.op==Op.variable){
			arithmetic.put(p,[t.id,1].idup,Number(1));
			h="Normalized.atom (atoms ρ) embed"~field(n.sort)~" (ρ."~leanSort(n.sort)~" "~to!string(n.value)~") "~to!string(t.id)~" rfl";
		}else if(opaque(t)){
			arithmetic.put(p,[t.id,1].idup,Number(1));
			h="Normalized.defined_atom (atoms ρ) embed"~field(n.sort)~" (n"~to!string(t.id)~".eval ρ) "~to!string(t.id)~" "~total(t)~" rfl";
		}else{
			auto left=prove(a.viewChild(t,0)),x=values[n.a];
			if(n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castRC){p=x;h=builtinInfo(cast(Builtin)n.value).code~" (a := n"~to!string(n.a)~".eval ρ) "~left;}
			else if(n.op==Op.add||n.op==Op.mul||n.op==Op.builtin&&(n.value==Builtin.addN||n.value==Builtin.addZ||n.value==Builtin.addQ||n.value==Builtin.mulN||n.value==Builtin.mulZ||n.value==Builtin.mulQ)){
				auto right=prove(a.viewChild(t,1)),y=values[n.b];
				auto add=n.op==Op.add||n.op==Op.builtin&&(n.value==Builtin.addN||n.value==Builtin.addZ||n.value==Builtin.addQ);
				p=add?arithmetic.add(x,y):arithmetic.mul(x,y);
				h=n.op==Op.builtin?"Normalized.total"~(add?"Add":"Mul")~" Functions."~builtinInfo(cast(Builtin)n.value).code~" (fun _ _ => rfl) (fun _ _ => True.intro)":"Normalized."~(add?"add":"mul");
				h~=" (a := n"~to!string(n.a)~".eval ρ) (b := n"~to!string(n.b)~".eval ρ) (p := "~poly(x)~") (q := "~poly(y)~") (r := "~poly(p)~") "~left~" "~right~" "~(add?addCalculation(x,y):mulCalculation(x,y));
			}else if(n.op==Op.inv||n.op==Op.builtin&&n.value==Builtin.invQ){
				enforce(x.length==1&&x.keys[0].length==0&&!x.values[0].zero,"nonconstant polynomial inverse");
				auto v=x.values[0];p=arithmetic.constant(arithmetic.budget.calc!"/"(Number(1),v));
				h=(n.op==Op.builtin?"inverseQ":"inverse")~" (a := n"~to!string(n.a)~".eval ρ) (c := "~coefficient(v)~") "~left~" (of_decide_eq_true rfl)";
			}else{
				enforce(n.op==Op.pow||n.op==Op.builtin&&n.value>=Builtin.powNN&&n.value<=Builtin.powCN,"unsupported polynomial proof node");
				auto k=n.op==Op.pow?cast(uint)n.value:cast(uint)a.number(a.viewChild(t,1)).re.integer;p=arithmetic.power(x,k);
				auto hp=powered(x,k);import std.array:replace;hp=replace(hp," σ)"," (atoms ρ))");
				if(n.op==Op.pow)h="Normalized.powered (a := n"~to!string(n.a)~".eval ρ) (q := "~poly(p)~") "~left~" "~hp;
				else h="Normalized.totalPowered (a := n"~to!string(n.a)~".eval ρ) (q := "~poly(p)~") Functions."~builtinInfo(cast(Builtin)n.value).code~" (fun _ _ => rfl) (fun _ _ => True.intro) "~left~" "~to!string(k)~" (Numeric.calculate_sound ρ n"~to!string(n.b)~" "~to!string(k)~" rfl) "~hp;
			}
		}
		values[t.id]=p;auto target=poly(p),name="normal"~to!string(t.id);
		if(a.isNumber(t))h="Normalized.reindex ("~h~") "~compute("AlgebraCertificate.constant "~coefficient(a.number(t)),target);
		code~="theorem "~name~" (ρ : Env) : Normalized (atoms ρ) embed"~field(n.sort)~" (n"~to!string(t.id)~".eval ρ) "~target~" := "~h~"\n";
		auto result="("~name~" ρ)";proofs[t.id]=result;return result;
	}
	string zero(Term input){
	auto proof=prove(input);enforce(!values[input.id].length,"nonzero polynomial certificate");
	auto injective=a.sort(input)==Sort.natural?"Nat.cast_injective":a.sort(input)==Sort.integer?"Int.cast_injective":a.sort(input)==Sort.rational?"Rat.cast_injective":a.sort(input)==Sort.real_?"Complex.ofReal_injective":"Function.injective_id";
	code~="theorem zero (ρ : Env) : n"~to!string(input.id)~".eval ρ = some 0 := Normalized.zero "~injective~" "~proof~"\n#qsym_check_axioms zero\nend "~namespace_~"\n";return code;
	}
}
