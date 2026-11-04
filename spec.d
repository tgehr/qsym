module qsym.spec;
import qsym.ir:Sort,sortName;
import qsym.table:Table;
import qsym.lexer;
import std.conv:to;
import std.exception:enforce;
import std.algorithm:canFind;
@safe:

struct Parameter{ string name; Sort sort; bool natural; }
final class Pattern{
	string name;
	Pattern[] args;
	long number;
	Sort sort;
	bool variable;
	bool natural;
	private uint candidates;
	this(string name){ this.name=name; }
}
struct Premise{ Pattern term; bool defined,literal; }
struct Rule{ string name; Parameter[] parameters; Pattern lhs,rhs; Premise[] premises; bool automatic=true,equality,inference,bounded; }

// Rules are scheduled automatically; lemmas require explicit selection.
// All declarations generate proof obligations, never Lean axioms.
struct Parser{
	string source;
	private Lexer lexer;
	private Token token;
	private void next(){ token=lexer.next(); }
	private bool take(string s){
		if(token.text!=s||token.kind==TokenKind.end) return false;
		next(); return true;
	}
	private void expect(string s){
		enforce(take(s),"expected '"~s~"' at byte "~to!string(token.offset));
	}
	private string ident(){
		enforce(token.kind==TokenKind.identifier,"identifier expected at byte "~to!string(token.offset));
		auto name=token.text; next(); return name;
	}
	private Pattern integer(bool negative=false){
		enforce(token.kind==TokenKind.integer,"integer expected at byte "~to!string(token.offset));
		auto p=new Pattern("#"); p.number=to!long((negative?"-":"")~token.text); next(); return p;
	}
	private Pattern primary(uint depth){
		enforce(depth<128,"rule pattern nesting limit exceeded");
		if(take("(")){ auto p=expression(depth+1); expect(")"); return p; }
		if(take("[")){ auto p=expression(depth+1); expect("]"); return pattern("$iverson",[p]); }
		if(take("|")){ auto p=expression(depth+1); expect("|"); return pattern("absR",[p]); }
		if(take("ⅈ")) return pattern("complex",[integerPattern(0),integerPattern(1)]);
		if(token.kind==TokenKind.integer) return integer();
		auto p=new Pattern(ident());
		if(take("(")){
			if(!take(")")){
				do{ p.args~=expression(depth+1); }while(take(","));
				expect(")");
			}
		}
		if(p.name=="inv"||p.name=="nonzero"||p.name=="mask") p.name="$"~p.name;
		if(p.name=="abs") p.name="absR";
		return p;
	}
	private Pattern factor(uint depth){
		enforce(depth<128,"rule pattern nesting limit exceeded");
		if(take("+")) return factor(depth+1);
		if(take("-")){
			// A signed payload must remain available to real()/complex(), including long.min.
			if(token.kind==TokenKind.integer){
				auto p=integer(true);
				if(token.kind==TokenKind.power||token.text=="^")
					return pattern("$neg",[postfix(pattern("$neg",[p]))]);
				return p;
			}
			return pattern("$neg",[factor(depth+1)]);
		}
		if(take("⅟")) return pattern("$inv",[factor(depth+1)]);
		if(take("!")) return pattern("not",[factor(depth+1)]);
		return postfix(primary(depth));
	}
	private Pattern postfix(Pattern p){
		if(token.kind==TokenKind.power||token.text=="^"){
			long exponent;
			if(token.kind==TokenKind.power){ exponent=to!long(token.text); next(); }
			else{
				expect("^"); auto parens=take("("); auto negative=take("-");
				if(!negative&&(parens||token.kind==TokenKind.identifier)){
					auto e=parens?expression():new Pattern(ident());
					if(parens) expect(")");
					return pattern("$pow",[p,e]);
				}
				exponent=integer(negative).number;
				if(parens) expect(")");
			}
			enforce(exponent>=-(cast(long)uint.max)&&exponent<=uint.max,"exponent exceeds uint range");
			if(exponent!=-1) p=pattern("$pow",[p,integerPattern(exponent<0?-exponent:exponent)]);
			if(exponent<0) p=pattern("$inv",[p]);
		}
		return p;
	}
	private Pattern product(uint depth){
		auto p=factor(depth);
		while(token.text=="*"||token.text=="/"){
			auto op=token.text; next();
			auto q=factor(depth);
			if(op=="/") q=pattern("$inv",[q]);
			p=pattern("$mul",[p,q]);
		}
		return p;
	}
	private Pattern sum(uint depth){
		auto p=product(depth);
		while(token.text=="+"||token.text=="-"){
			auto op=token.text; next();
			auto q=product(depth);
			if(op=="-") q=pattern("$neg",[q]);
			p=pattern("$add",[p,q]);
		}
		return p;
	}
	private Pattern comparison(uint depth){
		auto p=sum(depth);
		Pattern combined;
		while(token.text=="!="||token.text=="="||token.text=="<"||token.text==">"||token.text=="<="||token.text==">="){
			auto op=token.text; next();
			auto q=sum(depth);
			Pattern predicate;
			if(op=="!="||op=="="){
				auto difference=q.name=="#"&&q.number==0?p:pattern("$add",[p,pattern("$neg",[q])]);
				predicate=pattern("$nonzero",[difference]);
				if(op=="=") predicate=pattern("not",[predicate]);
			}else predicate=pattern(op=="<"||op==">"?"ltR":"leR",op==">"||op==">="?[q,p]:[p,q]);
			combined=combined is null?predicate:pattern("and",[combined,predicate]);
			p=q;
		}
		return combined is null?p:combined;
	}
	private Pattern conjunction(uint depth){
		auto p=comparison(depth);
		while(take("&&")) p=pattern("and",[p,comparison(depth)]);
		return p;
	}
	private Pattern expression(uint depth=0){
		auto p=conjunction(depth);
		while(take("||")) p=pattern("or",[p,conjunction(depth)]);
		return p;
	}
	private Parameter parameter(){
		auto name=ident(); expect(":"); auto ty=ident();
		Sort s; bool natural;
		switch(ty){
			case "Real","ℝ":s=Sort.real_; break;
			case "Complex","ℂ":s=Sort.complex; break;
			case "Bool","𝔹":s=Sort.boolean; break;
			case "Density":s=Sort.density; break;
			case "Measure":s=Sort.measure; break;
			case "Nat","ℕ":s=Sort.real_; natural=true; break;
			default:throw new Exception("unknown sort: "~ty);
		}
		enforce(!isConstructor(name)&&name!="inv"&&name!="nonzero"&&name!="mask"&&name!="abs","parameter shadows a constructor");
		return Parameter(name,s,natural);
	}
	Parameter[] parseParameters(){
		lexer=Lexer(source); next();
		Parameter[] parameters;
		do{ parameters~=parameter(); }while(take(","));
		take(";"); enforce(token.kind==TokenKind.end,"unexpected token: "~token.text);
		return parameters;
	}
	Pattern parseExpression(ref Parameter[] parameters){
		lexer=Lexer(source); next(); auto p=expression();
		take(";"); enforce(token.kind==TokenKind.end,"unexpected token: "~token.text);
		void variables(Pattern q,uint depth=0){
			enforce(depth<128,"expression nesting limit exceeded");
			if(!q.args.length&&q.name!="#"&&!isConstructor(q.name)){
				foreach(v;parameters) if(v.name==q.name) return;
				parameters~=Parameter(q.name,Sort.real_);
			}
			foreach(arg;q.args) variables(arg,depth+1);
		}
		variables(p);
		p=lower(p,choose(possible(p,parameters)));
		infer(p,parameters);
		return p;
	}
	Rule[] parse(){
		lexer=Lexer(source); next();
		Rule[] rules;
		while(token.kind!=TokenKind.end){
			auto kind=ident();
			enforce(["rule","rewrite","lemma","equation","fact"].canFind(kind),"unknown declaration kind");
			Rule r; r.automatic=kind=="rule"||kind=="rewrite"; r.bounded=kind=="rewrite";
			r.equality=kind=="equation"; r.inference=kind=="fact"; r.name=ident();
			foreach(old;rules) enforce(old.name!=r.name,"duplicate rule name");
			expect("(");
			if(!take(")")){
				do{
					auto v=parameter();
					foreach(old;r.parameters) enforce(old.name!=v.name,"duplicate parameter");
					r.parameters~=v;
				}while(take(","));
				expect(")");
			}
			expect(":"); r.lhs=expression();
			if(r.inference) r.rhs=pattern("true",[]);
			else{ expect(r.equality?"<=>":"=>"); r.rhs=expression(); }
			if(take("when")) do{
				Premise p;
				if(token.text=="defined"||token.text=="literal"){
					p.defined=take("defined"); if(!p.defined){ expect("literal"); p.literal=true; }
					expect("("); p.term=expression(); expect(")");
				}
				else p.term=expression();
				r.premises~=p;
			}while(take(","));
			expect(";");
			auto candidates=possible(r.lhs,r.parameters)&possible(r.rhs,r.parameters);
			enforce((candidates&~naturalBit)!=0,"rewrite changes its type");
			auto sort=choose(candidates);
			r.lhs=lower(r.lhs,sort); r.rhs=lower(r.rhs,sort);
			foreach(ref p;r.premises){
				auto types=possible(p.term,r.parameters);
				enforce((types&~naturalBit)!=0,"conditions require an IR expression");
				auto ty=p.defined||p.literal?choose(types):Sort.boolean;
				enforce(types&bit(ty),"condition must be Bool");
				p.term=lower(p.term,ty);
			}
			try{ validate(r); }catch(Exception e){ throw new Exception("in "~r.name~": "~e.msg); }
			rules~=r;
		}
		return rules;
	}
}

bool isConstructor(string n){
	return ["real","complex","true","false","addR","addC","mulR","mulC",
		"invR","invC","nonzeroR","nonzeroC","maskR","maskC","conj",
		"lebesgue","puncture","densityAt","forget","powR","powC","not","and","or","ltR","leR","absR"].canFind(n);
}

private Pattern pattern(string name,Pattern[] args){
	auto p=new Pattern(name); p.args=args; return p;
}
private Pattern integerPattern(long n){ auto p=new Pattern("#"); p.number=n; return p; }
private uint bit(Sort s){ return 1u<<cast(uint)s; }
private enum scalars=(1u<<Sort.real_)|(1u<<Sort.complex);
private enum naturalBit=1u<<5;
private Sort choose(uint candidates){
	foreach(s;[Sort.real_,Sort.complex,Sort.boolean,Sort.density,Sort.measure])
		if(candidates&bit(s)) return s;
	assert(0);
}

private struct Signature{ Sort result; Sort[] args; }
private Signature signature(string name){
	alias R=Sort.real_,C=Sort.complex,B=Sort.boolean,D=Sort.density,M=Sort.measure;
	switch(name){
		case "true","false":return Signature(B,[]);
		case "not":return Signature(B,[B]);
		case "and","or":return Signature(B,[B,B]);
		case "ltR","leR":return Signature(B,[R,R]);
		case "lebesgue":return Signature(D,[]);
		case "addR","mulR":return Signature(R,[R,R]);
		case "addC","mulC":return Signature(C,[C,C]);
		case "invR","absR":return Signature(R,[R]);
		case "invC","conj":return Signature(C,[C]);
		case "nonzeroR":return Signature(B,[R]);
		case "nonzeroC":return Signature(B,[C]);
		case "maskR":return Signature(R,[B,R]);
		case "maskC":return Signature(C,[B,C]);
		case "puncture":return Signature(D,[D]);
		case "densityAt":return Signature(R,[D,R]);
		case "forget":return Signature(M,[D]);
		default:throw new Exception("unknown constructor or unbound variable: "~name);
	}
}

// Propagate possible sorts before choosing a default for bare numeric literals.
// Both rule endpoints constrain the choice; there are no implicit scalar casts.
private uint possible(Pattern p,Parameter[] parameters,uint depth=0){
	enforce(depth<128,"rule pattern nesting limit exceeded");
	foreach(v;parameters) if(p.name==v.name){
		enforce(p.args.length==0,"metavariables cannot be applied");
		p.variable=true; p.natural=v.natural; return p.candidates=v.natural?naturalBit:bit(v.sort);
	}
	auto arity=p.args.length;
	if(p.name=="#") return p.candidates=scalars|(p.number>=0&&p.number<=uint.max?naturalBit:0);
	if(p.name=="real"||p.name=="complex"){
		enforce(arity==(p.name=="real"?1:2),"literal arity mismatch");
		foreach(arg;p.args) enforce(arg.name=="#","literal integer expected");
		return p.candidates=bit(p.name=="real"?Sort.real_:Sort.complex);
	}
	uint[] args;
	foreach(arg;p.args) args~=possible(arg,parameters,depth+1);
	uint result;
	switch(p.name){
		case "$pow","powR","powC":
			enforce(arity==2&&(args[1]&naturalBit),"natural exponent expected");
			result=args[0]&(p.name=="$pow"?scalars:bit(p.name=="powR"?Sort.real_:Sort.complex)); break;
		case "$add","$mul":
			enforce(arity==2,"binary operator arity mismatch");
			result=(scalars|naturalBit)&args[0]&args[1]; break;
		case "$neg","$inv":
			enforce(arity==1,"unary operator arity mismatch");
			result=scalars&args[0]; break;
		case "$nonzero":
			enforce(arity==1&&args[0]&scalars,"nonzero requires a scalar");
			result=bit(Sort.boolean); break;
		case "$iverson":
			enforce(arity==1&&args[0]&bit(Sort.boolean),"Iverson brackets require Bool");
			result=scalars; break;
		case "$mask":
			enforce(arity==2&&args[0]&bit(Sort.boolean),"mask requires Bool and a scalar");
			result=scalars&args[1]; break;
		default:
			auto sig=signature(p.name);
			enforce(arity==sig.args.length,"arity mismatch for "~p.name);
			foreach(i,s;sig.args) enforce(args[i]&bit(s),"type mismatch in "~p.name);
			result=bit(sig.result);
	}
	enforce(result!=0,"type mismatch in "~p.name);
	return p.candidates=result;
}

private Pattern literal(long n,Sort s){
	return s==Sort.real_?pattern("real",[integerPattern(n)]):pattern("complex",[integerPattern(n),integerPattern(0)]);
}

private Pattern lowerNat(Pattern p){
	enforce(p.candidates&naturalBit,"natural expression expected");
	p.natural=true;
	if(p.variable||p.name=="#") return p;
	enforce(p.name=="$add"||p.name=="$mul","unsupported natural operation");
	p.name=p.name=="$add"?"natAdd":"natMul";
	foreach(ref arg;p.args) arg=lowerNat(arg);
	return p;
}

private Pattern lower(Pattern p,Sort s){
	enforce(p.candidates&bit(s),"inconsistent elaboration sort");
	if(p.variable) return p;
	auto suffix=s==Sort.real_?"R":"C";
	switch(p.name){
		case "$pow","powR","powC":return pattern("pow"~suffix,[lower(p.args[0],s),lowerNat(p.args[1])]);
		case "#":return literal(p.number,s);
		case "real","complex":return p;
		case "$add":return pattern("add"~suffix,[lower(p.args[0],s),lower(p.args[1],s)]);
		case "$mul":
			// A bracket directly weighting the following factor is a mask, not
			// strict multiplication by a previously evaluated numeric indicator.
			if(p.args[0].name=="$iverson")
				return pattern("mask"~suffix,[lower(p.args[0].args[0],Sort.boolean),lower(p.args[1],s)]);
			return pattern("mul"~suffix,[lower(p.args[0],s),lower(p.args[1],s)]);
		case "$neg":return pattern("mul"~suffix,[literal(-1,s),lower(p.args[0],s)]);
		case "$inv":return pattern("inv"~suffix,[lower(p.args[0],s)]);
		case "$nonzero":
			auto operand=choose(p.args[0].candidates&scalars);
			return pattern(operand==Sort.real_?"nonzeroR":"nonzeroC",[lower(p.args[0],operand)]);
		case "$iverson":return pattern("mask"~suffix,[lower(p.args[0],Sort.boolean),literal(1,s)]);
		case "$mask":return pattern("mask"~suffix,[lower(p.args[0],Sort.boolean),lower(p.args[1],s)]);
		default:
			auto sig=signature(p.name);
			foreach(i,t;sig.args) p.args[i]=lower(p.args[i],t);
			return p;
	}
}

private Sort infer(Pattern p,Parameter[] parameters){
	foreach(v;parameters) if(p.name==v.name){
		enforce(p.args.length==0,"metavariables cannot be applied");
		p.variable=true; p.sort=v.sort; return p.sort;
	}
	enforce(isConstructor(p.name),"unknown constructor or unbound variable: "~p.name);
	if(p.name=="powR"||p.name=="powC"){
		p.sort=p.name=="powR"?Sort.real_:Sort.complex;
		enforce(p.args.length==2&&p.args[1].natural,"natural exponent expected");
		enforce(infer(p.args[0],parameters)==p.sort,"power type mismatch");
		return p.sort;
	}
	if(p.name=="real"||p.name=="complex"){
		enforce(p.args.length==(p.name=="real"?1:2),"literal arity mismatch");
		foreach(arg;p.args) enforce(arg.name=="#","literal integer expected");
		p.sort=p.name=="real"?Sort.real_:Sort.complex;
		return p.sort;
	}
	auto sig=signature(p.name); p.sort=sig.result;
	enforce(p.args.length==sig.args.length,"arity mismatch for "~p.name);
	foreach(i,arg;p.args)
		enforce(infer(arg,parameters)==sig.args[i],"type mismatch in "~p.name);
	return p.sort;
}

private size_t cost(Pattern p,ref Table!(string,uint) uses){
	if(p.variable){ uses.set(p.name,uses.get(p.name,0)+1); return 0; }
	if(p.natural){ foreach(arg;p.args) cost(arg,uses); return 0; }
	size_t n=1;
	// Integer payloads aren't IR nodes.
	if(p.name!="real"&&p.name!="complex")
		foreach(arg;p.args) if(arg.name!="#") n+=cost(arg,uses);
	return n;
}
void validate(ref Rule r){
	auto a=infer(r.lhs,r.parameters),b=infer(r.rhs,r.parameters);
	enforce(a==b,"rewrite changes its type");
	if(r.inference) enforce(!r.lhs.variable&&a==Sort.boolean,"facts require a Boolean pattern");
	if(r.automatic) enforce(!r.lhs.variable,"automatic root variable patterns are unsupported");
	Table!(string,uint) left,right;
	auto l=cost(r.lhs,left),k=cost(r.rhs,right);
	foreach(ref p;r.premises){
		auto s=infer(p.term,r.parameters);
		enforce(p.defined||p.literal||s==Sort.boolean,"condition must be Bool");
		cost(p.term,right);
	}
	if(r.automatic&&!r.bounded) enforce(k<l,"rules must strictly decrease constructor count");
	foreach(v;r.parameters){
		enforce(left.contains(v.name)||!r.automatic&&right.contains(v.name),"unused/unbound rule parameter: "~v.name);
		if(r.automatic&&!r.bounded){
			Table!(string,uint) rhs; cost(r.rhs,rhs);
			enforce(rhs.get(v.name,0)<=left.get(v.name,0),"rule duplicates a metavariable");
		}
	}
}

string leanSort(Sort s){ return s==Sort.boolean?"bool":s==Sort.real_?"real":to!string(s); }
string parameterCode(string name){ return "v_"~symbolCode(name); }
string ruleCode(string name){ return "r_"~symbolCode(name); }
string leanPattern(Pattern p){
	if(p.variable) return parameterCode(p.name);
	if(p.name=="natAdd"||p.name=="natMul")
		return "("~leanPattern(p.args[0])~(p.name=="natAdd"?" + ":" * ")~leanPattern(p.args[1])~")";
	if(p.name=="true"||p.name=="false") return "(.bool "~p.name~")";
	if(p.name=="#") return "("~to!string(p.number)~")";
	string s="(."~p.name;
	foreach(arg;p.args) s~=" "~leanPattern(arg);
	return s~")";
}

unittest{
	import std.exception:assertThrown;
	assert(Parser("rule z(x:Real): addR(x,real(0)) => x;").parse().length==1);
	assertThrown(Parser("rule z(x:Real): addC(x,complex(0,0)) => x;").parse());
	assertThrown(Parser("rule z(x:Real): addR(x,real(0)) => y;").parse());
	assertThrown(Parser("rule z(x:Real): x => x;").parse());
	assertThrown(Parser("rule z(x:Real): addR(x,real(0)) => addR(x,x);").parse());
	// Syntactic well-typedness is NOT a proof of mathematical validity.
	assert(Parser("rule bad(x:Real): mulR(real(0),x) => real(0);").parse().length==1);
}

unittest{
	import std.exception:assertThrown;
	void same(string surface,string constructors){
		auto a=Parser(surface).parse()[0],b=Parser(constructors).parse()[0];
		assert(a.lhs.sort==b.lhs.sort&&a.rhs.sort==b.rhs.sort);
		assert(leanPattern(a.lhs)==leanPattern(b.lhs));
		assert(leanPattern(a.rhs)==leanPattern(b.rhs));
	}
	same("rule r(x:ℝ):x+0⇒x;","rule r(x:Real):addR(x,real(0))=>x;");
	same("rule r(z:ℂ):(0+0)+z→z;",
		"rule r(z:Complex):addC(addC(complex(0,0),complex(0,0)),z)=>z;");
	same("rule r(x:ℝ,y:ℝ):x+y·1⇒x+y;",
		"rule r(x:Real,y:Real):addR(x,mulR(y,real(1)))=>addR(x,y);");
	same("rule r(x:ℝ,y:ℝ):(x+y)*1=>x+y;",
		"rule r(x:Real,y:Real):mulR(addR(x,y),real(1))=>addR(x,y);");
	same("rule r(x:ℝ,y:ℝ):x/1/y⇒x/y;",
		"rule r(x:Real,y:Real):mulR(mulR(x,invR(real(1))),invR(y))=>mulR(x,invR(y));");
	same("rule r(x:ℝ):[x≠0]·x⁻¹+0⇒[x!=0]*inv(x);",
		"rule r(x:Real):addR(maskR(nonzeroR(x),invR(x)),real(0))=>maskR(nonzeroR(x),invR(x));");
	same("rule r(x:ℝ):⅟x+0⇒x^(-1);",
		"rule r(x:Real):addR(invR(x),real(0))=>invR(x);");
	same("rule r(x:ℝ):x³+0⇒x^3;","rule r(x:Real):addR(powR(x,3),real(0))=>powR(x,3);");
	same("rule r(x:ℝ):|x|+0⇒abs(x);","rule r(x:Real):addR(absR(x),real(0))=>absR(x);");
	same("rule r(x:ℝ):[0≤x<1]+0⇒[0≤x∧x<1];",
		"rule r(x:Real):addR(maskR(and(leR(real(0),x),ltR(x,real(1))),real(1)),real(0))=>maskR(and(leR(real(0),x),ltR(x,real(1))),real(1));");
	same("rule r():[true]·(-2^2)⇒-4;",
		"rule r():maskR(true,mulR(real(-1),powR(mulR(real(-1),real(-2)),2)))=>real(-4);");
	same("rule r(x:ℝ):-x+0⇒−x;",
		"rule r(x:Real):addR(mulR(real(-1),x),real(0))=>mulR(real(-1),x);");
	same("rule r(z:ℂ):z−0⇒z;",
		"rule r(z:Complex):addC(z,mulC(complex(-1,0),complex(0,0)))=>z;");
	same("rule r():[false]⇒0;","rule r():maskR(false,real(1))=>real(0);");
	same("rule r():[false]⇒complex(0,0);","rule r():maskC(false,complex(1,0))=>complex(0,0);");
	same("rule r(p:𝔹):[p]+0⇒[p];","rule r(p:Bool):addR(maskR(p,real(1)),real(0))=>maskR(p,real(1));");
	same("rule r():[false]·(1÷0)⇒0;",
		"rule r():maskR(false,mulR(real(1),invR(real(0))))=>real(0);");
	same("rule r():[false]·ⅈ⇒0;","rule r():maskC(false,complex(0,1))=>complex(0,0);");
	same("rule r():[false]·(-9223372036854775808)⇒0;",
		"rule r():maskR(false,real(-9223372036854775808))=>real(0);");
	auto unicode=Parser("rule απλό(ρ₁':ℝ):ρ₁'+0⇒ρ₁';").parse()[0];
	assert(unicode.parameters[0].name=="ρ₁'");
	assert(parameterCode("ρ₁'")!=parameterCode("u_cf81e2828127"));
	assert(ruleCode("theorem")=="r_theorem");
	foreach(s;[
		"rule r(x:ℝ,z:ℂ):x+z⇒z;",
		"rule r(x:ℝ):[x]⇒0;",
		"rule r(x:ℂ):[x<1]⇒0;",
		"rule r(x:ℂ):|x|+0⇒x;",
		"rule r(x:ℝ):x^x⇒x;",
		"rule r(x:ℝ):x^2^3⇒x;",
		"rule r(x:ℝ):x+0⇒x; garbage",
		"rule r(x:ℝ):x+0⇒x; rule r(x:ℝ):x+0⇒x;",
		"rule r(α:ℝ,α:ℝ):α+0⇒α;",
		"rule r(x:ℝ):[false]·9223372036854775808⇒x;",
		"rule r(x:ℝ):x+⇒x;",
		"rule r(x:ℝ):(x+0⇒x;",
		"rule r(x:ℝ):[false⇒0;",
		"rule r(x:ℝ):∫x⇒x;",
		"rule r(x:ℝ):inv()⇒x;"
	]) assertThrown(Parser(s).parse(),s);
	string deep="x";
	foreach(i;0..150) deep~="+0";
	assertThrown(Parser("rule r(x:ℝ):"~deep~"⇒x;").parse());
}
