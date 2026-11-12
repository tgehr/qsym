module qsym.spec;
import qsym.ir:Sort,sortName;
import qsym.builtins;
import qsym.table:Table;
import qsym.lexer;
import std.conv:to;
import std.exception:enforce;
import std.algorithm:canFind;
import qsym.number:Rational,BigInt;
@safe:

// NatParam is a bounded constructor payload; ℕ is an expression type.
final class TypePattern{
	string name,binder;
	Pattern predicate;
	Pattern dimension;
	TypePattern[] args;
	this(string name,TypePattern[] args=[]){ this.name=name; this.args=args; }
}
struct TypedParameter{ string name; TypePattern type; }

struct Parameter{ string name; Sort sort; bool natural; }
final class Pattern{
	string name,binder;
	TypePattern annotation;
	bool called;
	Pattern[] args;
	long number;
	Sort sort;
	bool variable;
	bool natural;
	private uint candidates;
	private bool constantNatural,realDefault;
	private ulong naturalValue;
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
	private size_t integerEnd;
	private bool typeArrows;
	private void next(){
		integerEnd=token.kind==TokenKind.integer||token.kind==TokenKind.decimal?token.offset+token.text.length:size_t.max;
		token=lexer.next();
	}
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
		auto digits=token.text; next();
		enforce(digits.length<=1_000_000,"integer exceeds literal limit");
		auto value=BigInt((negative?"-":"")~digits);
		if(value>=long.min&&value<=long.max) return integerPattern(value.toLong());
		// The IR already has arbitrary precision constants. Use small exact
		// chunks in the parser so their printed decimal spelling round-trips
		// without enlarging the bounded rule-pattern and NatParam payloads.
		Pattern decimalInteger(string ds){
			if(ds.length<=9) return integerPattern(to!long(ds));
			auto middle=ds.length/2;
			auto scale=pattern("$pow",[integerPattern(10),integerPattern(cast(long)(ds.length-middle))]);
			return pattern("$add",[pattern("$mul",[decimalInteger(ds[0..middle]),scale]),decimalInteger(ds[middle..$])]);
		}
		auto p=decimalInteger(digits);
		return negative?pattern("$neg",[p]):p;
	}
	private Pattern decimal(){
		// Parse base ten exactly; decimal syntax never passes through floating point.
		auto spelling=token.text; next();
		string digits; long scale; bool fraction;
		foreach(i,c;spelling){
			if(c=='.'){ fraction=true; continue; }
			if(c=='e'||c=='E'){
				auto exponent=to!long(spelling[i+1..$]);
				enforce(exponent>=-4096&&exponent<=4096,"decimal exponent exceeds literal limit");
				scale-=exponent; break;
			}
			digits~=c; if(fraction) ++scale;
		}
		enforce(digits.length<=4096&&scale>=-4096&&scale<=4096,"decimal exceeds literal limit");
		auto numerator=BigInt(digits),denominator=BigInt(1);
		if(numerator==0) return pattern("rat",[integerPattern(0),integerPattern(1)]);
		foreach(i;0..(scale<0?-scale:scale)){
			if(scale<0) numerator*=10; else denominator*=10;
		}
		auto q=Rational(numerator,denominator);
		enforce(q.numerator<=long.max&&q.denominator<=long.max,"decimal exceeds exact literal range");
		return pattern("rat",[integerPattern(q.numerator.toLong()),integerPattern(q.denominator.toLong())]);
	}

	private Pattern primary(uint depth){
		enforce(depth<128,"rule pattern nesting limit exceeded");
		auto lookahead=lexer;
		if((token.text=="Π"||token.text=="Pi")&&lookahead.next().text=="("){
			auto p=pattern("$type",[]); p.annotation=typeExpression(depth+1); return p;
		}
		if((token.text=="μ"||token.text=="mu")&&lookahead.next().text=="("){
			next(); expect("("); auto name=ident(); expect(":"); auto ty=typeExpression(depth+1);
			expect(")"); expect("."); auto p=pattern("$fix",[expression(depth+1)]); p.binder=name; p.annotation=ty; return p;
		}
		if(token.text=="undefined"&&lookahead.next().text=="("){
			next(); expect("("); auto p=pattern("$bottom",[]); p.annotation=typeExpression(depth+1); expect(")"); return p;
		}
		if((token.text=="λ"||token.text=="lambda")&&lookahead.next().text=="("){
			next();
			expect("("); auto name=ident(); expect(":"); auto ty=typeExpression(depth+1);
			Pattern guard; if(take("|")) guard=expression(depth+1);
			expect(")"); expect("."); auto body=expression(depth+1);
			auto p=pattern("$lambda",guard is null?[body]:[guard,body]); p.binder=name; p.annotation=ty; return p;
		}
		if(take("{")){
			auto name=ident(); expect(":"); auto ty=typeExpression(depth+1); expect("|");
			auto p=pattern("$set",[expression(depth+1)]); expect("}"); p.binder=name; p.annotation=ty; return p;
		}
		if(take("if")){
			auto condition=expression(depth+1); expect("then");
			auto yes=expression(depth+1); expect("else");
			return pattern("$if",[condition,yes,expression(depth+1)]);
		}
		enforce(token.text!="then"&&token.text!="else","unexpected conditional keyword");
		if(take("(")){
			if(take(")")) return pattern("$tuple",[]);
			auto p=expression(depth+1);
			if(take(",")){
				auto q=pattern("$tuple",[p]);
				if(!take(")")){ do{ q.args~=expression(depth+1); }while(take(",")&&token.text!=")"); expect(")"); }
				return q;
			}
			if(take(":")){
				auto q=pattern("$ascribe",[p]); q.annotation=typeExpression(depth+1);
				if(!q.annotation.args.length&&q.annotation.name!="Type"&&q.annotation.name!="Unit") q.sort=parseSort(q.annotation.name); p=q;
			}
			expect(")"); return p;
		}
		if(take("[")){ auto p=expression(depth+1); expect("]"); return pattern("$iverson",[p]); }
		if(take("|")){ auto p=expression(depth+1); expect("|"); return pattern("$abs",[p]); }
		if(take("ⅈ")) return pattern("complex",[integerPattern(0),integerPattern(1)]);
		if(token.kind==TokenKind.integer) return integer();
		if(token.kind==TokenKind.decimal) return decimal();
		auto p=new Pattern(ident());
		if(take("(")){
			p.called=true;
			if(!take(")")){
				do{ p.args~=expression(depth+1); }while(take(","));
				expect(")");
			}
		}
		if(p.name=="inv"||p.name=="nonzero"||p.name=="mask") p.name="$"~p.name;
		if(p.name=="abs") p.name="$abs";
		if(p.name=="cinv") p.name="invC";
		if((p.name=="min"||p.name=="max")&&p.args.length==1){
			p.name="$ascribe"; p.sort=Sort.real_; return p;
		}
		if(p.name=="hypot"){
			if(!p.args.length) return pattern("real",[integerPattern(0)]);
			if(p.args.length==1){ p.name="$abs"; return p; }
		}
		if((p.name=="min"||p.name=="max"||p.name=="hypot")&&p.args.length>2){
			auto result=pattern(p.name,p.args[0..2]);
			foreach(arg;p.args[2..$]) result=pattern(p.name,[result,arg]);
			return result;
		}
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
					return pattern("$neg",[postfix(pattern("$neg",[p]),depth)]);
				return p;
			}
			return pattern("$neg",[factor(depth+1)]);
		}
		if(take("⅟")) return pattern("$inv",[factor(depth+1)]);
		if(take("!")) return pattern("not",[factor(depth+1)]);
		return postfix(primary(depth),depth);
	}
	private Pattern postfix(Pattern p,uint depth){
		while(p.name!="#"&&p.name!="rat"&&take("(")){
			p=pattern("$apply",[p,expression(depth+1)]); expect(")");
		}
		if(token.kind==TokenKind.power){
			auto exponent=to!long(token.text); next();
			return pattern("$pow",[p,integerPattern(exponent)]);
		}
		if(take("^")) return pattern("$pow",[p,factor(depth+1)]);
		return p;
	}

	private Pattern product(uint depth){
		auto p=factor(depth);
		bool adjacent(Pattern p){
			if(p.name=="$neg") return adjacent(p.args[0]);
			return (p.name=="#"||p.name=="rat")&&token.offset==integerEnd&&
				(token.kind==TokenKind.identifier||token.text=="("||token.text=="ⅈ");
		}
		auto implicit=adjacent(p);
		while(token.text=="*"||token.text=="×"||token.text=="@"||token.text=="/"||implicit){
			auto op=implicit?"*":token.text;
			if(!implicit) next();
			auto q=factor(depth);
			implicit=adjacent(q);
			if(op=="/") q=pattern("$inv",[q]);
			p=pattern(op=="@"?"$matmul":op=="×"?"$times":"$mul",[p,q]);
		}
		return p;
	}
	private Pattern sum(uint depth){
		auto p=product(depth);
		while(token.text=="+"||token.text=="-"||token.text=="sub"){
			auto op=token.text; next();
			auto q=product(depth);
			if(op=="-") q=pattern("$neg",[q]);
			p=pattern(op=="sub"?"subN":"$add",[p,q]);
		}
		return p;
	}
	private Pattern comparison(uint depth){
		auto p=sum(depth);
		Pattern combined;
		while(token.text=="!="||token.text=="="||token.text=="<"||token.text==">"||token.text=="<="||token.text==">="||token.text=="∈"||token.text=="∉"||token.text=="⊆"||token.text=="⊈"){
			auto op=token.text; next();
			auto q=sum(depth);
			Pattern predicate;
			if(op=="∈"||op=="∉"||op=="⊆"||op=="⊈"){
				predicate=pattern(op=="∈"||op=="∉"?"$member":"$subset",[p,q]);
				if(op=="∉"||op=="⊈") predicate=pattern("not",[predicate]);
			}
			else if(op=="!="||op=="="){
				predicate=pattern("$different",[p,q]);
				if(op=="=") predicate=pattern("not",[predicate]);
			}else predicate=pattern(op=="<"||op==">"?"$lt":"$le",op==">"||op==">="?[q,p]:[p,q]);
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
		if(typeArrows&&(take("->")||take("=>"))) p=pattern("$arrowtype",[p,expression(depth+1)]);
		return p;
	}
	private Parameter parameter(){
		auto name=ident(); expect(":"); auto ty=ident();
		auto natural=ty=="NatParam",s=natural?Sort.real_:parseSort(ty);
		enforce(name!="if"&&name!="then"&&name!="else"&&name!="sub","reserved expression keyword");
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
	private TypePattern typeAtom(uint depth){
		enforce(depth<128,"type nesting limit exceeded"); TypePattern t;
		if(take("Π")||take("Pi")){
			expect("("); auto name=ident(); expect(":"); auto input=typeExpression(depth+1); expect(")"); expect(".");
			t=new TypePattern("pi",[input,typeExpression(depth+1)]); t.binder=name; return t;
		}
		if(take("(")){ t=typeExpression(depth+1); expect(")"); }
		else if(take("{")){
			auto name=ident(); expect(":"); t=new TypePattern("$subset",[typeExpression(depth+1)]); expect("|");
			t.binder=name; t.predicate=expression(depth+1); expect("}");
		}
		else{
			auto name=ident();
			if(name=="Set"){ expect("("); t=new TypePattern("Set",[typeExpression(depth+1)]); expect(")"); }
			else{ if(name!="Type"&&name!="Unit") parseSort(name); t=new TypePattern(name); }
		}
		if(token.kind==TokenKind.power){
			auto n=to!long(token.text); next(); enforce(n>=0,"negative vector dimension");
			auto v=new TypePattern("vector",[t]); v.dimension=integerPattern(n); t=v;
		}else if(take("^")){
			auto v=new TypePattern("vector",[t]);
			if(take("(")){ v.dimension=expression(depth+1); expect(")"); }
			else v.dimension=primary(depth+1); t=v;
		}
		return t;
	}
	private TypePattern typeExpression(uint depth=0){
		auto t=typeAtom(depth);
		if(token.text=="*"||token.text=="×"){
			auto product=new TypePattern("tuple",[t]);
			while(take("*")||take("×")) product.args~=typeAtom(depth+1); t=product;
		}
		if(take("=>")||take("->")) t=new TypePattern("arrow",[t,typeExpression(depth+1)]);
		return t;
	}
	TypedParameter[] parseTypedParameters(){
		lexer=Lexer(source); next(); TypedParameter[] result;
		do{ auto name=ident(); expect(":"); result~=TypedParameter(name,typeExpression()); }while(take(","));
		take(";"); enforce(token.kind==TokenKind.end,"unexpected token: "~token.text); return result;
	}
	Pattern parseRawExpression(){
		typeArrows=true; lexer=Lexer(source); next(); auto p=expression();
		take(";"); enforce(token.kind==TokenKind.end,"unexpected token: "~token.text); return p;
	}
	Pattern parseExpression(ref Parameter[] parameters){ return elaborate(parseRawExpression(),parameters); }

	Rule[] parse(){
		typeArrows=false; lexer=Lexer(source); next();
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
			enforce((candidates&~naturalBit)!=0,"rewrite changes its type in "~r.name);
			auto sort=choose(candidates,r.lhs.realDefault||r.rhs.realDefault);
			r.lhs=lower(r.lhs,sort); r.rhs=lower(r.rhs,sort);
			foreach(ref p;r.premises){
				auto types=possible(p.term,r.parameters);
				enforce((types&~naturalBit)!=0,"conditions require an IR expression");
				auto ty=p.defined||p.literal?choose(types,p.term.realDefault):Sort.boolean;
				enforce(types&bit(ty),"condition must be Bool");
				p.term=lower(p.term,ty);
			}
			try{ validate(r); }catch(Exception e){ throw new Exception("in "~r.name~": "~e.msg); }
			rules~=r;
		}
		return rules;
	}
}

Pattern elaborate(Pattern p,ref Parameter[] parameters){
	void variables(Pattern q,uint depth=0){
		enforce(depth<128,"expression nesting limit exceeded");
		if(!q.args.length&&q.name!="#"&&!isConstructor(q.name)){
			foreach(v;parameters) if(v.name==q.name) return;
			parameters~=Parameter(q.name,Sort.real_);
		}
		foreach(arg;q.args) variables(arg,depth+1);
	}
	variables(p);
	p=lower(p,choose(possible(p,parameters),p.realDefault)); infer(p,parameters); return p;
}

Sort parseSort(string name){
	switch(name){
		case "Real","ℝ":return Sort.real_;
		case "Complex","ℂ":return Sort.complex;
		case "Bool","𝔹":return Sort.boolean;
		case "Density":return Sort.density;
		case "Measure":return Sort.measure;
		case "Nat","ℕ":return Sort.natural;
		case "Int","ℤ":return Sort.integer;
		case "Rat","ℚ":return Sort.rational;
		default:throw new Exception("unknown sort: "~name);
	}
}

bool isConstructor(string n){
	foreach(f;0..cast(uint)Builtin.invalid) if(builtinName(cast(Builtin)f,n)) return true;
	return ["nat","int","rat","powN","powZ","powQ","maskN","maskZ","maskQ","real","complex","true","false","addR","addC","mulR","mulC",
		"invR","invC","nonzeroR","nonzeroC","maskR","maskC","conj",
		"lebesgue","puncture","densityAt","forget","powR","powC","not","and","or","ltR","leR","absR"].canFind(n);
}

Pattern pattern(string name,Pattern[] args){
	auto p=new Pattern(name); p.args=args; return p;
}
private Pattern integerPattern(long n){ auto p=new Pattern("#"); p.number=n; return p; }
private uint bit(Sort s){ return 1u<<cast(uint)s; }
private enum scalars=(1u<<Sort.real_)|(1u<<Sort.complex)|(1u<<Sort.natural)|(1u<<Sort.integer)|(1u<<Sort.rational);
private enum naturalBit=1u<<8;
private Sort choose(uint candidates,bool realDefault=false){
	if(realDefault&&candidates&bit(Sort.real_)) return Sort.real_;
	foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean,Sort.density,Sort.measure])
		if(candidates&bit(s)) return s;
	throw new Exception("no expression type");
}

private uint widen(uint types){
	uint result=types;
	foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex])
		if(types&bit(s)) foreach(t;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(promotes(s,t)) result|=bit(t);
	return result;
}
private uint common(uint a,uint b){
	if(a&b&scalars) return a&b&scalars;
	a=widen(a)&widen(b)&scalars;
	foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(a&bit(s)) return bit(s);
	return 0;
}

private struct Signature{ Sort result; Sort[] args; }
private Signature signature(string name){
	auto f=builtin(name);
	if(f!=Builtin.invalid){ auto d=builtinInfo(f); return Signature(d.result,d.args.dup); }
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
		case "maskN":return Signature(Sort.natural,[B,Sort.natural]);
		case "maskZ":return Signature(Sort.integer,[B,Sort.integer]);
		case "maskQ":return Signature(Sort.rational,[B,Sort.rational]);
		case "maskR":return Signature(R,[B,R]);
		case "maskC":return Signature(C,[B,C]);
		case "puncture":return Signature(D,[D]);
		case "densityAt":return Signature(R,[D,R]);
		case "forget":return Signature(M,[D]);
		default:throw new Exception("unknown constructor or unbound variable: "~name);
	}
}

// Propagate possible sorts before choosing a default for bare numeric literals.
// Both rule endpoints constrain literals; widening inserts explicit IR casts.
private bool payload(Pattern p){ return p.name=="#"||p.variable&&p.natural; }
private bool powerPattern(string s){ return s=="powN"||s=="powZ"||s=="powQ"||s=="powR"||s=="powC"; }
private Sort literalSort(string name){
	switch(name){
		case "nat":return Sort.natural;
		case "int":return Sort.integer;
		case "rat":return Sort.rational;
		case "real":return Sort.real_;
		case "complex":return Sort.complex;
		default:assert(0);
	}
}
private bool literalName(string name){ return ["nat","int","rat","real","complex"].canFind(name); }
private uint possible(Pattern p,Parameter[] parameters,uint depth=0){
	enforce(depth<128,"rule pattern nesting limit exceeded");
	if(p.name=="$times") p.name="$mul";
	foreach(v;parameters) if(p.name==v.name){
		enforce(!p.args.length,"metavariables cannot be applied");
		p.variable=true; p.natural=v.natural; return p.candidates=v.natural?naturalBit:bit(v.sort);
	}
	auto arity=p.args.length;
	if(p.name=="#"){
		p.constantNatural=p.number>=0&&p.number<=uint.max; p.naturalValue=cast(ulong)p.number;
		return p.candidates=(p.number<0?scalars&~bit(Sort.natural):scalars)|(p.constantNatural?naturalBit:0);
	}
	uint[] args;
	foreach(arg;p.args){ args~=possible(arg,parameters,depth+1); p.realDefault|=arg.realDefault; }
	p.realDefault|=p.name=="$iverson";
	if(literalName(p.name)){
		enforce(arity==(p.name=="complex"||p.name=="rat"?2:1)||p.name=="real"&&arity==2,"literal arity mismatch");
		foreach(arg;p.args) enforce(payload(arg),"literal integer or NatParam expected");
		if(p.name=="real"&&arity==2){
			foreach(arg;p.args) enforce(arg.name=="#","rational real patterns require fixed integer payloads");
			enforce(p.args[1].number!=0,"zero rational denominator");
		}
		if(p.name=="nat") enforce(p.args[0].name!="#"||p.args[0].number>=0,"negative natural literal");
		if(p.name=="rat") enforce(p.args[1].name!="#"||p.args[1].number!=0,"zero rational denominator");
		return p.candidates=bit(literalSort(p.name));
	}
	uint result;
	if(powerPattern(p.name)){
		enforce(arity==2&&(args[1]&naturalBit),"NatParam exponent expected");
		result=args[0]&bit(p.name=="powN"?Sort.natural:p.name=="powZ"?Sort.integer:p.name=="powQ"?Sort.rational:p.name=="powR"?Sort.real_:Sort.complex);
	}else switch(p.name){
		case "$if":
			enforce(arity==3&&args[0]&bit(Sort.boolean),"conditional requires Bool condition");
			result=common(args[1],args[2])|(args[1]&args[2]&bit(Sort.boolean));
			p.realDefault=p.args[1].realDefault||p.args[2].realDefault; break;
		case "$ascribe":
			enforce(widen(args[0])&bit(p.sort),"invalid type ascription"); result=bit(p.sort); break;
		case "$pow":
			enforce(arity==2&&args[0]&scalars&&args[1]&(scalars|naturalBit),"numeric power expected");
			if(args[1]&naturalBit||p.args[1].name=="#"&&p.args[1].number>=0) result=args[0]&scalars;
			else if(p.args[1].name=="#"&&p.args[1].number<0){
				result=args[0]&(bit(Sort.rational)|bit(Sort.real_)|bit(Sort.complex));
				if(!result) result=common(args[0],bit(Sort.rational));
			}
			else if(choose(args[1],p.args[1].realDefault)==Sort.natural) result=args[0]&scalars;
			else if(choose(args[1],p.args[1].realDefault)==Sort.integer) result=common(args[0],bit(Sort.rational));
			else result=common(args[0],common(args[1],bit(Sort.real_)));
			break;
		case "$add","$mul":
			enforce(arity==2,"binary operator arity mismatch");
			result=common(args[0],args[1])|(naturalBit&args[0]&args[1]);
			if(p.args[0].constantNatural&&p.args[1].constantNatural){
				p.naturalValue=p.name=="$add"?p.args[0].naturalValue+p.args[1].naturalValue:p.args[0].naturalValue*p.args[1].naturalValue;
				p.constantNatural=p.naturalValue<=uint.max;
				if(!p.constantNatural) result&=~naturalBit;
			}
			break;
		case "$neg","$inv":
			enforce(arity==1,"unary operator arity mismatch");
			auto allowed=p.name=="$neg"?scalars&~bit(Sort.natural):bit(Sort.rational)|bit(Sort.real_)|bit(Sort.complex);
			result=args[0]&allowed;
			if(!result) result=common(args[0],bit(p.name=="$neg"?Sort.integer:Sort.rational));
			break;
		case "$nonzero":
			enforce(arity==1&&args[0]&scalars,"nonzero requires a scalar"); result=bit(Sort.boolean); break;
		case "$different":
			enforce(arity==2&&(common(args[0],args[1])||args[0]&args[1]&bit(Sort.boolean)),"comparison type mismatch");
			result=bit(Sort.boolean); break;
		case "$lt","$le":
			enforce(arity==2&&common(args[0],args[1])&~bit(Sort.complex),"ordering requires ordered scalars");
			result=bit(Sort.boolean); break;
		case "$abs":
			enforce(arity==1&&args[0]&scalars,"absolute value requires a scalar"); result=bit(Sort.real_); break;
		case "$iverson":
			enforce(arity==1&&args[0]&bit(Sort.boolean),"Iverson brackets require Bool"); result=scalars; break;
		case "$mask":
			enforce(arity==2&&args[0]&bit(Sort.boolean),"mask requires Bool and a scalar"); result=scalars&args[1]; break;
		default:
			// Resolve function overloads from argument types before surrounding casts.
			Builtin selected=Builtin.invalid; uint best=uint.max;
			foreach(i;0..cast(uint)Builtin.invalid){
				auto f=cast(Builtin)i,d=builtinInfo(f);
				if(!builtinName(f,p.name)||d.args.length!=arity) continue;
				uint cost; bool ok=true;
				foreach(j,t;d.args){
					if(!(widen(args[j])&bit(t))){ ok=false; break; }
					if(!(args[j]&bit(t))) cost+=10;
					else if(args[j]&bit(Sort.real_)&&t==Sort.complex) ++cost;
				}
				if(ok&&cost<best){ best=cost; selected=f; }
			}
			if(selected!=Builtin.invalid){ p.name=builtinInfo(selected).code; result=bit(builtinInfo(selected).result); break; }
			auto sig=signature(p.name);
			enforce(arity==sig.args.length,"arity mismatch for "~p.name);
			foreach(i,t;sig.args) enforce(widen(args[i])&bit(t),"type mismatch in "~p.name);
			result=bit(sig.result);
	}
	enforce(result!=0,"type mismatch in "~p.name);
	return p.candidates=result;
}

private Pattern literal(long n,Sort s){
	switch(s){
		case Sort.natural:return pattern("nat",[integerPattern(n)]);
		case Sort.integer:return pattern("int",[integerPattern(n)]);
		case Sort.rational:return pattern("rat",[integerPattern(n),integerPattern(1)]);
		case Sort.real_:return pattern("real",[integerPattern(n)]);
		case Sort.complex:return pattern("complex",[integerPattern(n),integerPattern(0)]);
		default:throw new Exception("numeric literal type expected");
	}
}
private Pattern lowerNat(Pattern p){
	enforce(p.candidates&naturalBit,"natural parameter expression expected");
	p.natural=true;
	if(p.variable||p.name=="#") return p;
	enforce(p.name=="$add"||p.name=="$mul","unsupported natural parameter operation");
	p.name=p.name=="$add"?"natAdd":"natMul";
	foreach(ref arg;p.args) arg=lowerNat(arg);
	return p;
}
private Pattern embed(Pattern p,Sort from,Sort to){
	enforce(promotes(from,to),"invalid numeric embedding");
	while(from!=to){
		auto next=from==Sort.natural?Sort.integer:from==Sort.integer?Sort.rational:from==Sort.rational?Sort.real_:Sort.complex;
		p=pattern("cast"~suffix(from)~suffix(next),[p]); from=next;
	}
	return p;
}
private Pattern lower(Pattern p,Sort s){
	if(!(p.candidates&bit(s))){
		auto from=choose(p.candidates&~naturalBit,p.realDefault);
		return embed(lower(p,from),from,s);
	}
	if(p.variable) return p;
	auto suf=numeric(s)?suffix(s):"";
	if(powerPattern(p.name)) return pattern(p.name,[lower(p.args[0],s),lowerNat(p.args[1])]);
	switch(p.name){
		case "$if":
			auto condition=lower(p.args[0],Sort.boolean),yes=lower(p.args[1],s),no=lower(p.args[2],s);
			auto opposite=pattern("not",[condition]);
			if(s==Sort.boolean) return pattern("or",[pattern("and",[condition,yes]),pattern("and",[opposite,no])]);
			return pattern("add"~suf,[pattern("mask"~suf,[condition,yes]),pattern("mask"~suf,[opposite,no])]);
		case "$ascribe":return lower(p.args[0],s);
		case "$pow":
			auto e=p.args[1];
			if(e.candidates&naturalBit) return pattern("pow"~suf,[lower(p.args[0],s),lowerNat(e)]);
			if(e.name=="#"&&e.number<0&&e.number>=-cast(long)uint.max){
				auto base=lower(p.args[0],s);
				if(e.number!=-1){ auto n=integerPattern(-e.number); n.natural=true; base=pattern("pow"~suf,[base,n]); }
				return pattern("inv"~suf,[base]);
			}
			if(e.name=="#") return pattern("pow"~suf~(e.number<0?"Z":"N"),
				[lower(p.args[0],s),lower(e,e.number<0?Sort.integer:Sort.natural)]);
			auto ty=choose(e.candidates,e.realDefault);
			if(ty==Sort.natural||ty==Sort.integer)
				return pattern("pow"~suf~suffix(ty),[lower(p.args[0],s),lower(e,ty)]);
			return pattern(s==Sort.complex?"powerC":"powerR",[lower(p.args[0],s),lower(e,s)]);
		case "#":return literal(p.number,s);
		case "nat","int","rat","real","complex":return p;
		case "$add":return pattern("add"~suf,[lower(p.args[0],s),lower(p.args[1],s)]);
		case "$mul":
			// Bracket factors guard the whole surface product, on either side
			// and across parentheses. Explicit mul*/mask* calls stay strict.
			Pattern[] guards;
			Pattern product(Pattern q){
				auto bare=q; while(bare.name=="$ascribe") bare=bare.args[0];
				if(bare.name=="$iverson"){ guards~=lower(bare.args[0],Sort.boolean); return null; }
				if(q.name!="$mul") return lower(q,s);
				auto l=product(q.args[0]),r=product(q.args[1]);
				return l is null?r:r is null?l:pattern("mul"~suf,[l,r]);
			}
			auto result=product(p); if(result is null) result=literal(1,s);
			// Preserve short-circuit order when predicates themselves are partial.
			foreach_reverse(g;guards) result=pattern("mask"~suf,[g,result]);
			return result;
		case "$neg":return pattern("mul"~suf,[literal(-1,s),lower(p.args[0],s)]);
		case "$inv":return pattern("inv"~suf,[lower(p.args[0],s)]);
		case "$abs":
			auto ty=choose(p.args[0].candidates);
			return pattern(ty==Sort.complex?"absC":"absR",[lower(p.args[0],ty==Sort.complex?ty:Sort.real_)]);
		case "$nonzero":
			auto operand=choose(p.args[0].candidates&scalars);
			return pattern("nonzero"~suffix(operand),[lower(p.args[0],operand)]);
		case "$different":
			auto types=common(p.args[0].candidates,p.args[1].candidates);
			if(!types) return pattern("not",[pattern("eqB",[lower(p.args[0],Sort.boolean),lower(p.args[1],Sort.boolean)])]);
			auto ty=choose(types,p.realDefault); if(ty==Sort.natural) ty=Sort.integer;
			auto diff=p.args[1].name=="#"&&p.args[1].number==0?lower(p.args[0],ty):
				pattern("add"~suffix(ty),[lower(p.args[0],ty),pattern("mul"~suffix(ty),[literal(-1,ty),lower(p.args[1],ty)])]);
			return pattern("nonzero"~suffix(ty),[diff]);
		case "$lt","$le":
			auto ty=choose(common(p.args[0].candidates,p.args[1].candidates)&~bit(Sort.complex),p.realDefault);
			return pattern((p.name=="$lt"?"lt":"le")~suffix(ty),[lower(p.args[0],ty),lower(p.args[1],ty)]);
		case "$iverson":return pattern("mask"~suf,[lower(p.args[0],Sort.boolean),literal(1,s)]);
		case "$mask":return pattern("mask"~suf,[lower(p.args[0],Sort.boolean),lower(p.args[1],s)]);
		default:
			auto sig=signature(p.name);
			foreach(i,t;sig.args) p.args[i]=lower(p.args[i],t);
			return p;
	}
}

private Sort infer(Pattern p,Parameter[] parameters){
	foreach(v;parameters) if(p.name==v.name){
		enforce(!p.args.length,"metavariables cannot be applied");
		p.variable=true; p.sort=v.sort; return p.sort;
	}
	enforce(isConstructor(p.name),"unknown constructor or unbound variable: "~p.name);
	if(powerPattern(p.name)){
		p.sort=p.name=="powN"?Sort.natural:p.name=="powZ"?Sort.integer:p.name=="powQ"?Sort.rational:p.name=="powR"?Sort.real_:Sort.complex;
		enforce(p.args.length==2&&p.args[1].natural,"natural parameter exponent expected");
		enforce(infer(p.args[0],parameters)==p.sort,"power type mismatch"); return p.sort;
	}
	if(literalName(p.name)){ p.sort=literalSort(p.name); return p.sort; }
	auto sig=signature(p.name); p.sort=sig.result;
	enforce(p.args.length==sig.args.length,"arity mismatch for "~p.name);
	foreach(i,arg;p.args) enforce(infer(arg,parameters)==sig.args[i],"type mismatch in "~p.name);
	return p.sort;
}

private size_t cost(Pattern p,ref Table!(string,uint) uses){
	if(p.variable){ uses.set(p.name,uses.get(p.name,0)+1); return 0; }
	if(p.natural){ foreach(arg;p.args) cost(arg,uses); return 0; }
	size_t n=1;
	// Integer payloads aren't IR nodes.
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
	if(p.name=="real"&&p.args.length==2) return "(.ratR (("~leanPattern(p.args[0])~" : ℚ) / "~leanPattern(p.args[1])~"))";
	if(p.name=="rat") return "(.rat (("~leanPattern(p.args[0])~" : ℚ) / "~leanPattern(p.args[1])~"))";
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
	assertThrown(Parser("rule bad():real(1,0)⇒0;").parse());
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
	same("rule r(x:ℝ):x×1⇒x;","rule r(x:Real):mulR(x,real(1))=>x;");
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
		"rule r(x:ℝ):[x]⇒0;",
		"rule r(x:ℂ):[x<1]⇒0;",
		"rule r(x:ℂ):|x|+0⇒x;",
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
