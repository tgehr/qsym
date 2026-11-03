module qsym.spec;
import qsym.ir:Sort,sortName;
import qsym.table:Table;
import std.ascii:isAlpha,isDigit,isWhite;
import std.conv:to;
import std.exception:enforce;
import std.algorithm:canFind;
@safe:

struct Parameter{ string name; Sort sort; }
final class Pattern{
	string name;
	Pattern[] args;
	long number;
	Sort sort;
	bool variable;
	this(string name){ this.name=name; }
}
struct Rule{ string name; Parameter[] parameters; Pattern lhs,rhs; }

/// Deliberately small, first-order, terminating rule DSL. No trusted axioms,
/// arbitrary D snippets, proof snippets, binders, or side-condition solvers.
struct Parser{
	string source;
	size_t pos;
	private void ws(){
		while(pos<source.length){
			if(isWhite(source[pos])){ ++pos; continue; }
			if(source[pos]=='#'){
				while(pos<source.length&&source[pos]!='\n')++pos;
				continue;
			}
			break;
		}
	}
	private bool take(string s){
		ws();
		if(source.length-pos>=s.length&&source[pos..pos+s.length]==s){
			pos+=s.length; return true;
		}
		return false;
	}
	private void expect(string s){
		enforce(take(s),"expected '"~s~"' at byte "~to!string(pos));
	}
	private string ident(){
		ws(); auto start=pos;
		enforce(pos<source.length&&isAlpha(source[pos]),"identifier expected at byte "~to!string(pos));
		while(pos<source.length&&(isAlpha(source[pos])||isDigit(source[pos])||source[pos]=='_'))++pos;
		return source[start..pos];
	}
	private Pattern pattern(uint depth=0){
		enforce(depth<128,"rule pattern nesting limit exceeded");
		ws();
		if(pos<source.length&&(isDigit(source[pos])||source[pos]=='-')){
			auto start=pos++;
			while(pos<source.length&&isDigit(source[pos]))++pos;
			auto p=new Pattern("#"); p.number=to!long(source[start..pos]); return p;
		}
		auto p=new Pattern(ident());
		if(take("(")){
			if(!take(")")){
				do{ p.args~=pattern(depth+1); }while(take(","));
				expect(")");
			}
		}
		return p;
	}
	Rule[] parse(){
		Rule[] rules;
		ws();
		while(pos!=source.length){
			enforce(ident()=="rule","expected rule declaration");
			Rule r; r.name=ident();
			foreach(old;rules) enforce(old.name!=r.name,"duplicate rule name");
			expect("(");
			if(!take(")")){
				do{
					auto name=ident(); expect(":"); auto ty=ident();
					Sort s;
					switch(ty){
						case "Real":s=Sort.real_; break;
						case "Complex":s=Sort.complex; break;
						case "Bool":s=Sort.boolean; break;
						case "Density":s=Sort.density; break;
						case "Measure":s=Sort.measure; break;
						default:throw new Exception("unknown sort: "~ty);
					}
					foreach(old;r.parameters) enforce(old.name!=name,"duplicate parameter");
					enforce(!isConstructor(name),"parameter shadows a constructor");
					r.parameters~=Parameter(name,s);
				}while(take(","));
				expect(")");
			}
			expect(":"); r.lhs=pattern(); expect("=>"); r.rhs=pattern(); expect(";");
			validate(r); rules~=r; ws();
		}
		return rules;
	}
}

bool isConstructor(string n){
	return ["real","complex","true","false","addR","addC","mulR","mulC",
		"invR","invC","nonzeroR","nonzeroC","maskR","maskC","conj",
		"lebesgue","puncture","densityAt","forget"].canFind(n);
}

private Sort infer(Pattern p,Parameter[] parameters){
	foreach(v;parameters) if(p.name==v.name){
		enforce(p.args.length==0,"metavariables cannot be applied");
		p.variable=true; p.sort=v.sort; return p.sort;
	}
	enforce(isConstructor(p.name),"unknown constructor or unbound variable: "~p.name);
	if(p.name=="real"||p.name=="complex"){
		enforce(p.args.length==(p.name=="real"?1:2),"literal arity mismatch");
		foreach(arg;p.args) enforce(arg.name=="#","literal integer expected");
		p.sort=p.name=="real"?Sort.real_:Sort.complex;
		return p.sort;
	}
	Sort[] expected;
	switch(p.name){
		case "true","false":p.sort=Sort.boolean; break;
		case "lebesgue":p.sort=Sort.density; break;
		case "addR","mulR":p.sort=Sort.real_; expected=[Sort.real_,Sort.real_]; break;
		case "addC","mulC":p.sort=Sort.complex; expected=[Sort.complex,Sort.complex]; break;
		case "invR":p.sort=Sort.real_; expected=[Sort.real_]; break;
		case "invC","conj":p.sort=Sort.complex; expected=[Sort.complex]; break;
		case "nonzeroR":p.sort=Sort.boolean; expected=[Sort.real_]; break;
		case "nonzeroC":p.sort=Sort.boolean; expected=[Sort.complex]; break;
		case "maskR":p.sort=Sort.real_; expected=[Sort.boolean,Sort.real_]; break;
		case "maskC":p.sort=Sort.complex; expected=[Sort.boolean,Sort.complex]; break;
		case "puncture":p.sort=Sort.density; expected=[Sort.density]; break;
		case "densityAt":p.sort=Sort.real_; expected=[Sort.density,Sort.real_]; break;
		case "forget":p.sort=Sort.measure; expected=[Sort.density]; break;
		default:assert(0);
	}
	enforce(p.args.length==expected.length,"arity mismatch for "~p.name);
	foreach(i,arg;p.args)
		enforce(infer(arg,parameters)==expected[i],"type mismatch in "~p.name);
	return p.sort;
}

private size_t cost(Pattern p,ref Table!(string,uint) uses){
	if(p.variable){ uses.set(p.name,uses.get(p.name,0)+1); return 0; }
	size_t n=1;
	// Integer payloads aren't IR nodes.
	if(p.name!="real"&&p.name!="complex")
		foreach(arg;p.args) n+=cost(arg,uses);
	return n;
}
void validate(ref Rule r){
	auto a=infer(r.lhs,r.parameters),b=infer(r.rhs,r.parameters);
	enforce(a==b,"rewrite changes its type");
	enforce(!r.lhs.variable,"root variable patterns are unsupported");
	Table!(string,uint) left,right;
	auto l=cost(r.lhs,left),k=cost(r.rhs,right);
	enforce(k<l,"rules must strictly decrease constructor count");
	foreach(v;r.parameters){
		enforce(left.contains(v.name),"unused/unbound rule parameter: "~v.name);
		enforce(right.get(v.name,0)<=left.get(v.name,0),"rule duplicates a metavariable");
	}
}

string leanSort(Sort s){ return s==Sort.boolean?"bool":s==Sort.real_?"real":to!string(s); }
string leanPattern(Pattern p){
	if(p.variable) return p.name;
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
