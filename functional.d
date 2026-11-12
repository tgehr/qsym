module qsym.functional;
import qsym.ir;
import qsym.binding;
import qsym.types:TypeId,TypeKind,TypePool;
import qsym.text:Syntax;
import qsym.spec:Parser,Pattern,TypePattern,Parameter,parseSort,isConstructor,elaborate,pattern;
import qsym.table:Table;
import qsym.simplify:Result,Options,simplify;
import qsym.domain:simplifyDomain;
import qsym.proof:exportLean,exportDomainLean;
import std.conv:to;
import std.exception:enforce;
import std.string:replace;
@safe:

struct FunctionVariable{ string name; TypeId type; }
struct FunctionResult{
	Bindings bindings;
	BoundTerm original;
	BindingResult reduction;
	Result scalar;
	Term scalarInput;
	bool scalarOnly,lowered,domainQuery;
	@property bool exhausted(){ return reduction.exhausted||scalar.exhausted; }
}
struct FunctionSyntax{
	Syntax scalar;
	TypePool pool;
	FunctionVariable[] functions;
	private void init(){ if(pool is null) pool=new TypePool; }
	private TypeId scalarType(Sort sort){
		init();
		final switch(sort){
			case Sort.natural:return pool.primitive(TypeKind.natural);
			case Sort.integer:return pool.primitive(TypeKind.integer);
			case Sort.rational:return pool.primitive(TypeKind.rational);
			case Sort.real_:return pool.primitive(TypeKind.real_);
			case Sort.complex:return pool.primitive(TypeKind.complex);
			case Sort.boolean:return pool.primitive(TypeKind.boolean);
			case Sort.density,Sort.measure:throw new Exception("unsupported function scalar type");
		}
	}
	private bool scalarSort(TypeId t,out Sort sort){
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean])
			if(t==scalarType(s)){ sort=s; return true; }
		return false;
	}
	private TypeId type(TypePattern t){
		init(); enforce(t !is null,"missing type");
		if(t.name=="arrow") return pool.function_(type(t.args[0]),type(t.args[1]));
		if(t.name=="Set") return pool.set(type(t.args[0]));
		return scalarType(parseSort(t.name));
	}
	string typeName(TypeId t){
		auto v=pool.view(t); Sort sort;
		if(scalarSort(t,sort)){
			switch(sort){
				case Sort.natural:return "ℕ";
				case Sort.integer:return "ℤ";
				case Sort.rational:return "ℚ";
				case Sort.real_:return "ℝ";
				case Sort.complex:return "ℂ";
				case Sort.boolean:return "𝔹";
				default:assert(0);
			}
		}
		if(v.kind==TypeKind.set) return "Set("~typeName(v.fields[0])~")";
		enforce(v.kind==TypeKind.function_,"unsupported function type");
		auto left=typeName(v.fields[0]);
		if(pool.view(v.fields[0]).kind==TypeKind.function_) left="("~left~")";
		return left~"→"~typeName(v.fields[1]);
	}
	private bool reserved(string name){
		return isConstructor(name)||name=="λ"||name=="lambda"||name=="if"||name=="then"||name=="else"||
			name=="domain"||name=="defined"||name=="holds"||name=="guard"||name=="seq"||name=="Set"||name=="sub";
	}
	void declare(string source){
		init(); auto declarations=Parser(source).parseTypedParameters();
		auto next=functions.dup,scalars=scalar;
		foreach(i,v;declarations){
			enforce(!reserved(v.name),"reserved variable name: "~v.name);
			foreach(old;declarations[0..i]) enforce(old.name!=v.name,"duplicate variable: "~v.name);
			auto ty=type(v.type); Sort sort;
			if(scalarSort(ty,sort)){
				foreach(f;next) enforce(f.name!=v.name,"use :reset before changing a function or set to a scalar");
				scalars.declare(v.name~":"~sortName(sort));
			}else{
				foreach(x;scalars.variables) enforce(x.name!=v.name,"use :reset before changing a scalar to a function or set");
				bool found;
				foreach(ref f;next) if(f.name==v.name){ f.type=ty; found=true; break; }
				if(!found) next~=FunctionVariable(v.name,ty);
			}
		}
		functions=next; scalar=scalars;
	}
	private bool special(Pattern p){
		if(p.name=="$lambda"||p.name=="$set"||p.name=="$apply"||p.name=="$member"||
			p.name=="domain"||p.name=="defined"||p.name=="holds"||p.name=="guard"||p.name=="seq") return true;
		if(p.annotation !is null&&p.annotation.args.length) return true;
		foreach(f;functions) if(f.name==p.name) return true;
		foreach(q;p.args) if(special(q)) return true;
		return false;
	}
	private BoundTerm parseBound(Arena a,Bindings b,Pattern raw){
		void collect(Pattern p,string[] bound){
			if(p.name=="$lambda"||p.name=="$set"){
				enforce(!reserved(p.binder),"reserved binder name: "~p.binder);
				foreach(q;p.args) collect(q,bound~p.binder); return;
			}
			if(!p.args.length&&!p.called&&p.name!="#"&&!reserved(p.name)){
				foreach(n;bound) if(p.name==n) return;
				foreach(f;functions) if(p.name==f.name) return;
				foreach(v;scalar.variables) if(p.name==v.name) return;
				scalar.variables~=Parameter(p.name,Sort.real_);
			}
			foreach(q;p.args) collect(q,bound);
		}
		collect(raw,[]);
		BoundTerm lift(Term root,Scope ctx,BoundTerm[] holes){
			Table!(uint,uint) memo;
			BoundTerm visit(Term t){
				auto old=memo.get(t.id,uint.max); if(old!=uint.max) return b.at(old);
				auto n=a.view(t); BoundTerm r;
				if(n.op==Op.variable&&n.value>=scalar.variables.length){
					auto index=n.value-scalar.variables.length;
					enforce(index<holes.length,"invalid function placeholder"); r=holes[index];
				}else if(!n.arity) r=b.scalar(ctx,t);
				else{
					BoundTerm[] args; bool plain=true;
					foreach(i;0..n.arity){ auto x=visit(a.viewChild(t,i)); args~=x; plain&=b.node(x).op==BoundOp.scalar; }
					if(plain){
						Term[] values; bool changed;
						foreach(i,x;args){ auto value=a.at(b.node(x).data); values~=value; changed|=value!=a.viewChild(t,cast(uint)i); }
						r=b.scalar(ctx,changed?a.viewRebuild(t,values,true):t);
					}else r=b.primitive(t,args);
				}
				memo.set(t.id,r.id); return r;
			}
			return visit(root);
		}
		BoundTerm coerce(BoundTerm t,TypeId expected){
			if(expected==TypeId.init||b.type(t)==expected) return t;
			Sort from,to;
			enforce(scalarSort(b.type(t),from)&&scalarSort(expected,to),"function type mismatch");
			auto placeholder=a.variable(from,cast(uint)scalar.variables.length);
			return lift(a.castTo(placeholder,to),b.context(t),[t]);
		}
		BoundTerm build(Pattern p,Scope ctx,string[] locals,TypeId expected=TypeId.init,uint depth=0) @safe{
			enforce(depth<128,"function expression nesting limit exceeded");
			BoundTerm finish(BoundTerm t){ return coerce(t,expected); }
			if(p.name=="$lambda"||p.name=="$set"){
				auto param=type(p.annotation),inner=b.push(ctx,param),names=[p.binder]~locals;
				if(p.name=="$set") return finish(b.set(build(p.args[0],inner,names,scalarType(Sort.boolean),depth+1)));
				TypeId resultType;
				if(expected!=TypeId.init){
					auto v=pool.view(expected); enforce(v.kind==TypeKind.function_&&v.fields[0]==param,"lambda parameter type mismatch"); resultType=v.fields[1];
				}
				auto body=build(p.args[$-1],inner,names,resultType,depth+1);
				if(p.args.length==2) body=b.guard(build(p.args[0],inner,names,scalarType(Sort.boolean),depth+1),body);
				return finish(b.lambda(body));
			}
			if(p.name=="$ascribe"&&p.annotation !is null){
				return finish(build(p.args[0],ctx,locals,type(p.annotation),depth+1));
			}
			if(p.name=="$apply"){
				auto f=build(p.args[0],ctx,locals,TypeId.init,depth+1),v=pool.view(b.type(f));
				enforce(v.kind==TypeKind.function_,"application requires a function");
				return finish(b.apply(f,build(p.args[1],ctx,locals,v.fields[0],depth+1)));
			}
			if(p.name=="$member"){
				auto s=build(p.args[1],ctx,locals,TypeId.init,depth+1),v=pool.view(b.type(s));
				enforce(v.kind==TypeKind.set,"membership requires a set");
				return finish(b.member(s,build(p.args[0],ctx,locals,v.fields[0],depth+1)));
			}
			if(p.name=="domain"||p.name=="defined"||p.name=="holds"){
				enforce(p.args.length==1,"expected one argument to "~p.name);
				auto x=build(p.args[0],ctx,locals,TypeId.init,depth+1);
				return finish(p.name=="domain"?b.domain(x):p.name=="defined"?b.defined(x):b.holds(x));
			}
			if(p.name=="guard"||p.name=="seq"){
				enforce(p.args.length==2,"expected two arguments to "~p.name);
				auto x=build(p.args[0],ctx,locals,p.name=="guard"?scalarType(Sort.boolean):TypeId.init,depth+1);
				auto y=build(p.args[1],ctx,locals,expected,depth+1);
				return p.name=="guard"?b.guard(x,y):b.sequence(x,y);
			}
			BoundTerm variable;
			foreach(i,name;locals) if(p.name==name){ variable=b.variable(ctx,cast(uint)i); break; }
			if(variable==BoundTerm.init) foreach(i,f;functions) if(p.name==f.name){ variable=b.global(ctx,f.type,cast(uint)i); break; }
			if(variable!=BoundTerm.init){
				if(!p.called) return finish(variable);
				enforce(p.args.length==1,"use f(x)(y) for curried application");
				auto v=pool.view(b.type(variable)); enforce(v.kind==TypeKind.function_,"application requires a function");
				return finish(b.apply(variable,build(p.args[0],ctx,locals,v.fields[0],depth+1)));
			}
			BoundTerm[] holes; auto params=scalar.variables.dup;
			Pattern hoist(Pattern q,bool root=false){
				bool local;
				foreach(name;locals) if(q.name==name) local=true;
				if(!root&&(special(q)||local)){
					auto term=build(q,ctx,locals,TypeId.init,depth+1); Sort sort;
					enforce(scalarSort(b.type(term),sort),"scalar operation received a function or set");
					auto name="$hole"~to!string(holes.length); holes~=term; params~=Parameter(name,sort); return new Pattern(name);
				}
				auto copy=new Pattern(q.name); copy.number=q.number; copy.sort=q.sort; copy.annotation=q.annotation; copy.called=q.called;
				foreach(arg;q.args) copy.args~=hoist(arg); return copy;
			}
			auto scalarPattern=hoist(p,true);
			if(expected!=TypeId.init){
				Sort sort; enforce(scalarSort(expected,sort),"expected a function or set expression");
				auto q=pattern("$ascribe",[scalarPattern]); q.sort=sort; scalarPattern=q;
			}
			auto elaborated=elaborate(scalarPattern,params);
			enforce(params.length==scalar.variables.length+holes.length,"unresolved function variable");
			return lift(Syntax.build(a,elaborated,params),ctx,holes);
		}
		return build(raw,b.empty(),[]);
	}
	Term assumption(Arena a,string source){
		enforce(!special(Parser(source).parseRawExpression()),"function and set assumptions are not supported yet");
		return scalar.parse(a,source);
	}
	FunctionResult run(Arena a,string source,Term[] facts=[],Options options=Options.init,bool domainQuery=false){
		init(); auto raw=Parser(source).parseRawExpression(); FunctionResult result; result.domainQuery=domainQuery;
		if(!special(raw)){
			result.scalarOnly=true; result.scalarInput=scalar.parse(a,source);
			result.scalar=domainQuery?simplifyDomain(a,result.scalarInput,facts,options):simplify(a,result.scalarInput,facts,options);
			return result;
		}
		auto b=new Bindings(a,pool); result.bindings=b; result.original=parseBound(a,b,raw);
		auto query=domainQuery?(pool.view(b.type(result.original)).kind==TypeKind.function_?b.domain(result.original):b.defined(result.original)):result.original;
		result.reduction=b.normalize(query,4096,true);
		Term lowered;
		try{ lowered=b.lower(result.reduction.output); }catch(Exception){}
		if(lowered!=Term.init){
			result.lowered=true; result.scalarInput=lowered; result.scalar=simplify(a,lowered,facts,options);
		}
		return result;
	}
	string format(Arena a,FunctionResult result){
		if(result.scalarOnly||result.lowered) return scalar.format(a,result.scalar.output);
		auto b=result.bindings;
		string render(BoundTerm t,string[] locals,uint depth=0) @safe{
			enforce(depth<256,"function formatting depth exceeded");
			auto n=b.node(t);
			string child(uint id){ return render(b.at(id),locals,depth+1); }
			switch(n.op){
				case BoundOp.lambda,BoundOp.set:
					string name="x"; uint index;
					for(;;){
						bool used;
						foreach(v;scalar.variables) if(v.name==name) used=true;
						foreach(f;functions) if(f.name==name) used=true;
						foreach(v;locals) if(v==name) used=true;
						if(!used) break; name="x"~to!string(++index);
					}
					auto param=typeName(pool.view(b.type(t)).fields[0]),body=render(b.at(n.a),[name]~locals,depth+1);
					return n.op==BoundOp.lambda?"λ("~name~":"~param~"). "~body:"{"~name~":"~param~" | "~body~"}";
				case BoundOp.global:return functions[n.data].name;
				case BoundOp.apply:return "("~child(n.a)~")("~child(n.b)~")";
				case BoundOp.sequence:return "seq("~child(n.a)~","~child(n.b)~")";
				case BoundOp.member:return "("~child(n.b)~"∈"~child(n.a)~")";
				case BoundOp.domain:return "domain("~child(n.a)~")";
				case BoundOp.defined:return "defined("~child(n.a)~")";
				case BoundOp.holds:return "holds("~child(n.a)~")";
				case BoundOp.guard:return "guard("~child(n.a)~","~child(n.b)~")";
				case BoundOp.variable:
					Sort sort; if(!scalarSort(b.type(t),sort)) return locals[n.data]; break;
				case BoundOp.scalar,BoundOp.primitive:break;
				default:assert(0);
			}
			auto printer=scalar; printer.variables=printer.variables.dup; Table!(uint,uint) memo;
			Term flatten(BoundTerm x){
				auto found=memo.get(x.id,uint.max); if(found!=uint.max) return a.at(found);
				auto v=b.node(x); Term r;
				if(v.op==BoundOp.scalar) r=a.at(v.data);
				else if(v.op==BoundOp.primitive){
					Term[] args=[flatten(b.at(v.a))]; if(v.b!=uint.max) args~=flatten(b.at(v.b));
					r=a.viewRebuild(a.at(v.data),args,true);
				}else{
					Sort sort; enforce(scalarSort(b.type(x),sort),"non-scalar primitive argument");
					auto name=v.op==BoundOp.variable?locals[v.data]:"("~render(x,locals,depth+1)~")";
					r=a.variable(sort,cast(uint)printer.variables.length); printer.variables~=Parameter(name,sort);
				}
				memo.set(x.id,r.id); return r;
			}
			auto flat=flatten(t),text=printer.format(a,flat); bool same;
			try{ auto check=printer; same=a.sort(check.parse(a,text))==a.sort(flat); }catch(Exception){}
			return same?text:"("~text~":"~sortName(a.sort(flat))~")";
		}
		return render(result.reduction.output,[]);
	}
	string exportCertificate(Arena a,FunctionResult result){
		if(result.scalarOnly) return result.domainQuery?exportDomainLean(a,result.scalarInput,result.scalar):exportLean(a,result.scalar);
		auto code=result.bindings.exportLean(result.reduction,result.lowered);
		if(!result.lowered) return code;
		auto part=replace(exportLean(a,result.scalar),"import QSym\n","");
		part=replace(part,"QSym.Certificate","QSym.FunctionScalar"); code~=part;
		auto r=result.scalar,embedded=a.castTo(r.output,a.sort(r.proofInput));
		string hypotheses,arguments;
		foreach(i,f;r.assumptions){
			auto h="h"~to!string(i); hypotheses~=" ("~h~" : Expr.eval ξ FunctionScalar.n"~to!string(f.id)~" = some true)"; arguments~=" "~h;
		}
		auto original="((BindingCertificate.t"~to!string(result.reduction.input.id)~" γ).eval ξ ρ)";
		auto output="(FunctionScalar.n"~to!string(embedded.id)~".eval ξ)";
		code~="namespace QSym.FunctionCertificate\n";
		code~="theorem refinement (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env [])"~hypotheses~" : Value.Refines "~original~" "~output~" :=\n"~
			"  Eq.mpr (congrArg (fun x => Value.Refines x "~output~") (BindingCertificate.lowered γ ξ ρ)) (FunctionScalar.refinement ξ"~arguments~")\n";
		code~="theorem sound (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env [])"~hypotheses~" (h : Value.Defined "~original~") : "~original~" = "~output~" :=\n"~
			"  (refinement γ ξ ρ"~arguments~").eq_of_defined h\n#qsym_check_axioms refinement\n#qsym_check_axioms sound\n";
		if(result.domainQuery) code~="theorem domain (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env [])"~hypotheses~" : "~original~" = "~output~" :=\n"~
			"  sound γ ξ ρ"~arguments~" ⟨_, rfl⟩\n#qsym_check_axioms domain\n";
		return code~"end QSym.FunctionCertificate\n";
	}
}
