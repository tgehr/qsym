module qsym.functional;
import qsym.ir;
import qsym.binding;
import qsym.types:TypeId,TypeView,TypeKind,TypePool,Dimension;
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
struct FunctionAssumption{ FunctionResult origin; Term term; }
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
	private Dimension dimension(Pattern p,string[] locals=[],Parameter[] parameters=null,TypeId[] localTypes=[]){
		if(p.name=="#"){ enforce(p.number>=0,"negative vector dimension"); return Dimension.literal(cast(ulong)p.number); }
		if(p.name=="$add"||p.name=="$mul"||p.name=="$pow")
			return Dimension.binary(p.name=="$add"?"+":p.name=="$mul"?"*":"^",dimension(p.args[0],locals,parameters,localTypes),dimension(p.args[1],locals,parameters,localTypes));
		enforce(!p.called&&!p.args.length,"dimensions require total natural literals, parameters, sums, products, or powers");
		foreach(i,name;locals) if(name==p.name){ enforce(i<localTypes.length&&pool.view(localTypes[i]).kind==TypeKind.natural,"dimension binder must have type ℕ"); return Dimension.bound(cast(uint)i); }
		foreach(i,v;parameters is null?scalar.variables:parameters) if(v.name==p.name){
			enforce(v.sort==Sort.natural,"dimension parameter must have type ℕ: "~p.name); return Dimension.variable(p.name,cast(uint)i);
		}
		throw new Exception("declare dimension parameter as ℕ: "~p.name);
	}
	private TypeId vectorType(TypeId element,Pattern shape,string[] locals=[],Parameter[] parameters=null,TypeId[] localTypes=[]){
		if(shape.name=="$times") return pool.vector(pool.vector(element,dimension(shape.args[1],locals,parameters,localTypes)),dimension(shape.args[0],locals,parameters,localTypes));
		return pool.vector(element,dimension(shape,locals,parameters,localTypes));
	}
	private TypeId type(TypePattern t,string[] locals=[],Parameter[] parameters=null,TypeId[] localTypes=[]){
		init(); enforce(t !is null,"missing type");
		enforce(t.name!="$subset","refinement annotations require a lambda or set binder");
		if(t.name=="pi"){
			enforce(!reserved(t.binder),"reserved binder name: "~t.binder); auto input=type(t.args[0],locals,parameters,localTypes);
			return pool.pi(input,type(t.args[1],[t.binder]~locals,parameters,[input]~localTypes));
		}
		if(t.name=="Type") return pool.primitive(TypeKind.type_);
		if(t.name=="Unit") return pool.primitive(TypeKind.unit);
		if(t.name=="arrow") return pool.function_(type(t.args[0],locals,parameters,localTypes),type(t.args[1],locals,parameters,localTypes));
		if(t.name=="Set") return pool.set(type(t.args[0],locals,parameters,localTypes));
		if(t.name=="vector") return vectorType(type(t.args[0],locals,parameters,localTypes),t.dimension,locals,parameters,localTypes);
		if(t.name=="tuple"){ TypeId[] fields; foreach(part;t.args) fields~=type(part,locals,parameters,localTypes); return pool.tuple(fields); }
		return scalarType(parseSort(t.name));
	}
	string typeName(TypeId t,string[] locals=[]){
		auto v=pool.view(t); Sort sort;
		if(v.kind==TypeKind.pi){
			Table!(string,bool) used; foreach(name;locals) used.set(name,true);
			void collect(TypeId ty){ auto w=pool.view(ty); if(w.dimension !is null) foreach(name;w.dimension.names) used.set(name,true); foreach(f;w.fields) collect(f); }
			collect(t); string name="n"; uint i; while(used.get(name,false)) name="n"~to!string(++i);
			return "Π("~name~":"~typeName(v.fields[0],locals)~"). "~typeName(v.fields[1],[name]~locals);
		}
		if(v.kind==TypeKind.type_) return "Type";
		if(v.kind==TypeKind.unit) return "Unit";
		if(v.kind==TypeKind.tuple){ string s; foreach(f;v.fields){ if(s.length) s~="×"; auto k=pool.view(f).kind; s~=k==TypeKind.function_||k==TypeKind.pi||k==TypeKind.tuple?"("~typeName(f,locals)~")":typeName(f,locals); } return s; }
		if(v.kind==TypeKind.vector){
			auto element=pool.view(v.fields[0]);
			if(element.kind==TypeKind.vector){ auto base=typeName(element.fields[0],locals); auto k=pool.view(element.fields[0]).kind; return (k==TypeKind.function_||k==TypeKind.pi||k==TypeKind.tuple||k==TypeKind.vector?"("~base~")":base)~"^("~v.dimension.format(locals)~"×"~element.dimension.format(locals)~")"; }
			auto base=typeName(v.fields[0],locals); if(element.kind==TypeKind.function_||element.kind==TypeKind.pi||element.kind==TypeKind.tuple) base="("~base~")";
			return base~"^"~v.dimension.format(locals);
		}
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
		if(v.kind==TypeKind.set) return "Set("~typeName(v.fields[0],locals)~")";
		enforce(v.kind==TypeKind.function_,"unsupported function type");
		auto left=typeName(v.fields[0],locals);
		if(pool.view(v.fields[0]).kind==TypeKind.function_||pool.view(v.fields[0]).kind==TypeKind.pi) left="("~left~")";
		return left~"→"~typeName(v.fields[1],locals);
	}
	private bool reserved(string name){
		return typeAlias(name)||isConstructor(name)||name=="λ"||name=="lambda"||name=="μ"||name=="mu"||name=="undefined"||name=="if"||name=="then"||name=="else"||
			name=="∑"||name=="sum"||name=="domain"||name=="defined"||name=="holds"||name=="guard"||name=="seq"||name=="Set"||name=="sub"||name=="dot"||name=="get"||name=="Π"||name=="Pi";
	}
	private bool typeAlias(string name){
		foreach(n;["Nat","ℕ","Int","ℤ","Rat","ℚ","Real","ℝ","Complex","ℂ","Bool","𝔹","Type","Unit"]) if(name==n) return true;
		return false;
	}
	void declare(string source){
		init(); auto declarations=Parser(source).parseTypedParameters();
		auto next=functions.dup,scalars=scalar;
		foreach(i,v;declarations){
			enforce(!reserved(v.name),"reserved variable name: "~v.name);
			foreach(old;declarations[0..i]) enforce(old.name!=v.name,"duplicate variable: "~v.name);
			auto ty=type(v.type,[],scalars.variables); Sort sort;
			if(scalarSort(ty,sort)){
				bool usesDimension(TypeId t){
					auto shape=pool.view(t); if(shape.dimension !is null) foreach(name;shape.dimension.names) if(name==v.name) return true;
					foreach(field;shape.fields) if(usesDimension(field)) return true; return false;
				}
				if(sort!=Sort.natural) foreach(f;next) enforce(!usesDimension(f.type),"dimension parameter must remain ℕ: "~v.name);
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
		if(p.name=="$type"||p.name=="$arrowtype"||p.name=="$tuple"||p.name=="$matmul"||p.name=="dot"||p.name=="get") return true;
		if(typeAlias(p.name)||p.name=="Set") return true;
		if(p.name=="$sum"||p.name=="$fix"||p.name=="$bottom"||p.name=="$lambda"||p.name=="$set"||p.name=="$apply"||p.name=="$member"||p.name=="$subset"||
			p.name=="domain"||p.name=="defined"||p.name=="holds"||p.name=="guard"||p.name=="seq") return true;
		if(p.annotation !is null&&p.annotation.args.length) return true;
		foreach(f;functions) if(f.name==p.name) return true;
		foreach(q;p.args) if(special(q)) return true;
		return false;
	}
	private BoundTerm parseBound(Arena a,Bindings b,Pattern raw){
		void collect(Pattern p,string[] bound){
			if(p.name=="$sum"||p.name=="$fix"||p.name=="$lambda"||p.name=="$set"){
				enforce(!reserved(p.binder),"reserved binder name: "~p.binder);
				for(auto ty=p.annotation;ty.name=="$subset";ty=ty.args[0]){
					enforce(!reserved(ty.binder),"reserved binder name: "~ty.binder); collect(ty.predicate,bound~ty.binder);
				}
				foreach(q;p.args) collect(q,bound~p.binder); return;
			}
			if(!p.args.length&&!p.called&&p.name!="#"&&p.name!="$tuple"&&p.name!="$bottom"&&p.name!="$type"&&!reserved(p.name)){
				foreach(n;bound) if(p.name==n) return;
				foreach(f;functions) if(p.name==f.name) return;
				foreach(v;scalar.variables) if(p.name==v.name) return;
				scalar.variables~=Parameter(p.name,Sort.real_);
			}
			foreach(q;p.args) collect(q,bound);
		}
		collect(raw,[]);
		foreach(i,v;scalar.variables) if(v.sort==Sort.natural) b.dimensionParameter(v.name,cast(uint)i);
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
			auto v=pool.view(b.type(t)),w=pool.view(expected),n=b.node(t);
			if(v.kind==TypeKind.vector&&w.kind==TypeKind.vector&&v.dimension.key==w.dimension.key&&(n.op==BoundOp.vectorCons||n.op==BoundOp.vectorNil)){
				BoundTerm[] fields; auto current=t;
				while(b.node(current).op==BoundOp.vectorCons){ auto q=b.node(current); fields~=coerce(b.at(q.a),w.fields[0]); current=b.at(q.b); }
				return b.tuple(b.context(t),fields,expected);
			}
			if(v.kind==TypeKind.tuple&&w.kind==TypeKind.tuple&&v.fields.length==w.fields.length){
				BoundTerm[] fields; auto ctx=b.context(t);
				foreach(i,field;w.fields) fields~=coerce(b.get(t,b.scalar(ctx,a.natural_(i))),field);
				return b.tuple(ctx,fields,expected);
			}
			Sort from,to;
			enforce(scalarSort(b.type(t),from)&&scalarSort(expected,to),"function type mismatch");
			auto placeholder=a.variable(from,cast(uint)scalar.variables.length);
			return lift(a.castTo(placeholder,to),b.context(t),[t]);
		}
		TypeId commonType(TypeId x,TypeId y){
			if(x==y) return x; auto v=pool.view(x),w=pool.view(y);
			if(v.kind==TypeKind.vector&&w.kind==TypeKind.vector&&v.dimension.key==w.dimension.key){ auto element=commonType(v.fields[0],w.fields[0]); return element==TypeId.init?element:pool.vector(element,v.dimension); }
			if(v.kind==TypeKind.tuple&&w.kind==TypeKind.tuple&&v.fields.length==w.fields.length){
				TypeId[] fields;
				foreach(i,field;v.fields){ auto common=commonType(field,w.fields[i]); if(common==TypeId.init) return common; fields~=common; }
				return pool.tuple(fields);
			}
			Sort xs,ys;
			if(scalarSort(x,xs)&&scalarSort(y,ys)&&xs!=Sort.boolean&&ys!=Sort.boolean){
				foreach(s;[Sort.complex,Sort.real_,Sort.rational,Sort.integer,Sort.natural]) if(xs==s||ys==s) return scalarType(s);
			}
			return TypeId.init;
		}
		BoundTerm conditional(BoundTerm predicate,BoundTerm yes,BoundTerm no){
			auto ty=b.type(yes),ctx=b.context(yes); Sort sort;
			enforce(b.type(no)==ty,"conditional branch type mismatch");
			auto neg=b.primitive(a.not_(a.boolean(false)),[predicate]);
			if(scalarSort(ty,sort)){
				if(sort==Sort.boolean){
					auto conjunction=a.and_(a.boolean(false),a.boolean(false));
					return b.primitive(a.or_(a.boolean(false),a.boolean(false)),[
						b.primitive(conjunction,[predicate,yes]),b.primitive(conjunction,[neg,no])]);
				}
				auto zero=a.number(Number(0),sort),mask=a.mask(a.boolean(false),zero);
				return b.primitive(a.add(zero,zero,true),[b.primitive(mask,[predicate,yes]),b.primitive(mask,[neg,no])]);
			}
			auto v=pool.view(ty);
			enforce(v.kind==TypeKind.tuple||v.kind==TypeKind.vector&&v.dimension.constant&&v.length>0&&v.length<=256,
				"conditional branches require scalars or nonempty finite products of scalars");
			BoundTerm[] fields;
			foreach(i;0..(v.kind==TypeKind.tuple?v.fields.length:v.length)){
				auto index=b.scalar(ctx,a.natural_(i));
				// Project the whole branch, preserving strict product definedness.
				fields~=conditional(predicate,b.get(yes,index),b.get(no,index));
			}
			return b.tuple(ctx,fields,ty);
		}
		BoundTerm build(Pattern p,Scope ctx,string[] locals,TypeId expected=TypeId.init,uint depth=0) @safe{
			enforce(depth<128,"function expression nesting limit exceeded");
			BoundTerm finish(BoundTerm t){ return coerce(t,expected); }
			TypeId[] localTypes; foreach(i;0..locals.length) localTypes~=b.type(b.variable(ctx,cast(uint)i));
			if(p.name=="$type") return finish(b.typeValue(ctx,type(p.annotation,locals,null,localTypes)));
			if(p.name=="$arrowtype") return finish(b.typeValue(ctx,pool.function_(b.typeDenoted(build(p.args[0],ctx,locals)),b.typeDenoted(build(p.args[1],ctx,locals)))));
			if(p.name=="$bottom") return finish(b.bottom(ctx,type(p.annotation,locals,null,localTypes)));
			if(p.name=="$if"){
				auto predicate=build(p.args[0],ctx,locals,scalarType(Sort.boolean),depth+1);
				auto yes=build(p.args[1],ctx,locals,expected,depth+1),no=build(p.args[2],ctx,locals,expected,depth+1);
				auto common=commonType(b.type(yes),b.type(no));
				enforce(common!=TypeId.init,"conditional branch type mismatch");
				return finish(conditional(predicate,coerce(yes,common),coerce(no,common)));
			}
			if(p.name=="$tuple"){
				BoundTerm[] elements; auto v=expected==TypeId.init?TypeView.init:pool.view(expected);
				foreach(i,q;p.args){
					TypeId element;
					if(v.kind==TypeKind.vector) element=v.fields[0];
					if(v.kind==TypeKind.tuple){ enforce(i<v.fields.length,"tuple arity mismatch"); element=v.fields[i]; }
					elements~=build(q,ctx,locals,element,depth+1);
				}
				if(expected==TypeId.init&&elements.length){
					auto common=b.type(elements[0]); foreach(e;elements[1..$]){ common=commonType(common,b.type(e)); if(common==TypeId.init) break; }
					if(common!=TypeId.init) foreach(ref e;elements) e=coerce(e,common);
				}
				return b.tuple(ctx,elements,expected);
			}
			if(p.name=="get"){
				enforce(p.args.length==2,"get requires a tuple or vector and an index");
				return finish(b.get(build(p.args[0],ctx,locals,TypeId.init,depth+1),build(p.args[1],ctx,locals,scalarType(Sort.natural),depth+1)));
			}
			if(p.name=="$mul"||p.name=="$times"||p.name=="$add"||p.name=="$pow"||p.name=="$matmul"||p.name=="dot"){
				enforce(p.args.length==2,"binary operation requires two arguments");
				auto left=build(p.args[0],ctx,locals,TypeId.init,depth+1),v=pool.view(b.type(left));
				if(v.kind==TypeKind.type_){
					if(p.name=="$pow") return finish(b.typeValue(ctx,vectorType(b.typeDenoted(left),p.args[1],locals,null,localTypes)));
					enforce(p.name=="$times"||p.name=="$mul","invalid type operation"); TypeId[] fields;
					void append(Pattern q){
						if(q.name=="$times"||q.name=="$mul"){ append(q.args[0]); append(q.args[1]); }
						else fields~=b.typeDenoted(build(q,ctx,locals,TypeId.init,depth+1));
					}
					append(p); return finish(b.typeValue(ctx,pool.tuple(fields)));
				}
				if(v.kind==TypeKind.vector){
					auto target=p.name=="$pow"?scalarType(Sort.natural):p.name=="$matmul"?TypeId.init:b.type(left);
					if(p.name=="$matmul"&&p.args[1].name=="$tuple"&&(!p.args[1].args.length||p.args[1].args[0].name!="$tuple")) target=v.fields[0];
					auto right=build(p.args[1],ctx,locals,target,depth+1);
					auto op=p.name=="$pow"?TensorOp.power:p.name=="dot"?TensorOp.dot:p.name=="$add"?TensorOp.add:TensorOp.mul;
					if(p.name=="$matmul"){
						auto w=pool.view(b.type(right)); enforce(w.kind==TypeKind.vector,"matrix multiplication requires a vector or matrix");
						op=pool.view(w.fields[0]).kind==TypeKind.vector?TensorOp.matmul:TensorOp.matvec;
						auto row=pool.view(v.fields[0]); enforce(row.kind==TypeKind.vector,"matrix multiplication requires a matrix on the left");
						auto ty=op==TensorOp.matmul?pool.vector(pool.vector(row.fields[0],pool.view(w.fields[0]).dimension),w.dimension):pool.vector(row.fields[0],w.dimension);
						right=coerce(right,ty);
					}
					return finish(b.tensor(op,left,right));
				}
			}
			if(p.name=="$fix"){
				auto ty=type(p.annotation,locals,null,localTypes),v=pool.view(ty);
				enforce(v.kind==TypeKind.function_,"fixed points currently require a function type");
				auto inner=b.push(ctx,ty),body=build(p.args[0],inner,[p.binder]~locals,ty,depth+1);
				if(b.node(body).op==BoundOp.variable&&b.node(body).data==0){
					auto arg=b.push(inner,v.fields[0]); uint[] indices;
					foreach(i;0..b.depth(inner)) indices~=i+1;
					body=b.lambda(b.apply(b.rename(body,arg,indices),b.variable(arg,0)));
				}
				return finish(b.hint(b.fixed(body),p.binder));
			}
			if(typeAlias(p.name)){
				enforce(!p.called,"a type name is not a function"); return finish(b.typeValue(ctx,type(new TypePattern(p.name))));
			}
			if(p.name=="Set"){
				enforce(p.args.length==1,"Set requires one type");
				return finish(b.typeValue(ctx,pool.set(b.typeDenoted(build(p.args[0],ctx,locals)))));
			}
			bool positive=p.name=="not"&&p.args.length==1&&p.args[0].name=="$different";
			auto comparison=positive?p.args[0]:p;
			if(comparison.name=="$different"){
				auto left=build(comparison.args[0],ctx,locals,TypeId.init,depth+1),kind=pool.view(b.type(left)).kind;
				if(kind==TypeKind.type_||kind==TypeKind.function_||kind==TypeKind.pi||kind==TypeKind.set||kind==TypeKind.vector||kind==TypeKind.tuple||kind==TypeKind.unit){
					auto right=build(comparison.args[1],ctx,locals,b.type(left),depth+1);
					auto eq=kind==TypeKind.type_?b.typeEq(left,right):b.equal(left,right);
					return finish(positive?eq:b.primitive(a.not_(a.boolean(false)),[eq]));
				}
			}
			if(p.name=="$sum"){
				auto param=type(p.annotation,locals,null,localTypes);
				enforce(param==scalarType(Sort.natural)||param==scalarType(Sort.integer),"summation index must be ℕ or ℤ");
				auto inner=b.push(ctx,param),body=build(p.args[0],inner,[p.binder]~locals,expected,depth+1);
				return finish(b.summation(b.hint(b.lambda(body),p.binder)));
			}
			if(p.name=="$lambda"||p.name=="$set"){
				auto base=p.annotation; while(base.name=="$subset") base=base.args[0];
				auto param=type(base,locals,null,localTypes),inner=b.push(ctx,param),names=[p.binder]~locals;
				BoundTerm restrict(BoundTerm body){
					for(auto ty=p.annotation;ty.name=="$subset";ty=ty.args[0])
						body=b.guard(build(ty.predicate,inner,[ty.binder]~locals,scalarType(Sort.boolean),depth+1),body);
					return body;
				}
				auto refinement=p.annotation.name=="$subset"?p.annotation.binder:"";
				if(p.name=="$set") return finish(b.hint(b.set(restrict(build(p.args[0],inner,names,scalarType(Sort.boolean),depth+1))),p.binder));
				TypeId resultType;
				if(expected!=TypeId.init){
					auto v=pool.view(expected); enforce((v.kind==TypeKind.function_||v.kind==TypeKind.pi)&&v.fields[0]==param,"lambda parameter type mismatch"); resultType=v.kind==TypeKind.pi?v.fields[1]:pool.shift(v.fields[1],1);
				}
				auto body=build(p.args[$-1],inner,names,resultType,depth+1);
				if(p.args.length==2) body=b.guard(build(p.args[0],inner,names,scalarType(Sort.boolean),depth+1),body);
				return finish(b.hint(b.lambda(restrict(body)),p.binder,refinement));
			}
			if(p.name=="$ascribe"&&p.annotation !is null){
				return finish(build(p.args[0],ctx,locals,type(p.annotation,locals,null,localTypes),depth+1));
			}
			if(p.name=="$apply"){
				auto f=build(p.args[0],ctx,locals,TypeId.init,depth+1),v=pool.view(b.type(f));
				enforce((v.kind==TypeKind.function_||v.kind==TypeKind.pi),"application requires a function");
				return finish(b.apply(f,build(p.args[1],ctx,locals,v.fields[0],depth+1)));
			}
			if(p.name=="$subset"){
				auto left=build(p.args[0],ctx,locals,TypeId.init,depth+1);
				return finish(b.subset(left,build(p.args[1],ctx,locals,b.type(left),depth+1)));
			}
			if(p.name=="$member"){
				auto s=build(p.args[1],ctx,locals,TypeId.init,depth+1);
				if(b.node(s).op==BoundOp.typeValue) s=b.set(b.scalar(b.push(ctx,b.typeDenoted(s)),a.boolean(true)));
				auto v=pool.view(b.type(s));
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
				auto v=pool.view(b.type(variable)); enforce((v.kind==TypeKind.function_||v.kind==TypeKind.pi),"application requires a function");
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
	FunctionAssumption analyzeAssumption(Arena a,string source){
		auto origin=run(a,source);
		if(!origin.scalarOnly) enforce(origin.bindings.type(origin.original)==scalarType(Sort.boolean),"assumptions must be Bool");
		enforce(origin.scalarOnly||origin.lowered,"assumption remains symbolic; it cannot yet be used as a scalar fact");
		enforce(a.sort(origin.scalarInput)==Sort.boolean,"assumptions must be Bool");
		return FunctionAssumption(origin,origin.scalarInput);
	}
	Term assumption(Arena a,string source){ return analyzeAssumption(a,source).term; }
	FunctionAssumption[] assumptions(Arena a,string[] sources){
		FunctionAssumption[] result; foreach(source;sources) result~=analyzeAssumption(a,source); return result;
	}
	static Term[] predicates(FunctionAssumption[] facts){
		Term[] result; foreach(f;facts) result~=f.term; return result;
	}
	string inspectType(Arena a,string source){
		init(); auto raw=Parser(source).parseRawExpression();
		if(!special(raw)) return typeName(scalarType(a.sort(scalar.parse(a,source))));
		auto b=new Bindings(a,pool); return typeName(b.type(parseBound(a,b,raw)));
	}
	FunctionResult run(Arena a,string source,Term[] facts=[],Options options=Options.init,bool domainQuery=false){
		init(); auto raw=Parser(source).parseRawExpression(); FunctionResult result; result.domainQuery=domainQuery;
		if(!special(raw)){
			result.scalarOnly=true; result.scalarInput=scalar.parse(a,source);
			result.scalar=domainQuery?simplifyDomain(a,result.scalarInput,facts,options):simplify(a,result.scalarInput,facts,options);
			return result;
		}
		auto b=new Bindings(a,pool); result.bindings=b; result.original=parseBound(a,b,raw);
		auto query=domainQuery?((pool.view(b.type(result.original)).kind==TypeKind.function_||pool.view(b.type(result.original)).kind==TypeKind.pi)?b.domain(result.original):b.defined(result.original)):result.original;
		result.reduction=b.normalize(query,4096,true);
		if(b.telescope) return result;
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
		Table!(string,bool) free;
		Table!(uint,bool) seen;
		void collectFree(BoundTerm t){
			if(seen.get(t.id,false)) return; seen.set(t.id,true); auto n=b.node(t);
			void dimensions(TypeId t){ auto v=pool.view(t); if(v.dimension !is null) foreach(name;v.dimension.names) free.set(name,true); foreach(f;v.fields) dimensions(f); }
			dimensions(b.type(t)); if(n.op==BoundOp.typeValue) dimensions(b.typeDenoted(t));
			if(n.op==BoundOp.global) free.set(functions[n.data].name,true);
			if(n.op==BoundOp.scalar) foreach(id;a.viewPostorder(a.at(n.data))){
				auto v=a.view(a.at(id)); if(v.op==Op.variable&&v.value<scalar.variables.length) free.set(scalar.variables[v.value].name,true);
			}
			if(n.a!=uint.max) collectFree(b.at(n.a)); if(n.b!=uint.max) collectFree(b.at(n.b));
		}
		collectFree(result.reduction.output);
		string fresh(string[] locals,string preferred=""){
			if(!preferred.length) preferred="x";
			string name=preferred; uint index;
			for(;;){
				bool used=free.get(name,false);
				foreach(v;locals) if(v==name) used=true;
				if(!used) return name; name=preferred~to!string(++index);
			}
		}
		string render(BoundTerm t,string[] locals,uint depth=0) @safe{
			enforce(depth<256,"function formatting depth exceeded");
			auto n=b.node(t);
			string child(uint id){ return render(b.at(id),locals,depth+1); }
			string projection(uint base,ulong index){
				while(b.node(b.at(base)).op==BoundOp.rest){ base=b.node(b.at(base)).a; ++index; }
				return "get("~child(base)~","~to!string(index)~")";
			}
			switch(n.op){
				case BoundOp.unit:return "()";
				case BoundOp.vectorNil:return "(():"~typeName(b.type(t),locals)~")";
				case BoundOp.vectorCons,BoundOp.pair:
					string text="("; auto current=t; bool first=true;
					while(b.node(current).op==BoundOp.vectorCons||b.node(current).op==BoundOp.pair){
						auto q=b.node(current); if(!first) text~=","; text~=child(q.a); first=false; current=b.at(q.b);
					}
					enforce(b.node(current).op==BoundOp.unit||b.node(current).op==BoundOp.vectorNil,"invalid tuple tail");
					if(b.node(t).b==current.id) text~=",";
					text~=")"; return n.op==BoundOp.pair?"("~text~":"~typeName(b.type(t),locals)~")":text;
				case BoundOp.first:return projection(n.a,0);
				case BoundOp.rest:
					auto v=pool.view(b.type(b.at(n.a))); string text="(";
					foreach(i;1..v.fields.length){ if(i!=1) text~=","; text~="get("~child(n.a)~","~to!string(i)~")"; }
					if(v.fields.length==2) text~=","; return text~")";
				case BoundOp.get:
					auto index=b.node(b.at(n.b));
					if(index.op==BoundOp.scalar&&a.isNumber(a.at(index.data))&&a.number(a.at(index.data)).re.small)
						return projection(n.a,cast(ulong)a.number(a.at(index.data)).re.integer);
					return "get("~child(n.a)~","~child(n.b)~")";
				case BoundOp.tensor:
					auto op=cast(TensorOp)n.data;
					if(op==TensorOp.dot) return "dot("~child(n.a)~","~child(n.b)~")";
					auto right=child(n.b),exponent=b.node(b.at(n.b));
					if(op==TensorOp.power&&exponent.op!=BoundOp.variable&&exponent.op!=BoundOp.global&&
						!(exponent.op==BoundOp.scalar&&!a.view(a.at(exponent.data)).arity)) right="("~right~")";
					return "("~child(n.a)~(op==TensorOp.add?"+":op==TensorOp.mul?"·":op==TensorOp.power?"^":"@")~right~")";
				case BoundOp.fixed:
					auto name=fresh(locals,b.binderHint(t).name); return "μ("~name~":"~typeName(b.type(t),locals)~"). "~render(b.at(n.a),[name]~locals,depth+1);
				case BoundOp.bottom:return "undefined("~typeName(b.type(t),locals)~")";
				case BoundOp.finiteSum:
					auto fn=b.at(n.a),body=b.node(fn),name=fresh(locals,b.binderHint(fn).name);
					return "∑("~name~":ℕ). ["~name~"<"~child(n.b)~"]·("~render(b.at(body.a),[name]~locals,depth+1)~")";
				case BoundOp.summation:
					auto fn=b.at(n.a),body=b.node(fn),ctx=b.context(b.at(body.a));
					auto name=fresh(locals,b.binderHint(fn).name);
					return "∑("~name~":"~typeName(b.type(b.variable(ctx,0)),locals)~"). "~render(b.at(body.a),[name]~locals,depth+1);
				case BoundOp.lambda,BoundOp.set:
					auto h=b.binderHint(t),name=fresh(locals,h.name),param=typeName(pool.view(b.type(t)).fields[0],locals),bodyTerm=b.at(n.a),v=b.node(bodyTerm);
					if(n.op==BoundOp.lambda&&v.op==BoundOp.guard){
						auto bound=fresh(locals,h.refinement.length?h.refinement:name);
						param="{"~bound~":"~param~" | "~render(b.at(v.a),[bound]~locals,depth+1)~"}"; bodyTerm=b.at(v.b);
					}
					auto body=render(bodyTerm,[name]~locals,depth+1);
					return n.op==BoundOp.lambda?"λ("~name~":"~param~"). "~body:"{"~name~":"~param~" | "~body~"}";
				case BoundOp.global:return functions[n.data].name;
				case BoundOp.typeValue:return typeName(b.typeDenoted(t),locals);
				case BoundOp.typeEq:return "("~child(n.a)~"="~child(n.b)~")";
				case BoundOp.equal:
					string operand(uint id){ auto op=b.node(b.at(id)).op; return op==BoundOp.lambda||op==BoundOp.fixed?"("~child(id)~")":child(id); }
					return "("~operand(n.a)~"="~operand(n.b)~")";
				case BoundOp.apply:
					auto f=b.node(b.at(n.a)); return (f.op==BoundOp.variable||f.op==BoundOp.global?child(n.a):"("~child(n.a)~")")~"("~child(n.b)~")";
				case BoundOp.sequence:return "seq("~child(n.a)~","~child(n.b)~")";
				case BoundOp.subset:return "("~child(n.a)~"⊆"~child(n.b)~")";
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
					auto name=v.op==BoundOp.variable?locals[v.data]:v.op==BoundOp.apply?render(x,locals,depth+1):"("~render(x,locals,depth+1)~")";
					r=a.variable(sort,cast(uint)printer.variables.length); printer.variables~=Parameter(name,sort);
				}
				memo.set(x.id,r.id); return r;
			}
			auto flat=flatten(t),text=printer.format(a,flat); bool same;
			try{ auto check=printer; same=a.sort(check.parse(a,text))==a.sort(flat); }catch(Exception){}
			return same?text:"("~text~":"~typeName(scalarType(a.sort(flat)))~")";
		}
		return render(result.reduction.output,[]);
	}
	private string exportResult(Arena a,FunctionResult result){
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
		auto dimArg=result.bindings.dependent?" ξ.natural":"";
		auto original="((BindingCertificate.t"~to!string(result.reduction.input.id)~dimArg~" γ).eval ξ ρ)";
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
	string exportCertificate(Arena a,FunctionResult result,FunctionAssumption[] facts=[]){
		auto code=exportResult(a,result); bool expanded;
		foreach(f;facts) expanded|=!f.origin.scalarOnly;
		if(!expanded||!result.scalarOnly&&!result.lowered) return code;
		enforce(facts.length==result.scalar.assumptions.length,"assumption certificate count mismatch");
		auto main=result.scalarOnly?"Certificate":"FunctionScalar";
		string hypotheses,arguments;
		foreach(i,f;facts){
			enforce(f.term==result.scalar.assumptions[i],"assumption certificate changed");
			auto h="h"~to!string(i); string source,proof=h;
			if(f.origin.scalarOnly) source="("~main~".n"~to!string(f.term.id)~".eval ξ)";
			else{
				auto prefix="QSym.Assumption"~to!string(i),r=f.origin.reduction;
				auto part=replace(f.origin.bindings.exportLean(r,true),"import QSym\n","");
				part=replace(part,"QSym.BindingScalar",prefix~".BindingScalar");
				part=replace(part,"QSym.BindingCertificate",prefix~".BindingCertificate"); code~=part;
				auto binding="Assumption"~to!string(i)~".BindingCertificate";
				source="(("~binding~".t"~to!string(r.input.id)~" γ).eval ξ ρ)";
				proof="(Eq.trans ("~binding~".lowered γ ξ ρ).symm "~h~")";
			}
			hypotheses~=" ("~h~" : "~source~" = some true)"; arguments~=" "~proof;
		}
		code~="namespace QSym.AssumptionCertificate\n";
		auto parameters=" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env [])"~hypotheses;
		if(result.scalarOnly&&result.domainQuery){
			auto input="(DomainCertificate.n"~to!string(result.scalarInput.id)~".eval ξ)";
			auto output="(Certificate.n"~to!string(result.scalar.output.id)~".eval ξ)";
			code~="theorem domain"~parameters~" : Domain.Correct "~input~" "~output~" :=\n  DomainCertificate.domain_correct ξ"~arguments~"\n#qsym_check_axioms domain\n";
		}else{
			auto r=result.scalar,embedded=a.castTo(r.output,a.sort(r.proofInput));
			auto input=result.scalarOnly?"(Certificate.n"~to!string(r.proofInput.id)~".eval ξ)":
				"((BindingCertificate.t"~to!string(result.reduction.input.id)~" γ).eval ξ ρ)";
			auto output="("~main~".n"~to!string(embedded.id)~".eval ξ)";
			auto call=result.scalarOnly?"Certificate.refinement ξ":"FunctionCertificate.refinement γ ξ ρ";
			code~="theorem refinement"~parameters~" : Value.Refines "~input~" "~output~" :=\n  "~call~arguments~"\n#qsym_check_axioms refinement\n";
			if(result.domainQuery) code~="theorem domain"~parameters~" : "~input~" = "~output~" :=\n  FunctionCertificate.domain γ ξ ρ"~arguments~"\n#qsym_check_axioms domain\n";
		}
		return code~"end QSym.AssumptionCertificate\n";
	}

}
