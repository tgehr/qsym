module qsym.binding;
import qsym.ir;
import qsym.types:TypeId,TypeKind,TypePool;
import qsym.number:Number;
import qsym.table:Table;
import qsym.generated.rules:Law,instantiate;
import qsym.proof:leanSyntaxCode,leanValueOperation,exportDomainLean,scalarExport=exportLean;
import qsym.domain:simplifyDomain;
import qsym.simplify:Result,ScalarResult=Result,Options,DensityMode,simplify;
import std.string:replace;
import qsym.spec:leanSort;
import std.exception:enforce;
import std.conv:to;
@safe:

struct Scope{
	private Bindings owner;
	private uint index=uint.max;
	bool opEquals(Scope rhs)const{ return owner is rhs.owner&&index==rhs.index; }
}
struct BoundTerm{
	private Bindings owner;
	private uint index=uint.max;
	@property uint id()const{ return index; }
	bool opEquals(BoundTerm rhs)const{ return owner is rhs.owner&&index==rhs.index; }
}
enum BoundOp:ubyte{ scalar,variable,primitive,lambda,apply,sequence,global,set,member,domain,defined,holds,guard,subset,typeValue,typeEq,bottom,fixed,equal,unit,vectorNil,vectorCons,pair,first,rest,get,tensor }
enum TensorOp:ubyte{ add,mul,dot,matvec,matmul,power }
struct BoundNode{
	BoundOp op;
	uint context,type,a=uint.max,b=uint.max,data;
}
struct BinderHint{ string name,refinement; }
private enum BindingRule:ubyte{
	refl,congr,beta,seqScalar,seqLam,seqSelf,trans,fold,seqTotal,seqGuard,domainLam,memberSet,
	definedTotal,definedGuardFalse,guardTrue,scalarDomain,scalarHolds,scalarSimplify,
	subsetRefl,subsetEmpty,subsetUniv,subsetUnivEmpty,definedMember,definedSubset,definedGuard,definedApp,domainGuardFalse,definedNot,
	guardAnd,pointwise,holdsGuard,setHolds,typeEqSelf,typeEqValues,shortCircuit,fixedApp,fixedConstant,fixedIdentity,domainBottom,definedFixed,appBottom,appScalarUndefined,memberDomain,
	equalSelf,equalBottomLeft,equalBottomRight,definedEqual,equalUnivEmpty,equalEmptyUniv,fixedRecurrence,tensorEval,tensorPower,tensorDefined,getBottom,getScalarUndefined
}
private struct BindingStep{ BindingRule rule; uint from,to,left=uint.max,right=uint.max,extra=uint.max; }
private struct ScalarDomain{ Term input; Result result,value; uint variable; Sort sort; uint[] path; BoundOp mode; }
private struct RecurrenceSolution{ uint source,target,base,delta; Law law,zero; bool left,cutoff; }
struct BindingResult{
	BoundTerm input,output;
	bool exhausted;
	uint steps;
	private BindingStep[] proofs;
	private uint proof;
	private ScalarDomain[] domains;
	private RecurrenceSolution[] solutions;
}

final class Bindings{
	private Arena arena;
	private TypePool pool;
	private TypeId[] types;
	private Table!(uint,uint) typeIds;
	private struct Context{ uint type,parent,length; }
	private struct ContextKey{ uint type,parent; }
	private Context[] contexts;
	private Table!(ContextKey,uint) contextIds;
	private BoundNode[] nodes;
	private Table!(BoundNode,uint) nodeIds;
	private Table!(uint,uint) binderHints;
	private BinderHint[] hints;
	private bool dependent_;
	@property bool dependent(){ return dependent_; }
	this(Arena arena,TypePool pool=null){
		enforce(arena !is null,"scalar arena required");
		this.arena=arena; this.pool=pool is null?new TypePool:pool;
		contexts~=Context(uint.max,uint.max,0);
	}
	@property TypePool typePool(){ return pool; }
	Scope empty(){ return Scope(this,0); }
	private void check(Scope s)const{ enforce(s.owner is this&&s.index<contexts.length,"invalid or foreign context"); }
	private void check(BoundTerm t)const{ enforce(t.owner is this&&t.id<nodes.length,"invalid or foreign bound term"); }
	private uint typeId(TypeId t){
		auto v=pool.view(t);
		if(v.dimension !is null&&v.dimension.names.length) dependent_=true;
		enforce(v.kind==TypeKind.type_||v.kind==TypeKind.function_||v.kind==TypeKind.set||v.kind==TypeKind.vector||v.kind==TypeKind.tuple||v.kind<=TypeKind.complex,"unsupported binding type");
		foreach(f;v.fields) typeId(f);
		auto id=typeIds.get(t.id,uint.max);
		if(id!=uint.max) return id;
		enforce(types.length<uint.max,"binding type limit exceeded");
		id=cast(uint)types.length; types~=t; typeIds.set(t.id,id); return id;
	}
	TypeId scalarType(Sort s){
		final switch(s){
			case Sort.natural:return pool.primitive(TypeKind.natural);
			case Sort.integer:return pool.primitive(TypeKind.integer);
			case Sort.rational:return pool.primitive(TypeKind.rational);
			case Sort.real_:return pool.primitive(TypeKind.real_);
			case Sort.complex:return pool.primitive(TypeKind.complex);
			case Sort.boolean:return pool.primitive(TypeKind.boolean);
			case Sort.density,Sort.measure:throw new Exception("unsupported binding scalar type");
		}
	}
	Scope push(Scope s,TypeId t){
		check(s); auto ty=typeId(t),key=ContextKey(ty,s.index);
		auto id=contextIds.get(key,uint.max);
		if(id!=uint.max) return Scope(this,id);
		enforce(contexts[s.index].length<128,"binding depth limit exceeded");
		id=cast(uint)contexts.length; contexts~=Context(ty,s.index,contexts[s.index].length+1);
		contextIds.set(key,id); return Scope(this,id);
	}
	BoundNode node(BoundTerm t){ check(t); return nodes[t.id]; }
	BinderHint binderHint(BoundTerm t){ check(t); auto i=binderHints.get(t.id,uint.max); return i==uint.max?BinderHint.init:hints[i]; }
	BoundTerm hint(BoundTerm t,string name,string refinement=""){
		auto op=node(t).op; enforce(op==BoundOp.lambda||op==BoundOp.set||op==BoundOp.fixed,"binder hint requires a binder");
		if(!binderHint(t).name.length){ binderHints.set(t.id,cast(uint)hints.length); hints~=BinderHint(name,refinement); }
		return t;
	}
	private BoundTerm inheritHint(BoundTerm from,BoundTerm to){
		auto h=binderHint(from); if(h.name.length) hint(to,h.name,h.refinement);
		return to;
	}
	TypeId type(BoundTerm t){ return types[node(t).type]; }
	Scope context(BoundTerm t){ return Scope(this,node(t).context); }
	BoundTerm at(uint id){ enforce(id<nodes.length,"invalid binding index"); return BoundTerm(this,id); }
	private BoundTerm intern(BoundNode n){
		auto id=nodeIds.get(n,uint.max); if(id!=uint.max) return at(id);
		enforce(nodes.length<1_000_000,"binding arena limit exceeded");
		id=cast(uint)nodes.length; nodes~=n; nodeIds.set(n,id); return at(id);
	}
	uint depth(Scope s){ check(s); return contexts[s.index].length; }
	BoundTerm global(Scope s,TypeId t,uint index){
		check(s); return intern(BoundNode(BoundOp.global,s.index,typeId(t),uint.max,uint.max,index));
	}
	BoundTerm typeValue(Scope s,TypeId t){
		check(s); return intern(BoundNode(BoundOp.typeValue,s.index,typeId(pool.primitive(TypeKind.type_)),uint.max,uint.max,typeId(t)));
	}
	TypeId typeDenoted(BoundTerm t){ enforce(node(t).op==BoundOp.typeValue,"a known type is required"); return types[node(t).data]; }
	BoundTerm typeEq(BoundTerm x,BoundTerm y){
		enforce(type(x)==pool.primitive(TypeKind.type_)&&type(y)==type(x)&&context(x)==context(y),"type equality requires types");
		return intern(BoundNode(BoundOp.typeEq,node(x).context,typeId(scalarType(Sort.boolean)),x.id,y.id));
	}
	BoundTerm equal(BoundTerm x,BoundTerm y){
		enforce(type(x)==type(y)&&context(x)==context(y),"equality requires matching types");
		return intern(BoundNode(BoundOp.equal,node(x).context,typeId(scalarType(Sort.boolean)),x.id,y.id));
	}
	BoundTerm bottom(Scope s,TypeId t){ check(s); return intern(BoundNode(BoundOp.bottom,s.index,typeId(t))); }
	BoundTerm tuple(Scope ctx,BoundTerm[] elements,TypeId expected=TypeId.init){
		check(ctx); enforce(elements.length<=256,"aggregate literal size limit exceeded"); TypeId[] fields;
		foreach(e;elements){ enforce(context(e)==ctx,"tuple context mismatch"); fields~=type(e); }
		auto ty=expected==TypeId.init?pool.tuple(fields):expected,v=pool.view(ty);
		enforce(v.kind==TypeKind.unit||v.kind==TypeKind.tuple||v.kind==TypeKind.vector,"expected a tuple or vector type");
		if(v.kind==TypeKind.unit){ enforce(!elements.length,"unit has no elements"); return intern(BoundNode(BoundOp.unit,ctx.index,typeId(ty))); }
		if(v.kind==TypeKind.vector){
			enforce(v.dimension.constant&&v.length==elements.length,"vector literal dimension mismatch");
			foreach(f;fields) enforce(f==v.fields[0],"vector element type mismatch");
			if(!elements.length) return intern(BoundNode(BoundOp.vectorNil,ctx.index,typeId(ty)));
			auto tail=tuple(ctx,elements[1..$],pool.vector(v.fields[0],v.length-1));
			return intern(BoundNode(BoundOp.vectorCons,ctx.index,typeId(ty),elements[0].id,tail.id));
		}
		enforce(fields==v.fields,"tuple element type mismatch");
		auto tail=tuple(ctx,elements[1..$]);
		return intern(BoundNode(BoundOp.pair,ctx.index,typeId(ty),elements[0].id,tail.id));
	}
	BoundTerm get(BoundTerm value,BoundTerm index){
		auto n=node(value),v=pool.view(type(value));
		enforce(context(value)==context(index)&&type(index)==scalarType(Sort.natural),"index must have type ℕ");
		if(v.kind==TypeKind.tuple){
			auto i=node(index); enforce(i.op==BoundOp.scalar&&arena.isNumber(arena.at(i.data)),"heterogeneous tuple indices must be literals");
			auto number=arena.number(arena.at(i.data)); enforce(number.re.small&&number.re.integer>=0&&number.re.numerator<v.fields.length,"tuple index out of range");
			auto k=cast(uint)number.re.integer;
			if(!k) return intern(BoundNode(BoundOp.first,n.context,typeId(v.fields[0]),value.id));
			auto tail=intern(BoundNode(BoundOp.rest,n.context,typeId(pool.tuple(v.fields[1..$])),value.id));
			return get(tail,scalar(context(index),arena.natural_(k-1)));
		}
		enforce(v.kind==TypeKind.vector,"indexing requires a tuple or vector");
		return intern(BoundNode(BoundOp.get,n.context,typeId(v.fields[0]),value.id,index.id));
	}
	private Sort elementSort(TypeId t){
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(t==scalarType(s)) return s;
		throw new Exception("numeric scalar elements required");
	}
	BoundTerm tensor(TensorOp op,BoundTerm x,BoundTerm y){
		auto a=node(x),v=pool.view(type(x)),w=pool.view(type(y)); TypeId output;
		enforce(context(x)==context(y)&&v.kind==TypeKind.vector,"tensor operation requires vectors");
		if(op==TensorOp.add||op==TensorOp.mul){
			enforce(type(x)==type(y),"elementwise shape or type mismatch");
			elementSort(typeLeaf(type(x))); output=type(x);
		}else if(op==TensorOp.dot){
			enforce(type(x)==type(y),"inner product shape or type mismatch"); elementSort(v.fields[0]); output=v.fields[0];
		}else{
			auto row=pool.view(v.fields[0]); enforce(row.kind==TypeKind.vector,"matrix operation requires a matrix"); elementSort(row.fields[0]);
			if(op==TensorOp.power){
				enforce(v.dimension.key==row.dimension.key&&type(y)==scalarType(Sort.natural),"matrix powers require a square matrix and a natural exponent"); output=type(x);
			}else{
				enforce(w.kind==TypeKind.vector&&row.dimension.key==w.dimension.key,"matrix multiplication dimension mismatch");
				if(op==TensorOp.matvec){ enforce(row.fields[0]==w.fields[0],"matrix/vector element type mismatch"); output=pool.vector(row.fields[0],v.dimension); }
				else{ auto other=pool.view(w.fields[0]); enforce(other.kind==TypeKind.vector&&other.fields[0]==row.fields[0],"matrix element type mismatch"); output=pool.vector(pool.vector(row.fields[0],other.dimension),v.dimension); }
			}
		}
		return intern(BoundNode(BoundOp.tensor,a.context,typeId(output),x.id,y.id,cast(uint)op));
	}
	private TypeId typeLeaf(TypeId t){ auto v=pool.view(t); return v.kind==TypeKind.vector?typeLeaf(v.fields[0]):t; }
	private bool concreteType(TypeId t){
		auto v=pool.view(t); if(v.dimension !is null&&!v.dimension.constant) return false;
		foreach(f;v.fields) if(!concreteType(f)) return false; return true;
	}
	private bool literalData(BoundTerm t){
		auto n=node(t);
		if(n.op==BoundOp.unit||n.op==BoundOp.vectorNil) return true;
		if(n.op==BoundOp.scalar){
			bool total(Term t){
				auto q=arena.view(t); if(!q.arity) return true;
				return q.op==Op.builtin&&q.value>=Builtin.castNZ&&q.value<=Builtin.castRC&&total(arena.viewChild(t,0));
			}
			return total(arena.at(n.data));
		}
		return (n.op==BoundOp.pair||n.op==BoundOp.vectorCons)&&literalData(at(n.a))&&literalData(at(n.b));
	}
	private BoundTerm tensorEval(BoundTerm t){
		auto n=node(t); if(n.a==uint.max||!literalData(at(n.a))) return BoundTerm.init;
		BoundTerm entry(BoundTerm x,ulong i){ while(i--){ x=at(node(x).b); } return at(node(x).a); }
		if(n.op==BoundOp.first) return at(nodes[n.a].a);
		if(n.op==BoundOp.rest) return at(nodes[n.a].b);
		if(n.op==BoundOp.get&&nodes[n.b].op==BoundOp.scalar&&arena.isNumber(arena.at(nodes[n.b].data))){
			auto i=arena.number(arena.at(nodes[n.b].data)).re,v=pool.view(type(at(n.a)));
			if(!i.small||i.integer>=v.length) return bottom(context(t),type(t));
			return entry(at(n.a),cast(ulong)i.integer);
		}
		if(n.op!=BoundOp.tensor||!literalData(at(n.b))) return BoundTerm.init;
		auto x=at(n.a),y=at(n.b),v=pool.view(type(x)),op=cast(TensorOp)n.data;
		if(!v.dimension.constant||v.length>32) return BoundTerm.init;
		auto ctx=context(t),leaf=typeLeaf(type(x));
		BoundTerm scalarOp(TensorOp op,BoundTerm a,BoundTerm b){
			if(pool.view(type(a)).kind==TypeKind.vector) return tensor(op,a,b);
			auto prototype=scalarOperator(type(a),op);
			return primitive(prototype,[a,b]);
		}
		BoundTerm dot(BoundTerm[] a,BoundTerm[] b,bool dual){
			auto s=scalar(ctx,arena.number(Number(0),elementSort(leaf)));
			foreach_reverse(i;0..a.length){
				auto term=a[i];
				if(dual&&leaf==scalarType(Sort.complex)) term=primitive(arena.conj(arena.variable(Sort.complex,0)),[term]);
				s=scalarOp(TensorOp.add,scalarOp(TensorOp.mul,term,b[i]),s);
			}
			return s;
		}
		BoundTerm[] elements;
		if(op==TensorOp.add||op==TensorOp.mul){
			foreach(i;0..v.length) elements~=scalarOp(op,entry(x,i),entry(y,i)); return tuple(ctx,elements,type(t));
		}
		if(op==TensorOp.dot){
			BoundTerm[] a,b; foreach(i;0..v.length){ a~=entry(x,i); b~=entry(y,i); } return dot(a,b,true);
		}
		auto row=pool.view(v.fields[0]); if(!row.dimension.constant||row.length>32) return BoundTerm.init;
		if(op==TensorOp.power){
			if(nodes[n.b].op!=BoundOp.scalar||!arena.isNumber(arena.at(nodes[n.b].data))) return BoundTerm.init;
			auto exponent=arena.number(arena.at(nodes[n.b].data)).re; if(!exponent.small||exponent.integer>16) return BoundTerm.init;
			if(exponent.integer) return tensor(TensorOp.matmul,x,tensor(TensorOp.power,x,scalar(ctx,arena.natural_(cast(ulong)exponent.integer-1))));
			foreach(i;0..v.length){
				BoundTerm[] cells; foreach(j;0..v.length) cells~=scalar(ctx,arena.number(Number(i==j?1:0),elementSort(leaf)));
				elements~=tuple(ctx,cells,v.fields[0]);
			}
			return tuple(ctx,elements,type(x));
		}
		auto w=pool.view(type(y));
		auto columns=op==TensorOp.matmul?pool.view(w.fields[0]).length:1;
		if(columns>32) return BoundTerm.init;
		foreach(i;0..v.length){
			BoundTerm[] cells;
			foreach(j;0..columns){
				BoundTerm[] a,b;
				foreach(k;0..row.length){ a~=entry(entry(x,i),k); b~=op==TensorOp.matmul?entry(entry(y,k),j):entry(y,k); }
				cells~=dot(a,b,false);
			}
			elements~=op==TensorOp.matmul?tuple(ctx,cells,pool.view(type(t)).fields[0]):cells[0];
		}
		return tuple(ctx,elements,type(t));
	}
	private bool depends(BoundTerm t,uint index){
		auto n=node(t); if(n.op==BoundOp.variable) return n.data==index;
		if(n.op==BoundOp.lambda||n.op==BoundOp.set||n.op==BoundOp.fixed) ++index;
		return n.a!=uint.max&&depends(at(n.a),index)||n.b!=uint.max&&depends(at(n.b),index);
	}
	private void checkProgram(BoundTerm t){
		if(!depends(t,1)) return;
		auto n=node(t);
		if(n.op==BoundOp.primitive||n.op==BoundOp.guard||n.op==BoundOp.sequence){
			checkProgram(at(n.a)); if(n.b!=uint.max) checkProgram(at(n.b)); return;
		}
		if(n.op==BoundOp.apply){
			auto f=nodes[n.a];
			enforce(f.op==BoundOp.variable&&f.data==1,"unsupported higher-order recursion");
			checkProgram(at(n.b)); return;
		}
		throw new Exception("recursive definitions cannot inspect definedness or use higher-order recursion yet");
	}
	BoundTerm fixed(BoundTerm body){
		auto n=node(body),v=pool.view(type(body));
		enforce(n.op==BoundOp.lambda&&n.context!=0&&contexts[n.context].type==n.type,"fixed-point body must be a lambda of the declared type");
		foreach(t;v.fields){ auto k=pool.view(t).kind; enforce(k>=TypeKind.boolean&&k<=TypeKind.complex,"fixed points currently require scalar arguments and results"); }
		checkProgram(at(n.a)); return intern(BoundNode(BoundOp.fixed,contexts[n.context].parent,n.type,body.id));
	}
	BoundTerm variable(Scope s,uint index){
		check(s); auto ctx=s.index;
		foreach(i;0..index){ enforce(ctx!=0,"unbound variable"); ctx=contexts[ctx].parent; }
		enforce(ctx!=0,"unbound variable");
		return intern(BoundNode(BoundOp.variable,s.index,contexts[ctx].type,uint.max,uint.max,index));
	}
	BoundTerm scalar(Scope s,Term value){
		check(s); auto ty=typeId(scalarType(arena.sort(value)));
		return intern(BoundNode(BoundOp.scalar,s.index,ty,uint.max,uint.max,value.id));
	}
	BoundTerm primitive(Term prototype,BoundTerm[] args){
		auto n=arena.view(prototype);
		enforce(n.arity>0&&n.arity<=2&&args.length==n.arity,"primitive arity mismatch");
		auto ctx=context(args[0]);
		foreach(i,x;args){
			enforce(context(x)==ctx,"primitive context mismatch");
			enforce(type(x)==scalarType(arena.sort(arena.viewChild(prototype,cast(uint)i))),"primitive type mismatch");
		}
		Term[] placeholders;
		foreach(i;0..n.arity){
			auto sort=arena.sort(arena.viewChild(prototype,i));
			placeholders~=sort==Sort.boolean?arena.boolean(false):arena.number(Number(0),sort);
		}
		prototype=arena.viewRebuild(prototype,placeholders,true);
		return intern(BoundNode(BoundOp.primitive,ctx.index,typeId(scalarType(n.sort)),
			args[0].id,args.length==2?args[1].id:uint.max,prototype.id));
	}
	BoundTerm lambda(BoundTerm body){
		auto n=node(body); enforce(n.context!=0,"lambda requires a bound variable");
		auto ctx=contexts[n.context],ty=typeId(pool.function_(types[ctx.type],types[n.type]));
		return intern(BoundNode(BoundOp.lambda,ctx.parent,ty,body.id));
	}
	BoundTerm apply(BoundTerm function_,BoundTerm argument){
		auto f=node(function_),x=node(argument),ty=pool.view(types[f.type]);
		enforce(f.context==x.context,"application context mismatch");
		enforce(ty.kind==TypeKind.function_&&ty.fields[0]==types[x.type],"application type mismatch");
		return intern(BoundNode(BoundOp.apply,f.context,typeId(ty.fields[1]),function_.id,argument.id));
	}
	BoundTerm sequence(BoundTerm x,BoundTerm y){
		auto a=node(x),b=node(y); enforce(a.context==b.context,"sequence context mismatch");
		return intern(BoundNode(BoundOp.sequence,b.context,b.type,x.id,y.id));
	}
	BoundTerm set(BoundTerm predicate){
		auto n=node(predicate); enforce(n.context!=0&&type(predicate)==scalarType(Sort.boolean),"set requires a bound Boolean predicate");
		auto ctx=contexts[n.context];
		return intern(BoundNode(BoundOp.set,ctx.parent,typeId(pool.set(types[ctx.type])),predicate.id));
	}
	BoundTerm member(BoundTerm set_,BoundTerm x){
		auto n=node(set_),v=pool.view(type(set_));
		enforce(v.kind==TypeKind.set&&v.fields[0]==type(x),"membership type mismatch");
		enforce(context(set_)==context(x),"membership context mismatch");
		return intern(BoundNode(BoundOp.member,n.context,typeId(scalarType(Sort.boolean)),set_.id,x.id));
	}
	BoundTerm subset(BoundTerm x,BoundTerm y){
		auto n=node(x); enforce(pool.view(type(x)).kind==TypeKind.set&&type(x)==type(y),"inclusion requires sets of the same type");
		enforce(context(x)==context(y),"inclusion context mismatch");
		return intern(BoundNode(BoundOp.subset,n.context,typeId(scalarType(Sort.boolean)),x.id,y.id));
	}
	BoundTerm domain(BoundTerm f){
		auto n=node(f),v=pool.view(type(f)); enforce(v.kind==TypeKind.function_,"domain requires a function");
		return intern(BoundNode(BoundOp.domain,n.context,typeId(pool.set(v.fields[0])),f.id));
	}
	BoundTerm defined(BoundTerm x){
		auto n=node(x); return intern(BoundNode(BoundOp.defined,n.context,typeId(scalarType(Sort.boolean)),x.id));
	}
	BoundTerm holds(BoundTerm p){
		enforce(type(p)==scalarType(Sort.boolean),"holds requires Bool");
		auto n=node(p); return intern(BoundNode(BoundOp.holds,n.context,n.type,p.id));
	}
	BoundTerm guard(BoundTerm p,BoundTerm x){
		enforce(type(p)==scalarType(Sort.boolean)&&context(p)==context(x),"guard requires Bool in the same scope");
		auto n=node(x); return intern(BoundNode(BoundOp.guard,n.context,n.type,p.id,x.id));
	}
	private BoundTerm rebuild(BoundTerm t,Scope target,BoundTerm[] args){
		auto n=node(t);
		final switch(n.op){
			case BoundOp.unit,BoundOp.vectorNil:return tuple(target,[],types[n.type]);
			case BoundOp.vectorCons,BoundOp.pair:return intern(BoundNode(n.op,target.index,n.type,args[0].id,args[1].id));
			case BoundOp.first,BoundOp.rest:return intern(BoundNode(n.op,target.index,n.type,args[0].id));
			case BoundOp.get:return get(args[0],args[1]);
			case BoundOp.tensor:return tensor(cast(TensorOp)n.data,args[0],args[1]);
			case BoundOp.scalar:return scalar(target,arena.at(n.data));
			case BoundOp.global:return global(target,types[n.type],n.data);
			case BoundOp.variable:assert(0,"variable requires substitution");
			case BoundOp.primitive:return primitive(arena.at(n.data),args);
			case BoundOp.lambda:return inheritHint(t,lambda(args[0]));
			case BoundOp.set:return inheritHint(t,set(args[0]));
			case BoundOp.member:return member(args[0],args[1]);
			case BoundOp.subset:return subset(args[0],args[1]);
			case BoundOp.typeEq:return typeEq(args[0],args[1]);
			case BoundOp.equal:return equal(args[0],args[1]);
			case BoundOp.typeValue:return typeValue(target,types[n.data]);
			case BoundOp.bottom:return bottom(target,types[n.type]);
			case BoundOp.fixed:return inheritHint(t,fixed(args[0]));
			case BoundOp.domain:return domain(args[0]);
			case BoundOp.defined:return defined(args[0]);
			case BoundOp.holds:return holds(args[0]);
			case BoundOp.guard:return guard(args[0],args[1]);
			case BoundOp.apply:return apply(args[0],args[1]);
			case BoundOp.sequence:return sequence(args[0],args[1]);
		}
	}
	BoundTerm rename(BoundTerm term,Scope target,uint[] indices){
		check(term); check(target); auto ctx=node(term).context;
		enforce(indices.length==contexts[ctx].length,"renaming arity mismatch");
		foreach(i,index;indices){
			enforce(type(variable(target,index))==type(variable(context(term),cast(uint)i)),"renaming type mismatch");
		}
		Table!(uint,uint) memo;
		BoundTerm visit(BoundTerm t){
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return at(old);
			auto n=node(t); BoundTerm result;
			if(n.op==BoundOp.variable) result=variable(target,indices[n.data]);
			else if(n.op==BoundOp.lambda||n.op==BoundOp.set||n.op==BoundOp.fixed){
				uint[] lifted=[0]; foreach(index;indices) lifted~=index+1;
				auto body=rename(at(n.a),push(target,types[contexts[nodes[n.a].context].type]),lifted);
				result=inheritHint(t,n.op==BoundOp.lambda?lambda(body):n.op==BoundOp.set?set(body):fixed(body));
			}else{
				BoundTerm[] children;
				if(n.a!=uint.max) children~=visit(at(n.a));
				if(n.b!=uint.max) children~=visit(at(n.b));
				result=rebuild(t,target,children);
			}
			memo.set(t.id,result.id); return result;
		}
		return visit(term);
	}
	BoundTerm substitute(BoundTerm term,Scope target,BoundTerm[] values){
		check(term); check(target); auto ctx=node(term).context;
		enforce(values.length==contexts[ctx].length,"substitution arity mismatch");
		foreach(i,value;values){
			enforce(context(value)==target&&type(value)==type(variable(context(term),cast(uint)i)),"substitution type mismatch");
		}
		Table!(uint,uint) memo;
		BoundTerm visit(BoundTerm t){
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return at(old);
			auto n=node(t); BoundTerm result;
			if(n.op==BoundOp.variable) result=values[n.data];
			else if(n.op==BoundOp.lambda||n.op==BoundOp.set||n.op==BoundOp.fixed){
				auto inner=push(target,types[contexts[nodes[n.a].context].type]);
				BoundTerm[] lifted=[variable(inner,0)]; uint[] indices;
				foreach(i;0..contexts[target.index].length) indices~=i+1;
				foreach(value;values) lifted~=rename(value,inner,indices);
				auto body=substitute(at(n.a),inner,lifted); result=inheritHint(t,n.op==BoundOp.lambda?lambda(body):n.op==BoundOp.set?set(body):fixed(body));
			}else{
				BoundTerm[] children;
				if(n.a!=uint.max) children~=visit(at(n.a));
				if(n.b!=uint.max) children~=visit(at(n.b));
				result=rebuild(t,target,children);
			}
			memo.set(t.id,result.id); return result;
		}
		return visit(term);
	}
	BoundTerm beta(BoundTerm body,BoundTerm argument){
		auto target=context(argument); enforce(context(body)==push(target,type(argument)),"beta context mismatch");
		BoundTerm[] values=[argument];
		foreach(i;0..contexts[target.index].length) values~=variable(target,i);
		return sequence(argument,substitute(body,target,values));
	}
	private bool totalScalar(BoundTerm t){
		auto n=node(t); if(n.op!=BoundOp.scalar) return false;
		auto v=arena.node(arena.at(n.data));
		return v.arity==0;
	}
	private bool closedScalar(BoundTerm t){
		auto n=node(t); if(n.op!=BoundOp.scalar) return false;
		foreach(id;arena.viewPostorder(arena.at(n.data))) if(arena.view(arena.at(id)).op==Op.variable) return false;
		return true;
	}
	private Term scalarBody(BoundTerm term,Term argument){
		auto n=node(term);
		if(n.op==BoundOp.scalar) return arena.at(n.data);
		if(n.op==BoundOp.variable) return n.data==0?argument:Term.init;
		if(n.op!=BoundOp.primitive) return Term.init;
		auto x=scalarBody(at(n.a),argument); if(x==Term.init) return Term.init;
		Term[] args=[x];
		if(n.b!=uint.max){ auto y=scalarBody(at(n.b),argument); if(y==Term.init) return Term.init; args~=y; }
		return arena.viewRebuild(arena.at(n.data),args,true);
	}
	private BoundTerm restoreBody(Term t,Scope ctx,Term argument){
		if(t==argument) return variable(ctx,0);
		auto n=arena.view(t); if(!n.arity) return scalar(ctx,t);
		BoundTerm[] args; bool plain=true;
		foreach(i;0..n.arity){ auto child=restoreBody(arena.viewChild(t,i),ctx,argument); args~=child; plain&=node(child).op==BoundOp.scalar; }
		return plain?scalar(ctx,t):primitive(t,args);
	}
	private BoundTerm solveRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),body=node(at(n.a)),ty=pool.view(type(t));
		if(ty.fields[0]!=scalarType(Sort.natural)||ty.fields[1]!=scalarType(Sort.natural)) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool unary(uint id,Op op){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==op; }
		bool variableAt(uint id,uint index){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==index; }
		bool previous(uint id){
			auto q=nodes[id]; if(q.op!=BoundOp.apply||!variableAt(q.a,1)||!call(q.b,Builtin.subN)) return false;
			auto arg=nodes[q.b],one=nodes[arg.b];
			return variableAt(arg.a,0)&&one.op==BoundOp.scalar&&arena.isNumber(arena.at(one.data))&&arena.number(arena.at(one.data)).one;
		}
		if(!call(body.a,Builtin.addN)) return BoundTerm.init;
		auto sum=nodes[body.a]; if(!unary(sum.a,Op.mask)||!unary(sum.b,Op.mask)) return BoundTerm.init;
		auto yes=nodes[sum.a],no=nodes[sum.b],p=nodes[yes.a];
		if(!unary(yes.a,Op.not_)||!unary(no.a,Op.not_)||nodes[no.a].a!=yes.a) return BoundTerm.init;
		if(!call(p.a,Builtin.nonzeroZ)||!call(nodes[p.a].a,Builtin.castNZ)||!variableAt(nodes[nodes[p.a].a].a,0)) return BoundTerm.init;
		if(!totalScalar(at(yes.b))||!call(no.b,Builtin.addN)&&!call(no.b,Builtin.mulN)) return BoundTerm.init;
		if(call(no.b,Builtin.addN)){
			auto branch=nodes[no.b],down=nodes[branch.a],up=nodes[branch.b];
			if(unary(branch.a,Op.mask)&&unary(branch.b,Op.mask)&&call(down.a,Builtin.leN)&&
				unary(up.a,Op.not_)&&nodes[up.a].a==down.a&&previous(down.b)){
				auto condition=nodes[down.a],forward=nodes[up.b];
				if(variableAt(condition.a,0)&&totalScalar(at(condition.b))&&forward.op==BoundOp.apply&&
					variableAt(forward.a,1)&&call(forward.b,Builtin.addN)){
					auto successor=nodes[forward.b],one=nodes[successor.b];
					if(variableAt(successor.a,0)&&one.op==BoundOp.scalar&&arena.isNumber(arena.at(one.data))&&arena.number(arena.at(one.data)).one){
						auto inner=push(context(t),ty.fields[0]);
						auto predicate=primitive(arena.at(condition.data),[variable(inner,0),scalar(inner,arena.at(nodes[condition.b].data))]);
						auto output=inheritHint(at(n.a),lambda(guard(predicate,scalar(inner,arena.at(nodes[yes.b].data)))));
						solution=RecurrenceSolution(t.id,output.id,yes.b,condition.b,Law.init,Law.init,false,true); return output;
					}
				}
			}
		}
		auto step=nodes[no.b]; bool left=previous(step.b); auto delta=left?step.a:step.b;
		if(!previous(left?step.b:step.a)||!totalScalar(at(delta))) return BoundTerm.init;
		bool mul=call(no.b,Builtin.mulN);
		auto law=mul?(left?Law.natural_recurrence_mul_left_step:Law.natural_recurrence_mul_step):
			(left?Law.natural_recurrence_add_left_step:Law.natural_recurrence_add_step);
		uint index;
		foreach(id;0..arena.length){ auto q=arena.node(arena.at(cast(uint)id)); if(q.op==Op.variable){ enforce(q.value<uint.max-1,"scalar variable limit exceeded"); if(q.value>=index) index=cast(uint)q.value+1; } }
		auto argument=arena.variable(Sort.natural,index),instance=instantiate(arena,law,[arena.at(nodes[yes.b].data),arena.at(nodes[delta].data),argument],true);
		auto candidate=arena.viewChild(instance.before,left?1:0),inner=push(context(t),ty.fields[0]);
		auto output=inheritHint(at(n.a),lambda(restoreBody(candidate,inner,argument)));
		solution=RecurrenceSolution(t.id,output.id,yes.b,delta,law,mul?Law.natural_recurrence_mul_base:Law.natural_recurrence_add_base,left);
		return output;
	}
	BindingResult normalize(BoundTerm term,uint budget=4096,bool domains=false){
		check(term); uint steps,fixedSteps; bool exhausted; BindingStep[] proofs; ScalarDomain[] scalarDomains; RecurrenceSolution[] solutions;
		struct Result{ uint output,proof; }
		Table!(uint,Result) memo;
		Table!(uint,bool) active;
		uint emit(BindingRule rule,uint from,uint to,uint left=uint.max,uint right=uint.max,uint extra=uint.max){
			enforce(proofs.length<1_000_000,"binding proof limit exceeded");
			proofs~=BindingStep(rule,from,to,left,right,extra); return cast(uint)proofs.length-1;
		}
		BoundTerm pointwise(BoundTerm binder,out uint extra){
			auto body=at(node(binder).a),ctx=context(body),param=type(variable(ctx,0)); Sort sort; bool scalarParam;
			foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean])
				if(param==scalarType(s)){ sort=s; scalarParam=true; break; }
			if(!scalarParam) return BoundTerm.init;
			uint index;
			foreach(id;0..arena.length){
				auto n=arena.node(arena.at(cast(uint)id));
				if(n.op==Op.variable){ enforce(n.value<uint.max-1,"scalar variable limit exceeded"); if(n.value>=index) index=cast(uint)n.value+1; }
			}
			auto argument=arena.variable(sort,index);
			BoundTerm rewrite(BoundTerm t,uint[] path){
				auto n=node(t),mode=n.op==BoundOp.defined||n.op==BoundOp.holds?n.op:BoundOp.scalar;
				auto source=scalarBody(mode==BoundOp.scalar?t:at(n.a),argument);
				if(source!=Term.init){
					ScalarResult value; BoundTerm simplified;
					if(mode==BoundOp.scalar){
						if(arena.isNumber(source)) return BoundTerm.init;
						value=simplify(arena,source,Options(DensityMode.preserve,true)); exhausted|=value.exhausted;
						if(arena.castTo(value.output,arena.sort(source))==source) return BoundTerm.init;
						simplified=restoreBody(arena.castTo(value.output,arena.sort(source)),ctx,argument);
						if(simplified==t) return BoundTerm.init;
					}
					auto d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true)); exhausted|=d.exhausted;
					extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d,value,index,sort,path,mode);
					if(mode==BoundOp.defined) return restoreBody(d.output,ctx,argument);
					if(mode==BoundOp.holds) return restoreBody(arena.and_(d.output,source),ctx,argument);
					return d.output==arena.boolean(true)?simplified:guard(restoreBody(d.output,ctx,argument),simplified);
				}
				if(n.op==BoundOp.guard||n.op==BoundOp.primitive||n.op==BoundOp.defined||n.op==BoundOp.holds){
					auto x=rewrite(at(n.a),path~0u);
					if(x!=BoundTerm.init) return rebuild(t,ctx,n.b==uint.max?[x]:[x,at(n.b)]);
					if(n.b!=uint.max){ auto y=rewrite(at(n.b),path~1u); if(y!=BoundTerm.init) return rebuild(t,ctx,[at(n.a),y]); }
				}
				return BoundTerm.init;
			}
			auto output=rewrite(body,[]);
			return output==BoundTerm.init?output:inheritHint(binder,node(binder).op==BoundOp.lambda?lambda(output):set(output));
		}
		Result visit(BoundTerm t,uint depth){
			enforce(depth<512,"binding normalization depth exceeded");
			auto old=memo.get(t.id,Result(uint.max,uint.max)); if(old.output!=uint.max) return old;
			if(active.get(t.id,false)){ exhausted=true; return Result(t.id,emit(BindingRule.refl,t.id,t.id)); }
			active.set(t.id,true);
			auto n=node(t); Result result;
			if(n.a==uint.max) result=Result(t.id,emit(BindingRule.refl,t.id,t.id));
			else{
				auto x=n.op==BoundOp.fixed?Result(n.a,emit(BindingRule.refl,n.a,n.a)):visit(at(n.a),depth+1); BoundTerm[] args=[at(x.output)]; uint y=uint.max;
				if(n.b!=uint.max){
					bool skip; auto left=nodes[x.output];
					if(domains&&left.op==BoundOp.scalar){
						auto v=arena.view(arena.at(left.data));
						if(v.op==Op.boolLit){
							auto op=n.op==BoundOp.primitive?arena.view(arena.at(n.data)).op:Op.variable;
							skip=!v.value&&(n.op==BoundOp.guard||op==Op.mask||op==Op.and_)||v.value&&op==Op.or_;
						}
					}
					auto r=skip?Result(n.b,emit(BindingRule.refl,n.b,n.b)):visit(at(n.b),depth+1); args~=at(r.output); y=r.proof;
				}
				auto rebuilt=rebuild(t,context(t),args);
				result=Result(rebuilt.id,emit(BindingRule.congr,t.id,rebuilt.id,x.proof,y));
			}
			auto current=node(at(result.output)); BoundTerm next; BindingRule rule; uint extra=uint.max;
			auto ctx=context(at(result.output));
			bool isTrue(uint id,bool value){
				auto n=nodes[id]; if(n.op!=BoundOp.scalar) return false;
				auto v=arena.view(arena.at(n.data)); return v.op==Op.boolLit&&v.value==value;
			}
			bool constantSet(uint id,bool value){ auto n=nodes[id]; return n.op==BoundOp.set&&isTrue(n.a,value); }
			BoundTerm both(BoundTerm x,BoundTerm y){ return primitive(arena.and_(arena.boolean(true),arena.boolean(true)),[x,y]); }
			if(domains&&current.op==BoundOp.apply&&nodes[current.b].op==BoundOp.bottom){
				next=bottom(ctx,type(at(result.output))); rule=BindingRule.appBottom;
			}else if(current.op==BoundOp.apply&&nodes[current.a].op==BoundOp.lambda){
				if(steps<budget){ next=beta(at(nodes[current.a].a),at(current.b)); rule=BindingRule.beta; }
				else exhausted=true;
			}else if(domains&&current.op==BoundOp.apply&&nodes[current.a].op==BoundOp.fixed&&nodes[current.b].op==BoundOp.scalar){
				if(closedScalar(at(current.b))){
					auto source=arena.at(nodes[current.b].data),d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true)); exhausted|=d.exhausted;
					if(d.output==arena.boolean(false)){
						extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d);
						next=bottom(ctx,type(at(result.output))); rule=BindingRule.appScalarUndefined;
					}else if(steps<budget&&depth<128&&fixedSteps<64){
						++fixedSteps; next=apply(apply(lambda(at(nodes[current.a].a)),at(current.a)),at(current.b)); rule=BindingRule.fixedApp;
					}else exhausted=true;
				}
			}else if(current.op==BoundOp.sequence){
				if(domains&&nodes[current.a].op==BoundOp.bottom){ next=bottom(ctx,type(at(current.b))); rule=BindingRule.shortCircuit; }
				else if(current.a==current.b){ next=at(current.b); rule=BindingRule.seqSelf; }
				else if(totalScalar(at(current.a))){ next=at(current.b); rule=BindingRule.seqScalar; }
				else if(nodes[current.a].op==BoundOp.lambda){ next=at(current.b); rule=BindingRule.seqLam; }
				else if(domains){
					auto op=nodes[current.a].op;
					if(op==BoundOp.typeValue||op==BoundOp.set||op==BoundOp.global||op==BoundOp.domain||op==BoundOp.defined||op==BoundOp.holds){ next=at(current.b); rule=BindingRule.seqTotal; }
					else{ next=guard(defined(at(current.a)),at(current.b)); rule=BindingRule.seqGuard; }
				}
				if(next!=BoundTerm.init&&steps>=budget){ next=BoundTerm.init; exhausted=true; }
			}
			if(domains&&next==BoundTerm.init){
				if(current.op==BoundOp.get&&nodes[current.b].op==BoundOp.scalar&&!totalScalar(at(current.b))){
					auto source=arena.at(nodes[current.b].data),d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true)); exhausted|=d.exhausted;
					if(d.output==arena.boolean(false)){
						extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d);
						next=bottom(ctx,type(at(result.output))); rule=BindingRule.getScalarUndefined;
					}
				}
				if(current.op==BoundOp.get&&(nodes[current.a].op==BoundOp.bottom||nodes[current.b].op==BoundOp.bottom)){
					next=bottom(ctx,type(at(result.output))); rule=BindingRule.getBottom;
				}else if(next==BoundTerm.init&&(current.op==BoundOp.tensor||current.op==BoundOp.get||current.op==BoundOp.first||current.op==BoundOp.rest)){
					next=tensorEval(at(result.output)); if(next!=BoundTerm.init) rule=current.op==BoundOp.tensor&&current.data==TensorOp.power&&node(next).op==BoundOp.tensor?BindingRule.tensorPower:BindingRule.tensorEval;
				}
				if(next==BoundTerm.init&&current.op==BoundOp.fixed){
					auto body=at(current.a),v=pool.view(type(body)),inner=push(ctx,v.fields[0]);
					if(!depends(body,0)){
						BoundTerm[] values=[lambda(bottom(inner,v.fields[1]))];
						foreach(i;0..this.depth(ctx)) values~=variable(ctx,i);
						next=substitute(body,ctx,values); rule=BindingRule.fixedConstant;
					}else{
						auto b=node(at(node(body).a));
						if(b.op==BoundOp.apply&&nodes[b.a].op==BoundOp.variable&&nodes[b.a].data==1&&nodes[b.b].op==BoundOp.variable&&nodes[b.b].data==0){
							next=inheritHint(body,lambda(bottom(inner,v.fields[1]))); rule=BindingRule.fixedIdentity;
						}
					}
					if(next==BoundTerm.init){
						RecurrenceSolution solution; next=solveRecurrence(at(result.output),solution);
						if(next!=BoundTerm.init){ extra=cast(uint)solutions.length; solutions~=solution; rule=BindingRule.fixedRecurrence; }
					}
				}else if(current.op==BoundOp.guard&&isTrue(current.a,false)){
					next=bottom(ctx,type(at(current.b))); rule=BindingRule.shortCircuit;
				}else if(current.op==BoundOp.primitive&&nodes[current.a].op==BoundOp.bottom&&arena.view(arena.at(current.data)).op==Op.not_){
					next=bottom(ctx,scalarType(Sort.boolean)); rule=BindingRule.shortCircuit;
				}else if(current.op==BoundOp.primitive&&nodes[current.a].op==BoundOp.scalar){
					auto op=arena.view(arena.at(current.data)).op;
					if(isTrue(current.a,false)&&(op==Op.mask||op==Op.and_)){
						auto ty=arena.sort(arena.at(current.data));
						next=scalar(ctx,ty==Sort.boolean?arena.boolean(false):arena.number(Number(0),ty)); rule=BindingRule.shortCircuit;
					}else if(isTrue(current.a,true)&&op==Op.or_){ next=scalar(ctx,arena.boolean(true)); rule=BindingRule.shortCircuit; }
					else if(isTrue(current.a,true)&&(op==Op.mask||op==Op.and_)||isTrue(current.a,false)&&op==Op.or_){ next=at(current.b); rule=BindingRule.shortCircuit; }
				}
				if(next==BoundTerm.init){
					if(current.op==BoundOp.set&&nodes[current.a].op==BoundOp.guard){
						next=set(holds(at(current.a))); rule=BindingRule.setHolds;
					}else if((current.op==BoundOp.lambda||current.op==BoundOp.set)&&steps<budget){
						next=pointwise(at(result.output),extra); rule=BindingRule.pointwise;
					}else if(current.op==BoundOp.scalar&&steps<budget&&!arena.isNumber(arena.at(current.data))){
						auto source=arena.at(current.data),value=simplify(arena,source,Options(DensityMode.preserve,true));
						auto embedded=arena.castTo(value.output,arena.sort(source));
						if(embedded!=source){
							auto d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true));
							auto predicate=arena.view(d.output);
							if(predicate.op==Op.boolLit&&predicate.value){
								extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d,value);
								next=guard(scalar(ctx,d.output),scalar(ctx,embedded)); rule=BindingRule.scalarSimplify;
							}
						}
						exhausted|=value.exhausted;
					}else if(current.op==BoundOp.primitive&&nodes[current.a].op==BoundOp.scalar&&
						(current.b==uint.max||nodes[current.b].op==BoundOp.scalar)){
						Term[] args=[arena.at(nodes[current.a].data)]; if(current.b!=uint.max) args~=arena.at(nodes[current.b].data);
						next=scalar(ctx,arena.viewRebuild(arena.at(current.data),args,true)); rule=BindingRule.fold;
					}else if(current.op==BoundOp.domain&&nodes[current.a].op==BoundOp.lambda){
						next=inheritHint(at(current.a),set(defined(at(nodes[current.a].a)))); rule=BindingRule.domainLam;
					}else if(current.op==BoundOp.domain&&nodes[current.a].op==BoundOp.bottom){
						next=set(scalar(push(ctx,pool.view(types[current.type]).fields[0]),arena.boolean(false))); rule=BindingRule.domainBottom;
					}else if(current.op==BoundOp.domain&&nodes[current.a].op==BoundOp.guard&&isTrue(nodes[current.a].a,false)){
						next=set(scalar(push(ctx,pool.view(types[current.type]).fields[0]),arena.boolean(false))); rule=BindingRule.domainGuardFalse;
					}else if(current.op==BoundOp.typeEq){
						if(current.a==current.b){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.typeEqSelf; }
						else if(nodes[current.a].op==BoundOp.typeValue&&nodes[current.b].op==BoundOp.typeValue&&concreteType(typeDenoted(at(current.a)))&&concreteType(typeDenoted(at(current.b)))){
							next=scalar(ctx,arena.boolean(nodes[current.a].data==nodes[current.b].data)); rule=BindingRule.typeEqValues;
						}
					}else if(current.op==BoundOp.equal){
						if(nodes[current.a].op==BoundOp.bottom){ next=bottom(ctx,scalarType(Sort.boolean)); rule=BindingRule.equalBottomLeft; }
						else if(nodes[current.b].op==BoundOp.bottom){ next=bottom(ctx,scalarType(Sort.boolean)); rule=BindingRule.equalBottomRight; }
						else if(current.a==current.b){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.equalSelf; }
						else if(constantSet(current.a,true)&&constantSet(current.b,false)){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.equalUnivEmpty; }
						else if(constantSet(current.a,false)&&constantSet(current.b,true)){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.equalEmptyUniv; }
					}else if(current.op==BoundOp.subset){
						if(current.a==current.b){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.subsetRefl; }
						else if(constantSet(current.a,false)){ next=sequence(at(current.b),scalar(ctx,arena.boolean(true))); rule=BindingRule.subsetEmpty; }
						else if(constantSet(current.b,true)){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.subsetUniv; }
						else if(constantSet(current.a,true)&&constantSet(current.b,false)){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.subsetUnivEmpty; }
					}else if(current.op==BoundOp.member&&nodes[current.a].op==BoundOp.domain&&nodes[nodes[current.a].a].op==BoundOp.fixed&&closedScalar(at(current.b))){
						next=sequence(at(current.b),defined(apply(at(nodes[current.a].a),at(current.b)))); rule=BindingRule.memberDomain;
					}else if(current.op==BoundOp.member&&nodes[current.a].op==BoundOp.set){
						auto reduction=beta(at(nodes[current.a].a),at(current.b));
						next=sequence(at(current.b),holds(at(node(reduction).b))); rule=BindingRule.memberSet;
					}else if(current.op==BoundOp.guard&&isTrue(current.a,true)){
						next=at(current.b); rule=BindingRule.guardTrue;
					}else if(current.op==BoundOp.guard&&nodes[current.b].op==BoundOp.guard){
						next=guard(both(at(current.a),at(nodes[current.b].a)),at(nodes[current.b].b)); rule=BindingRule.guardAnd;
					}else if(current.op==BoundOp.holds&&nodes[current.a].op==BoundOp.guard){
						next=both(holds(at(nodes[current.a].a)),holds(at(nodes[current.a].b))); rule=BindingRule.holdsGuard;
					}else if(current.op==BoundOp.defined){
						auto child=nodes[current.a];
						if(child.op==BoundOp.pair||child.op==BoundOp.vectorCons){
							next=both(defined(at(child.a)),defined(at(child.b))); rule=BindingRule.tensorDefined;
						}else if(child.op==BoundOp.unit||child.op==BoundOp.vectorNil){ next=scalar(ctx,arena.boolean(true)); rule=BindingRule.tensorEval; }
						else if(child.op==BoundOp.bottom){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.shortCircuit; }
						else if(child.op==BoundOp.fixed){ next=scalar(ctx,arena.boolean(true)); rule=BindingRule.definedFixed; }
						else if(child.op==BoundOp.typeValue||child.op==BoundOp.lambda||child.op==BoundOp.set||child.op==BoundOp.global||child.op==BoundOp.domain||child.op==BoundOp.defined||child.op==BoundOp.holds){
							next=scalar(ctx,arena.boolean(true)); rule=BindingRule.definedTotal;
						}else if(child.op==BoundOp.guard&&isTrue(child.a,false)){
							next=scalar(ctx,arena.boolean(false)); rule=BindingRule.definedGuardFalse;
						}else if(child.op==BoundOp.guard){
							next=both(holds(at(child.a)),defined(at(child.b))); rule=BindingRule.definedGuard;
						}else if(child.op==BoundOp.member||child.op==BoundOp.subset||child.op==BoundOp.equal){
							next=both(defined(at(child.a)),defined(at(child.b))); rule=child.op==BoundOp.member?BindingRule.definedMember:child.op==BoundOp.subset?BindingRule.definedSubset:BindingRule.definedEqual;
						}else if(child.op==BoundOp.primitive&&arena.view(arena.at(child.data)).op==Op.not_){
							next=defined(at(child.a)); rule=BindingRule.definedNot;
						}else if(child.op==BoundOp.apply){
							next=holds(member(domain(at(child.a)),at(child.b))); rule=BindingRule.definedApp;
						}
					}
				}
				if(current.op==BoundOp.holds&&nodes[current.a].op==BoundOp.bottom){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.shortCircuit; }
				if((current.op==BoundOp.defined||current.op==BoundOp.holds)&&nodes[current.a].op==BoundOp.scalar&&steps<budget){
					auto source=arena.at(nodes[current.a].data),r=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true));
					exhausted|=r.exhausted;
					extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,r);
					next=scalar(ctx,current.op==BoundOp.defined?r.output:arena.and_(r.output,source));
					rule=current.op==BoundOp.defined?BindingRule.scalarDomain:BindingRule.scalarHolds;
				}
				if(steps>=budget){
					if(next!=BoundTerm.init){
						if(rule==BindingRule.fixedRecurrence) --solutions.length;
						next=BoundTerm.init; exhausted=true;
					}
					if(current.op==BoundOp.scalar&&!totalScalar(at(result.output))||
						(current.op==BoundOp.defined||current.op==BoundOp.holds)&&nodes[current.a].op==BoundOp.scalar) exhausted=true;
				}
			}
			if(next!=BoundTerm.init&&steps>=budget){ next=BoundTerm.init; exhausted=true; }
			if(next!=BoundTerm.init){
				if(node(next).op==current.op&&(current.op==BoundOp.lambda||current.op==BoundOp.set||current.op==BoundOp.fixed)) inheritHint(at(result.output),next);
				++steps; auto step=emit(rule,result.output,next.id,uint.max,uint.max,extra),tail=visit(next,depth+1);
				auto rest=emit(BindingRule.trans,result.output,tail.output,step,tail.proof);
				result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
			}
			active.set(t.id,false); memo.set(t.id,result); return result;
		}
		auto result=visit(term,0); return BindingResult(term,at(result.output),exhausted,steps,proofs,result.proof,scalarDomains,solutions);
	}

	Term lower(BoundTerm term){
		enforce(context(term)==empty(),"cannot lower an open binding");
		Table!(uint,uint) memo;
		Term visit(BoundTerm t){
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return arena.at(old);
			auto n=node(t); Term result;
			if(n.op==BoundOp.scalar) result=arena.at(n.data);
			else{
				enforce(n.op==BoundOp.primitive,"residual function or argument domain");
				Term[] args=[visit(at(n.a))]; if(n.b!=uint.max) args~=visit(at(n.b));
				result=arena.viewRebuild(arena.at(n.data),args,true);
			}
			memo.set(t.id,result.id); return result;
		}
		return visit(term);
	}
	private string name(uint id){ return "(t"~to!string(id)~(dependent_?" δ":"")~" γ)"; }
	private string ctxName(uint id){ auto s="c"~to!string(id); return dependent_?"("~s~" δ)":s; }
	private Term scalarOperator(TypeId t,TensorOp op){
		auto x=arena.variable(elementSort(t),0); return op==TensorOp.add?arena.add(x,x,true):arena.mul(x,x,true);
	}
	private string tensorOperation(TypeId t,TensorOp op){
		auto v=pool.view(t);
		if(v.kind==TypeKind.vector) return "(Tensor.zipValue "~tensorOperation(v.fields[0],op)~" "~v.dimension.lean~")";
		return leanValueOperation(arena,scalarOperator(t,op));
	}
	private string tensorLiteral(TypeId t,uint n){
		auto s=to!string(n),sort=elementSort(t);
		if(sort==Sort.rational) return "("~s~" / 1 : ℚ)";
		if(sort==Sort.real_) return "(("~s~" : ℤ) : ℝ)";
		if(sort==Sort.complex) return "((("~s~" : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I)";
		return s;
	}
	private string valueOperation(BoundNode n){
		final switch(n.op){
			case BoundOp.pair:return "Tensor.pairValue";
			case BoundOp.vectorCons:return "Tensor.consValue";
			case BoundOp.first:return "(fun x => x.map Prod.fst)";
			case BoundOp.rest:return "(fun x => x.map Prod.snd)";
			case BoundOp.get:return "Tensor.getValue";
			case BoundOp.tensor:
				auto op=cast(TensorOp)n.data,ty=types[nodes[n.a].type],v=pool.view(ty);
				if(op==TensorOp.add||op==TensorOp.mul) return tensorOperation(ty,op);
				auto element=typeLeaf(ty),add=tensorOperation(element,TensorOp.add),mul=tensorOperation(element,TensorOp.mul),zero=tensorLiteral(element,0);
				if(op==TensorOp.dot) return "(Tensor.dotValue "~add~" "~mul~" "~(element==scalarType(Sort.complex)?"Value.conj":"id")~" "~zero~" "~v.dimension.lean~")";
				auto row=pool.view(v.fields[0]);
				if(op==TensorOp.power) return "(Tensor.matrixPowerValue "~add~" "~mul~" "~zero~" "~tensorLiteral(element,1)~" "~v.dimension.lean~")";
				auto dimensions=v.dimension.lean~" "~row.dimension.lean;
				if(op==TensorOp.matmul) dimensions~=" "~pool.view(pool.view(types[nodes[n.b].type]).fields[0]).dimension.lean;
				return "(Tensor."~(op==TensorOp.matmul?"matmulValue":"matvecValue")~" "~add~" "~mul~" "~zero~" "~dimensions~")";
			case BoundOp.primitive:return leanValueOperation(arena,arena.at(n.data));
			case BoundOp.member:return "Binding.memberValue";
			case BoundOp.subset:return "Binding.subsetValue";
			case BoundOp.typeEq:return "Binding.typeEqValue";
			case BoundOp.equal:return "Binding.equalValue";
			case BoundOp.domain:return "Binding.inputDomain";
			case BoundOp.defined:return "Binding.definedValue";
			case BoundOp.holds:return "Binding.holdsValue";
			case BoundOp.guard:return "Binding.guardValue";
			case BoundOp.scalar,BoundOp.variable,BoundOp.lambda,BoundOp.apply,BoundOp.sequence,BoundOp.global,BoundOp.set,BoundOp.typeValue,BoundOp.bottom,BoundOp.fixed,BoundOp.unit,BoundOp.vectorNil:assert(0);
		}
	}
	private string leanType(TypeId t){
		auto v=pool.view(t);
		if(v.kind==TypeKind.unit) return ".unit";
		if(v.kind==TypeKind.vector) return "(.vector "~leanType(v.fields[0])~" "~v.dimension.lean~")";
		if(v.kind==TypeKind.tuple) return "(.pair "~leanType(v.fields[0])~" "~leanType(pool.tuple(v.fields[1..$]))~")";
		if(v.kind==TypeKind.set) return "(.set "~leanType(v.fields[0])~")";
		if(v.kind==TypeKind.function_) return "(.arrow "~leanType(v.fields[0])~" "~leanType(v.fields[1])~")";
		if(v.kind==TypeKind.type_) return ".type";
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean])
			if(t==scalarType(s)) return "(.scalar ."~leanSort(s)~")";
		throw new Exception("unsupported binding type");
	}
	private string leanWitness(TypeId t){
		auto v=pool.view(t);
		if(v.kind==TypeKind.unit) return "()";
		if(v.kind==TypeKind.vector) return "(fun _ => "~leanWitness(v.fields[0])~")";
		if(v.kind==TypeKind.tuple) return "("~leanWitness(v.fields[0])~", "~leanWitness(pool.tuple(v.fields[1..$]))~")";
		return v.kind==TypeKind.type_?"Binding.Ty.type":v.kind==TypeKind.function_?"(fun _ => none)":v.kind==TypeKind.set?"∅":v.kind==TypeKind.boolean?"false":"0";
	}
	private string tensorEvaluationProof(uint from,uint target){
		uint[] leaves; Table!(uint,bool) seen;
		void collect(uint id){
			if(seen.get(id,false)) return; seen.set(id,true); auto n=nodes[id];
			if(n.op==BoundOp.scalar&&arena.view(arena.at(n.data)).arity&&literalData(at(id))) leaves~=id;
			if(n.a!=uint.max) collect(n.a); if(n.b!=uint.max) collect(n.b);
		}
		collect(from);
		struct Total{ string value,proof; }
		Total total(Term t){
			auto n=arena.view(t);
			auto source="n"~to!string(t.id)~".eval ξ";
			if(!n.arity){
				auto v="(("~source~").getD "~(n.sort==Sort.boolean?"false":"0")~")";
				return Total(v,"(show "~source~" = some "~v~" from rfl)");
			}
			enforce(n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castRC,"unsupported total tensor scalar");
			auto child=total(arena.viewChild(t,0)),f="Functions."~builtinInfo(cast(Builtin)n.value).code;
			auto v="("~f~".value "~child.value~")";
			return Total(v,"(show "~source~" = some "~v~" from Eq.trans (congrArg "~f~".apply "~child.proof~") (Tensor.apply_some "~f~" "~child.value~" True.intro))");
		}
		string[] values; foreach(id;leaves) values~="("~name(id)~".eval ξ ρ)";
		string value(uint id){
			foreach(i,leaf;leaves) if(id==leaf) return values[i]; auto n=nodes[id];
			if(n.a==uint.max) return "("~name(id)~".eval ξ ρ)";
			return "("~valueOperation(n)~" "~value(n.a)~(n.b==uint.max?"":" "~value(n.b))~")";
		}
		string prove(size_t i){
			if(i==leaves.length) return "rfl";
			auto id=leaves[i],v=total(arena.at(nodes[id].data)); values[i]="w"~to!string(i);
			auto predicate="(fun "~values[i]~" : Option ("~leanType(type(at(id)))~" : Binding.Ty).denote => "~value(from)~" = "~value(target)~")";
			values[i]="(some "~v.value~")"; return "(Eq.mpr (congrArg "~predicate~" "~v.proof~") "~prove(i+1)~")";
		}
		return ".ofEq (fun ξ ρ => "~prove(0)~")";
	}
	string exportLean(BindingResult result,bool lowerResult=false){
		check(result.input); check(result.output); enforce(result.proof<result.proofs.length,"missing binding proof");
		auto lowered=lowerResult?lower(result.output):Term.init;
		string code="import QSym\n",dimDecl=dependent_?" (δ : ℕ → ℕ)":"",dimArg=dependent_?" δ":"";
		foreach(i,d;result.domains){
			auto prefix="QSym.BindingScalar"~to!string(i),part=exportDomainLean(arena,d.input,d.result);
			part=replace(part,"import QSym\n","");
			part=replace(part,"QSym.Certificate",prefix~".Certificate");
			part=replace(part,"QSym.DomainCertificate",prefix~".DomainCertificate"); code~=part;
			if(d.value.traced){
				part=replace(scalarExport(arena,d.value),"import QSym\n","");
				code~=replace(part,"QSym.Certificate",prefix~".ValueCertificate");
			}
		}
		code~="namespace QSym.BindingCertificate\n";
		bool[] used=new bool[nodes.length]; uint[] stack=[result.input.id,result.output.id];
		foreach(p;result.proofs){ stack~=p.from; stack~=p.to; }
		while(stack.length){
			auto id=stack[$-1]; --stack.length; if(used[id]) continue;
			used[id]=true; auto n=nodes[id];
			if(n.a!=uint.max) stack~=n.a; if(n.b!=uint.max) stack~=n.b;
		}
		uint[] scalarNodes;
		foreach(i,n;nodes) if(used[i]&&n.op==BoundOp.scalar) scalarNodes~=arena.viewPostorder(arena.at(n.data));
		foreach(d;result.domains){
			scalarNodes~=arena.viewPostorder(d.input); scalarNodes~=arena.viewPostorder(d.result.output);
			if(d.value.traced) scalarNodes~=arena.viewPostorder(arena.castTo(d.value.output,arena.sort(d.input)));
		}
		if(lowerResult) scalarNodes~=arena.viewPostorder(lowered);
		bool[] needed=new bool[arena.length]; foreach(id;scalarNodes) needed[id]=true;
		foreach(i,yes;needed) if(yes) code~=leanSyntaxCode(arena,arena.at(cast(uint)i));
		foreach(i,ctx;contexts){
			code~="abbrev c"~to!string(i)~dimDecl~" : List Binding.Ty := ";
			code~=i==0?"[]\n":leanType(types[ctx.type])~" :: "~ctxName(ctx.parent)~"\n";
		}
		foreach(i,n;nodes) if(used[i]){
			string expr;
			final switch(n.op){
				case BoundOp.unit:expr=".constant (some ())"; break;
				case BoundOp.vectorNil:expr=".constant Tensor.nilValue"; break;
				case BoundOp.scalar:expr=".scalar n"~to!string(n.data); break;
				case BoundOp.variable:
					expr=".here"; foreach(j;0..n.data) expr="(.there "~expr~")";
					expr=".var "~expr; break;
				case BoundOp.primitive,BoundOp.member,BoundOp.subset,BoundOp.domain,BoundOp.defined,BoundOp.holds,BoundOp.guard,BoundOp.typeEq,BoundOp.equal,BoundOp.vectorCons,BoundOp.pair,BoundOp.first,BoundOp.rest,BoundOp.get,BoundOp.tensor:
					expr="."~(n.b==uint.max?"unary":"binary")~" "~valueOperation(n)~" "~name(n.a);
					if(n.b!=uint.max) expr~=" "~name(n.b); break;
				case BoundOp.lambda:expr=".lam "~name(n.a); break;
				case BoundOp.set:expr=".set "~name(n.a); break;
				case BoundOp.global:expr=".constant (some (γ "~leanType(types[n.type])~" "~to!string(n.data)~"))"; break;
				case BoundOp.typeValue:expr=".constant (some "~leanType(types[n.data])~")"; break;
				case BoundOp.bottom:expr=".constant none"; break;
				case BoundOp.fixed:expr=".unary Recursion.fixedValue (.lam "~name(n.a)~")"; break;
				case BoundOp.apply:expr=".app "~name(n.a)~" "~name(n.b); break;
				case BoundOp.sequence:expr=".seq "~name(n.a)~" "~name(n.b); break;
			}
			code~="noncomputable def t"~to!string(i)~dimDecl~" (γ : Binding.Globals) : Binding.Expr "~ctxName(n.context)~" "~leanType(types[n.type])~" := "~expr~"\n";
		}
		foreach(i,n;nodes) if(used[i]&&n.op==BoundOp.fixed){
			auto v=pool.view(types[n.type]),a="("~leanType(v.fields[0])~" : Binding.Ty).denote",b="("~leanType(v.fields[1])~" : Binding.Ty).denote";
			auto env="(Binding.Env.cons (a := "~leanType(v.fields[0])~") (some x) (Binding.Env.cons (a := "~leanType(types[n.type])~") (some (fun (_ : "~a~") => (none : Option "~b~"))) ρ))";
			string program(uint id){
				auto t=at(id),q=nodes[id];
				if(!depends(t,1)) return "(.constant (fun x => "~name(id)~".eval ξ "~env~"))";
				if(q.op==BoundOp.apply) return "(.call "~program(q.b)~")";
				auto x=program(q.a),y=q.b==uint.max?"":program(q.b);
				if(q.op==BoundOp.guard) return "(.branch "~x~" "~y~" (.constant (fun _ => none)))";
				if(q.op==BoundOp.primitive){
					auto op=arena.view(arena.at(q.data)).op;
					if(op==Op.mask||op==Op.and_) return "(.branch "~x~" "~y~" (.constant (fun _ => some "~(op==Op.mask?"0":"false")~")))";
					if(op==Op.or_) return "(.branch "~x~" (.constant (fun _ => some true)) "~y~")";
				}
				auto op=q.op==BoundOp.sequence?"(fun (x : Option ("~leanType(types[nodes[q.a].type])~" : Binding.Ty).denote) (y : Option ("~leanType(types[nodes[q.b].type])~" : Binding.Ty).denote) => x.bind (fun _ => y))":valueOperation(q);
				return q.b==uint.max?"(.unary "~op~" rfl "~x~")":
					"(.binary "~op~" (fun _ => rfl) (fun x => Option.casesOn x rfl (fun _ => rfl)) "~x~" "~y~")";
			}
			string programProof(uint id){
				auto q=nodes[id]; if(!depends(at(id),1)) return "rfl";
				if(q.op==BoundOp.apply){ auto h=programProof(q.b); return h=="rfl"?h:"(congrArg (fun z : Option "~a~" => z.bind g) "~h~")"; }
				auto x=programProof(q.a),y=q.b==uint.max?"":programProof(q.b);
				auto op=q.op==BoundOp.sequence?"(fun (x : Option ("~leanType(types[nodes[q.a].type])~" : Binding.Ty).denote) (y : Option ("~leanType(types[nodes[q.b].type])~" : Binding.Ty).denote) => x.bind (fun _ => y))":valueOperation(q);
				auto proof=q.b==uint.max?"(congrArg "~op~" "~x~")":"(congrArg₂ "~op~" "~x~" "~y~")";
				string bridge;
				if(q.op==BoundOp.guard) bridge="Binding.guard_branch";
				else if(q.op==BoundOp.primitive){
					auto kind=arena.view(arena.at(q.data)).op;
					if(kind==Op.mask) bridge="Recursion.mask_branch";
					if(kind==Op.and_) bridge="Recursion.and_branch";
					if(kind==Op.or_) bridge="Recursion.or_branch";
				}
				return bridge.length?"(Eq.trans "~proof~" ("~bridge~" _ _))":x=="rfl"&&(q.b==uint.max||y=="rfl")?"rfl":proof;
			}
			auto id=to!string(i),args=dimDecl~" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctxName(n.context)~")";
			auto h="(fun g => congrArg some (funext (fun x => "~programProof(nodes[n.a].a)~")))";
			code~="noncomputable def rec"~id~args~" : Recursion.Program "~a~" "~b~" "~b~" := "~program(nodes[n.a].a)~"\n";
			code~="theorem fixed"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = some (FixedPoint.value (rec"~id~dimArg~" γ ξ ρ).functional) := Recursion.fixed_program (rec"~id~dimArg~" γ ξ ρ) _ "~h~"\n";
			code~="theorem unroll"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = (Binding.Expr.app (.lam "~name(n.a)~") "~name(cast(uint)i)~").eval ξ ρ := Recursion.program_unfold (rec"~id~dimArg~" γ ξ ρ) _ "~h~"\n";
			foreach(s;result.solutions) if(s.source==i){
				auto base="(n"~to!string(nodes[s.base].data)~".eval ξ)",delta="(n"~to!string(nodes[s.delta].data)~".eval ξ)";
				if(s.cutoff){
					auto hp="(fun g x => ("~programProof(nodes[n.a].a)~").symm)";
					code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n"~
						"  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (Recursion.solve_nat_cutoff (rec"~id~dimArg~" γ ξ ρ) ("~base~".getD 0) ("~delta~".getD 0) "~hp~"))\n";
					continue;
				}
				auto op=s.zero==Law.natural_recurrence_mul_base?"Functions.mulN.apply":"Functions.addN.apply";
				if(s.left) op="(fun x y => "~op~" y x)";
				auto k="(fun (x : ℕ) => "~name(nodes[s.target].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some x) ρ))";
				auto hp="(fun g x => ("~programProof(nodes[n.a].a)~").symm)";
				auto hz="(Generated.r_"~to!string(s.zero)~" "~base~" "~delta~" ⟨_, rfl⟩)";
				auto successor="(congrArg (fun (z : Option ℕ) => "~name(nodes[s.target].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) z ρ)) (Recursion.nat_successor x).symm)";
				auto hs="(fun x => Eq.trans "~successor~" (Generated.r_"~to!string(s.law)~" "~base~" "~delta~" (some x)).symm)";
				code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n"~
					"  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (Recursion.solve_nat_step (rec"~id~dimArg~" γ ξ ρ) "~op~" "~base~" "~delta~" "~k~" "~hp~" "~hz~" "~hs~"))\n";
			}
		}
		string proofName(uint id){ return "(p"~to!string(id)~dimArg~" γ)"; }
		foreach(i,p;result.proofs){
			auto n=nodes[p.from]; string proof;
			final switch(p.rule){
				case BindingRule.getScalarUndefined:
					proof="Tensor.getScalarUndefined "~name(n.a)~" n"~to!string(nodes[n.b].data)~" QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct"; break;
				case BindingRule.getBottom:
					auto left=nodes[n.a].op==BoundOp.bottom;
					proof=".ofEq (fun ξ ρ => Tensor.get_none_"~(left?"left":"right")~" ("~name(left?n.b:n.a)~".eval ξ ρ))"; break;
				case BindingRule.tensorEval:proof=tensorEvaluationProof(p.from,p.to); break;
				case BindingRule.tensorPower:
					auto v=pool.view(types[n.type]),element=typeLeaf(types[n.type]),exponent=arena.number(arena.at(nodes[n.b].data)).re.integer;
					proof=".ofEq (fun ξ ρ => Tensor.matrixPowerValue_succ "~tensorOperation(element,TensorOp.add)~" "~tensorOperation(element,TensorOp.mul)~" "~tensorLiteral(element,0)~" "~tensorLiteral(element,1)~" "~v.dimension.lean~" ("~name(n.a)~".eval ξ ρ) "~to!string(exponent-1)~")"; break;
				case BindingRule.tensorDefined:
					auto child=nodes[n.a];
					proof=".ofEq (fun ξ ρ => Tensor."~(child.op==BoundOp.pair?"defined_pair":"defined_cons")~" ("~name(child.a)~".eval ξ ρ) ("~name(child.b)~".eval ξ ρ))"; break;
				case BindingRule.fixedRecurrence:proof=".ofEq (fun ξ ρ => solve"~to!string(p.from)~dimArg~" γ ξ ρ)"; break;
				case BindingRule.refl:proof=".refl "~name(p.from); break;
				case BindingRule.trans:proof=".trans "~proofName(p.left)~" "~proofName(p.right); break;
				case BindingRule.beta:proof=".beta "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.seqScalar:proof=".seqScalar n"~to!string(nodes[n.a].data)~" "~name(n.b)~" (fun _ => ⟨_, rfl⟩)"; break;
				case BindingRule.seqLam:proof=".seqLam "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.seqSelf:proof=".seqSelf "~name(n.a); break;
				case BindingRule.shortCircuit:
					if(n.op==BoundOp.primitive&&arena.view(arena.at(n.data)).op==Op.mask&&!arena.view(arena.at(nodes[n.a].data)).value){
						auto sort=arena.sort(arena.at(n.data)),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":sort==Sort.complex?"C":"";
						if(suffix.length){ proof=".maskFalse"~suffix~" "~name(n.b); break; }
					}
					goto case BindingRule.fold;
				case BindingRule.fold,BindingRule.seqTotal:proof=".ofEq (fun _ _ => rfl)"; break;
				case BindingRule.domainBottom:proof=".domainBottom"; break;
				case BindingRule.appBottom:proof=".appBottom "~name(n.a); break;
				case BindingRule.appScalarUndefined:
					proof=".appScalarUndefined "~name(n.a)~" n"~to!string(nodes[n.b].data)~" QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct"; break;
				case BindingRule.definedFixed:proof=".ofEq (fun ξ ρ => congrArg Binding.definedValue (fixed"~to!string(n.a)~dimArg~" γ ξ ρ))"; break;
				case BindingRule.fixedApp:
					proof=".ofEq (fun ξ ρ => congrArg (fun f : Option ("~leanType(types[nodes[n.a].type])~" : Binding.Ty).denote => f.bind (fun g => ("~name(n.b)~".eval ξ ρ).bind g)) (unroll"~to!string(n.a)~dimArg~" γ ξ ρ))"; break;
				case BindingRule.fixedConstant:
					proof=".ofEq (fun ξ ρ => Recursion.fixed_constant (fun x => "~name(nodes[p.to].a)~".eval ξ (ρ.cons (some x))))"; break;
				case BindingRule.fixedIdentity:proof=".ofEq (fun _ _ => Recursion.fixed_identity)"; break;
				case BindingRule.seqGuard:proof=".seqGuard "~name(n.a)~" "~name(n.b); break;
				case BindingRule.domainLam:proof=".domainLam "~name(nodes[n.a].a); break;
				case BindingRule.memberDomain:proof=".memberDomain "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.memberSet:proof=".memberSet "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.guardTrue:proof=".guardTrue "~name(n.b); break;
				case BindingRule.guardAnd:proof=".guardAnd "~name(n.a)~" "~name(nodes[n.b].a)~" "~name(nodes[n.b].b); break;
				case BindingRule.holdsGuard:proof=".holdsGuard "~name(nodes[n.a].a)~" "~name(nodes[n.a].b); break;
				case BindingRule.setHolds:proof=".setHolds "~name(n.a); break;
				case BindingRule.typeEqSelf:proof=".typeEqSelf "~name(n.a); break;
				case BindingRule.equalSelf:proof=".equalSelf "~name(n.a); break;
				case BindingRule.equalBottomLeft:proof=".equalBottomLeft "~name(n.b); break;
				case BindingRule.equalBottomRight:proof=".equalBottomRight "~name(n.a); break;
				case BindingRule.definedEqual:proof=".definedEqual "~name(nodes[n.a].a)~" "~name(nodes[n.a].b); break;
				case BindingRule.typeEqValues:proof=".ofEq (fun _ _ => rfl)"; break;
				case BindingRule.definedGuardFalse:proof=".definedGuardFalse "~name(nodes[n.a].b); break;
				case BindingRule.definedTotal:proof=".ofEq (fun _ _ => rfl)"; break;
				case BindingRule.subsetRefl:proof=".subsetRefl "~name(n.a); break;
				case BindingRule.subsetEmpty:proof=".subsetEmpty "~name(n.b); break;
				case BindingRule.subsetUniv:proof=".subsetUniv "~name(n.a); break;
				case BindingRule.subsetUnivEmpty,BindingRule.equalUnivEmpty,BindingRule.equalEmptyUniv:
					auto ty=pool.view(types[nodes[n.a].type]).fields[0],witness=leanWitness(ty);
					auto op=p.rule==BindingRule.subsetUnivEmpty?"subsetUnivEmpty":p.rule==BindingRule.equalUnivEmpty?"equalUnivEmpty":"equalEmptyUniv";
					proof="."~op~" (a := "~leanType(ty)~") "~witness; break;
				case BindingRule.definedMember,BindingRule.definedSubset,BindingRule.definedGuard,BindingRule.definedApp:
					auto op=p.rule==BindingRule.definedMember?"definedMember":p.rule==BindingRule.definedSubset?"definedSubset":p.rule==BindingRule.definedGuard?"definedGuard":"definedApp";
					proof="."~op~" "~name(nodes[n.a].a)~" "~name(nodes[n.a].b); break;
				case BindingRule.definedNot:proof=".definedNot "~name(nodes[n.a].a); break;
				case BindingRule.domainGuardFalse:proof=".domainGuardFalse "~name(nodes[n.a].b); break;
				case BindingRule.pointwise:
					auto d=result.domains[p.extra],prefix="QSym.BindingScalar"~to!string(p.extra),field=leanSort(d.sort);
					auto env="({ ξ with "~field~" := fun i => if i = "~to!string(d.variable)~" then x else ξ."~field~" i })";
					auto hd="("~prefix~".DomainCertificate.domain_correct "~env~")";
					auto input="(n"~to!string(d.input.id)~".eval "~env~")",domain="(n"~to!string(d.result.output.id)~".eval "~env~")";
					string equality;
					if(d.mode==BoundOp.defined) equality=hd~".symm";
					else if(d.mode==BoundOp.holds) equality="(Binding.holdsDomain "~input~" "~domain~" "~hd~")";
					else equality="(Binding.preserveDomain "~input~" (n"~to!string(arena.castTo(d.value.output,arena.sort(d.input)).id)~".eval "~env~") "~domain~
						" "~hd~" ("~prefix~".ValueCertificate.refinement "~env~"))";
					string wrap(uint id,size_t depth){
						if(depth==d.path.length) return equality;
						auto q=nodes[id],left=d.path[depth]==0?wrap(q.a,depth+1):"rfl";
						if(q.b==uint.max) return "(congrArg "~valueOperation(q)~" "~left~")";
						auto right=d.path[depth]==1?wrap(q.b,depth+1):"rfl";
						return "(congrArg₂ "~valueOperation(q)~" "~left~" "~right~")";
					}
					proof=(n.op==BoundOp.lambda?".lamPointwise":".setPointwise")~" (fun ξ ρ x => "~wrap(n.a,0)~")"; break;
				case BindingRule.scalarSimplify:
					auto d=result.domains[p.extra],prefix="QSym.BindingScalar"~to!string(p.extra);
					proof=".scalarSimplify n"~to!string(d.input.id)~" n"~to!string(d.result.output.id)~" n"~to!string(arena.castTo(d.value.output,arena.sort(d.input)).id)~
						" "~prefix~".DomainCertificate.domain_correct "~prefix~".ValueCertificate.refinement"; break;
				case BindingRule.scalarDomain,BindingRule.scalarHolds:
					auto d=result.domains[p.extra];
					proof=p.rule==BindingRule.scalarDomain?".scalarDomain ":".scalarHolds ";
					proof~="n"~to!string(d.input.id)~" n"~to!string(d.result.output.id)~" QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct"; break;
				case BindingRule.congr:
					if(n.op==BoundOp.fixed){ auto ty=leanType(types[n.type]); proof=".unary (a := .arrow "~ty~" "~ty~") (b := "~ty~") Recursion.fixedValue (.lam "~proofName(p.left)~")"; break; }
					auto generic=n.op==BoundOp.equal||n.op==BoundOp.typeEq||n.op==BoundOp.primitive||n.op==BoundOp.member||n.op==BoundOp.subset||n.op==BoundOp.domain||n.op==BoundOp.defined||n.op==BoundOp.holds||n.op==BoundOp.guard||n.op==BoundOp.pair||n.op==BoundOp.vectorCons||n.op==BoundOp.get||n.op==BoundOp.first||n.op==BoundOp.rest||n.op==BoundOp.tensor;
					auto op=generic?(n.b==uint.max?"unary":"binary"):
						n.op==BoundOp.lambda?"lam":n.op==BoundOp.set?"set":n.op==BoundOp.apply?"app":"seq";
					proof="."~op;
					if(generic){
						proof~=" (a := "~leanType(types[nodes[n.a].type])~")";
						if(n.b!=uint.max) proof~=" (b := "~leanType(types[nodes[n.b].type])~")";
						proof~=" ("~(n.b==uint.max?"b":"c")~" := "~leanType(types[n.type])~") "~valueOperation(n);
					}
					proof~=" "~proofName(p.left);
					if(p.right!=uint.max) proof~=" "~proofName(p.right); break;
			}
			code~="theorem p"~to!string(i)~dimDecl~" (γ : Binding.Globals) : Binding.Reduction "~name(p.from)~" "~name(p.to)~" := "~proof~"\n";
		}
		code~="theorem reduction"~dimDecl~" (γ : Binding.Globals) : Binding.Reduction "~name(result.input.id)~" "~name(result.output.id)~" := "~proofName(result.proof)~"\n";
		string left=replace(name(result.input.id)," δ γ"," ξ.natural γ")~".eval ξ ρ",right=replace(name(result.output.id)," δ γ"," ξ.natural γ")~".eval ξ ρ";
		auto ctx=replace(ctxName(node(result.input).context)," δ)"," ξ.natural)"),sizes=dependent_?" ξ.natural":"";
		code~="theorem sound (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctx~") : "~left~" = "~right~" := Binding.Reduction.sound (reduction"~sizes~" γ) ξ ρ\n";
		code~="theorem domain (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctx~") : Value.Defined ("~left~") ↔ Value.Defined ("~right~") := Binding.Reduction.defined (reduction"~sizes~" γ) ξ ρ\n";
		if(lowerResult){
			code~="theorem lowered (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctx~") : "~left~" = n"~to!string(lowered.id)~".eval ξ := Eq.trans (sound γ ξ ρ) rfl\n";
			code~="#qsym_check_axioms lowered\n";
		}
		return code~"#qsym_check_axioms sound\n#qsym_check_axioms domain\nend QSym.BindingCertificate\n";
	}
}
