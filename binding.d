module qsym.binding;
import qsym.ir;
import qsym.summation:sumAntidifference,SumPrimitive;
import qsym.types:TypeId,TypeKind,TypePool,Dimension;
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
enum BoundOp:ubyte{ scalar,variable,primitive,lambda,apply,sequence,global,set,member,domain,defined,holds,guard,subset,typeValue,typeEq,bottom,fixed,equal,unit,vectorNil,vectorCons,pair,first,rest,get,tensor,summation,finiteSum }
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
	equalSelf,equalBottomLeft,equalBottomRight,definedEqual,equalUnivEmpty,equalEmptyUniv,fixedRecurrence,tensorEval,tensorPower,tensorDefined,getBottom,getScalarUndefined,domainFixedTotal,tensorSpectral,getCons,tensorSpectrumCast,tensorDomain,getDomain,sumZero,sumRange,rangeZero,rangeStep,rangeLift,rangeSolution,sumGeometric,sumDelta,sumRangeLe,sumConstant,sumInterval,sumDeltaOffset,rangeGeometric,sumBounds,sumRound,sumMaskAnd,rangeAdd,rangeMaskLt,rangeMaskGe,sumTail,sumMaskEqOffset,sumMaskNeOffset,sumTailNatural,sumTailStrict,sumShiftGeometric,sumRationalBound,sumDeltaZero,sumBoundedAdd,sumCastMask,sumCastAdd,sumExcludeOffset,addBottom,sumPowerNatural,sumPowerNegative,sumAffineNatural,sumNaturalBound,sumExcludeZero
}
private struct BindingStep{ BindingRule rule; uint from,to,left=uint.max,right=uint.max,extra=uint.max; }
private struct SummationSolution{ uint source,target,candidate,variable,zero,step; SumPrimitive[] tail; uint[] totals,convergence; }
private struct ScalarDomain{ Term input; Result result,value; uint variable; Sort sort; uint[] path; BoundOp mode; }
private struct RecurrenceFact{ uint node,index; Term input; Result domain,value; }
private struct RecurrenceSolution{ uint source,target,base,delta; Law law,zero; bool left,cutoff; ubyte band; uint lower; bool affine,prefix; uint order,variable; Term[] seeds; RecurrenceFact[] facts; }
private struct DomainLeaf{ uint node; Term value; Result domain; }
private struct DomainRank{ uint source,variable; Result result,lower,upper; DomainLeaf[] leaves; Result[] iterations; Sort sort; Term slope,bound,step; }
private struct SpectralFact{ Term input; Result domain,value; }
private struct SpectralSolution{ uint source,target,size; bool diagonal; Term[] matrix,vector; Term first,second,minus; SpectralFact[] parameters,checks; uint split; uint[4] blocks; bool repeated,nilpotent,cubeZero,zeroRoot; Term[] roots,components; }
struct BindingResult{
	BoundTerm input,output;
	bool exhausted;
	uint steps;
	private BindingStep[] proofs;
	private uint proof;
	private ScalarDomain[] domains;
	private RecurrenceSolution[] solutions;
	private DomainRank[] ranks;
	private SpectralSolution[] spectra;
	private SummationSolution[] sums;
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
	private bool dependent_,telescope_;
	private Table!(uint,string) dimensionParameters;
	void dimensionParameter(string name,uint index){ dimensionParameters.set(index,name); }
	@property bool telescope(){ return telescope_; }
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
		auto v=pool.view(t); telescope_|=pool.dependent(t);
		if(v.dimension !is null&&v.dimension.names.length) dependent_=true;
		enforce(v.kind==TypeKind.type_||v.kind==TypeKind.pi||v.kind==TypeKind.function_||v.kind==TypeKind.set||v.kind==TypeKind.vector||v.kind==TypeKind.tuple||v.kind<=TypeKind.complex,"unsupported binding type");
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
		return intern(BoundNode(BoundOp.variable,s.index,typeId(pool.shift(types[contexts[ctx].type],cast(int)index+1)),uint.max,uint.max,index));
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
	Dimension dimension(BoundTerm t){
		enforce(type(t)==scalarType(Sort.natural),"dependent argument must have type ℕ"); auto n=node(t);
		if(n.op==BoundOp.variable) return Dimension.bound(n.data);
		if(n.op==BoundOp.scalar){
			Dimension scalarDimension(Term x){
				auto q=arena.view(x);
				if(arena.isNumber(x)){ auto v=arena.number(x).re; enforce(v.small&&v.integer>=0,"dimension literal exceeds range"); return Dimension.literal(cast(ulong)v.integer); }
				if(q.op==Op.variable){ auto name=dimensionParameters.get(cast(uint)q.value,""); enforce(name.length,"unknown dimension parameter"); return Dimension.variable(name,cast(uint)q.value); }
				if(q.op==Op.builtin&&(q.value==Builtin.addN||q.value==Builtin.mulN||q.value==Builtin.powNN))
					return Dimension.binary(q.value==Builtin.addN?"+":q.value==Builtin.mulN?"*":"^",scalarDimension(arena.viewChild(x,0)),scalarDimension(arena.viewChild(x,1)));
				throw new Exception("dependent arguments require total natural literals, parameters, sums, products, or powers");
			}
			return scalarDimension(arena.at(n.data));
		}
		if(n.op==BoundOp.primitive){ auto q=arena.view(arena.at(n.data));
			if(q.op==Op.builtin&&(q.value==Builtin.addN||q.value==Builtin.mulN||q.value==Builtin.powNN))
				return Dimension.binary(q.value==Builtin.addN?"+":q.value==Builtin.mulN?"*":"^",dimension(at(n.a)),dimension(at(n.b)));
		}
		throw new Exception("dependent arguments require total natural dimensions");
	}
	BoundTerm lambda(BoundTerm body){
		auto n=node(body); enforce(n.context!=0,"lambda requires a bound variable");
		auto ctx=contexts[n.context],ty=typeId(pool.pi(types[ctx.type],types[n.type]));
		return intern(BoundNode(BoundOp.lambda,ctx.parent,ty,body.id));
	}
	BoundTerm apply(BoundTerm function_,BoundTerm argument){
		auto f=node(function_),x=node(argument),ty=pool.view(types[f.type]);
		enforce(f.context==x.context,"application context mismatch");
		enforce((ty.kind==TypeKind.function_||ty.kind==TypeKind.pi)&&ty.fields[0]==types[x.type],"application type mismatch");
		return intern(BoundNode(BoundOp.apply,f.context,typeId(ty.kind==TypeKind.pi?pool.instantiate(ty.fields[1],dimension(argument)):ty.fields[1]),function_.id,argument.id));
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
	BoundTerm finiteSum(BoundTerm f,BoundTerm n){
		auto v=pool.view(type(f));
		enforce(v.kind==TypeKind.function_&&v.fields[0]==scalarType(Sort.natural)&&type(n)==scalarType(Sort.natural)&&context(f)==context(n),"invalid finite sum");
		return intern(BoundNode(BoundOp.finiteSum,node(f).context,typeId(v.fields[1]),f.id,n.id));
	}
	private BoundTerm dropIndex(BoundTerm t){
		auto inner=context(t),parent=Scope(this,contexts[inner.index].parent);
		BoundTerm[] values=[scalar(parent,arena.number(Number(0),elementSort(type(variable(inner,0)))))];
		foreach(i;0..depth(parent)) values~=variable(parent,i);
		return substitute(t,parent,values);
	}
	BoundTerm summation(BoundTerm f){
		auto n=node(f),v=pool.view(type(f));
		enforce(v.kind==TypeKind.function_&&(v.fields[0]==scalarType(Sort.natural)||v.fields[0]==scalarType(Sort.integer)),"summation requires a natural or integer index");
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(v.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		enforce(numeric,"summation requires scalar numeric values");
		return intern(BoundNode(BoundOp.summation,n.context,typeId(v.fields[1]),f.id));
	}
	BoundTerm domain(BoundTerm f){
		auto n=node(f),v=pool.view(type(f)); enforce(v.kind==TypeKind.function_||v.kind==TypeKind.pi,"domain requires a function");
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
	private BoundTerm rebuild(BoundTerm t,Scope target,BoundTerm[] args,Dimension delegate(uint) @safe dimensions=null){
		auto n=node(t);
		TypeId mapped(uint id){ return dimensions is null?types[id]:pool.map(types[id],dimensions); }
		final switch(n.op){
			case BoundOp.unit,BoundOp.vectorNil:return tuple(target,[],mapped(n.type));
			case BoundOp.vectorCons,BoundOp.pair:return intern(BoundNode(n.op,target.index,typeId(mapped(n.type)),args[0].id,args[1].id));
			case BoundOp.first,BoundOp.rest:return intern(BoundNode(n.op,target.index,typeId(mapped(n.type)),args[0].id));
			case BoundOp.get:return get(args[0],args[1]);
			case BoundOp.tensor:return tensor(cast(TensorOp)n.data,args[0],args[1]);
			case BoundOp.scalar:return scalar(target,arena.at(n.data));
			case BoundOp.global:return global(target,mapped(n.type),n.data);
			case BoundOp.variable:assert(0,"variable requires substitution");
			case BoundOp.primitive:return primitive(arena.at(n.data),args);
			case BoundOp.lambda:return inheritHint(t,lambda(args[0]));
			case BoundOp.set:return inheritHint(t,set(args[0]));
			case BoundOp.member:return member(args[0],args[1]);
			case BoundOp.subset:return subset(args[0],args[1]);
			case BoundOp.typeEq:return typeEq(args[0],args[1]);
			case BoundOp.equal:return equal(args[0],args[1]);
			case BoundOp.typeValue:return typeValue(target,mapped(n.data));
			case BoundOp.bottom:return bottom(target,mapped(n.type));
			case BoundOp.fixed:return inheritHint(t,fixed(args[0]));
			case BoundOp.finiteSum:return finiteSum(args[0],args[1]);
			case BoundOp.summation:return summation(args[0]);
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
		Dimension mapped(uint i){ enforce(i<indices.length,"unbound renamed dimension"); return Dimension.bound(indices[i]); }
		foreach(i,index;indices){
			enforce(type(variable(target,index))==pool.map(type(variable(context(term),cast(uint)i)),&mapped),"renaming type mismatch");
		}
		Table!(uint,uint) memo;
		BoundTerm visit(BoundTerm t){
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return at(old);
			auto n=node(t); BoundTerm result;
			if(n.op==BoundOp.variable) result=variable(target,indices[n.data]);
			else if(n.op==BoundOp.lambda||n.op==BoundOp.set||n.op==BoundOp.fixed){
				uint[] lifted=[0]; foreach(index;indices) lifted~=index+1;
				auto body=rename(at(n.a),push(target,pool.map(types[contexts[nodes[n.a].context].type],&mapped)),lifted);
				result=inheritHint(t,n.op==BoundOp.lambda?lambda(body):n.op==BoundOp.set?set(body):fixed(body));
			}else{
				BoundTerm[] children;
				if(n.a!=uint.max) children~=visit(at(n.a));
				if(n.b!=uint.max) children~=visit(at(n.b));
				result=rebuild(t,target,children,&mapped);
			}
			memo.set(t.id,result.id); return result;
		}
		return visit(term);
	}
	BoundTerm substitute(BoundTerm term,Scope target,BoundTerm[] values){
		check(term); check(target); auto ctx=node(term).context;
		enforce(values.length==contexts[ctx].length,"substitution arity mismatch");
		Dimension mapped(uint i){ enforce(i<values.length,"unbound substituted dimension"); return dimension(values[i]); }
		foreach(i,value;values){
			enforce(context(value)==target&&type(value)==pool.map(type(variable(context(term),cast(uint)i)),&mapped),"substitution type mismatch");
		}
		Table!(uint,uint) memo;
		BoundTerm visit(BoundTerm t){
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return at(old);
			auto n=node(t); BoundTerm result;
			if(n.op==BoundOp.variable) result=values[n.data];
			else if(n.op==BoundOp.lambda||n.op==BoundOp.set||n.op==BoundOp.fixed){
				auto inner=push(target,pool.map(types[contexts[nodes[n.a].context].type],&mapped));
				BoundTerm[] lifted=[variable(inner,0)]; uint[] indices;
				foreach(i;0..contexts[target.index].length) indices~=i+1;
				foreach(value;values) lifted~=rename(value,inner,indices);
				auto body=substitute(at(n.a),inner,lifted); result=inheritHint(t,n.op==BoundOp.lambda?lambda(body):n.op==BoundOp.set?set(body):fixed(body));
			}else{
				BoundTerm[] children;
				if(n.a!=uint.max) children~=visit(at(n.a));
				if(n.b!=uint.max) children~=visit(at(n.b));
				result=rebuild(t,target,children,&mapped);
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
		bool isForward(uint id){
			auto q=nodes[id]; if(q.op!=BoundOp.apply||!variableAt(q.a,1)||!call(q.b,Builtin.addN)) return false;
			auto x=nodes[q.b],one=nodes[x.b]; return variableAt(x.a,0)&&one.op==BoundOp.scalar&&arena.isNumber(arena.at(one.data))&&arena.number(arena.at(one.data)).one;
		}
		bool splitBranch(uint id,out uint p,out uint yes,out uint no){
			if(!call(id,Builtin.addN)) return false; auto q=nodes[id];
			if(!unary(q.a,Op.mask)||!unary(q.b,Op.mask)) return false; auto x=nodes[q.a],y=nodes[q.b];
			if(!unary(y.a,Op.not_)||nodes[y.a].a!=x.a) return false; p=x.a; yes=x.b; no=y.b; return true;
		}
		bool literal(uint id,out ulong value){
			auto q=nodes[id]; if(q.op!=BoundOp.scalar||!arena.isNumber(arena.at(q.data))) return false;
			auto x=arena.number(arena.at(q.data)).re; if(!x.small||x.integer<0) return false; value=cast(ulong)x.integer; return true;
		}
		uint bandLowerTest,bandDown,bandRest,bandEq,bandBase,bandTail,bandUpperTest,bandDownAgain,bandUp; ulong bandLower,bandUpper;
		if(splitBranch(body.a,bandLowerTest,bandDown,bandRest)&&previous(bandDown)&&call(bandLowerTest,Builtin.ltN)&&
			variableAt(nodes[bandLowerTest].a,0)&&literal(nodes[bandLowerTest].b,bandLower)&&
			splitBranch(bandRest,bandEq,bandBase,bandTail)&&totalScalar(at(bandBase))&&splitBranch(bandTail,bandUpperTest,bandDownAgain,bandUp)&&bandDownAgain==bandDown&&isForward(bandUp)&&
			call(bandUpperTest,Builtin.ltN)&&variableAt(nodes[bandUpperTest].a,0)&&literal(nodes[bandUpperTest].b,bandUpper)&&bandLower<bandUpper&&
			unary(bandEq,Op.not_)&&call(nodes[bandEq].a,Builtin.nonzeroZ)&&call(nodes[nodes[bandEq].a].a,Builtin.addZ)){
			auto sum=nodes[nodes[nodes[bandEq].a].a]; bool matches;
			if(call(sum.a,Builtin.castNZ)&&variableAt(nodes[sum.a].a,0)&&nodes[sum.b].op==BoundOp.scalar){
				auto neg=arena.at(nodes[sum.b].data),q=arena.view(neg);
				if(q.op==Op.builtin&&q.value==Builtin.mulZ){
					auto x=arena.viewChild(neg,0),y=arena.viewChild(neg,1);
					matches=arena.isNumber(x)&&arena.isNumber(y)&&arena.number(x).re==Rational(-1)&&arena.number(y).re==Rational(bandLower);
				}
			}
			if(matches){
				auto inner=push(context(t),ty.fields[0]),arg=variable(inner,0);
				auto lo=primitive(arena.le(arena.natural_(0),arena.natural_(0)),[scalar(inner,arena.at(nodes[nodes[bandLowerTest].b].data)),arg]);
				auto hi=primitive(arena.at(nodes[bandUpperTest].data),[arg,scalar(inner,arena.at(nodes[nodes[bandUpperTest].b].data))]);
				auto pred=primitive(arena.and_(arena.boolean(true),arena.boolean(true)),[lo,hi]);
				auto output=inheritHint(at(n.a),lambda(guard(pred,scalar(inner,arena.at(nodes[bandBase].data)))));
				solution=RecurrenceSolution(t.id,output.id,bandBase,nodes[bandUpperTest].b,Law.init,Law.init,false,true,2,nodes[bandLowerTest].b); return output;
			}
		}
		if(!call(body.a,Builtin.addN)) return BoundTerm.init;
		auto sum=nodes[body.a]; if(!unary(sum.a,Op.mask)||!unary(sum.b,Op.mask)) return BoundTerm.init;
		auto yes=nodes[sum.a],no=nodes[sum.b],p=nodes[yes.a];
		if(!unary(yes.a,Op.not_)||!unary(no.a,Op.not_)||nodes[no.a].a!=yes.a) return BoundTerm.init;
		if(!call(p.a,Builtin.nonzeroZ)||!call(nodes[p.a].a,Builtin.castNZ)||!variableAt(nodes[nodes[p.a].a].a,0)) return BoundTerm.init;
		if(!totalScalar(at(yes.b))||!call(no.b,Builtin.addN)&&!call(no.b,Builtin.mulN)) return BoundTerm.init;
		if(call(no.b,Builtin.addN)){
			auto branch=nodes[no.b],down=nodes[branch.a],up=nodes[branch.b];
			if(unary(branch.a,Op.mask)&&unary(branch.b,Op.mask)&&(call(down.a,Builtin.leN)||call(down.a,Builtin.ltN))&&
				unary(up.a,Op.not_)&&nodes[up.a].a==down.a&&previous(down.b)){
				auto condition=nodes[down.a],forward=nodes[up.b];
				if(variableAt(condition.a,0)&&totalScalar(at(condition.b))&&forward.op==BoundOp.apply&&
					variableAt(forward.a,1)&&call(forward.b,Builtin.addN)){
					auto successor=nodes[forward.b],one=nodes[successor.b];
					if(variableAt(successor.a,0)&&one.op==BoundOp.scalar&&arena.isNumber(arena.at(one.data))&&arena.number(arena.at(one.data)).one){
						bool strict=call(down.a,Builtin.ltN); ulong upper; if(strict&&(!literal(condition.b,upper)||!upper)) return BoundTerm.init;
						auto inner=push(context(t),ty.fields[0]);
						auto predicate=primitive(arena.at(condition.data),[variable(inner,0),scalar(inner,arena.at(nodes[condition.b].data))]);
						auto output=inheritHint(at(n.a),lambda(guard(predicate,scalar(inner,arena.at(nodes[yes.b].data)))));
						solution=RecurrenceSolution(t.id,output.id,yes.b,condition.b,Law.init,Law.init,false,true,cast(ubyte)(strict?1:0)); return output;
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
	private bool recurrenceConstant(Term t){
		auto q=arena.view(t); if(arena.isNumber(t)||q.op==Op.variable) return true;
		if(q.op!=Op.add&&q.op!=Op.mul&&q.op!=Op.pow&&q.op!=Op.abs&&q.op!=Op.conj&&!(q.op==Op.builtin&&builtinInfo(cast(Builtin)q.value).total)) return false;
		foreach(i;0..q.arity) if(!recurrenceConstant(arena.viewChild(t,i))) return false; return true;
	}
	private bool recurrenceBranches(uint id,out uint test,out uint yes,out uint no,out bool reverse){
		auto q=nodes[id]; if(q.op!=BoundOp.primitive||q.b==uint.max) return false;
		auto kind=arena.view(arena.at(q.data)),add=arena.view(scalarOperator(types[q.type],TensorOp.add));
		if(kind.op!=add.op||kind.value!=add.value) return false;
		bool op(uint id,Op f){ auto n=nodes[id]; return n.op==BoundOp.primitive&&arena.view(arena.at(n.data)).op==f; }
		if(!op(q.a,Op.mask)||!op(q.b,Op.mask)) return false;
		auto x=nodes[q.a],y=nodes[q.b];
		if(op(y.a,Op.not_)&&nodes[y.a].a==x.a){ test=x.a; yes=x.b; no=y.b; return true; }
		if(op(x.a,Op.not_)&&nodes[x.a].a==y.a){ test=y.a; yes=y.b; no=x.b; reverse=true; return true; }
		return false;
	}
	private BoundTerm solveAffineRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),body=node(at(n.a)),ty=pool.view(type(t));
		if(ty.fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(ty.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		if(!numeric) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool op(uint id,Op f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==f; }
		bool variableAt(uint id,uint index){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==index; }
		bool arithmetic(uint id,bool mul){ return sort==Sort.natural?call(id,mul?Builtin.mulN:Builtin.addN):sort==Sort.integer?call(id,mul?Builtin.mulZ:Builtin.addZ):sort==Sort.rational?call(id,mul?Builtin.mulQ:Builtin.addQ):op(id,mul?Op.mul:Op.add); }
		bool constant(uint id){ auto q=nodes[id]; return q.op==BoundOp.scalar&&recurrenceConstant(arena.at(q.data)); }
		if(!arithmetic(body.a,false)) return BoundTerm.init;
		auto sum=nodes[body.a]; if(!op(sum.a,Op.mask)||!op(sum.b,Op.mask)) return BoundTerm.init;
		auto yes=nodes[sum.a],no=nodes[sum.b],p=nodes[yes.a];
		if(!op(yes.a,Op.not_)||!op(no.a,Op.not_)||nodes[no.a].a!=yes.a) return BoundTerm.init;
		if(!call(p.a,Builtin.nonzeroZ)||!call(nodes[p.a].a,Builtin.castNZ)||!variableAt(nodes[nodes[p.a].a].a,0)||!constant(yes.b)) return BoundTerm.init;
		auto zero=arena.number(Number(0),sort),one=arena.number(Number(1),sort); bool recursive;
		Law[3] laws;
		final switch(sort){
			case Sort.natural:laws=[Law.natural_affine_add,Law.natural_affine_left,Law.natural_affine_right]; break;
			case Sort.integer:laws=[Law.integer_affine_add,Law.integer_affine_left,Law.integer_affine_right]; break;
			case Sort.rational:laws=[Law.rational_affine_add,Law.rational_affine_left,Law.rational_affine_right]; break;
			case Sort.real_:laws=[Law.real_affine_add,Law.real_affine_left,Law.real_affine_right]; break;
			case Sort.complex:laws=[Law.complex_affine_add,Law.complex_affine_left,Law.complex_affine_right]; break;
			case Sort.boolean,Sort.density,Sort.measure:assert(0);
		}
		void coefficients(Law law,Term[] args,out Term coefficient,out Term offset){
			auto expression=instantiate(arena,law,args~one,true).result;
			coefficient=arena.viewChild(arena.viewChild(expression,0),0); offset=arena.viewChild(expression,1);
		}
		bool collect(uint id,out Term coefficient,out Term offset){
			auto q=nodes[id];
			if(constant(id)){ coefficient=zero; offset=arena.at(q.data); return true; }
			if(q.op==BoundOp.apply&&variableAt(q.a,1)&&call(q.b,Builtin.subN)){
				auto arg=nodes[q.b],amount=nodes[arg.b];
				if(variableAt(arg.a,0)&&amount.op==BoundOp.scalar&&arena.isNumber(arena.at(amount.data))&&arena.number(arena.at(amount.data)).one){ coefficient=one; offset=zero; recursive=true; return true; }
			}
			if(arithmetic(id,false)){
				Term a,b,c,d; if(!collect(q.a,a,b)||!collect(q.b,c,d)) return false;
				coefficients(laws[0],[a,b,c,d],coefficient,offset); return true;
			}
			if(arithmetic(id,true)){
				bool left=constant(q.a); auto c=left?q.a:q.b,child=left?q.b:q.a;
				if(!constant(c)||!collect(child,coefficient,offset)) return false;
				auto value=arena.at(nodes[c].data);
				coefficients(laws[left?1:2],left?[value,coefficient,offset]:[coefficient,offset,value],coefficient,offset); return true;
			}
			return false;
		}
		Term coefficient,offset; if(!collect(no.b,coefficient,offset)||!recursive) return BoundTerm.init;
		auto inner=push(context(t),ty.fields[0]),vec=pool.vector(ty.fields[1],2),mat=pool.vector(vec,2);
		auto row0=tuple(inner,[scalar(inner,coefficient),scalar(inner,offset)],vec);
		auto row1=tuple(inner,[scalar(inner,zero),scalar(inner,one)],vec);
		auto matrix=tuple(inner,[row0,row1],mat),initial=tuple(inner,[scalar(inner,arena.at(nodes[yes.b].data)),scalar(inner,one)],vec);
		auto output=inheritHint(at(n.a),lambda(get(tensor(TensorOp.matvec,tensor(TensorOp.power,matrix,variable(inner,0)),initial),scalar(inner,arena.natural_(0)))));
		solution=RecurrenceSolution(t.id,output.id,yes.b,no.b); solution.affine=true; return output;
	}
	// Preserve arbitrary additive forcing as a finite prefix sum. Unlike a
	// closed-form guess, this also handles partial and uninterpreted summands.
	private BoundTerm solvePrefixRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),ty=pool.view(type(t)); if(ty.fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(ty.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		if(!numeric) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool op(uint id,Op f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==f; }
		bool variableAt(uint id,uint index){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==index; }
		bool add(uint id){ return sort==Sort.natural?call(id,Builtin.addN):sort==Sort.integer?call(id,Builtin.addZ):sort==Sort.rational?call(id,Builtin.addQ):op(id,Op.add); }
		auto body=nodes[n.a]; if(body.op!=BoundOp.lambda||!add(body.a)) return BoundTerm.init;
		auto sum=nodes[body.a]; if(!op(sum.a,Op.mask)||!op(sum.b,Op.mask)) return BoundTerm.init;
		auto yes=nodes[sum.a],no=nodes[sum.b],p=nodes[yes.a];
		if(!op(yes.a,Op.not_)||!op(no.a,Op.not_)||nodes[no.a].a!=yes.a||!call(p.a,Builtin.nonzeroZ)||!call(nodes[p.a].a,Builtin.castNZ)||!variableAt(nodes[nodes[p.a].a].a,0)||depends(at(yes.b),0)||depends(at(yes.b),1)||!add(no.b)) return BoundTerm.init;
		auto step=nodes[no.b];
		bool recursive(uint id){
			auto q=nodes[id]; if(q.op!=BoundOp.apply||!variableAt(q.a,1)||!call(q.b,Builtin.subN)) return false;
			auto arg=nodes[q.b],amount=nodes[arg.b];
			return variableAt(arg.a,0)&&amount.op==BoundOp.scalar&&arena.isNumber(arena.at(amount.data))&&arena.number(arena.at(amount.data)).one;
		}
		bool reverse=recursive(step.b); auto forcing=reverse?step.a:step.b;
		if(!(reverse||recursive(step.a))||depends(at(forcing),1)) return BoundTerm.init;
		auto outer=context(t),inner=push(outer,scalarType(Sort.natural)),summandScope=push(inner,scalarType(Sort.natural));
		BoundTerm[] baseValues=[scalar(inner,arena.natural_(0)),bottom(inner,type(t))];
		foreach(i;0..depth(outer)) baseValues~=variable(inner,i+1);
		auto base=substitute(at(yes.b),inner,baseValues);
		auto successor=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(summandScope,0),scalar(summandScope,arena.natural_(1))]);
		BoundTerm[] values=[successor,bottom(summandScope,type(t))];
		foreach(i;0..depth(outer)) values~=variable(summandScope,i+2);
		auto summand=lambda(substitute(at(forcing),summandScope,values));
		auto prefix=finiteSum(summand,variable(inner,0));
		auto output=inheritHint(at(n.a),lambda(primitive(scalarOperator(ty.fields[1],TensorOp.add),[base,prefix])));
		solution=RecurrenceSolution(t.id,output.id,yes.b,forcing); solution.prefix=true; solution.left=reverse; return output;
	}
	private BoundTerm solveLinearRecurrence(BoundTerm t,out RecurrenceSolution solution){
		auto n=node(t),ty=pool.view(type(t)); if(ty.fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
		Sort sort; bool numeric;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex]) if(ty.fields[1]==scalarType(s)){ sort=s; numeric=true; }
		if(!numeric) return BoundTerm.init;
		bool call(uint id,Builtin f){ auto q=nodes[id]; return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f; }
		bool variableAt(uint id,uint index){ auto q=nodes[id]; return q.op==BoundOp.variable&&q.data==index; }
		bool constant(uint id){ auto q=nodes[id]; return q.op==BoundOp.scalar&&recurrenceConstant(arena.at(q.data)); }
		bool arithmetic(uint id,bool mul){
			auto q=nodes[id]; if(q.op!=BoundOp.primitive) return false;
			auto a=arena.view(arena.at(q.data)),b=arena.view(scalarOperator(ty.fields[1],mul?TensorOp.mul:TensorOp.add)); return a.op==b.op&&a.value==b.value;
		}
		uint lag(uint id){
			auto q=nodes[id]; if(q.op!=BoundOp.apply||!variableAt(q.a,1)||!call(q.b,Builtin.subN)) return 0;
			auto arg=nodes[q.b],amount=nodes[arg.b]; if(!variableAt(arg.a,0)||amount.op!=BoundOp.scalar) return 0;
			auto v=arena.at(amount.data); if(!arena.isNumber(v)) return 0;
			auto k=arena.number(v).re.integer; return k>0&&k<=16?cast(uint)k:0;
		}
		auto body=nodes[n.a].a,tail=body; uint test,yes,no; bool reverse;
		while(recurrenceBranches(tail,test,yes,no,reverse)){
			if(depends(at(yes),1)==depends(at(no),1)||depends(at(test),1)) break;
			tail=depends(at(yes),1)?yes:no;
		}
		if(tail==body) return BoundTerm.init;
		uint order;
		bool scan(uint id){
			if(constant(id)) return true;
			auto k=lag(id); if(k){ if(k>order) order=k; return true; }
			auto q=nodes[id]; if(arithmetic(id,false)) return scan(q.a)&&scan(q.b);
			return arithmetic(id,true)&&((constant(q.a)&&scan(q.b))||(constant(q.b)&&scan(q.a)));
		}
		if(!scan(tail)||!order) return BoundTerm.init;
		uint variableIndex;
		foreach(id;0..arena.length){ auto q=arena.view(arena.at(cast(uint)id)); if(q.op==Op.variable){ enforce(q.value<uint.max-1,"scalar variable limit exceeded"); if(q.value>=variableIndex) variableIndex=cast(uint)q.value+1; } }
		auto argument=arena.variable(Sort.natural,variableIndex);
		RecurrenceFact[] facts; Term[] seeds;
		bool fact(uint id,uint index,out Term output){
			auto arg=index==uint.max?arena.call(Builtin.addN,[argument,arena.natural_(order)]):arena.natural_(index);
			auto input=scalarBody(at(id),arg); if(input==Term.init) return false;
			auto options=Options(DensityMode.preserve,true),d=simplifyDomain(arena,input,[],options),v=simplify(arena,input,options);
			if(d.exhausted||v.exhausted||d.output!=arena.boolean(true)) return false;
			output=arena.castTo(v.output,arena.sort(input)); facts~=RecurrenceFact(id,index,input,d,v); return true;
		}
		bool prefix(){
			facts=null; seeds=null;
			auto id=body; Term output;
			while(id!=tail){
				if(!recurrenceBranches(id,test,yes,no,reverse)||!fact(test,uint.max,output)) return false;
				auto next=output==arena.boolean(true)?yes:output==arena.boolean(false)?no:uint.max;
				if(next==uint.max||!depends(at(next),1)) return false; id=next;
			}
			foreach(i;0..order){
				id=body;
				while(depends(at(id),1)){
					if(id==tail||!recurrenceBranches(id,test,yes,no,reverse)||!fact(test,i,output)) return false;
					id=output==arena.boolean(true)?yes:output==arena.boolean(false)?no:uint.max; if(id==uint.max) return false;
				}
				if(!fact(id,i,output)||!recurrenceConstant(output)) return false; seeds~=output;
			}
			return true;
		}
		for(;order<=16;++order) if(prefix()) break;
		if(order>16) return BoundTerm.init;
		auto zero=arena.number(Number(0),sort),one=arena.number(Number(1),sort);
		Law[3] laws;
		final switch(sort){
			case Sort.natural:laws=[Law.natural_affine_add,Law.natural_affine_left,Law.natural_affine_right]; break;
			case Sort.integer:laws=[Law.integer_affine_add,Law.integer_affine_left,Law.integer_affine_right]; break;
			case Sort.rational:laws=[Law.rational_affine_add,Law.rational_affine_left,Law.rational_affine_right]; break;
			case Sort.real_:laws=[Law.real_affine_add,Law.real_affine_left,Law.real_affine_right]; break;
			case Sort.complex:laws=[Law.complex_affine_add,Law.complex_affine_left,Law.complex_affine_right]; break;
			case Sort.boolean,Sort.density,Sort.measure:assert(0);
		}
		void coefficients(Law law,Term[] args,out Term coefficient,out Term offset){
			auto expression=instantiate(arena,law,args~one,true).result;
			coefficient=arena.viewChild(arena.viewChild(expression,0),0); offset=arena.viewChild(expression,1);
		}
		void collect(uint id,out Term[] c,out Term b){
			c=new Term[order]; c[]=zero; b=zero; auto q=nodes[id];
			if(constant(id)){ b=arena.at(q.data); return; }
			auto k=lag(id); if(k){ c[order-k]=one; return; }
			Term[] x,y; Term u,v;
			if(arithmetic(id,false)){
				collect(q.a,x,u); collect(q.b,y,v);
				foreach(i;0..order) coefficients(laws[0],[x[i],u,y[i],v],c[i],b);
			}else{
				bool left=constant(q.a); auto value=arena.at(nodes[left?q.a:q.b].data); collect(left?q.b:q.a,x,u);
				foreach(i;0..order) coefficients(laws[left?1:2],left?[value,x[i],u]:[x[i],u,value],c[i],b);
			}
		}
		Term[] coefficients_; Term offset; collect(tail,coefficients_,offset);
		auto inner=push(context(t),ty.fields[0]),vec=pool.vector(ty.fields[1],order+1),mat=pool.vector(vec,order+1);
		BoundTerm[] rows;
		foreach(i;0..order+1){
			BoundTerm[] cells;
			foreach(j;0..order+1){
				auto value=i==order?(j==order?one:zero):i+1==order?(j==order?offset:coefficients_[j]):j==i+1?one:zero;
				cells~=scalar(inner,value);
			}
			rows~=tuple(inner,cells,vec);
		}
		BoundTerm[] values; foreach(seed;seeds) values~=scalar(inner,seed); values~=scalar(inner,one);
		auto matrix=tuple(inner,rows,mat),initial=tuple(inner,values,vec);
		auto output=inheritHint(at(n.a),lambda(get(tensor(TensorOp.matvec,tensor(TensorOp.power,matrix,variable(inner,0)),initial),scalar(inner,arena.natural_(0)))));
		solution=RecurrenceSolution(t.id,output.id,0,tail); solution.order=order; solution.variable=variableIndex; solution.seeds=seeds; solution.facts=facts; return output;
	}
	private bool literalNumber(Term t,out Number value){
		if(arena.isNumber(t)){ value=arena.number(t); return true; }
		auto q=arena.view(t); return q.op==Op.builtin&&q.value>=Builtin.castNZ&&q.value<=Builtin.castRC&&literalNumber(arena.viewChild(t,0),value);
	}
	private BoundTerm spectral(BoundTerm t,out SpectralSolution solution){
		auto n=node(t); if(n.op!=BoundOp.tensor||n.data!=TensorOp.matvec) return BoundTerm.init;
		auto p=nodes[n.a]; if(p.op!=BoundOp.tensor||p.data!=TensorOp.power||!definitionallyTotal(at(p.b))) return BoundTerm.init;
		auto mt=pool.view(type(at(p.a))),row=pool.view(mt.fields[0]);
		if(!mt.dimension.constant||!row.dimension.constant||!mt.length||mt.length>16||mt.length!=row.length) return BoundTerm.init;
		auto size=cast(uint)mt.length,sort=elementSort(row.fields[0]),ctx=context(t);
		solution=SpectralSolution(t.id,0,size); solution.diagonal=true;
		bool elements(uint id,uint count,out uint[] values){
			foreach(i;0..count){ auto q=nodes[id]; if(q.op!=BoundOp.vectorCons) return false; values~=q.a; id=q.b; }
			return nodes[id].op==BoundOp.vectorNil;
		}
		uint[] rows,values; if(!elements(p.a,size,rows)||!elements(n.b,size,values)) return BoundTerm.init;
		foreach(i,r;rows){
			uint[] cells; if(!elements(r,size,cells)) return BoundTerm.init;
			foreach(j,c;cells){
				if(nodes[c].op!=BoundOp.scalar) return BoundTerm.init;
				auto v=arena.at(nodes[c].data); solution.matrix~=v;
				Number number; if(i!=j&&(!literalNumber(v,number)||!number.zero)) solution.diagonal=false;
			}
		}
		foreach(v;values){ if(nodes[v].op!=BoundOp.scalar) return BoundTerm.init; solution.vector~=arena.at(nodes[v].data); }
		if(!solution.diagonal){
			if(size==3){
				Number[9] entries; bool numeric=true;
				foreach(i,v;solution.matrix) if(!literalNumber(v,entries[i])) numeric=false;
				if(numeric){
					solution.cubeZero=true;
					foreach(i;0..3) foreach(j;0..3){
						auto entry=Number(0);
						foreach(k;0..3) foreach(l;0..3) entry=entry+entries[i*3+k]*entries[k*3+l]*entries[l*3+j];
						if(!entry.zero) solution.cubeZero=false;
					}
				}
			}
			// Keep unsupported scalar mask normalizations symbolic: nonreal complex coefficients
			// and symbolic real/complex seeds can exhaust the scalar normalizer.
			if(solution.cubeZero&&(sort==Sort.real_||sort==Sort.complex)) foreach(v;solution.vector){
				Number value; if(!literalNumber(v,value)||sort==Sort.complex&&!value.im.zero) solution.cubeZero=false;
			}
			if(solution.cubeZero&&sort==Sort.complex) foreach(v;solution.matrix){
				Number value; if(!literalNumber(v,value)||!value.im.zero) solution.cubeZero=false;
			}
			if(size>3) foreach(k;1..size){
				bool separate=true;
				foreach(i;0..size) foreach(j;0..size) if((i<k)!=(j<k)){
					Number number; if(!literalNumber(solution.matrix[i*size+j],number)||!number.zero) separate=false;
				}
				if(separate){ solution.split=k; break; }
			}
			if(!solution.split&&!solution.cubeZero){
				if(size>3||sort==Sort.natural||sort==Sort.integer) return BoundTerm.init;
				foreach(v;solution.matrix){ Number number; if(!literalNumber(v,number)) return BoundTerm.init; }
				if(size==3){
					bool block=true;
					foreach(i;[2,5,6,7]){ Number number; literalNumber(solution.matrix[i],number); if(!number.zero) block=false; }
					if(!block){
						Number[] a; foreach(v;solution.matrix){ Number number; literalNumber(v,number); a~=number; }
						auto determinant=a[0]*(a[4]*a[8]-a[5]*a[7])-a[1]*(a[3]*a[8]-a[5]*a[6])+a[2]*(a[3]*a[7]-a[4]*a[6]);
						auto trace=a[0]+a[4]+a[8],pairs=a[0]*a[4]+a[0]*a[8]+a[4]*a[8]-a[1]*a[3]-a[2]*a[6]-a[5]*a[7];
						if(!determinant.zero||pairs.zero||(trace*trace-Number(4)*pairs).zero) return BoundTerm.init;
						// Literal inputs bound coefficient normalization; every candidate is certified below.
						foreach(v;solution.vector){ Number number; if(!literalNumber(v,number)) return BoundTerm.init; }
						solution.zeroRoot=true;
					}
				}
			}
		}
		auto options=Options(DensityMode.preserve,true);
		Table!(uint,uint) parameters;
		bool parameter(Term t){
			if(parameters.get(t.id,uint.max)!=uint.max) return true;
			auto d=simplifyDomain(arena,t,[],options); if(d.exhausted||d.output!=arena.boolean(true)) return false;
			parameters.set(t.id,cast(uint)solution.parameters.length); solution.parameters~=SpectralFact(t,d); return true;
		}
		foreach(v;solution.matrix) if(!parameter(v)) return BoundTerm.init;
		foreach(v;solution.vector) if(!parameter(v)) return BoundTerm.init;
		if(solution.split){
			BoundTerm[] output;
			foreach(part;0..2){
				auto start=part?solution.split:0,count=part?size-solution.split:solution.split,vec=pool.vector(row.fields[0],count),mat=pool.vector(vec,count);
				BoundTerm[] blockRows,seed;
				foreach(i;start..start+count){
					BoundTerm[] cells; foreach(j;start..start+count) cells~=scalar(ctx,solution.matrix[i*size+j]);
					blockRows~=tuple(ctx,cells,vec); seed~=scalar(ctx,solution.vector[i]);
				}
				auto a=tuple(ctx,blockRows,mat),x=tuple(ctx,seed,vec);
				solution.blocks[part]=a.id; solution.blocks[part+2]=x.id;
				auto value=tensor(TensorOp.matvec,tensor(TensorOp.power,a,at(p.b)),x);
				foreach(i;0..count) output~=get(value,scalar(ctx,arena.natural_(i)));
			}
			auto result=tuple(ctx,output,type(t)); solution.target=result.id; return result;
		}
		auto zero=arena.number(Number(0),sort),neg=arena.number(Number(sort==Sort.natural?0:-1),sort);
		Term difference(Term a,Term b){ return arena.add(a,arena.mul(neg,b,true),true); }
		bool check(Term t,bool isZero){
			auto d=simplifyDomain(arena,t,[],options); if(d.exhausted||d.output!=arena.boolean(true)) return false;
			Result v;
			if(isZero){ v=simplify(arena,t,options); if(v.exhausted||!arena.isNumber(v.output)||!arena.number(v.output).zero) return false; }
			solution.checks~=SpectralFact(t,d,v); return true;
		}
		Term stepWith(Term[] matrix,Term[] vector,uint i){
			return arena.add(arena.add(arena.mul(matrix[i*3],vector[0],true),arena.mul(matrix[i*3+1],vector[1],true),true),arena.mul(matrix[i*3+2],vector[2],true),true);
		}
		Term step(Term[] vector,uint i){ return stepWith(solution.matrix,vector,i); }
		Term[] stepVector(Term[] vector){ Term[] result; foreach(i;0..3) result~=step(vector,i); return result; }
		if(solution.zeroRoot){
			Number[] a; foreach(v;solution.matrix){ Number number; literalNumber(v,number); a~=number; }
			auto trace=a[0]+a[4]+a[8],pairs=a[0]*a[4]+a[0]*a[8]+a[4]*a[8]-a[1]*a[3]-a[2]*a[6]-a[5]*a[7];
			auto rs=sort==Sort.complex?Sort.complex:Sort.real_;
			auto root=simplify(arena,arena.call(sort==Sort.complex?Builtin.sqrtC:Builtin.sqrtR,[arena.number(trace*trace-Number(4)*pairs,rs)]),options);
			if(root.exhausted||(sort==Sort.rational||sort==Sort.complex)&&!arena.isNumber(root.output)) return BoundTerm.init;
			// Irrational or nonreal complex components currently exceed scalar normalization budgets.
			if(sort==Sort.complex){
				if(!arena.number(root.output).im.zero) return BoundTerm.init;
				foreach(v;solution.matrix~solution.vector){ Number value; if(!literalNumber(v,value)||!value.im.zero) return BoundTerm.init; }
			}
			auto delta=arena.isNumber(root.output)?arena.number(arena.number(root.output),sort):arena.castTo(root.output,sort),half=arena.number(Number(1)/Number(2),sort);
			Term compact(Term x){ auto r=simplify(arena,x,options); return r.exhausted?Term.init:arena.castTo(r.output,sort); }
			auto r=compact(arena.mul(arena.add(arena.number(trace,sort),delta),half)),s=compact(arena.mul(difference(arena.number(trace,sort),delta),half));
			if(r==Term.init||s==Term.init) return BoundTerm.init;
			solution.roots=[zero,r,s]; solution.minus=neg;
			auto first=stepVector(solution.vector),second=stepVector(first); Term[][3] parts;
			foreach(i;0..3){
				auto cr=compact(arena.mul(difference(second[i],arena.mul(s,first[i],true)),arena.inv(arena.mul(r,difference(r,s),true)),true));
				auto cs=compact(arena.mul(difference(arena.mul(r,first[i],true),second[i]),arena.inv(arena.mul(s,difference(r,s),true)),true));
				if(cr==Term.init||cs==Term.init) return BoundTerm.init;
				auto c0=compact(difference(difference(solution.vector[i],cr),cs)); if(c0==Term.init) return BoundTerm.init;
				parts[0]~=c0; parts[1]~=cr; parts[2]~=cs;
			}
			foreach(part;parts) solution.components~=part;
			foreach(v;solution.roots~solution.components~[neg]) if(!parameter(v)) return BoundTerm.init;
			foreach(i;0..3) if(!check(difference(arena.add(arena.add(parts[0][i],parts[1][i],true),parts[2][i],true),solution.vector[i]),true)) return BoundTerm.init;
			foreach(j;0..3) foreach(i;0..3) if(!check(difference(step(parts[j],i),arena.mul(solution.roots[j],parts[j][i],true)),true)) return BoundTerm.init;
		}else if(solution.cubeZero){
			// Numeric detection is only a candidate filter; certify all nine entries of A³.
			foreach(i;0..3) foreach(j;0..3){
				Term[] column; foreach(k;0..3) column~=solution.matrix[k*3+j];
				if(!check(step(stepVector(column),i),true)) return BoundTerm.init;
			}
		}else if(!solution.diagonal){
			auto a=solution.matrix[0],b=solution.matrix[1],c=solution.matrix[size],d=solution.matrix[size+1];
			Number av,bv,cv,dv; literalNumber(a,av); literalNumber(b,bv); literalNumber(c,cv); literalNumber(d,dv);
			auto trace=arena.number(av+dv,sort);
			auto discriminant=(av-dv)*(av-dv)+Number(4)*bv*cv;
			solution.repeated=discriminant.zero;
			solution.nilpotent=solution.repeated&&(av+dv).zero;
			auto rs=sort==Sort.complex?Sort.complex:Sort.real_;
			auto root=arena.call(sort==Sort.complex?Builtin.sqrtC:Builtin.sqrtR,[arena.number(discriminant,rs)]);
			auto simple=simplify(arena,root,options); if(simple.exhausted) return BoundTerm.init;
			if(sort==Sort.rational&&!arena.isNumber(simple.output)) return BoundTerm.init;
			root=arena.isNumber(simple.output)?arena.number(arena.number(simple.output),sort):arena.castTo(simple.output,sort);
			auto half=arena.number(Number(1)/Number(2),sort);
			solution.first=arena.mul(arena.add(trace,root),half); solution.second=arena.mul(difference(trace,root),half); solution.minus=neg;
			if(solution.repeated) solution.first=solution.second=arena.number((av+dv)/Number(2),sort);
			if(!parameter(solution.first)||!parameter(solution.second)||!parameter(neg)) return BoundTerm.init;
			if(!check(difference(arena.add(a,d,true),arena.add(solution.first,solution.second,true)),true)||
				!check(difference(difference(arena.mul(a,d,true),arena.mul(b,c,true)),arena.mul(solution.first,solution.second,true)),true)||
				(!solution.nilpotent&&!check(arena.inv(solution.repeated?solution.first:difference(solution.first,solution.second)),false))) return BoundTerm.init;
		}
		uint index;
		foreach(id;0..arena.length){ auto q=arena.view(arena.at(cast(uint)id)); if(q.op==Op.variable){ enforce(q.value<uint.max-1,"scalar variable limit exceeded"); if(q.value>=index) index=cast(uint)q.value+1; } }
		auto argument=arena.variable(Sort.natural,index),exponent=at(p.b);
		BoundTerm restore(Term v){
			if(v==argument) return exponent;
			auto q=arena.view(v); if(!q.arity) return scalar(ctx,v);
			BoundTerm[] args; bool plain=true;
			foreach(i;0..q.arity){ auto a=restore(arena.viewChild(v,i)); plain&=node(a).op==BoundOp.scalar; args~=a; }
			if(!plain) return primitive(v,args);
			Term[] values; foreach(a;args) values~=arena.at(node(a).data);
			return scalar(ctx,arena.viewRebuild(v,values,true));
		}
		auto power=sort==Sort.natural?Builtin.powNN:sort==Sort.integer?Builtin.powZN:sort==Sort.rational?Builtin.powQN:sort==Sort.real_?Builtin.powRN:Builtin.powCN;
		Term[] square;
		if(solution.cubeZero) foreach(i;0..3) foreach(j;0..3){
			Term[] column; foreach(k;0..3) column~=solution.matrix[k*3+j];
			square~=step(column,i);
		}
		Term[] firstValues,secondValues;
		if(solution.cubeZero){
			// Simplify the coefficients before introducing masks, and retain their equality certificates.
			foreach(matrix;[solution.matrix,square]) foreach(i;0..3){
				auto term=stepWith(matrix,solution.vector,i),domain=simplifyDomain(arena,term,[],options),value=simplify(arena,term,options);
				if(domain.exhausted||domain.output!=arena.boolean(true)||value.exhausted) return BoundTerm.init;
				solution.checks~=SpectralFact(term,domain,value);
				if(solution.checks.length<=12) firstValues~=arena.castTo(value.output,sort); else secondValues~=arena.castTo(value.output,sort);
			}
		}
		BoundTerm[] output;
		foreach(i;0..size){
			Term value;
			if(solution.zeroRoot){
				Term part(uint j){ return arena.mul(arena.call(power,[solution.roots[j],argument]),solution.components[j*3+i],true); }
				value=arena.add(arena.add(part(0),part(1),true),part(2),true);
			}else if(solution.cubeZero){
				Term atIndex(uint k){ auto literal=arena.natural_(k); return arena.and_(arena.le(literal,argument),arena.le(argument,literal)); }
				value=arena.add(arena.add(arena.mask(atIndex(0),solution.vector[i]),arena.mask(atIndex(1),firstValues[i]),true),arena.mask(atIndex(2),secondValues[i]),true);
			}else if(solution.diagonal||i==2) value=arena.mul(arena.call(power,[solution.matrix[i*size+i],argument]),solution.vector[i],true);
			else{
				auto first=arena.add(arena.mul(solution.matrix[i*size],solution.vector[0],true),arena.mul(solution.matrix[i*size+1],solution.vector[1],true),true);
				if(solution.nilpotent){
					// A²=0: retain both boundary values without dividing by the zero eigenvalue.
					auto one=arena.natural_(1);
					auto atZero=arena.not_(arena.nonzero(argument));
					auto atOne=arena.and_(arena.le(one,argument),arena.le(argument,one));
					value=arena.add(arena.mask(atZero,solution.vector[i]),arena.mask(atOne,first),true);
				}else if(solution.repeated){
					auto law=sort==Sort.rational?Law.rational_spectral_repeated:sort==Sort.real_?Law.real_spectral_repeated:Law.complex_spectral_repeated;
					value=instantiate(arena,law,[solution.vector[i],first,solution.first,argument],true).result;
				}else{
					auto law=sort==Sort.rational?Law.rational_spectral_interpolation:sort==Sort.real_?Law.real_spectral_interpolation:Law.complex_spectral_interpolation;
					value=instantiate(arena,law,[solution.vector[i],first,solution.first,solution.second,argument],true).result;
				}
			}
			output~=restore(value);
		}
		auto result=tuple(ctx,output,type(t)); solution.target=result.id; return result;
	}
	private BoundTerm liftSpectrum(BoundTerm t,out uint promoted){
		auto n=node(t); if(n.op!=BoundOp.tensor||n.data!=TensorOp.matvec) return BoundTerm.init;
		auto p=nodes[n.a]; if(p.op!=BoundOp.tensor||p.data!=TensorOp.power||!definitionallyTotal(at(p.b))) return BoundTerm.init;
		auto mt=pool.view(type(at(p.a))),row=pool.view(mt.fields[0]),sort=elementSort(row.fields[0]);
		if(sort!=Sort.natural&&sort!=Sort.integer||!mt.dimension.constant||!row.dimension.constant||mt.length<2||mt.length>3||mt.length!=row.length) return BoundTerm.init;
		auto ctx=context(t),size=cast(uint)mt.length;
		Term[] coefficients;
		bool entries(uint id,uint depth){
			if(!depth){ if(nodes[id].op!=BoundOp.scalar) return false; coefficients~=arena.at(nodes[id].data); return true; }
			foreach(i;0..size){ auto v=nodes[id]; if(v.op!=BoundOp.vectorCons||!entries(v.a,depth-1)) return false; id=v.b; }
			return nodes[id].op==BoundOp.vectorNil;
		}
		if(!entries(p.a,2)) return BoundTerm.init;
		Number[] values; foreach(c;coefficients){ Number v; if(!literalNumber(c,v)) return BoundTerm.init; values~=v; }
		auto delta=(values[0]-values[size+1])*(values[0]-values[size+1])+Number(4)*values[1]*values[size];
		if(size==3){
			bool block=true; foreach(i;[2,5,6,7]) if(!values[i].zero) block=false;
			if(!block){
				auto a=values,trace=a[0]+a[4]+a[8],pairs=a[0]*a[4]+a[0]*a[8]+a[4]*a[8]-a[1]*a[3]-a[2]*a[6]-a[5]*a[7];
				delta=trace*trace-Number(4)*pairs;
			}
		}
		auto target=delta.re<Rational(0)?Sort.complex:Sort.real_,leaf=scalarType(target),vec=pool.vector(leaf,size),mat=pool.vector(vec,size);
		BoundTerm lift(uint id,uint depth){
			auto v=nodes[id];
			if(!depth){ if(v.op!=BoundOp.scalar) return BoundTerm.init; Number value; if(!literalNumber(arena.at(v.data),value)) return BoundTerm.init; return scalar(ctx,arena.castTo(arena.at(v.data),target)); }
			BoundTerm[] xs;
			foreach(i;0..size){ v=nodes[id]; if(v.op!=BoundOp.vectorCons) return BoundTerm.init; auto x=lift(v.a,depth-1); if(x==BoundTerm.init) return x; xs~=x; id=v.b; }
			if(nodes[id].op!=BoundOp.vectorNil) return BoundTerm.init;
			return tuple(ctx,xs,depth==1?vec:mat);
		}
		auto matrix=lift(p.a,2),initial=lift(n.b,1); if(matrix==BoundTerm.init||initial==BoundTerm.init) return BoundTerm.init;
		auto source=tensor(TensorOp.matvec,tensor(TensorOp.power,matrix,at(p.b)),initial);
		SpectralSolution probe; if(spectral(source,probe)==BoundTerm.init) return BoundTerm.init;
		BoundTerm[] output;
		foreach(i;0..size){
			auto value=get(source,scalar(ctx,arena.natural_(i)));
			if(target==Sort.complex) value=primitive(arena.call(Builtin.reC,[arena.complex(0)]),[value]);
			output~=primitive(arena.call(sort==Sort.natural?Builtin.floorN:Builtin.floorR,[arena.real_(0)]),[value]);
		}
		promoted=source.id; return tuple(ctx,output,type(t));
	}
	private bool definitionallyTotal(BoundTerm t){
		auto n=node(t);
		if(n.op==BoundOp.variable||n.op==BoundOp.global||n.op==BoundOp.lambda||n.op==BoundOp.typeValue||n.op==BoundOp.unit||n.op==BoundOp.vectorNil) return true;
		if(n.op==BoundOp.scalar) return totalScalar(t);
		return (n.op==BoundOp.vectorCons||n.op==BoundOp.pair)&&definitionallyTotal(at(n.a))&&definitionallyTotal(at(n.b));
	}
	private bool domainStrict(BoundNode n){
		if(n.op==BoundOp.sequence) return true;
		if(n.op!=BoundOp.primitive) return false;
		auto q=arena.view(arena.at(n.data));
		if(q.op==Op.builtin) return builtinInfo(cast(Builtin)q.value).total;
		return q.op==Op.add||q.op==Op.mul||q.op==Op.lt||q.op==Op.le||q.op==Op.nonzero||q.op==Op.not_||q.op==Op.conj||q.op==Op.abs||q.op==Op.pow;
	}
	private bool rankDomain(BoundTerm fixed_,out DomainRank rank){
		auto n=node(fixed_),ty=pool.view(type(fixed_));
		bool scalar;
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean]) if(ty.fields[0]==scalarType(s)){ rank.sort=s; scalar=true; break; }
		if(!scalar) return false;
		uint index;
		foreach(id;0..arena.length){ auto q=arena.view(arena.at(cast(uint)id)); if(q.op==Op.variable){ enforce(q.value<uint.max-1,"scalar variable limit exceeded"); if(q.value>=index) index=cast(uint)q.value+1; } }
		auto argument=arena.variable(rank.sort,index); rank.source=fixed_.id; rank.variable=index;
		Term leaf(uint id){
			foreach(d;rank.leaves) if(d.node==id) return d.domain.output;
			auto value=scalarBody(at(id),argument); if(value==Term.init) return Term.init;
			auto domain=simplifyDomain(arena,value,[],Options(DensityMode.preserve,true));
			if(domain.exhausted) return Term.init;
			rank.leaves~=DomainLeaf(id,value,domain); return domain.output;
		}
		Term substitute(Term t,Term value){
			Table!(uint,uint) memo;
			Term go(Term x){
				if(x==argument) return value;
				auto old=memo.get(x.id,uint.max); if(old!=uint.max) return arena.at(old);
				auto q=arena.view(x); Term[] cs;
				foreach(i;0..q.arity) cs~=go(arena.viewChild(x,i));
				auto y=cs.length?arena.viewRebuild(x,cs,true):x; memo.set(x.id,y.id); return y;
			}
			return go(t);
		}
		Term candidate; bool restricted;
		Term visit(uint id){
			auto q=nodes[id];
			if(!depends(at(id),1)) return leaf(id);
			if(q.op==BoundOp.apply){
				if(nodes[q.a].op!=BoundOp.variable||nodes[q.a].data!=1||depends(at(q.b),1)) return Term.init;
				auto d=leaf(q.b),value=scalarBody(at(q.b),argument);
				if(d==Term.init||value==Term.init) return Term.init;
				if(rank.step!=Term.init){
					auto x=arena.mul(rank.slope,argument,true),y=arena.mul(rank.slope,value,true);
					return arena.and_(d,arena.and_(arena.lt(rank.bound,x),arena.le(arena.add(y,rank.step,true),x)));
				}
				auto test=candidate==Term.init?arena.lt(value,argument):substitute(candidate,value);
				if(restricted) test=arena.and_(arena.lt(value,argument),test);
				return arena.and_(d,test);
			}
			auto op=q.op==BoundOp.primitive?arena.view(arena.at(q.data)).op:Op.variable;
			if(q.op==BoundOp.guard||op==Op.mask||op==Op.and_||op==Op.or_){
				if(depends(at(q.a),1)) return Term.init;
				auto dp=leaf(q.a),p=scalarBody(at(q.a),argument),d=visit(q.b);
				if(dp==Term.init||p==Term.init||d==Term.init) return Term.init;
				return q.op==BoundOp.guard?arena.and_(arena.and_(dp,p),d):arena.and_(dp,arena.or_(op==Op.or_?p:arena.not_(p),d));
			}
			if(!domainStrict(q)) return Term.init;
			auto x=visit(q.a); if(x==Term.init||q.b==uint.max) return x;
			auto y=visit(q.b); return y==Term.init?Term.init:arena.and_(x,y);
		}
		auto options=Options(DensityMode.preserve,true); options.maxRewrites=4096; options.maxAlgebraWork=65536;

		if(rank.sort==Sort.natural){
			auto condition=visit(nodes[n.a].a); if(condition==Term.init) return false;
			rank.result=simplify(arena,condition,[],options);
			auto out_=arena.view(rank.result.output);
			if(!rank.result.exhausted&&out_.op==Op.boolLit&&out_.value) return true;
			if(!rank.result.exhausted){
				candidate=rank.result.output; restricted=true;
				auto lower=simplify(arena,arena.or_(arena.not_(candidate),visit(nodes[n.a].a)),[],options);
				restricted=false;
				if(!lower.exhausted&&lower.output==arena.boolean(true)){
					auto upper=simplify(arena,arena.or_(arena.not_(visit(nodes[n.a].a)),candidate),[],options);
					if(!upper.exhausted&&upper.output==arena.boolean(true)){ rank.lower=lower; rank.upper=upper; return true; }
				}
				candidate=Term.init;
			}
		}
		if(rank.sort==Sort.real_){
			if(visit(nodes[n.a].a)==Term.init) return false;
			auto limit=Rational(0),step=Rational(1);
			foreach(l;rank.leaves){
				auto value=simplify(arena,l.value,options).output;
				foreach(id;arena.viewPostorder(value)) if(arena.isNumber(arena.at(id))){
					auto q=arena.number(arena.at(id)).re; if(q<Rational(0)) q=-q;
					if(q>limit) limit=q;
					if(q>Rational(0)&&q<step) step=q;
				}
			}
			rank.bound=arena.real_(-limit-Rational(1)); rank.step=arena.real_(step);
			foreach(slope;[1L,-1L]){
				rank.slope=arena.real_(slope);
				auto condition=visit(nodes[n.a].a); if(condition==Term.init) break;
				rank.result=simplify(arena,condition,[],options);
				if(!rank.result.exhausted&&rank.result.output==arena.boolean(true)) return true;
			}
			rank.slope=rank.bound=rank.step=Term.init;
		}
		candidate=arena.boolean(false);
		auto initial=arena.length;
		foreach(iteration;0..32){
			auto condition=visit(nodes[n.a].a); if(condition==Term.init) return false;
			auto step=simplify(arena,condition,[],options);
			if(step.exhausted||arena.length-initial>16384||arena.viewPostorder(step.output).length>256) return false;
			rank.iterations~=step;
			if(step.output==candidate) return true;
			candidate=step.output;
		}
		return false;
	}
	private BindingResult normalizeDependent(BoundTerm term,uint budget){
		uint steps; bool exhausted; Table!(uint,uint) memo;
		BoundTerm visit(BoundTerm t,uint depth=0){
			if(depth>=128||steps>=budget){ exhausted=true; return t; }
			auto old=memo.get(t.id,uint.max); if(old!=uint.max) return at(old);
			auto n=node(t); BoundTerm[] args;
			if(n.a!=uint.max) args~=visit(at(n.a),depth+1);
			if(n.b!=uint.max) args~=visit(at(n.b),depth+1);
			auto r=args.length?rebuild(t,context(t),args):t; n=node(r);
			if(n.op==BoundOp.apply&&nodes[n.a].op==BoundOp.lambda&&definitionallyTotal(at(n.b))){
				++steps; r=visit(beta(at(nodes[n.a].a),at(n.b)),depth+1);
			}else if(n.op==BoundOp.sequence&&definitionallyTotal(at(n.a))){ ++steps; r=at(n.b); }
			memo.set(t.id,r.id); return r;
		}
		auto output=visit(term); BindingResult r; r.input=term; r.output=output; r.exhausted=exhausted; return r;
	}
	BindingResult normalize(BoundTerm term,uint budget=4096,bool domains=false){
		if(telescope_) return normalizeDependent(term,budget);
		check(term); uint steps,fixedSteps; bool exhausted; BindingStep[] proofs; ScalarDomain[] scalarDomains; RecurrenceSolution[] solutions; DomainRank[] ranks; SpectralSolution[] spectra; SummationSolution[] sums;
		struct Result{ uint output,proof; }
		Table!(uint,Result) memo;
		Table!(uint,bool) active;
		uint emit(BindingRule rule,uint from,uint to,uint left=uint.max,uint right=uint.max,uint extra=uint.max){
			enforce(proofs.length<1_000_000,"binding proof limit exceeded");
			proofs~=BindingStep(rule,from,to,left,right,extra); return cast(uint)proofs.length-1;
		}
		Result delegate(BoundTerm,uint) @safe normalizeClosed;
		bool affineNaturalParts(BoundTerm t,out BoundTerm coefficient,out BoundTerm offset,out BoundTerm index){
			bool call(BoundNode q,Builtin f){return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f;}
			auto n=node(t);if(!call(n,Builtin.addN)||depends(at(n.b),0))return false;
			auto mul=nodes[n.a];if(!call(mul,Builtin.mulN)||nodes[mul.b].op!=BoundOp.variable||nodes[mul.b].data!=0)return false;
			auto c=nodes[mul.a];if(c.op!=BoundOp.scalar||!arena.isNumber(arena.at(c.data))||arena.number(arena.at(c.data)).re<=Number(0).re)return false;
			coefficient=at(mul.a);offset=at(n.b);index=at(mul.b);return true;
		}
		// Round real comparisons only in a summand. These are equalities on
		// partial values, including negative and undefined bounds.
		Result roundSumBounds(BoundTerm t,bool splitMasks=false){
			auto n=node(t);
			if((n.op==BoundOp.scalar||n.op==BoundOp.primitive)&&!depends(t,0)&&scalarBody(t,arena.natural_(0))!=Term.init) return normalizeClosed(t,0);
			if(n.op==BoundOp.primitive){
				auto op=arena.view(arena.at(n.data)).op;
				if(op==Op.builtin){
					auto cmp=arena.view(arena.at(n.data)).value;
					if(cmp>=Builtin.powQZ&&cmp<=Builtin.powCZ){
						bool call(BoundNode q,Builtin f){return q.op==BoundOp.primitive&&arena.view(arena.at(q.data)).op==Op.builtin&&arena.view(arena.at(q.data)).value==f;}
						auto exponent=nodes[n.b],pow=cast(Builtin)(Builtin.powQN+cmp-Builtin.powQZ),zero=arena.number(Number(0),elementSort(type(t)));
						if(call(exponent,Builtin.castNZ)){
							auto out_=primitive(arena.call(pow,[zero,arena.natural_(0)]),[at(n.a),at(exponent.a)]);
							return Result(out_.id,emit(BindingRule.sumPowerNatural,t.id,out_.id));
						}
						if(call(exponent,Builtin.addZ))foreach(reverse;0..2){
							auto offset=nodes[reverse?exponent.b:exponent.a],product=nodes[reverse?exponent.a:exponent.b];
							if(offset.op!=BoundOp.scalar||!arena.isNumber(arena.at(offset.data))||arena.number(arena.at(offset.data)).re>=Number(0).re||!call(product,Builtin.mulZ))continue;
							auto minus=nodes[product.a],cast_=nodes[product.b];
							if(minus.op!=BoundOp.scalar||!arena.isNumber(arena.at(minus.data))||arena.number(arena.at(minus.data))!=Number(-1)||!call(cast_,Builtin.castNZ))continue;
							auto count=scalar(context(t),arena.number(-arena.number(arena.at(offset.data)),Sort.natural));
							auto power=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[at(cast_.a),count]);
							auto out_=primitive(arena.call(pow,[zero,arena.natural_(0)]),[primitive(arena.inv(zero),[at(n.a)]),power]);
							return Result(out_.id,emit(BindingRule.sumPowerNegative,t.id,out_.id,uint.max,uint.max,reverse));
						}
					}
					if(cmp==Builtin.ltN||cmp==Builtin.leN){
						BoundTerm a,b,i;
						if(affineNaturalParts(at(n.a),a,b,i)&&!depends(at(n.b),0)||affineNaturalParts(at(n.b),a,b,i)&&!depends(at(n.a),0)){
							BoundTerm asReal(BoundTerm x){foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR])x=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[x]);return x;}
							auto out_=primitive(cmp==Builtin.ltN?arena.lt(arena.real_(0),arena.real_(0)):arena.le(arena.real_(0),arena.real_(0)),[asReal(at(n.a)),asReal(at(n.b))]);
							return Result(out_.id,emit(BindingRule.sumNaturalBound,t.id,out_.id));
						}
					}
					if(cmp==Builtin.ltQ||cmp==Builtin.leQ){
						auto cast_=arena.call(Builtin.castQR,[arena.number(Number(0),Sort.rational)]);
						auto left=primitive(cast_,[at(n.a)]),right=primitive(cast_,[at(n.b)]);
						auto out_=primitive(cmp==Builtin.ltQ?arena.lt(arena.real_(0),arena.real_(0)):arena.le(arena.real_(0),arena.real_(0)),[left,right]);
						return Result(out_.id,emit(BindingRule.sumRationalBound,t.id,out_.id));
					}
				}
				if(splitMasks&&op==Op.mask){
					auto pred=nodes[n.a];
					if(pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.and_){
						auto inside=primitive(arena.at(n.data),[at(pred.b),at(n.b)]);
						auto out_=primitive(arena.at(n.data),[at(pred.a),inside]);
						return Result(out_.id,emit(BindingRule.sumMaskAnd,t.id,out_.id));
					}
				}
				if(op==Op.mask){
					auto pred=at(n.a),pn=node(pred);bool equality=pn.op==BoundOp.primitive&&arena.view(arena.at(pn.data)).op==Op.not_;
					if(equality) pn=nodes[pn.a];
					if((equality||splitMasks)&&pn.op==BoundOp.primitive&&arena.view(arena.at(pn.data)).op==Op.builtin&&arena.view(arena.at(pn.data)).value==Builtin.nonzeroZ){
						auto diff=nodes[pn.a];
						if(diff.op==BoundOp.primitive&&arena.view(arena.at(diff.data)).op==Op.builtin&&arena.view(arena.at(diff.data)).value==Builtin.addZ){
							auto cast_=nodes[diff.a];
							if(equality&&(nodes[diff.b].op!=BoundOp.scalar||!arena.isNumber(arena.at(nodes[diff.b].data)))) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
							if(cast_.op==BoundOp.primitive&&arena.view(arena.at(cast_.data)).op==Op.builtin&&arena.view(arena.at(cast_.data)).value==Builtin.castNZ&&nodes[cast_.a].op==BoundOp.variable&&nodes[cast_.a].data==0&&!depends(at(diff.b),0)){
								auto ctx=context(t),iv=at(cast_.a),c=at(diff.b);
								BoundTerm unary(Builtin op,BoundTerm x){return primitive(arena.call(op,[arena.number(Number(0),builtinInfo(op).args[0])]),[x]);}
								auto negative=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[scalar(ctx,arena.integer(-1)),c]);
								auto plus=primitive(arena.add(arena.integer(0),arena.integer(0),true),[negative,scalar(ctx,arena.integer(1))]);
								BoundTerm count(BoundTerm x){return unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,x)));}
								auto lo=count(negative),hi=count(plus),zero=arena.natural_(0);
								BoundTerm lt(BoundTerm a,BoundTerm b){return primitive(arena.call(Builtin.ltN,[zero,zero]),[a,b]);}
								BoundTerm le(BoundTerm a,BoundTerm b){return primitive(arena.call(Builtin.leN,[zero,zero]),[a,b]);}
								BoundTerm mask(BoundTerm p){return primitive(arena.at(n.data),[p,at(n.b)]);}
								auto out_=equality?mask(primitive(arena.and_(arena.boolean(false),arena.boolean(false)),[le(lo,iv),lt(iv,hi)])):
									primitive(scalarOperator(type(t),TensorOp.add),[mask(lt(iv,lo)),mask(le(hi,iv))]);
								return Result(out_.id,emit(equality?BindingRule.sumMaskEqOffset:BindingRule.sumMaskNeOffset,t.id,out_.id,uint.max,uint.max,c.id));
							}
						}
					}
				}
				if(op==Op.lt||op==Op.le)foreach(reverse;0..2){
					auto expression=at(reverse?n.b:n.a),bound=at(reverse?n.a:n.b);
					foreach(c;[Builtin.castQR,Builtin.castZQ,Builtin.castNZ]){
						auto v=node(expression);
						if(v.op!=BoundOp.primitive||arena.view(arena.at(v.data)).op!=Op.builtin||arena.view(arena.at(v.data)).value!=c){expression=BoundTerm.init;break;}
						expression=at(v.a);
					}
					BoundTerm a,b,i;if(expression==BoundTerm.init||depends(bound,0)||!affineNaturalParts(expression,a,b,i))continue;
					BoundTerm asReal(BoundTerm x){foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR])x=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[x]);return x;}
					auto ctx=context(t),z=arena.real_(0);
					auto negative=primitive(arena.mul(z,z,true),[scalar(ctx,arena.real_(-1)),asReal(b)]);
					auto shifted=primitive(arena.add(z,z,true),[bound,negative]);
					auto threshold=primitive(arena.mul(z,z,true),[shifted,primitive(arena.inv(z),[asReal(a)])]);
					auto out_=primitive(arena.at(n.data),reverse?[threshold,asReal(i)]:[asReal(i),threshold]);
					return Result(out_.id,emit(BindingRule.sumAffineNatural,t.id,out_.id,uint.max,uint.max,reverse));
				}
				if(op==Op.lt||op==Op.le) foreach(reverse;0..2){
					auto index=at(reverse?n.b:n.a),bound=at(reverse?n.a:n.b);
					foreach(c;[Builtin.castQR,Builtin.castZQ]){
						auto v=node(index);
						if(v.op!=BoundOp.primitive||arena.view(arena.at(v.data)).op!=Op.builtin||arena.view(arena.at(v.data)).value!=c){ index=BoundTerm.init; break; }
						index=at(v.a);
					}
					if(index==BoundTerm.init) continue;
					bool natural; auto v=node(index);
					if(v.op==BoundOp.primitive&&arena.view(arena.at(v.data)).op==Op.builtin&&arena.view(arena.at(v.data)).value==Builtin.castNZ){ natural=true;index=at(v.a);v=node(index); }
					if(v.op!=BoundOp.variable||v.data!=0||depends(bound,0)) continue;
					auto ctx=context(t);
					BoundTerm unary(Builtin f,BoundTerm x){ return primitive(arena.call(f,[arena.number(Number(0),builtinInfo(f).args[0])]),[x]); }
					bool ceiling=(op==Op.lt)!=cast(bool)reverse;
					auto rounded=unary(ceiling?Builtin.ceilR:Builtin.floorR,bound);
					if(!ceiling) rounded=primitive(arena.add(arena.integer(0),arena.integer(0),true),[rounded,scalar(ctx,arena.integer(1))]);
					if(natural) rounded=unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,rounded)));
					auto cmp=natural?(reverse?Builtin.leN:Builtin.ltN):(reverse?Builtin.leZ:Builtin.ltZ),zero=arena.number(Number(0),natural?Sort.natural:Sort.integer);
					auto out_=primitive(arena.call(cmp,[zero,zero]),reverse?[rounded,index]:[index,rounded]);
					auto flags=cast(uint)(!natural)*4+reverse*2+cast(uint)(op==Op.le);
					return Result(out_.id,emit(BindingRule.sumRound,t.id,out_.id,uint.max,uint.max,flags));
				}
			}
			// Do not cross another binder: its de Bruijn zero is a different index.
			if(n.op!=BoundOp.primitive) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
			auto x=roundSumBounds(at(n.a),splitMasks); auto y=n.b==uint.max?Result(uint.max,uint.max):roundSumBounds(at(n.b),splitMasks);
			if(x.output==n.a&&y.output==n.b) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
			auto out_=rebuild(t,context(t),n.b==uint.max?[at(x.output)]:[at(x.output),at(y.output)]);
			return Result(out_.id,emit(BindingRule.congr,t.id,out_.id,x.proof,y.proof));
		}
		bool boundedMask(BoundNode x){
			if(x.op!=BoundOp.primitive||arena.view(arena.at(x.data)).op!=Op.mask) return false;
			auto p=nodes[x.a]; if(p.op!=BoundOp.primitive) return false;
			auto op=arena.view(arena.at(p.data));
			return op.op==Op.builtin&&(op.value==Builtin.ltN||op.value==Builtin.leN)&&nodes[p.a].op==BoundOp.variable&&nodes[p.a].data==0&&!depends(at(p.b),0);
		}
		bool zeroSelector(BoundNode x){
			if(x.op!=BoundOp.primitive||arena.view(arena.at(x.data)).op!=Op.mask)return false;
			auto p=nodes[x.a];if(p.op!=BoundOp.primitive||arena.view(arena.at(p.data)).op!=Op.not_)return false;
			auto nz=nodes[p.a];if(nz.op!=BoundOp.primitive)return false;
			auto op=arena.view(arena.at(nz.data));if(op.op!=Op.builtin||(op.value!=Builtin.nonzeroN&&op.value!=Builtin.nonzeroZ))return false;
			auto iv=nodes[nz.a];
			if(iv.op==BoundOp.primitive&&arena.view(arena.at(iv.data)).op==Op.builtin&&arena.view(arena.at(iv.data)).value==Builtin.castNZ)iv=nodes[iv.a];
			return iv.op==BoundOp.variable&&iv.data==0;
		}
		bool additive(BoundNode x){
			if(x.op!=BoundOp.primitive) return false;
			auto a=arena.view(arena.at(x.data));
			return a.op==Op.add||a.op==Op.builtin&&(a.value==Builtin.addN||a.value==Builtin.addZ||a.value==Builtin.addQ);
		}
		// Expose finite masks across numeric embeddings, but commit this direction
		// only when the resulting sum can immediately become a finite sum.
		Result exposeSumMasks(BoundTerm t){
			auto n=node(t); if(n.op!=BoundOp.primitive) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
			auto op=arena.view(arena.at(n.data));
			bool cast_=op.op==Op.builtin&&op.value>=Builtin.castNZ&&op.value<=Builtin.castRC;
			if(!cast_&&!additive(n)) return Result(t.id,emit(BindingRule.refl,t.id,t.id));
			auto x=exposeSumMasks(at(n.a)),y=n.b==uint.max?Result(uint.max,uint.max):exposeSumMasks(at(n.b));
			auto out_=rebuild(t,context(t),n.b==uint.max?[at(x.output)]:[at(x.output),at(y.output)]);
			auto proof=emit(BindingRule.congr,t.id,out_.id,x.proof,y.proof);
			auto child=nodes[x.output];
			if(cast_&&child.op==BoundOp.primitive){
				bool mask=arena.view(arena.at(child.data)).op==Op.mask;
				if(mask||additive(child)){
					auto left=mask?at(child.a):primitive(arena.at(n.data),[at(child.a)]),right=primitive(arena.at(n.data),[at(child.b)]);
					auto op2=mask?arena.mask(arena.boolean(false),arena.number(Number(0),elementSort(type(t)))):scalarOperator(type(t),TensorOp.add);
					auto next=primitive(op2,[left,right]),step=emit(mask?BindingRule.sumCastMask:BindingRule.sumCastAdd,out_.id,next.id);
					return Result(next.id,emit(BindingRule.trans,t.id,next.id,proof,step));
				}
			}
			return Result(out_.id,proof);
		}
		BoundTerm solveFinite(BoundTerm t,out uint extra,bool infinite=false){
			auto n=node(t),fn=nodes[n.a]; if(fn.op!=BoundOp.lambda||pool.view(type(at(n.a))).fields[0]!=scalarType(Sort.natural)) return BoundTerm.init;
			auto sort=elementSort(types[n.type]); if(sort!=Sort.rational&&sort!=Sort.real_&&sort!=Sort.complex) return BoundTerm.init;
			uint index; foreach(id;0..arena.length){ auto v=arena.node(arena.at(cast(uint)id)); if(v.op==Op.variable&&v.value>=index) index=cast(uint)v.value+1; }
			auto variable=arena.variable(Sort.natural,index),body=scalarBody(at(fn.a),variable); if(body==Term.init) return BoundTerm.init;
			SumPrimitive[] tail;
			auto candidate=sumAntidifference(arena,body,variable,tail); if(candidate==Term.init) return BoundTerm.init;
			if(!infinite) tail=null;
			auto zero=arena.number(Number(0),sort);
			if(infinite){
				if(pool.view(type(at(n.a))).fields[0]!=scalarType(Sort.natural)||!tail.length) return BoundTerm.init;
				candidate=zero;
				auto power=sort==Sort.rational?Builtin.powQN:sort==Sort.real_?Builtin.powRN:Builtin.powCN;
				foreach_reverse(p;tail){
					if(!arena.isNumber(p.ratio)) return BoundTerm.init;
					auto q=arena.number(p.ratio); if(q.re*q.re+q.im*q.im>=Rational(1)) return BoundTerm.init;
					auto monomial=arena.mul(arena.mul(p.coefficient,arena.call(power,[arena.castTo(variable,sort),arena.natural_(p.degree)]),true),arena.call(power,[p.ratio,variable]),true);
					candidate=arena.add(monomial,candidate,true);
				}
			}
			Term subst(Term t,Term x){ auto v=arena.view(t); if(t==variable) return x; Term[] args; foreach(i;0..v.arity) args~=subst(arena.viewChild(t,i),x); return args.length?arena.viewRebuild(t,args,true):t; }
			auto initial=subst(candidate,arena.natural_(0));
			auto step=arena.add(subst(candidate,arena.add(variable,arena.natural_(1),true)),arena.mul(arena.number(Number(-1),sort),arena.add(candidate,body,true),true),true);
			auto opts=Options(DensityMode.preserve,true); opts.expandPowers=true; opts.expandScalarEmbeddings=true;
			ScalarDomain[] checks;
			foreach(rawInput;infinite?[step]:[initial,step]){
				auto input=sort==Sort.rational?arena.castTo(rawInput,Sort.real_):rawInput;
				auto domain=simplifyDomain(arena,input,[],opts),value=simplify(arena,input,[],opts);
				if(domain.exhausted||value.exhausted||domain.output!=arena.boolean(true)||!arena.isNumber(value.output)||!arena.number(value.output).zero) return BoundTerm.init;
				checks~=ScalarDomain(input,domain,value,index,Sort.natural);
			}
			auto g=inheritHint(at(n.a),lambda(restoreBody(candidate,context(at(fn.a)),variable)));
			auto output=infinite?scalar(context(t),arena.mul(arena.number(Number(-1),sort),initial,true)):apply(g,at(n.b));
			auto start=cast(uint)scalarDomains.length;
			uint[] totals,convergence;
			if(infinite) foreach(p;tail) foreach(input;[p.coefficient,p.ratio]){
				auto domain=simplifyDomain(arena,input,[],opts);
				if(domain.exhausted||domain.output!=arena.boolean(true)) return BoundTerm.init;
				totals~=start+cast(uint)checks.length; checks~=ScalarDomain(input,domain);
			}
			if(infinite) foreach(p;tail){
				auto norm=sort==Sort.complex?arena.call(Builtin.absC,[p.ratio]):arena.abs(arena.castTo(p.ratio,Sort.real_));
				auto pred=arena.lt(norm,arena.real_(1)),domain=simplifyDomain(arena,pred,[],opts),value=simplify(arena,pred,[],opts);
				if(domain.exhausted||value.exhausted||domain.output!=arena.boolean(true)||value.output!=arena.boolean(true)) return BoundTerm.init;
				convergence~=start+cast(uint)checks.length; checks~=ScalarDomain(pred,domain,value);
			}
			scalarDomains~=checks;
			extra=cast(uint)sums.length; sums~=SummationSolution(t.id,output.id,g.id,index,infinite?uint.max:start,infinite?start:start+1,tail,totals,convergence); return output;
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
						// Re-embedding may change only where closed scalar subtrees
						// are split into binder primitives. Do not cycle on that split.
						if(simplified==t||scalarBody(simplified,argument)==source) return BoundTerm.init;
					}
					auto d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true)); exhausted|=d.exhausted;
					extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d,value,index,sort,path,mode);
					if(mode==BoundOp.defined) return restoreBody(d.output,ctx,argument);
					if(mode==BoundOp.holds) return restoreBody(arena.and_(d.output,source),ctx,argument);
					return d.output==arena.boolean(true)?simplified:guard(restoreBody(d.output,ctx,argument),simplified);
				}
				if(n.op==BoundOp.guard||n.op==BoundOp.primitive||n.op==BoundOp.defined||n.op==BoundOp.holds||n.op==BoundOp.vectorCons||n.op==BoundOp.pair||n.op==BoundOp.get||n.op==BoundOp.first||n.op==BoundOp.rest||n.op==BoundOp.tensor){
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
			if(domains&&steps<budget&&n.op==BoundOp.defined&&nodes[n.a].op==BoundOp.get){
				auto child=nodes[n.a],index=nodes[child.b],v=pool.view(type(at(child.a)));
				if(v.dimension.constant&&index.op==BoundOp.scalar&&arena.isNumber(arena.at(index.data))){
					auto i=arena.number(arena.at(index.data)).re;
					if(i.small&&i.integer>=0&&cast(ulong)i.integer<v.length){
						auto next=defined(at(child.a)); ++steps;
						auto proof=emit(BindingRule.getDomain,t.id,next.id),tail=visit(next,depth+1);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
						active.set(t.id,false); memo.set(t.id,result); return result;
					}
				}
			}
			if(domains&&steps<budget&&(n.op==BoundOp.defined&&nodes[n.a].op==BoundOp.tensor||n.op==BoundOp.domain&&nodes[n.a].op==BoundOp.lambda)){
				auto child=nodes[n.a]; BoundTerm next; BindingRule rule;
				if(n.op==BoundOp.domain){ next=inheritHint(at(n.a),set(defined(at(child.a)))); rule=BindingRule.domainLam; }
				else{ next=primitive(arena.and_(arena.boolean(true),arena.boolean(true)),[defined(at(child.a)),defined(at(child.b))]); rule=BindingRule.tensorDomain; }
				++steps; auto proof=emit(rule,t.id,next.id),tail=visit(next,depth+1);
				result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
				active.set(t.id,false); memo.set(t.id,result); return result;
			}
			if(domains&&n.op==BoundOp.domain&&nodes[n.a].op==BoundOp.fixed&&steps<budget){
				DomainRank rank;
				if(rankDomain(at(n.a),rank)){
					auto extra=cast(uint)ranks.length; ranks~=rank;
					auto predicate=rank.iterations.length?rank.iterations[$-1].output:rank.lower.output!=Term.init?rank.result.output:arena.boolean(true);
					auto next=inheritHint(at(nodes[n.a].a),set(restoreBody(predicate,push(context(t),scalarType(rank.sort)),arena.variable(rank.sort,rank.variable))));
					++steps; auto proof=emit(BindingRule.domainFixedTotal,t.id,next.id,uint.max,uint.max,extra),tail=visit(next,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
			}
			if(domains&&n.op==BoundOp.defined&&nodes[n.a].op==BoundOp.apply&&nodes[nodes[n.a].a].op==BoundOp.fixed&&steps<budget){
				auto call=nodes[n.a],d=visit(domain(at(call.a)),depth+1);
				if(nodes[d.output].op==BoundOp.set&&steps<budget){
					++steps; auto next=holds(member(domain(at(call.a)),at(call.b)));
					auto proof=emit(BindingRule.definedApp,t.id,next.id),tail=visit(next,depth+1);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,proof,tail.proof));
					active.set(t.id,false); memo.set(t.id,result); return result;
				}
			}
			if(n.a==uint.max) result=Result(t.id,emit(BindingRule.refl,t.id,t.id));
			else{
				Result x=Result(uint.max,uint.max);
				bool applied=n.op==BoundOp.apply&&closedScalar(at(n.b));
				if(domains&&applied&&nodes[n.a].op==BoundOp.fixed&&steps<budget){
					RecurrenceSolution solution; auto function_=at(n.a),solved=solveRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solveAffineRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solveLinearRecurrence(function_,solution);
					if(solved==BoundTerm.init) solved=solvePrefixRecurrence(function_,solution);
					if(solved!=BoundTerm.init){
						auto extra=cast(uint)solutions.length; solutions~=solution; ++steps;
						x=Result(solved.id,emit(BindingRule.fixedRecurrence,n.a,solved.id,uint.max,uint.max,extra));
					}
				}
				if(x.output==uint.max) x=n.op==BoundOp.finiteSum||n.op==BoundOp.summation||n.op==BoundOp.fixed||applied&&nodes[n.a].op==BoundOp.lambda?Result(n.a,emit(BindingRule.refl,n.a,n.a)):visit(at(n.a),depth+1);
				BoundTerm[] args=[at(x.output)]; uint y=uint.max;
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
			if(current.op==BoundOp.summation&&nodes[current.a].op==BoundOp.lambda){
				auto body=nodes[nodes[current.a].a],ty=types[current.type];
				if(steps<budget){
					auto rounded=roundSumBounds(at(nodes[current.a].a));
					if(rounded.output!=nodes[current.a].a){
						auto fn=inheritHint(at(current.a),lambda(at(rounded.output))),out_=summation(fn);
						auto fp=emit(BindingRule.congr,current.a,fn.id,rounded.proof);
						auto sp=emit(BindingRule.congr,result.output,out_.id,fp); ++steps;
						auto tail=visit(out_,depth+1),rest=emit(BindingRule.trans,result.output,tail.output,sp,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false);memo.set(t.id,result);return result;
					}
				}
				if(steps<budget){
					auto exposed=exposeSumMasks(at(nodes[current.a].a)),b=nodes[exposed.output];
					if(exposed.output!=nodes[current.a].a&&(boundedMask(b)||zeroSelector(b)||additive(b)&&boundedMask(nodes[b.a])&&boundedMask(nodes[b.b]))){
						auto fn=inheritHint(at(current.a),lambda(at(exposed.output))),out_=summation(fn);
						auto fp=emit(BindingRule.congr,current.a,fn.id,exposed.proof),sp=emit(BindingRule.congr,result.output,out_.id,fp);++steps;
						auto tail=visit(out_,depth+1),rest=emit(BindingRule.trans,result.output,tail.output,sp,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false);memo.set(t.id,result);return result;
					}
				}
				// Distribute finite-support summands without assuming arbitrary infinite linearity.
				if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==arena.view(scalarOperator(ty,TensorOp.add)).op&&arena.view(arena.at(body.data)).value==arena.view(scalarOperator(ty,TensorOp.add)).value&&type(variable(context(at(nodes[current.a].a)),0))==scalarType(Sort.natural)){
					auto left=nodes[body.a],right=nodes[body.b];

					if(boundedMask(left)&&boundedMask(right)){
						auto lp=nodes[left.a],rp=nodes[right.a],lo=dropIndex(at(lp.b)),hi=dropIndex(at(rp.b));
						bool li=arena.view(arena.at(lp.data)).value==Builtin.leN,ri=arena.view(arena.at(rp.data)).value==Builtin.leN;
						BoundTerm upper(BoundTerm n,bool inclusive){return inclusive?primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[n,scalar(ctx,arena.natural_(1))]):n;}
						next=primitive(arena.at(body.data),[finiteSum(inheritHint(at(current.a),lambda(at(left.b))),upper(lo,li)),finiteSum(inheritHint(at(current.a),lambda(at(right.b))),upper(hi,ri))]);
						extra=tuple(ctx,[lo,hi,scalar(ctx,arena.natural_((li?1:0)|(ri?2:0)))]).id;rule=BindingRule.sumBoundedAdd;
					}
				}
				if(next!=BoundTerm.init){}
				else if(body.op==BoundOp.scalar&&arena.isNumber(arena.at(body.data))&&arena.number(arena.at(body.data)).zero){
					next=scalar(ctx,arena.number(Number(0),elementSort(ty))); rule=BindingRule.sumZero;
				}else if(!depends(at(nodes[current.a].a),0)){
					auto c=dropIndex(at(nodes[current.a].a)),sort=elementSort(ty),placeholder=arena.number(Number(0),sort);
					auto pred=primitive(arena.not_(arena.boolean(false)),[primitive(arena.nonzero(placeholder),[c])]);
					next=guard(pred,scalar(ctx,placeholder)); rule=BindingRule.sumConstant; extra=c.id;
				}else if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.builtin&&arena.view(arena.at(body.data)).value>=Builtin.powQN&&arena.view(arena.at(body.data)).value<=Builtin.powCN&&nodes[body.b].op==BoundOp.variable&&nodes[body.b].data==0&&!depends(at(body.a),0)){
					auto q=dropIndex(at(body.a)),sort=elementSort(ty),placeholder=arena.number(Number(0),sort);
					auto abs=sort==Sort.complex?primitive(arena.call(Builtin.absC,[placeholder]),[q]):primitive(arena.abs(arena.real_(0)),[sort==Sort.rational?primitive(arena.call(Builtin.castQR,[placeholder]),[q]):q]);
					auto pred=primitive(arena.lt(arena.real_(0),arena.real_(1)),[abs,scalar(ctx,arena.real_(1))]);
					auto neg=primitive(arena.mul(placeholder,placeholder,true),[scalar(ctx,arena.number(Number(-1),sort)),q]);
					auto den=primitive(arena.add(placeholder,placeholder,true),[scalar(ctx,arena.number(Number(1),sort)),neg]);
					next=guard(pred,primitive(arena.inv(placeholder),[den])); rule=BindingRule.sumGeometric; extra=q.id;
				}else if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.builtin&&arena.view(arena.at(body.data)).value>=Builtin.powQN&&arena.view(arena.at(body.data)).value<=Builtin.powCN&&!depends(at(body.a),0)){
					auto exponent=nodes[body.b];
					if(exponent.op==BoundOp.primitive&&arena.view(arena.at(exponent.data)).op==Op.builtin&&arena.view(arena.at(exponent.data)).value==Builtin.addN&&nodes[exponent.a].op==BoundOp.variable&&nodes[exponent.a].data==0&&!depends(at(exponent.b),0)){
						auto q=dropIndex(at(body.a)),offset=dropIndex(at(exponent.b)),power=arena.at(body.data),sort=elementSort(ty),placeholder=arena.number(Number(0),sort);
						auto abs=sort==Sort.complex?primitive(arena.call(Builtin.absC,[placeholder]),[q]):primitive(arena.abs(arena.real_(0)),[sort==Sort.rational?primitive(arena.call(Builtin.castQR,[placeholder]),[q]):q]);
						auto pred=primitive(arena.lt(arena.real_(0),arena.real_(1)),[abs,scalar(ctx,arena.real_(1))]);
						auto neg=primitive(arena.mul(placeholder,placeholder,true),[scalar(ctx,arena.number(Number(-1),sort)),q]);
						auto den=primitive(arena.add(placeholder,placeholder,true),[scalar(ctx,arena.number(Number(1),sort)),neg]);
						next=guard(pred,primitive(scalarOperator(ty,TensorOp.mul),[primitive(power,[q,offset]),primitive(arena.inv(placeholder),[den])])); rule=BindingRule.sumShiftGeometric; extra=tuple(ctx,[q,offset]).id;
					}
				}else if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.mask){
					auto pred=nodes[body.a];
					if(pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.builtin&&(arena.view(arena.at(pred.data)).value==Builtin.ltN||arena.view(arena.at(pred.data)).value==Builtin.leN)&&nodes[pred.a].op==BoundOp.variable&&nodes[pred.a].data==0&&!depends(at(pred.b),0)){
						auto bound=dropIndex(at(pred.b)); extra=bound.id;
						bool inclusive=arena.view(arena.at(pred.data)).value==Builtin.leN;
						auto end=inclusive?primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[bound,scalar(ctx,arena.natural_(1))]):bound;
						next=finiteSum(inheritHint(at(current.a),lambda(at(body.b))),end); rule=inclusive?BindingRule.sumRangeLe:BindingRule.sumRange;
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.builtin&&(arena.view(arena.at(pred.data)).value==Builtin.leN||arena.view(arena.at(pred.data)).value==Builtin.ltN)&&nodes[pred.b].op==BoundOp.variable&&nodes[pred.b].data==0&&!depends(at(pred.a),0)){
						auto bound=dropIndex(at(pred.a)),inner=context(at(body.b)); extra=bound.id;
						bool strict=arena.view(arena.at(pred.data)).value==Builtin.ltN;
						auto lo=strict?primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[at(pred.a),scalar(inner,arena.natural_(1))]):at(pred.a);
						BoundTerm[] values=[primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(inner,0),lo])];
						foreach(i;0..this.depth(ctx)) values~=variable(inner,i+1);
						auto shifted=substitute(at(body.b),inner,values);
						next=sequence(bound,summation(inheritHint(at(current.a),lambda(shifted)))); rule=strict?BindingRule.sumTailStrict:BindingRule.sumTailNatural;
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.and_){
						auto lower=nodes[pred.a],upper=nodes[pred.b],indexType=type(variable(context(at(body.a)),0));
						auto ns=indexType==scalarType(Sort.natural),le=ns?Builtin.leN:Builtin.leZ,lt=ns?Builtin.ltN:Builtin.ltZ;
						bool comparison(BoundNode x,Builtin op){ return x.op==BoundOp.primitive&&arena.view(arena.at(x.data)).op==Op.builtin&&arena.view(arena.at(x.data)).value==op; }
						if((comparison(lower,le)||comparison(lower,lt))&&(comparison(upper,lt)||comparison(upper,le))&&nodes[lower.b].op==BoundOp.variable&&nodes[lower.b].data==0&&nodes[upper.a].op==BoundOp.variable&&nodes[upper.a].data==0&&!depends(at(lower.a),0)&&!depends(at(upper.b),0)){
							bool strict=comparison(lower,lt),inclusive=comparison(upper,le);
							if(strict||inclusive){
								extra=tuple(ctx,[dropIndex(at(lower.a)),dropIndex(at(upper.b)),scalar(ctx,arena.natural_(cast(uint)strict+2*cast(uint)inclusive))]).id;
								auto inner=context(at(body.a)),zero=arena.number(Number(0),ns?Sort.natural:Sort.integer),one=scalar(inner,arena.number(Number(1),ns?Sort.natural:Sort.integer));
								auto l=strict?primitive(arena.add(zero,zero,true),[at(lower.a),one]):at(lower.a),u=inclusive?primitive(arena.add(zero,zero,true),[at(upper.b),one]):at(upper.b);
								auto lp=primitive(arena.call(le,[zero,zero]),[l,variable(inner,0)]),up=primitive(arena.call(lt,[zero,zero]),[variable(inner,0),u]);
								auto predicate=primitive(arena.and_(arena.boolean(false),arena.boolean(false)),[lp,up]);
								next=summation(inheritHint(at(current.a),lambda(primitive(arena.mask(arena.boolean(false),arena.number(Number(0),elementSort(ty))),[predicate,at(body.b)])))); rule=BindingRule.sumBounds;
							}else{
							auto lo=dropIndex(at(lower.a)),hi=dropIndex(at(upper.b));
							extra=tuple(ctx,[lo,hi]).id;
							BoundTerm unary(Builtin op,BoundTerm x){ return primitive(arena.call(op,[arena.number(Number(0),builtinInfo(op).args[0])]),[x]); }
							auto lz=ns?unary(Builtin.castNZ,lo):lo,uz=ns?unary(Builtin.castNZ,hi):hi;
							auto minus=scalar(ctx,arena.integer(-1)),neg=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[minus,lz]);
							auto difference=primitive(arena.add(arena.integer(0),arena.integer(0),true),[uz,neg]);
							auto count=unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,difference)));
							auto inner=push(ctx,scalarType(Sort.natural)),iv=variable(inner,0);
							BoundTerm[] values=[scalar(inner,arena.number(Number(0),ns?Sort.natural:Sort.integer))];
							foreach(i;0..this.depth(ctx)) values~=variable(inner,i+1);
							auto newlo=substitute(at(lower.a),inner,values);
							values[0]=primitive(arena.add(arena.number(Number(0),ns?Sort.natural:Sort.integer),arena.number(Number(0),ns?Sort.natural:Sort.integer),true),[ns?iv:unary(Builtin.castNZ,iv),newlo]);
							auto shifted=substitute(at(body.b),inner,values);
							next=finiteSum(inheritHint(at(current.a),lambda(shifted)),count); rule=BindingRule.sumInterval;
							}
						}
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive){
						auto indexType=type(variable(context(at(body.a)),0)),ns=indexType==scalarType(Sort.natural);
						auto pop=arena.view(arena.at(pred.data));
						bool lower=pop.op==Op.builtin&&pop.value==(ns?Builtin.leN:Builtin.leZ),upper=!ns&&pop.op==Op.builtin&&pop.value==Builtin.ltZ;
						auto iv=lower?pred.b:pred.a,k=lower?pred.a:pred.b;
						if((lower||upper)&&nodes[iv].op==BoundOp.variable&&nodes[iv].data==0&&!depends(at(k),0)){
							auto endpoint=dropIndex(at(k)); extra=endpoint.id;
							auto inner=push(ctx,scalarType(Sort.natural)),j=variable(inner,0);
							BoundTerm unary(Builtin op,BoundTerm x){return primitive(arena.call(op,[arena.number(Number(0),builtinInfo(op).args[0])]),[x]);}
							auto zero=arena.number(Number(0),ns?Sort.natural:Sort.integer);
							BoundTerm add(BoundTerm a,BoundTerm b){return primitive(arena.add(zero,zero,true),[a,b]);}
							BoundTerm[] values=[scalar(inner,zero)];foreach(i;0..this.depth(ctx))values~=variable(inner,i+1);
							auto shiftedK=substitute(at(k),inner,values);
							if(ns) values[0]=add(j,shiftedK);
							else if(lower) values[0]=add(unary(Builtin.castNZ,j),shiftedK);
							else values[0]=add(add(shiftedK,scalar(inner,arena.integer(-1))),primitive(arena.mul(zero,zero,true),[scalar(inner,arena.integer(-1)),unary(Builtin.castNZ,j)]));
							next=sequence(endpoint,summation(inheritHint(at(current.a),lambda(substitute(at(body.b),inner,values)))));rule=BindingRule.sumTail;
						}
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.builtin&&arena.view(arena.at(pred.data)).value==Builtin.nonzeroZ){
						auto cast_=nodes[pred.a];
						if(cast_.op==BoundOp.primitive&&arena.view(arena.at(cast_.data)).op==Op.builtin&&arena.view(arena.at(cast_.data)).value==Builtin.castNZ&&nodes[cast_.a].op==BoundOp.variable&&nodes[cast_.a].data==0){
							auto inner=context(at(body.b)),shift=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(inner,0),scalar(inner,arena.natural_(1))]);
							BoundTerm[] values=[shift];foreach(i;0..this.depth(ctx))values~=variable(inner,i+1);
							next=summation(inheritHint(at(current.a),lambda(substitute(at(body.b),inner,values))));rule=BindingRule.sumExcludeZero;
						}
					}
					if(next==BoundTerm.init&&elementSort(ty)!=Sort.natural&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.builtin&&arena.view(arena.at(pred.data)).value==Builtin.nonzeroZ){
						auto diff=nodes[pred.a];
						if(diff.op==BoundOp.primitive&&arena.view(arena.at(diff.data)).op==Op.builtin&&arena.view(arena.at(diff.data)).value==Builtin.addZ){
							auto cast_=nodes[diff.a];
							if(cast_.op==BoundOp.primitive&&arena.view(arena.at(cast_.data)).op==Op.builtin&&arena.view(arena.at(cast_.data)).value==Builtin.castNZ&&nodes[cast_.a].op==BoundOp.variable&&nodes[cast_.a].data==0&&!depends(at(diff.b),0)){
								auto c=dropIndex(at(diff.b));extra=c.id;
								BoundTerm unary(Builtin op,BoundTerm x){return primitive(arena.call(op,[arena.number(Number(0),builtinInfo(op).args[0])]),[x]);}
								auto negative=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[scalar(ctx,arena.integer(-1)),c]);
								auto plus=primitive(arena.add(arena.integer(0),arena.integer(0),true),[negative,scalar(ctx,arena.integer(1))]);
								BoundTerm count(BoundTerm x){return unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,x)));}
								auto lo=count(negative),hi=count(plus),inner=context(at(body.b));
								uint[] indices;foreach(i;0..this.depth(ctx))indices~=i+1;
								auto shift=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(inner,0),rename(hi,inner,indices)]);
								BoundTerm[] values=[shift];foreach(i;0..this.depth(ctx))values~=variable(inner,i+1);
								auto f=inheritHint(at(current.a),lambda(at(body.b))),g=inheritHint(at(current.a),lambda(substitute(at(body.b),inner,values)));
								next=primitive(scalarOperator(ty,TensorOp.add),[finiteSum(f,lo),summation(g)]);rule=BindingRule.sumExcludeOffset;
							}
						}
					}
					if(next==BoundTerm.init&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.not_){
						auto nz=nodes[pred.a],indexType=type(variable(context(at(body.a)),0));
						if(nz.op==BoundOp.primitive&&arena.view(arena.at(nz.data)).op==Op.builtin&&(arena.view(arena.at(nz.data)).value==Builtin.nonzeroZ||arena.view(arena.at(nz.data)).value==Builtin.nonzeroN)){
							auto iv=nodes[nz.a];
							if(indexType==scalarType(Sort.natural)&&iv.op==BoundOp.primitive&&arena.view(arena.at(iv.data)).op==Op.builtin&&arena.view(arena.at(iv.data)).value==Builtin.castNZ) iv=nodes[iv.a];
							if(iv.op==BoundOp.variable&&iv.data==0){
								next=apply(inheritHint(at(current.a),lambda(at(body.b))),scalar(ctx,arena.number(Number(0),elementSort(indexType))));rule=BindingRule.sumDeltaZero;extra=arena.view(arena.at(nz.data)).value==Builtin.nonzeroN?1:0;
							}
						}
					}
					if(next==BoundTerm.init&&type(variable(context(at(body.a)),0))==scalarType(Sort.integer)&&pred.op==BoundOp.primitive&&arena.view(arena.at(pred.data)).op==Op.not_){
						auto nz=nodes[pred.a];
						if(nz.op==BoundOp.primitive&&arena.view(arena.at(nz.data)).op==Op.builtin&&arena.view(arena.at(nz.data)).value==Builtin.nonzeroZ){
							auto diff=nodes[nz.a];
							if(diff.op==BoundOp.primitive&&arena.view(arena.at(diff.data)).op==Op.builtin&&arena.view(arena.at(diff.data)).value==Builtin.addZ&&nodes[diff.a].op==BoundOp.variable&&nodes[diff.a].data==0&&!depends(at(diff.b),0)){
								auto c=dropIndex(at(diff.b)); extra=c.id;
								auto bound=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[scalar(ctx,arena.integer(-1)),c]);
								next=apply(inheritHint(at(current.a),lambda(at(body.b))),bound); rule=BindingRule.sumDeltaOffset;
							}
						}
					}
					if(next==BoundTerm.init){
						auto indexType=type(variable(context(at(body.a)),0)),indexSort=elementSort(indexType);
						auto idx=arena.variable(indexSort,cast(uint)arena.length),predicate=scalarBody(at(body.a),idx);
						BoundTerm find(uint id){
							auto t=at(id),v=node(t);
							if(type(t)==indexType&&!depends(t,0)){
								auto k=scalarBody(t,idx);
								if(k!=Term.init&&predicate==arena.equal(idx,k)) return t;
							}
							if(v.op==BoundOp.scalar) foreach(scalarId;arena.viewPostorder(arena.at(v.data))){
								auto k=arena.at(scalarId);
								if(arena.sort(k)==indexSort&&predicate==arena.equal(idx,k)) return scalar(context(t),k);

							}
							if(v.a!=uint.max){ auto r=find(v.a); if(r!=BoundTerm.init) return r; }
							return v.b!=uint.max?find(v.b):BoundTerm.init;
						}
						auto bound=predicate==Term.init?BoundTerm.init:find(body.a);
						if(bound!=BoundTerm.init){ next=apply(inheritHint(at(current.a),lambda(at(body.b))),dropIndex(bound)); rule=BindingRule.sumDelta; }
					}
				}
				if(next==BoundTerm.init){ next=solveFinite(at(result.output),extra,true); rule=BindingRule.rangeSolution; }
			}else if(current.op==BoundOp.finiteSum&&nodes[current.a].op==BoundOp.lambda){
				auto summand=nodes[nodes[current.a].a];
				if(steps<budget){
					auto rounded=roundSumBounds(at(nodes[current.a].a),true);
					if(rounded.output!=nodes[current.a].a){
						auto fn=inheritHint(at(current.a),lambda(at(rounded.output))),out_=finiteSum(fn,at(current.b));
						auto fp=emit(BindingRule.congr,current.a,fn.id,rounded.proof);
						auto bp=emit(BindingRule.refl,current.b,current.b);
						auto sp=emit(BindingRule.congr,result.output,out_.id,fp,bp);++steps;
						auto tail=visit(out_,depth+1),rest=emit(BindingRule.trans,result.output,tail.output,sp,tail.proof);
						result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
						active.set(t.id,false);memo.set(t.id,result);return result;
					}
				}
				auto bound=nodes[current.b],sort=elementSort(types[current.type]);
				auto bop=summand.op==BoundOp.primitive?arena.view(arena.at(summand.data)):Node.init;
				bool hasMask(uint id){auto n=nodes[id];if(n.op!=BoundOp.primitive)return false;if(arena.view(arena.at(n.data)).op==Op.mask)return true;return n.a!=uint.max&&hasMask(n.a)||n.b!=uint.max&&hasMask(n.b);}
				if(hasMask(nodes[current.a].a)&&summand.op==BoundOp.primitive&&(bop.op==Op.add||bop.op==Op.builtin&&(bop.value==Builtin.addN||bop.value==Builtin.addZ||bop.value==Builtin.addQ))){
					auto f=inheritHint(at(current.a),lambda(at(summand.a))),g=inheritHint(at(current.a),lambda(at(summand.b)));
					next=primitive(arena.at(summand.data),[finiteSum(f,at(current.b)),finiteSum(g,at(current.b))]);rule=BindingRule.rangeAdd;
				}else if(summand.op==BoundOp.primitive&&bop.op==Op.mask){
					auto pred=nodes[summand.a];
					auto pop=pred.op==BoundOp.primitive?arena.view(arena.at(pred.data)):Node.init;
					bool lt=pop.op==Op.builtin&&pop.value==Builtin.ltN,ge=pop.op==Op.builtin&&pop.value==Builtin.leN;
					auto index=lt?pred.a:pred.b,k=lt?pred.b:pred.a;
					if((lt||ge)&&nodes[index].op==BoundOp.variable&&nodes[index].data==0&&!depends(at(k),0)){
						auto endpoint=dropIndex(at(k));extra=endpoint.id;
						BoundTerm unary(Builtin f,BoundTerm x){return primitive(arena.call(f,[arena.number(Number(0),builtinInfo(f).args[0])]),[x]);}
						BoundTerm realN(BoundTerm x){return unary(Builtin.castQR,unary(Builtin.castZQ,unary(Builtin.castNZ,x)));}
						auto nz=unary(Builtin.nonzeroZ,unary(Builtin.castNZ,at(current.b)));
						BoundTerm count,fn;
						if(lt){
							count=unary(Builtin.floorN,primitive(arena.call(Builtin.minR,[arena.real_(0),arena.real_(0)]),[realN(at(current.b)),realN(endpoint)]));
							fn=inheritHint(at(current.a),lambda(at(summand.b)));rule=BindingRule.rangeMaskLt;
						}else{
							auto negative=primitive(arena.mul(arena.integer(0),arena.integer(0),true),[scalar(ctx,arena.integer(-1)),unary(Builtin.castNZ,endpoint)]);
							auto delta=primitive(arena.add(arena.integer(0),arena.integer(0),true),[unary(Builtin.castNZ,at(current.b)),negative]);
							count=unary(Builtin.floorN,unary(Builtin.castQR,unary(Builtin.castZQ,delta)));
							auto inner=context(at(summand.b)),shift=primitive(arena.add(arena.natural_(0),arena.natural_(0),true),[variable(inner,0),at(k)]);
							BoundTerm[] values=[shift];foreach(i;1..this.depth(inner))values~=variable(inner,i);
							fn=inheritHint(at(current.a),lambda(substitute(at(summand.b),inner,values)));rule=BindingRule.rangeMaskGe;
						}
						next=primitive(arena.mask(arena.boolean(false),arena.number(Number(0),sort)),[nz,finiteSum(fn,count)]);
					}
				}
				if(next==BoundTerm.init&&bound.op==BoundOp.bottom){ next=bottom(ctx,types[current.type]); rule=BindingRule.shortCircuit; }
				else if(next==BoundTerm.init&&bound.op==BoundOp.scalar&&arena.isNumber(arena.at(bound.data))&&arena.number(arena.at(bound.data)).re.small){
					auto count=arena.number(arena.at(bound.data)).re.integer;
					if(count==0){ next=scalar(ctx,arena.number(Number(0),sort)); rule=BindingRule.rangeZero; }
					else if(count<=64){
						auto prev=scalar(ctx,arena.natural_(cast(ulong)(count-1))),term=apply(at(current.a),prev),prefix=finiteSum(at(current.a),prev);
						next=primitive(scalarOperator(types[current.type],TensorOp.add),[prefix,term]); rule=BindingRule.rangeStep;
					}
				}
				if(next==BoundTerm.init&&(sort==Sort.rational||sort==Sort.real_||sort==Sort.complex)){ next=solveFinite(at(result.output),extra); rule=BindingRule.rangeSolution; }
				if(next==BoundTerm.init&&(sort==Sort.rational||sort==Sort.real_||sort==Sort.complex)){
					auto body=nodes[nodes[current.a].a];
					if(body.op==BoundOp.primitive&&arena.view(arena.at(body.data)).op==Op.builtin&&arena.view(arena.at(body.data)).value>=Builtin.powQN&&arena.view(arena.at(body.data)).value<=Builtin.powCN&&nodes[body.b].op==BoundOp.variable&&nodes[body.b].data==0&&!depends(at(body.a),0)){
						auto q=dropIndex(at(body.a)),countBound=at(current.b),zero=arena.number(Number(0),sort);
						BoundTerm unary(Term op,BoundTerm x){ return primitive(op,[x]); }
						BoundTerm add(BoundTerm x,BoundTerm y){ return primitive(arena.add(zero,zero,true),[x,y]); }
						BoundTerm mask(BoundTerm p,BoundTerm x){ return primitive(arena.mask(arena.boolean(false),zero),[p,x]); }
						BoundTerm not_(BoundTerm p){ return unary(arena.not_(arena.boolean(false)),p); }
						auto nz=unary(arena.nonzero(arena.natural_(0)),countBound),z=scalar(ctx,zero),minus=scalar(ctx,arena.number(Number(-1),sort));
						auto diff=add(q,minus),neq=unary(arena.nonzero(zero),diff),count=countBound;
						foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR,Builtin.castRC]) if(type(count)!=scalarType(sort)) count=unary(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),count);
						auto power=primitive(arena.call(cast(Builtin)arena.view(arena.at(body.data)).value,[zero,arena.natural_(0)]),[q,countBound]);
						auto formula=primitive(arena.mul(zero,zero,true),[add(power,minus),unary(arena.inv(zero),diff)]);
						next=add(mask(not_(nz),z),mask(nz,add(mask(not_(neq),count),mask(neq,formula)))); rule=BindingRule.rangeGeometric; extra=q.id;
					}
				}
				if(next==BoundTerm.init&&(sort==Sort.natural||sort==Sort.integer)){
					auto body=at(nodes[current.a].a),lift=body;
					foreach(c;[Builtin.castNZ,Builtin.castZQ,Builtin.castQR]){
						if(type(lift)==scalarType(builtinInfo(c).args[0])) lift=primitive(arena.call(c,[arena.number(Number(0),builtinInfo(c).args[0])]),[lift]);
					}
					auto lifted=finiteSum(inheritHint(at(current.a),lambda(lift)),at(current.b));
					next=primitive(arena.call(sort==Sort.natural?Builtin.floorN:Builtin.floorR,[arena.real_(0)]),[lifted]); rule=BindingRule.rangeLift;
				}
			}else if(domains&&current.op==BoundOp.apply&&nodes[current.b].op==BoundOp.bottom){
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
			if(next==BoundTerm.init&&additive(current)&&(nodes[current.a].op==BoundOp.bottom||nodes[current.b].op==BoundOp.bottom)){
				next=bottom(ctx,types[current.type]);rule=BindingRule.addBottom;
			}
			if(domains&&next==BoundTerm.init&&(current.op==BoundOp.primitive||current.op==BoundOp.guard)&&current.a!=uint.max&&nodes[current.a].op==BoundOp.bottom){ next=bottom(ctx,type(at(result.output))); rule=BindingRule.shortCircuit; }
			if(domains&&next==BoundTerm.init){
				if(current.op==BoundOp.get&&nodes[current.b].op==BoundOp.scalar&&!totalScalar(at(current.b))){
					auto source=arena.at(nodes[current.b].data),d=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true)); exhausted|=d.exhausted;
					if(d.output==arena.boolean(false)){
						extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,d);
						next=bottom(ctx,type(at(result.output))); rule=BindingRule.getScalarUndefined;
					}
				}
				if(next==BoundTerm.init&&current.op==BoundOp.get&&nodes[current.a].op==BoundOp.vectorCons&&nodes[current.b].op==BoundOp.scalar&&arena.isNumber(arena.at(nodes[current.b].data))){
					auto index=arena.number(arena.at(nodes[current.b].data)).re,cons=nodes[current.a];
					if(index.small){
						next=index.integer?sequence(at(cons.a),get(at(cons.b),scalar(ctx,arena.natural_(cast(ulong)index.integer-1)))):sequence(at(cons.b),at(cons.a));
						rule=BindingRule.getCons;
					}
				}
				if(current.op==BoundOp.get&&(nodes[current.a].op==BoundOp.bottom||nodes[current.b].op==BoundOp.bottom)){
					next=bottom(ctx,type(at(result.output))); rule=BindingRule.getBottom;
				}else if(next==BoundTerm.init&&(current.op==BoundOp.tensor||current.op==BoundOp.get||current.op==BoundOp.first||current.op==BoundOp.rest)){
					SpectralSolution spectrum; next=spectral(at(result.output),spectrum);
					if(next!=BoundTerm.init){ extra=cast(uint)spectra.length; spectra~=spectrum; rule=BindingRule.tensorSpectral; }
					else{
						next=liftSpectrum(at(result.output),extra);
						if(next!=BoundTerm.init) rule=BindingRule.tensorSpectrumCast;
						else{ next=tensorEval(at(result.output)); if(next!=BoundTerm.init) rule=current.op==BoundOp.tensor&&current.data==TensorOp.power&&node(next).op==BoundOp.tensor?BindingRule.tensorPower:BindingRule.tensorEval; }
					}
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
						if(next==BoundTerm.init) next=solveAffineRecurrence(at(result.output),solution);
						if(next==BoundTerm.init) next=solveLinearRecurrence(at(result.output),solution);
						if(next==BoundTerm.init) next=solvePrefixRecurrence(at(result.output),solution);
						if(next!=BoundTerm.init){ extra=cast(uint)solutions.length; solutions~=solution; rule=BindingRule.fixedRecurrence; }
					}
				}else if(current.op==BoundOp.guard&&isTrue(current.a,false)){
					next=bottom(ctx,type(at(current.b))); rule=BindingRule.shortCircuit;
				}else if(current.op==BoundOp.primitive&&current.b==uint.max&&nodes[current.a].op==BoundOp.bottom){
					auto op=arena.view(arena.at(current.data)).op;
					if(op==Op.not_||op==Op.builtin){ next=bottom(ctx,type(at(result.output))); rule=BindingRule.shortCircuit; }
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
					}else if(current.op==BoundOp.domain&&nodes[current.a].op==BoundOp.fixed){
						DomainRank rank;
						if(rankDomain(at(current.a),rank)){
							extra=cast(uint)ranks.length; ranks~=rank;
							auto predicate=rank.iterations.length?rank.iterations[$-1].output:rank.lower.output!=Term.init?rank.result.output:arena.boolean(true);
							next=inheritHint(at(nodes[current.a].a),set(restoreBody(predicate,push(ctx,scalarType(rank.sort)),arena.variable(rank.sort,rank.variable)))); rule=BindingRule.domainFixedTotal;
						}
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
						if(rule==BindingRule.tensorSpectral) --spectra.length;
						next=BoundTerm.init; exhausted=true;
					}
					if(current.op==BoundOp.scalar&&!totalScalar(at(result.output))||
						(current.op==BoundOp.defined||current.op==BoundOp.holds)&&nodes[current.a].op==BoundOp.scalar) exhausted=true;
				}
			}
			// Try the original binder first: scalar narrowing can hide a geometric
			// power behind casts, and normalizing masks can obscure their bounds.
			if(next==BoundTerm.init&&current.op==BoundOp.summation&&steps<budget){
				auto function_=visit(at(current.a),depth+1);
				if(function_.output!=current.a){
					auto normalized=summation(at(function_.output)); ++steps;
					auto step=emit(BindingRule.congr,result.output,normalized.id,function_.proof),tail=visit(normalized,depth+1);
					auto rest=emit(BindingRule.trans,result.output,tail.output,step,tail.proof);
					result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
					active.set(t.id,false); memo.set(t.id,result); return result;
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
		normalizeClosed=&visit;
		auto result=visit(term,0); return BindingResult(term,at(result.output),exhausted,steps,proofs,result.proof,scalarDomains,solutions,ranks,spectra,sums);
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
	private string tensorDomainOperation(TypeId t,TensorOp op){
		auto v=pool.view(t);
		if(v.kind==TypeKind.vector) return "(TensorDomains.zip "~tensorOperation(v.fields[0],op)~" "~tensorDomainOperation(v.fields[0],op)~" "~v.dimension.lean~")";
		auto n=arena.view(scalarOperator(t,op));
		if(n.op==Op.builtin) return "(TensorDomains.builtin2 Functions."~builtinInfo(cast(Builtin)n.value).code~" (fun _ _ => True.intro))";
		return op==TensorOp.add?"TensorDomains.add":"TensorDomains.mul";
	}
	private string tensorDomainProof(BoundNode n){
		auto op=cast(TensorOp)n.data,ty=type(at(n.a)),v=pool.view(ty);
		if(op==TensorOp.add||op==TensorOp.mul) return tensorDomainOperation(ty,op);
		auto element=typeLeaf(ty),add=tensorOperation(element,TensorOp.add),mul=tensorOperation(element,TensorOp.mul);
		auto proofs=" "~tensorDomainOperation(element,TensorOp.add)~" "~tensorDomainOperation(element,TensorOp.mul),zero=tensorLiteral(element,0);
		if(op==TensorOp.dot) return "(TensorDomains.dot "~add~" "~mul~" "~(element==scalarType(Sort.complex)?"Value.conj":"id")~proofs~" "~(element==scalarType(Sort.complex)?"TensorDomains.conjugate":"TensorDomains.identity")~" "~zero~" "~v.dimension.lean~")";
		if(op==TensorOp.power) return "(TensorDomains.power "~add~" "~mul~proofs~" "~zero~" "~tensorLiteral(element,1)~" "~v.dimension.lean~")";
		auto dimensions=v.dimension.lean~" "~pool.view(v.fields[0]).dimension.lean;
		if(op==TensorOp.matmul) dimensions~=" "~pool.view(pool.view(type(at(n.b))).fields[0]).dimension.lean;
		return "(TensorDomains."~(op==TensorOp.matmul?"matmul":"matvec")~" "~add~" "~mul~proofs~" "~zero~" "~dimensions~")";
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
			case BoundOp.finiteSum:return "Summation.rangeValue";
			case BoundOp.summation:
				auto sort=elementSort(types[n.type]);
				return "(Summation.value "~(sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm")~")";
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
	private string exportDependent(BindingResult result){
		enforce(depth(context(result.input))==0,"dependent certificates require a closed context");
		string code="import QSym\nnamespace QSym.DependentCertificate\n";
		Table!(uint,bool) scalarNeeded,visited;
		void collect(BoundTerm t){
			if(visited.get(t.id,false)) return; visited.set(t.id,true); auto n=node(t);
			if(n.op==BoundOp.scalar||n.op==BoundOp.primitive) foreach(id;arena.viewPostorder(arena.at(n.data))) scalarNeeded.set(id,true);
			if(n.a!=uint.max) collect(at(n.a)); if(n.b!=uint.max) collect(at(n.b));
		}
		collect(result.input); collect(result.output);
		foreach(i;0..arena.length) if(scalarNeeded.get(cast(uint)i,false)) code~=leanSyntaxCode(arena,arena.at(cast(uint)i));
		string dim(Dimension d,string[] vars){
			if(d.index!=uint.max){ enforce(d.index<vars.length,"unbound exported dimension"); return vars[d.index]; }
			if(d.op.length) return "("~dim(d.left,vars)~d.op~dim(d.right,vars)~")";
			return replace(d.lean,"δ","ξ.natural");
		}
		string quotedDim(Dimension d,string[] vars,uint depth){
			bool bound; d.map((uint i){ bound|=i<depth; return Dimension.bound(i); });
			if(!bound){ auto closed=d.map((uint i)=>Dimension.bound(i-depth)); return "(.literal "~dim(closed,vars)~")"; }
			if(d.index!=uint.max) return "(.bound "~to!string(d.index)~")";
			return "(."~(d.op=="+"?"add":d.op=="*"?"mul":"pow")~" "~quotedDim(d.left,vars,depth)~" "~quotedDim(d.right,vars,depth)~")";
		}
		string quotedType(TypeId t,string[] vars,uint depth=0){
			auto v=pool.view(t);
			if(v.kind==TypeKind.unit) return ".unit";
			if(v.kind==TypeKind.type_) return ".type";
			if(v.kind==TypeKind.vector) return "(.vector "~quotedType(v.fields[0],vars,depth)~" "~(depth?quotedDim(v.dimension,vars,depth):dim(v.dimension,vars))~")";
			if(v.kind==TypeKind.tuple) return "(.pair "~quotedType(v.fields[0],vars,depth)~" "~quotedType(pool.tuple(v.fields[1..$]),vars,depth)~")";
			if(v.kind==TypeKind.set) return "(.set "~quotedType(v.fields[0],vars,depth)~")";
			if(v.kind==TypeKind.pi) return "(.piNat "~quotedType(v.fields[1],vars,depth+1)~")";
			if(v.kind==TypeKind.function_) return "(.arrow "~quotedType(v.fields[0],vars,depth)~" "~quotedType(v.fields[1],vars,depth)~")";
			foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean]) if(t==scalarType(s)) return "(.scalar ."~leanSort(s)~")";
			throw new Exception("unsupported dependent type");
		}
		string ty(TypeId t,string[] vars){ return "("~quotedType(t,vars)~" : Binding.Ty).denote"; }
		string tensorOp(TypeId t,TensorOp op,string[] vars){
			auto v=pool.view(t);
			return v.kind==TypeKind.vector?"(Tensor.zipValue "~tensorOp(v.fields[0],op,vars)~" "~dim(v.dimension,vars)~")":leanValueOperation(arena,scalarOperator(t,op));
		}
		string term(BoundTerm t,string[] vars) @safe{
			auto n=node(t);
			string child(uint id){ return term(at(id),vars); }
			switch(n.op){
				case BoundOp.variable:return "(some "~vars[n.data]~")";
				case BoundOp.scalar:return "(n"~to!string(n.data)~".eval ξ)";
				case BoundOp.global:return "(some (γ ("~ty(type(t),vars)~") "~to!string(n.data)~"))";
				case BoundOp.typeValue:return "(some ("~quotedType(typeDenoted(t),vars)~" : Binding.Ty))";
				case BoundOp.unit:return "(some ())";
				case BoundOp.vectorNil:return "Tensor.nilValue";
				case BoundOp.bottom:return "(none : Option ("~ty(type(t),vars)~"))";
				case BoundOp.lambda,BoundOp.set:
					auto name="x"~to!string(vars.length),param=pool.view(type(t)).fields[0];
					if(n.op==BoundOp.set) return "(some {"~name~" : "~ty(param,vars)~" | "~term(at(n.a),[name]~vars)~" = some true})";
					return "(some (fun "~name~" : "~ty(param,vars)~" => "~term(at(n.a),[name]~vars)~"))";
				case BoundOp.apply:
					if(pool.view(type(at(n.a))).kind==TypeKind.pi) return "(Dependent.apply "~child(n.a)~" "~dim(dimension(at(n.b)),vars)~")";
					return "("~child(n.a)~".bind (fun f => "~child(n.b)~".bind f))";
				case BoundOp.sequence:return "("~child(n.a)~".bind (fun _ => "~child(n.b)~"))";
				case BoundOp.typeEq:return "(Binding.typeEqValue "~child(n.a)~" "~child(n.b)~")";
				case BoundOp.domain:
					return "("~(pool.view(type(at(n.a))).kind==TypeKind.pi?"Dependent.inputDomain":"Binding.inputDomain")~" "~child(n.a)~")";
				case BoundOp.tensor:
					auto op=cast(TensorOp)n.data,v=pool.view(type(at(n.a))),element=typeLeaf(type(at(n.a))); string operation;
					if(op==TensorOp.add||op==TensorOp.mul) operation=tensorOp(type(t),op,vars);
					else{
						auto add=tensorOp(element,TensorOp.add,vars),mul=tensorOp(element,TensorOp.mul,vars),zero=tensorLiteral(element,0),size=dim(v.dimension,vars);
						if(op==TensorOp.dot) operation="(Tensor.dotValue "~add~" "~mul~" "~(element==scalarType(Sort.complex)?"Value.conj":"id")~" "~zero~" "~size~")";
						else if(op==TensorOp.power) operation="(Tensor.matrixPowerValue "~add~" "~mul~" "~zero~" "~tensorLiteral(element,1)~" "~size~")";
						else{ auto row=pool.view(v.fields[0]); size~=" "~dim(row.dimension,vars);
							if(op==TensorOp.matmul) size~=" "~dim(pool.view(pool.view(type(at(n.b))).fields[0]).dimension,vars);
							operation="(Tensor."~(op==TensorOp.matmul?"matmulValue":"matvecValue")~" "~add~" "~mul~" "~zero~" "~size~")";
						}
					}
					return "("~operation~" "~child(n.a)~" "~child(n.b)~")";
				case BoundOp.fixed:throw new Exception("dependent fixed-point certificates are not supported yet");
				default:return "("~valueOperation(n)~" "~child(n.a)~(n.b==uint.max?"":" "~child(n.b))~")";
			}
		}
		auto parameters=" (γ : Dependent.Globals) (ξ : Env)",outputType=ty(type(result.input),[]);
		code~="noncomputable def input"~parameters~" : Option ("~outputType~") := "~term(result.input,[])~"\n";
		code~="noncomputable def output"~parameters~" : Option ("~outputType~") := "~term(result.output,[])~"\n";
		code~="theorem sound"~parameters~" : input γ ξ = output γ ξ := rfl\n";
		code~="theorem domain"~parameters~" : Value.Defined (input γ ξ) ↔ Value.Defined (output γ ξ) := Iff.of_eq (congrArg Value.Defined (sound γ ξ))\n";
		return code~"#qsym_check_axioms sound\n#qsym_check_axioms domain\nend QSym.DependentCertificate\n";
	}
	string exportLean(BindingResult result,bool lowerResult=false){
		if(telescope_) return exportDependent(result);
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
		foreach(i,r;result.ranks){
			auto prefix="QSym.BindingRank"~to!string(i);
			if(!r.iterations.length) code~=replace(replace(scalarExport(arena,r.result),"import QSym\n",""),"QSym.Certificate",prefix~".Certificate");
			if(r.lower.output!=Term.init){
				code~=replace(replace(scalarExport(arena,r.lower),"import QSym\n",""),"QSym.Certificate",prefix~".Lower");
				code~=replace(replace(scalarExport(arena,r.upper),"import QSym\n",""),"QSym.Certificate",prefix~".Upper");
			}
			foreach(j,step;r.iterations) code~=replace(replace(scalarExport(arena,step),"import QSym\n",""),"QSym.Certificate",prefix~".Step"~to!string(j));
			foreach(j,d;r.leaves){
				auto p=prefix~".Leaf"~to!string(j),part=replace(exportDomainLean(arena,d.value,d.domain),"import QSym\n","");
				part=replace(part,"QSym.Certificate",p~".Certificate");
				code~=replace(part,"QSym.DomainCertificate",p~".DomainCertificate");
			}
		}
		foreach(i,s;result.solutions) foreach(j,f;s.facts){
			auto prefix="QSym.Linear"~to!string(i)~"_"~to!string(j),part=replace(exportDomainLean(arena,f.input,f.domain),"import QSym\n","");
			part=replace(part,"QSym.Certificate",prefix~".Certificate");
			code~=replace(part,"QSym.DomainCertificate",prefix~".DomainCertificate");
			code~=replace(replace(scalarExport(arena,f.value),"import QSym\n",""),"QSym.Certificate",prefix~".ValueCertificate");
		}
		foreach(i,s;result.spectra){
			foreach(kind,fs;[s.parameters,s.checks]) foreach(j,f;fs){
				auto prefix="QSym.Spectral"~to!string(i)~"_"~to!string(kind)~"_"~to!string(j);
				auto part=replace(exportDomainLean(arena,f.input,f.domain),"import QSym\n","");
				part=replace(part,"QSym.Certificate",prefix~".Certificate"); code~=replace(part,"QSym.DomainCertificate",prefix~".DomainCertificate");
				if(f.value.traced) code~=replace(replace(scalarExport(arena,f.value),"import QSym\n",""),"QSym.Certificate",prefix~".ValueCertificate");
			}
		}
		code~="namespace QSym.BindingCertificate\nattribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv\n";
		bool[] used=new bool[nodes.length]; uint[] stack=[result.input.id,result.output.id];
		foreach(p;result.proofs){ stack~=p.from; stack~=p.to; }
		foreach(s;result.sums) stack~=s.candidate;
		foreach(p;result.proofs) if(p.rule==BindingRule.sumInterval||p.rule==BindingRule.sumBounds||p.rule==BindingRule.sumBoundedAdd) stack~=p.extra;
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
		foreach(r;result.ranks) foreach(step;r.iterations) scalarNodes~=arena.viewPostorder(step.output);
		foreach(r;result.ranks) if(r.lower.output!=Term.init) scalarNodes~=arena.viewPostorder(r.result.output);
		foreach(r;result.ranks) if(r.step!=Term.init) foreach(t;[r.slope,r.bound,r.step]) scalarNodes~=arena.viewPostorder(t);
		foreach(s;result.solutions) foreach(f;s.facts){ scalarNodes~=arena.viewPostorder(f.input); scalarNodes~=arena.viewPostorder(arena.castTo(f.value.output,arena.sort(f.input))); }
		foreach(s;result.spectra){
			foreach(fs;[s.parameters,s.checks]) foreach(f;fs){
				scalarNodes~=arena.viewPostorder(f.input);
				if(f.value.traced) scalarNodes~=arena.viewPostorder(arena.castTo(f.value.output,arena.sort(f.input)));
				Number value; if(literalNumber(f.input,value)&&(value.zero||value.one)) scalarNodes~=arena.viewPostorder(arena.number(value,arena.sort(f.input)));
			}
			scalarNodes~=arena.viewPostorder(arena.number(Number(0),elementSort(typeLeaf(type(at(s.source))))));
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
				case BoundOp.finiteSum,BoundOp.summation,BoundOp.primitive,BoundOp.member,BoundOp.subset,BoundOp.domain,BoundOp.defined,BoundOp.holds,BoundOp.guard,BoundOp.typeEq,BoundOp.equal,BoundOp.vectorCons,BoundOp.pair,BoundOp.first,BoundOp.rest,BoundOp.get,BoundOp.tensor:
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
			foreach(ri,r;result.ranks) if(r.source==i){
				auto prefix="QSym.BindingRank"~to!string(ri),field=leanSort(r.sort),eta="({ ξ with "~field~" := fun i => if i = "~to!string(r.variable)~" then x else ξ."~field~" i })";
				string constant(Term t){ return "((n"~to!string(t.id)~".eval ξ).getD 0)"; }
				string leafProof(uint q){ foreach(j,l;r.leaves) if(l.node==q) return "("~prefix~".Leaf"~to!string(j)~".DomainCertificate.domain_correct "~eta~")"; assert(0,"missing rank leaf"); }
				string value(uint q){ return "("~name(q)~".eval ξ "~env~")"; }
				string dp(uint q){
					auto z=nodes[q]; if(!depends(at(q),1)) return "(.pure (fun x => Value.Defined "~value(q)~"))";
					if(z.op==BoundOp.apply) return "(.call (fun x => "~value(z.b)~"))";
					auto op=z.op==BoundOp.primitive?arena.view(arena.at(z.data)).op:Op.variable;
					if(z.op==BoundOp.guard||op==Op.mask||op==Op.and_||op==Op.or_){
						auto yes="(.pure (fun x => "~value(z.a)~" = some true))",no="(.pure (fun x => "~value(z.a)~" = some false))",d=dp(z.b);
						return z.op==BoundOp.guard?"(.both "~yes~" "~d~")":op==Op.or_?"(.either "~yes~" (.both "~no~" "~d~"))":"(.either "~no~" (.both "~yes~" "~d~"))";
					}
					auto x=dp(z.a); return z.b==uint.max?x:"(.both "~x~" "~dp(z.b)~")";
				}
				string erase(uint q){
					auto z=nodes[q]; if(!depends(at(q),1)) return "Iff.rfl";
					if(z.op==BoundOp.apply) return "(SetFixed.defined_bind _ _)";
					auto op=z.op==BoundOp.primitive?arena.view(arena.at(z.data)).op:Op.variable;
					if(z.op==BoundOp.guard||op==Op.mask||op==Op.and_||op==Op.or_){
						auto d="(and_congr Iff.rfl "~erase(z.b)~")",lemma=z.op==BoundOp.guard?"SetFixed.defined_guard":op==Op.mask?"Value.defined_mask":op==Op.and_?"Value.defined_and":"Value.defined_or";
						return "(("~lemma~" _ _).trans "~(z.op==BoundOp.guard?d:"(or_congr Iff.rfl "~d~")")~")";
					}
					string lemma;
					if(z.op==BoundOp.sequence) lemma="SetFixed.defined_sequence _ _";
					else if(op==Op.builtin){ auto qv=arena.view(arena.at(z.data)),info=builtinInfo(cast(Builtin)qv.value); lemma="SetFixed.defined_total"~to!string(qv.arity)~" Functions."~info.code~(qv.arity==1?" (fun _ => True.intro) _":" (fun _ _ => True.intro) _ _"); }
					else{
						auto s=op==Op.add?"add":op==Op.mul?"mul":op==Op.lt?"lt":op==Op.le?"le":op==Op.nonzero?"nonzero":op==Op.not_?"not":op==Op.conj?"conj":"map _";
						lemma="Value.defined_"~s~(z.b==uint.max?" _":" _ _");
					}
					return "(("~lemma~").trans "~(z.b==uint.max?erase(z.a):"(and_congr "~erase(z.a)~" "~erase(z.b)~")")~")";
				}
				Term previous; string previousTotal,previousFunction; bool restricted;
				string substituteProof(Term t){
					auto z=arena.view(t); if(t==arena.variable(r.sort,r.variable)) return "h";
					if(!z.arity) return "rfl";
					auto x=substituteProof(arena.at(z.a)),y=z.arity==1?"":substituteProof(arena.at(z.b)),op=leanValueOperation(arena,t);
					if(x=="rfl"&&(y==""||y=="rfl")) return "rfl";
					return z.arity==1?"(congrArg "~op~" "~x~")":"(congrArg₂ "~op~" "~x~" "~y~")";
				}
				string rankProof(uint q){
					auto z=nodes[q]; if(!depends(at(q),1)) return "(SetFixed.pure_rank "~leafProof(q)~")";
					if(z.op==BoundOp.apply){
						if(r.step!=Term.init) return "(SetFixed.call_measure x "~constant(r.slope)~" "~constant(r.bound)~" "~constant(r.step)~" "~leafProof(z.b)~")";
						if(previous==Term.init) return "(SetFixed.call_rank x "~leafProof(z.b)~")";
						if(restricted) return "(SetFixed.call_rank_test x "~previousFunction~" "~leafProof(z.b)~" "~previousTotal~" (fun y h => "~substituteProof(previous)~"))";
						return "(SetFixed.call_test "~previousFunction~" "~leafProof(z.b)~" "~previousTotal~" (fun y h => "~substituteProof(previous)~"))";
					}
					auto op=z.op==BoundOp.primitive?arena.view(arena.at(z.data)).op:Op.variable;
					if(z.op==BoundOp.guard||op==Op.mask||op==Op.and_||op==Op.or_){
						auto d=rankProof(z.b);
						return z.op==BoundOp.guard?"(SetFixed.both_rank (SetFixed.true_rank "~leafProof(z.a)~") "~d~")":"(SetFixed."~(op==Op.or_?"or_test":"mask_test")~" "~leafProof(z.a)~" "~d~")";
					}
					auto x=rankProof(z.a); return z.b==uint.max?x:"(SetFixed.both_rank "~x~" "~rankProof(z.b)~")";
				}
				auto body=nodes[n.a].a,tag=to!string(ri),d="(drec"~tag~dimArg~" γ ξ ρ)",p="(rec"~id~dimArg~" γ ξ ρ)";
				code~="noncomputable def drec"~tag~args~" : SetFixed.Predicate "~a~" := "~dp(body)~"\n";
				code~="theorem erase"~tag~args~" (g : "~a~" → Option "~b~") (x : "~a~") : Value.Defined ("~p~".eval g x) ↔ "~d~".eval {y | Value.Defined (g y)} x :=\n  ((Iff.of_eq (congrArg Value.Defined "~programProof(body)~")).symm).trans "~erase(body)~"\n";
				if(r.iterations.length){
					auto full=dimArg~" γ ξ ρ";
					previous=arena.boolean(false); previousTotal="(fun _ => ⟨false, rfl⟩)"; previousFunction="(fun (_ : "~a~") => some false)";
					string subset="(SetFixed.Predicate.start_least "~d~")",lastTest,lastSet;
					foreach(j,step;r.iterations){
						auto name="iter"~tag~"_"~to!string(j),function_="("~name~full~")",test="("~name~"_test"~full~")";
						code~="noncomputable def "~name~args~" (x : "~a~") : Option Bool := n"~to!string(step.output.id)~".eval "~eta~"\n";
						code~="theorem "~name~"_test"~args~" (x : "~a~") : SetFixed.Test ("~function_~" x) ("~d~".eval {y | "~previousFunction~" y = some true} x) :=\n  SetFixed.Test.refine "~rankProof(body)~" ("~prefix~".Step"~to!string(j)~".refinement "~eta~")\n";
						lastSet="{x | "~function_~" x = some true}"; lastTest=test;
						code~="theorem "~name~"_subset"~args~" : "~lastSet~" ⊆ "~d~".least := SetFixed.Predicate.step_least "~d~" "~subset~" (fun x => ("~test~" x).1)\n";
						subset="("~name~"_subset"~full~")"; previous=step.output; previousTotal="(fun x => ("~test~" x).2)"; previousFunction=function_;
					}
					code~="theorem domainTotal"~tag~args~" : Binding.inputDomain ("~name(cast(uint)i)~".eval ξ ρ) = some "~lastSet~" :=\n  SetFixed.domain_set "~p~" "~d~" _ (fixed"~id~full~") (erase"~tag~full~") _ (SetFixed.Predicate.least_of_stable "~d~" _ "~subset~" (fun x => ("~lastTest~" x).1.symm))\n";
				}else if(r.lower.output!=Term.init){
					auto full=dimArg~" γ ξ ρ",function_="(candidate"~tag~full~")",test="(candidate"~tag~"_test"~full~")",set_="{x | "~function_~" x = some true}";
					code~="noncomputable def candidate"~tag~args~" (x : ℕ) : Option Bool := n"~to!string(r.result.output.id)~".eval "~eta~"\n";
					code~="theorem candidate"~tag~"_test"~args~" (x : ℕ) : SetFixed.Test ("~function_~" x) ("~d~".eval {y | y < x} x) :=\n  SetFixed.Test.refine "~rankProof(body)~" ("~prefix~".Certificate.refinement "~eta~")\n";
					previous=r.result.output; previousTotal="(fun x => ("~test~" x).2)"; previousFunction=function_; restricted=true;
					auto self="(And.intro Iff.rfl ("~test~" x).2)";
					code~="theorem lower"~tag~args~" (x : ℕ) : "~function_~" x = some true → "~d~".eval {y | y < x ∧ "~function_~" y = some true} x :=\n  SetFixed.rank_true (SetFixed.implies_test "~self~" "~rankProof(body)~") ("~prefix~".Lower.refinement "~eta~")\n";
					restricted=false;
					code~="theorem upper"~tag~args~" (x : ℕ) : "~d~".eval "~set_~" x → "~function_~" x = some true :=\n  SetFixed.rank_true (SetFixed.implies_test "~rankProof(body)~" "~self~") ("~prefix~".Upper.refinement "~eta~")\n";
					code~="theorem domainTotal"~tag~args~" : Binding.inputDomain ("~name(cast(uint)i)~".eval ξ ρ) = some "~set_~" :=\n  SetFixed.domain_set "~p~" "~d~" _ (fixed"~id~full~") (erase"~tag~full~") _ (SetFixed.Predicate.least_nat_of_closed "~d~" _ (lower"~tag~full~") (upper"~tag~full~"))\n";
				}else if(r.step!=Term.init){
					auto c=constant(r.slope),bnd=constant(r.bound),e=constant(r.step),full=dimArg~" γ ξ ρ";
					code~="theorem rank"~tag~args~" (x : ℝ) : "~d~".eval {y | "~bnd~" < "~c~" * x ∧ "~c~" * y + "~e~" ≤ "~c~" * x} x :=\n  SetFixed.rank_true "~rankProof(body)~" ("~prefix~".Certificate.refinement "~eta~")\n";
					auto positive="(SetFixed.positive_step "~e~" (Numeric.sound ξ (.ltR (.real 0) n"~to!string(r.step.id)~") (.bool true) (of_decide_eq_true rfl)))";
					code~="theorem domainTotal"~tag~args~" : Binding.inputDomain ("~name(cast(uint)i)~".eval ξ ρ) = some Set.univ :=\n  SetFixed.domain_set "~p~" "~d~" _ (fixed"~id~full~") (erase"~tag~full~") _ (SetFixed.Predicate.total_measure "~d~" (fun x => "~c~" * x) "~bnd~" "~e~" "~positive~" (rank"~tag~full~"))\n";
				}else{
					code~="theorem rank"~tag~args~" (x : ℕ) : "~d~".eval {y | y < x} x :=\n  SetFixed.rank_true "~rankProof(body)~" ("~prefix~".Certificate.refinement "~eta~")\n";
					code~="theorem domainTotal"~tag~args~" : Binding.inputDomain ("~name(cast(uint)i)~".eval ξ ρ) = some Set.univ :=\n  SetFixed.domain_univ "~p~" "~d~" _ (fixed"~id~dimArg~" γ ξ ρ) (erase"~tag~dimArg~" γ ξ ρ) (rank"~tag~dimArg~" γ ξ ρ)\n";
				}
			}
			foreach(si,s;result.solutions) if(s.source==i){
				if(s.prefix){
					auto leaf=pool.view(type(at(s.source))).fields[1],sort=elementSort(leaf),add=tensorOperation(leaf,TensorOp.add);
					auto ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					auto emptyEnv="(Binding.Env.cons (a := "~leanType(type(at(s.source)))~") none ρ)";
					auto base="("~name(s.base)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some 0) "~emptyEnv~"))";
					auto forcing="(fun (x : Option ℕ) => "~name(s.delta)~".eval ξ (Binding.Env.cons (a := .scalar .natural) x "~emptyEnv~"))";
					auto hp="(fun g x => ("~programProof(nodes[n.a].a)~").symm)";
					code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ := Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (Summation.solve_prefix "~add~" "~ha~" (rec"~id~dimArg~" γ ξ ρ) "~(s.left?"true":"false")~" "~base~" "~forcing~" "~hp~"))\n";
					continue;
				}
				if(s.affine||s.order){
					auto leaf=pool.view(type(at(s.source))).fields[1];
					struct Total{ string value,proof; }
					Table!(uint,uint) totalIds; Total[] totals;
					Total total(Term t){
						auto old=totalIds.get(t.id,uint.max); if(old!=uint.max) return totals[old];
						auto q=arena.view(t),source="n"~to!string(t.id)~".eval ξ",tag="affine"~id~"_"~to!string(t.id); Total v;
						if(!q.arity){
							if((q.sort==Sort.real_||q.sort==Sort.complex)&&arena.isNumber(t)&&(arena.number(t).zero||arena.number(t).one)){
								auto suffix=q.sort==Sort.complex?"C":"R"; v.value="("~(arena.number(t).zero?"0":"1")~" : "~(q.sort==Sort.complex?"ℂ":"ℝ")~")"; v.proof="AffineRecurrence."~(arena.number(t).zero?"zero":"one")~suffix;
							}else{ v.value="(("~source~").getD "~(q.sort==Sort.boolean?"false":"0")~")"; v.proof="rfl"; }
						}else{
							auto x=total(arena.viewChild(t,0)); auto op=leanValueOperation(arena,t);
							if(q.op==Op.builtin){
								auto f="Functions."~builtinInfo(cast(Builtin)q.value).code;
								if(q.arity==1){ v.value="("~f~".value "~x.value~")"; v.proof="Eq.trans (congrArg "~op~" "~x.proof~") (Tensor.apply_some "~f~" "~x.value~" True.intro)"; }
								else{ auto y=total(arena.viewChild(t,1)); v.value="("~f~".value "~x.value~" "~y.value~")"; v.proof="Eq.trans (congrArg₂ "~op~" "~x.proof~" "~y.proof~") (AffineRecurrence.apply2_some "~f~" "~x.value~" "~y.value~" True.intro)"; }
							}else if(q.op==Op.add||q.op==Op.mul){
								auto y=total(arena.viewChild(t,1)); v.value="("~x.value~(q.op==Op.add?" + ":" * ")~y.value~")"; v.proof="congrArg₂ "~op~" "~x.proof~" "~y.proof;
							}else{ v.value=q.op==Op.pow?"("~x.value~" ^ "~to!string(q.value)~")":q.op==Op.abs?"|"~x.value~"|":"(star "~x.value~")"; v.proof="congrArg "~op~" "~x.proof; }
						}
						code~="theorem "~tag~" (ξ : Env) : "~source~" = some "~v.value~" := "~v.proof~"\n";
						v.proof="("~tag~" ξ)"; totalIds.set(t.id,cast(uint)totals.length); totals~=v; return v;
					}
					string value(uint q){ return total(arena.at(nodes[q].data)).value; }
					string expression(uint q){
						auto z=nodes[q];
						if(z.op==BoundOp.scalar) return "(.constant "~value(q)~")";
						if(z.op==BoundOp.apply) return s.order?"(.previous ⟨"~to!string(s.order-cast(uint)arena.number(arena.at(nodes[nodes[z.b].b].data)).re.integer)~", of_decide_eq_true rfl⟩)":".previous";
						auto kind=arena.view(arena.at(z.data)),add=arena.view(scalarOperator(leaf,TensorOp.add));
						if(kind.op==add.op&&kind.value==add.value) return "(.add "~expression(z.a)~" "~expression(z.b)~")";
						return nodes[z.a].op==BoundOp.scalar?"(.left "~value(z.a)~" "~expression(z.b)~")":"(.right "~expression(z.a)~" "~value(z.b)~")";
					}
					string constants(uint q){
						auto z=nodes[q];
						if(z.op==BoundOp.scalar) return total(arena.at(z.data)).proof;
						if(s.order&&z.op==BoundOp.apply) return "(congrArg (fun z : Option ℕ => z.bind g) (LinearRecurrence.lag x "~to!string(s.order)~" "~to!string(arena.number(arena.at(nodes[nodes[z.b].b].data)).re.integer)~" (of_decide_eq_true rfl)))";
						if(z.op==BoundOp.vectorCons||z.op==BoundOp.primitive&&z.b!=uint.max)
							return "(congrArg₂ "~valueOperation(z)~" "~constants(z.a)~" "~constants(z.b)~")";
						return "rfl";
					}
					string raw(uint q){ auto z=nodes[q]; return z.op==BoundOp.scalar?"(n"~to!string(z.data)~".eval ξ)":z.op==BoundOp.vectorNil?"Tensor.nilValue":"(Tensor.consValue "~raw(z.a)~" "~raw(z.b)~")"; }
					auto add=tensorOperation(leaf,TensorOp.add),mul=tensorOperation(leaf,TensorOp.mul),sort=elementSort(leaf);
					auto suffix=sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":"";
					auto ha=suffix.length?"AffineRecurrence.add"~suffix:"rfl",hm=suffix.length?"AffineRecurrence.mul"~suffix:"rfl";
					auto body=nodes[n.a].a;
					auto get=nodes[nodes[s.target].a],product=nodes[get.a],matrix=nodes[product.a].a;
					auto expr=expression(s.delta),hmat=constants(matrix),hv=constants(product.b);
					auto field=sort==Sort.complex?"C":sort==Sort.real_?"R":"";
					auto hz=field.length?"(Option.some.inj AffineRecurrence.zero"~field~")":"rfl",ho=field.length?"(Option.some.inj AffineRecurrence.one"~field~")":"rfl";
					if(s.order){
						string eta="({ ξ with natural := fun i => if i = "~to!string(s.variable)~" then x else ξ.natural i })";
						string specialized(uint q,uint index){
							auto z=nodes[q]; if(z.op==BoundOp.scalar) return "rfl";
							if(z.op==BoundOp.variable) return index==uint.max?"(AffineRecurrence.apply2_some Functions.addN x "~to!string(s.order)~" True.intro).symm":"rfl";
							auto a=specialized(z.a,index),op=valueOperation(z);
							return z.b==uint.max?"(congrArg "~op~" "~a~")":"(congrArg₂ "~op~" "~a~" "~specialized(z.b,index)~")";
						}
						string fact(uint q,uint index){
							foreach(j,f;s.facts) if(f.node==q&&f.index==index){
								auto p="QSym.Linear"~to!string(si)~"_"~to!string(j),e=index==uint.max?eta:"ξ";
								auto at=index==uint.max?"x+"~to!string(s.order):to!string(index),rho=replace(env,"(some x)","(some ("~at~"))");
								auto bridge="(show "~name(q)~".eval ξ "~rho~" = n"~to!string(f.input.id)~".eval "~e~" from "~specialized(q,index)~")";
								return "(Eq.trans "~bridge~" (LinearRecurrence.known ("~p~".DomainCertificate.domain_correct "~e~") ("~p~".ValueCertificate.refinement "~e~")))";
							}
							assert(0,"missing recurrence fact");
						}
						string select(uint q,uint index){
							if(index==uint.max&&q==s.delta) return constants(q);
							if(!depends(at(q),1)){
								foreach(f;s.facts) if(f.node==q&&f.index==index) return "(Eq.trans "~fact(q,index)~" "~total(arena.castTo(f.value.output,sort)).proof~")";
								assert(0,"missing recurrence seed");
							}
							uint test,yes,no; bool reverse; enforce(recurrenceBranches(q,test,yes,no,reverse),"missing recurrence branch"); bool selected;
							foreach(f;s.facts) if(f.node==test&&f.index==index) selected=f.value.output==arena.boolean(true);
							return "(Eq.trans (LinearRecurrence."~(reverse?"select_rev":"select")~" "~add~" "~ha~" "~(selected?"true":"false")~" _ _ "~fact(test,index)~") "~select(selected?yes:no,index)~")";
						}
						string cases(string[] proofs){
							auto r="(fun i => i.elim0)"; foreach_reverse(p;proofs) r="(Fin.cases "~p~" "~r~")"; return r;
						}
						string vector(string[] values){
							auto r="(fun i : Fin 0 => i.elim0)"; foreach_reverse(v;values) r="(Fin.cons "~v~" "~r~")"; return r;
						}
						string[] seeds,baseProofs,eqs;
						foreach(j,seed;s.seeds){ seeds~=total(seed).value; baseProofs~="(Eq.trans ("~programProof(body)~").symm "~select(body,cast(uint)j)~")"; }
						foreach(j;0..s.order+1) eqs~="rfl";
						auto heq="(funext "~cases(eqs)~")"; string[] rows; foreach(j;0..s.order+1) rows~=heq;
						hmat="(Eq.trans "~hmat~" (congrArg some (funext "~cases(rows)~")))";
						hv="(Eq.trans "~hv~" (congrArg some "~heq~"))";
						auto hb="(fun g => "~cases(baseProofs)~")",hs="(fun g x => Eq.trans ("~programProof(body)~").symm "~select(body,uint.max)~")";
						code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (LinearRecurrence.solve_matrix (k := "~to!string(s.order-1)~") (rec"~id~dimArg~" γ ξ ρ) "~add~" "~mul~" "~ha~" "~hm~" "~expr~" "~vector(seeds)~" "~hb~" "~hs~" "~tensorLiteral(leaf,0)~" "~tensorLiteral(leaf,1)~" "~hz~" "~ho~" "~raw(matrix)~" "~raw(product.b)~" "~hmat~" "~hv~"))\n";
						continue;
					}
					auto base=value(s.base),hp="(fun g x => Eq.trans ("~programProof(body)~").symm "~constants(body)~")";
					code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (AffineRecurrence.solve_matrix (rec"~id~dimArg~" γ ξ ρ) "~add~" "~mul~" "~ha~" "~hm~" "~base~" "~expr~" "~hp~" "~tensorLiteral(leaf,0)~" "~tensorLiteral(leaf,1)~" "~hz~" "~ho~" "~raw(matrix)~" "~raw(product.b)~" "~hmat~" "~hv~"))\n";
					continue;
				}
				auto base="(n"~to!string(nodes[s.base].data)~".eval ξ)",delta="(n"~to!string(nodes[s.delta].data)~".eval ξ)";
				if(s.cutoff){
					auto hp="(fun g x => ("~programProof(nodes[n.a].a)~").symm)";
					auto lemma=s.band==2?"solve_nat_interval":s.band==1?"solve_nat_cutoff_lt":"solve_nat_cutoff";
					auto lower=s.band==2?" ((n"~to!string(nodes[s.lower].data)~".eval ξ).getD 0)":"";
					auto side=s.band?" (of_decide_eq_true rfl)":"";
					code~="theorem solve"~id~args~" : "~name(cast(uint)i)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ :=\n"~
						"  Eq.trans (fixed"~id~dimArg~" γ ξ ρ) (congrArg some (Recursion."~lemma~" (rec"~id~dimArg~" γ ξ ρ) ("~base~".getD 0)"~lower~" ("~delta~".getD 0)"~side~" "~hp~"))\n";
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
		foreach(si,s;result.spectra){
			auto tag=to!string(si),source=nodes[s.source],powerNode=nodes[source.a],element=typeLeaf(type(at(s.source))),sort=elementSort(element);
			auto add=tensorOperation(element,TensorOp.add),mul=tensorOperation(element,TensorOp.mul);
			auto suffix=sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":sort==Sort.real_?"R":"C";
			auto ha=sort==Sort.real_||sort==Sort.complex?"rfl":"AffineRecurrence.add"~suffix,hm=sort==Sort.real_||sort==Sort.complex?"rfl":"AffineRecurrence.mul"~suffix;
			auto pow="Functions.pow"~suffix~"N.apply",hp="Spectral.pow"~suffix;
			auto hz=sort==Sort.real_||sort==Sort.complex?"(Option.some.inj AffineRecurrence.zero"~suffix~")":sort==Sort.rational?"(div_one (0 : ℚ))":"rfl",ho=sort==Sort.real_||sort==Sort.complex?"(Option.some.inj AffineRecurrence.one"~suffix~")":sort==Sort.rational?"(div_one (1 : ℚ))":"rfl";
			auto units=" "~tensorLiteral(element,0)~" "~tensorLiteral(element,1)~" "~hz~" "~ho;
			string raw(Term t){ return "(n"~to!string(t.id)~".eval ξ)"; }
			string val(Term t){ Number v; return !s.cubeZero&&literalNumber(t,v)&&(v.zero||v.one)?"("~(v.zero?"0":"1")~" : "~"("~leanType(element)~" : Binding.Ty).denote"~")":"("~raw(t)~".getD 0)"; }
			string[uint] totalProofs;
			string total(Term t){
				if(s.zeroRoot) if(auto old=t.id in totalProofs) return *old;
				foreach(j,f;s.parameters) if(f.input==t){
					auto id="spectral"~tag~"_"~to!string(j),v=val(t),h="Spectral.some_of_domain 0 "~raw(t)~" (QSym.Spectral"~tag~"_0_"~to!string(j)~".DomainCertificate.domain_correct ξ)";
					Number number;
					if(!s.cubeZero&&literalNumber(t,number)&&(number.zero||number.one)){
						auto literal=arena.number(number,sort),last=sort==Sort.real_||sort==Sort.complex?"AffineRecurrence."~(number.zero?"zero":"one")~suffix:sort==Sort.rational?"(congrArg some (div_one ("~(number.zero?"0":"1")~" : ℚ)))":"rfl";
						h="Eq.trans (LinearRecurrence.known (QSym.Spectral"~tag~"_0_"~to!string(j)~".DomainCertificate.domain_correct ξ) (Numeric.sound ξ n"~to!string(t.id)~" n"~to!string(literal.id)~" (of_decide_eq_true rfl))) "~last;
						if(sort==Sort.rational) h=arena.isNumber(t)?last:"Numeric.calculate_sound ξ n"~to!string(t.id)~" ("~(number.zero?"0":"1")~" : ℚ) rfl";
					}
					if(s.zeroRoot){
						auto name="spectralTotal"~tag~"_"~to!string(j),reference="("~name~" ξ)";
						code~="theorem "~name~" (ξ : Env) : "~raw(t)~" = some "~v~" := "~h~"\n";
						totalProofs[t.id]=reference; return reference;
					}
					return "(show "~raw(t)~" = some "~v~" from "~h~")";
				}
				assert(0,"missing spectral parameter");
			}
			string cases(string[] proofs){ auto r="(fun i => i.elim0)"; foreach_reverse(p;proofs) r="(Fin.cases "~p~" "~r~")"; return r; }
			string vector(string[] xs){ auto r="(fun i : Fin 0 => i.elim0)"; foreach_reverse(x;xs) r="(Fin.cons "~x~" "~r~")"; return r; }
			string constants(uint q){
				auto z=nodes[q]; if(z.op==BoundOp.scalar) return total(arena.at(z.data));
				if(z.op==BoundOp.vectorNil) return "rfl";
				return "(congrArg₂ Tensor.consValue "~constants(z.a)~" "~constants(z.b)~")";
			}
			auto mat="("~name(powerNode.a)~".eval ξ ρ)",vec="("~name(source.b)~".eval ξ ρ)",exponent="("~name(powerNode.b)~".eval ξ ρ)";
			auto hmat=constants(powerNode.a),hv=constants(source.b); string proof;
			auto spectralArgs=dimDecl~" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctxName(source.context)~")";
			if(s.split){
				string[] matrices,vectors; auto left=s.split,right=s.size-left;
				foreach(part;0..2){
					auto start=part?left:0,count=part?right:left; string[] rows,seed;
					foreach(i;start..start+count){
						string[] cells; foreach(j;start..start+count) cells~=val(s.matrix[i*s.size+j]);
						rows~=vector(cells); seed~=val(s.vector[i]);
					}
					matrices~=vector(rows); vectors~=vector(seed);
				}
				string[] eqs,rows; foreach(i;0..s.size) eqs~="rfl";
				auto heq="(funext "~cases(eqs)~")"; foreach(i;0..s.size) rows~=heq;
				hmat="(Eq.trans "~hmat~" (congrArg some (funext "~cases(rows)~")))";
				hv="(Eq.trans "~hv~" (congrArg some "~heq~"))";
				proof="MatrixBlocks.split_value (m := "~to!string(left)~") (n := "~to!string(right)~") (of_decide_eq_true rfl) (of_decide_eq_true rfl) "~add~" "~mul~" "~ha~" "~hm~units~" "~matrices[0]~" "~matrices[1]~" "~vectors[0]~" "~vectors[1]~" "~mat~" "~vec;
				foreach(q;s.blocks) proof~=" ("~name(q)~".eval ξ ρ)";
				proof~=" "~hmat~" "~hv;
				foreach(q;s.blocks) proof~=" "~constants(q);
				proof~=" "~exponent;
			}else if(s.zeroRoot){
				code~="attribute [local irreducible] Value.add Value.mul\n";
				string[] av,ar,at_,vv,vr,vt,rv,rr,rt,cv,cr,ct;
				foreach(i;0..3){
					string[] vals,raws,totals,cvals,craws,ctotals;
					foreach(j;0..3){
						auto a=s.matrix[i*3+j],c=s.components[i*3+j];
						vals~=val(a); raws~=raw(a); totals~=total(a);
						cvals~=val(c); craws~=raw(c); ctotals~=total(c);
					}
					av~=vector(vals); ar~=vector(raws); at_~=cases(totals);
					cv~=vector(cvals); cr~=vector(craws); ct~=cases(ctotals);
					vv~=val(s.vector[i]); vr~=raw(s.vector[i]); vt~=total(s.vector[i]);
					rv~=val(s.roots[i]); rr~=raw(s.roots[i]); rt~=total(s.roots[i]);
				}
				auto scalar="("~leanType(element)~" : Binding.Ty).denote";
				auto rawMatrix="("~vector(ar)~" : Fin 3 → Fin 3 → Option ("~scalar~"))";
				auto hn=sort==Sort.real_||sort==Sort.complex?"Spectral.minus"~suffix:"(congrArg some (div_one (-1 : ℚ)))";
				string checked(uint k){
					auto f=s.checks[k],prefix="QSym.Spectral"~tag~"_1_"~to!string(k),out_=arena.castTo(f.value.output,sort),zero=arena.number(Number(0),sort);
					auto hz=sort==Sort.real_||sort==Sort.complex?"AffineRecurrence.zero"~suffix:"(congrArg some (div_one (0 : ℚ)))";
					return "Spectral.checked_eq "~add~" "~mul~" "~ha~" "~hm~" "~raw(s.minus)~" _ _ "~hn~" (Eq.trans (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) (Value.Refines.trans ("~prefix~".ValueCertificate.refinement ξ) (Numeric.sound ξ n"~to!string(out_.id)~" n"~to!string(zero.id)~" (of_decide_eq_true rfl)))) "~hz~")";
				}
				string[] sums,eigen;
				foreach(i;0..3){
					auto id="spectralRoot"~tag~"_"~to!string(i);
					code~="theorem "~id~" (ξ : Env) : "~add~" ("~add~" "~raw(s.components[i])~" "~raw(s.components[3+i])~") "~raw(s.components[6+i])~" = "~vr[i]~" := "~checked(i)~"\n";
					sums~="("~id~" ξ)";
				}
				foreach(j;0..3){
					string[] row;
					foreach(i;0..3){
						auto k=3+j*3+i,id="spectralRoot"~tag~"_"~to!string(k);
						code~="theorem "~id~" (ξ : Env) : CubeZeroSpectra.step "~add~" "~mul~" "~rawMatrix~" "~cr[j]~" "~to!string(i)~" = "~mul~" "~rr[j]~" "~raw(s.components[j*3+i])~" := "~checked(k)~"\n";
						row~="("~id~" ξ)";
					}
					eigen~=cases(row);
				}
				code~="theorem spectralMatrix"~tag~spectralArgs~" : "~mat~" = some "~vector(av)~" := "~hmat~"\n";
				code~="theorem spectralVector"~tag~spectralArgs~" : "~vec~" = some "~vector(vv)~" := "~hv~"\n";
				proof="ZeroRootSpectra.three_value "~add~" "~mul~" "~pow~" "~ha~" "~hm~" "~hp~units~" "~vector(av)~" "~vector(vv)~" "~vector(rv)~" "~vector(cv)~" "~vector(ar)~" "~vector(vr)~" "~vector(rr)~" "~vector(cr)~" "~cases(at_)~" "~cases(vt)~" "~cases(rt)~" "~cases(ct)~" "~cases(sums)~" "~cases(eigen)~" "~mat~" "~vec~" (spectralMatrix"~tag~dimArg~" γ ξ ρ) (spectralVector"~tag~dimArg~" γ ξ ρ) "~exponent;
			}else if(s.cubeZero){
				code~="attribute [local irreducible] Value.add Value.mul\n";
				string[] matrixValues,matrixRaw,matrixTotal,cube,vectorValues,vectorRaw,vectorTotal,zeroProofs;
				foreach(i;0..3){
					string[] vals,raws,totals,zeros;
					foreach(j;0..3){
						auto entry=s.matrix[i*3+j]; vals~=val(entry); raws~=raw(entry); totals~=total(entry);
						auto f=s.checks[i*3+j],prefix="QSym.Spectral"~tag~"_1_"~to!string(i*3+j),out_=arena.castTo(f.value.output,sort),zero=arena.number(Number(0),sort);
						auto hzero=sort==Sort.real_||sort==Sort.complex?"AffineRecurrence.zero"~suffix:sort==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":"rfl";
						zeros~="(Eq.trans (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) (Value.Refines.trans ("~prefix~".ValueCertificate.refinement ξ) (Numeric.sound ξ n"~to!string(out_.id)~" n"~to!string(zero.id)~" (of_decide_eq_true rfl)))) "~hzero~")";
					}
					matrixValues~=vector(vals); matrixRaw~=vector(raws); matrixTotal~=cases(totals); zeroProofs~=zeros;
					vectorValues~=val(s.vector[i]); vectorRaw~=raw(s.vector[i]); vectorTotal~=total(s.vector[i]);
				}
				// Keep each scalar-to-matrix bridge in its own declaration, so elaboration
				// does not repeatedly unfold all nine arithmetic expressions in the final proof.
				auto scalar="("~leanType(element)~" : Binding.Ty).denote";
				auto rawMatrix="("~vector(matrixRaw)~" : Fin 3 → Fin 3 → Option ("~scalar~"))",rawVector="("~vector(vectorRaw)~" : Fin 3 → Option ("~scalar~"))";
				foreach(i;0..3){
					string[] row;
					foreach(j;0..3){
						auto id="spectralCube"~tag~"_"~to!string(i*3+j);
						code~="theorem "~id~" (ξ : Env) : CubeZeroSpectra.step "~add~" "~mul~" "~rawMatrix~" (fun k => CubeZeroSpectra.step "~add~" "~mul~" "~rawMatrix~" (fun l => "~rawMatrix~" l "~to!string(j)~") k) "~to!string(i)~" = some 0 := "~zeroProofs[i*3+j]~"\n";
						row~="("~id~" ξ)";
					}
					cube~=cases(row);
				}
				string compactArgs; string[] compactProofs;
				foreach(part;0..2){
					string[] vals,proofs;
					foreach(i;0..3){
						auto index=9+part*3+i,f=s.checks[index],prefix="QSym.Spectral"~tag~"_1_"~to!string(index);
						vals~=raw(arena.castTo(f.value.output,sort));
						auto id="spectralCube"~tag~"_"~to!string(index),matrix=part?"(CubeZeroSpectra.square "~add~" "~mul~" "~rawMatrix~")":rawMatrix;
						code~="theorem "~id~" (ξ : Env) : CubeZeroSpectra.step "~add~" "~mul~" "~matrix~" "~rawVector~" "~to!string(i)~" = "~vals[$-1]~" := LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) ("~prefix~".ValueCertificate.refinement ξ)\n";
						proofs~="("~id~" ξ)";
					}
					compactArgs~=" "~vector(vals); compactProofs~=cases(proofs);
				}
				foreach(p;compactProofs) compactArgs~=" "~p;
				proof="CubeZeroSpectra.three_compact_value "~add~" "~mul~" "~ha~" "~hm~units~" "~vector(matrixValues)~" "~vector(vectorValues)~" "~vector(matrixRaw)~" "~vector(vectorRaw)~" "~cases(matrixTotal)~" "~cases(vectorTotal)~" "~cases(cube)~compactArgs~" "~mat~" "~vec~" "~hmat~" "~hv~" "~exponent;
			}else if(s.diagonal){
				string[] vals,vs,ars,vrs,da,dv,eqs,rows;
				foreach(j;0..s.size){ auto a=s.matrix[j*s.size+j],v=s.vector[j]; vals~=val(a); vs~=val(v); ars~=raw(a); vrs~=raw(v); da~=total(a); dv~=total(v); eqs~="rfl"; }
				foreach(j;0..s.size) rows~="(funext "~cases(eqs)~")";
				hmat="(Eq.trans "~hmat~" (congrArg some (funext "~cases(rows)~")))";
				proof="Spectral.diagonal_value "~add~" "~mul~" "~pow~" "~ha~" "~hm~" "~hp~units~" "~vector(vals)~" "~vector(vs)~" "~vector(ars)~" "~vector(vrs)~" "~cases(da)~" "~cases(dv)~" "~mat~" "~vec~" "~hmat~" "~hv~" "~exponent;
			}else{
				auto inv=sort==Sort.rational?"Functions.invQ.apply":"Value.inv",hi=sort==Sort.rational?"Spectral.invQ":"rfl";
				auto hn=sort==Sort.real_||sort==Sort.complex?"Spectral.minus"~suffix:sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"rfl";
				string check(uint j){
					auto f=s.checks[j],prefix="QSym.Spectral"~tag~"_1_"~to!string(j),out_=arena.castTo(f.value.output,sort),zero=arena.number(Number(0),sort);
					auto hz=sort==Sort.real_||sort==Sort.complex?"AffineRecurrence.zero"~suffix:sort==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":"rfl";
					return "(Spectral.checked_eq "~add~" "~mul~" "~ha~" "~hm~" "~raw(s.minus)~" _ _ "~hn~" (Eq.trans (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) (Value.Refines.trans ("~prefix~".ValueCertificate.refinement ξ) (Numeric.sound ξ n"~to!string(out_.id)~" n"~to!string(zero.id)~" (of_decide_eq_true rfl)))) "~hz~"))";
				}
				Term[] ps=[s.matrix[0],s.matrix[1],s.matrix[s.size],s.matrix[s.size+1],s.first];
				if(!s.repeated) ps~=s.second;
				ps~=[s.vector[0],s.vector[1]];
				if(s.size==3) ps~=[s.matrix[8],s.vector[2]];
				string args,raws,totals;
				foreach(t;ps){ args~=" "~val(t); raws~=" "~raw(t); totals~=" "~total(t); }
				string cast_,hc;
				if(s.repeated){
					cast_=" (fun n => Functions.castZQ.apply (Functions.castNZ.apply n))";
					if(sort==Sort.real_) cast_=" (fun n => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n)))";
					if(sort==Sort.complex) cast_=" (fun n => Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))))";
					hc=" RepeatedSpectra.cast"~suffix;
				}
				if(s.nilpotent){
					proof="NilpotentSpectra."~(s.size==2?"two_value":"block_value")~" "~add~" "~mul~" "~pow~" "~ha~" "~hm~" "~hp~units~args~raws~" "~raw(s.minus)~totals~" "~hn~" "~check(0)~" "~check(1)~" rfl "~mat~" "~vec~" "~hmat~" "~hv~" "~exponent;
				}else{
					proof=(s.repeated?"RepeatedSpectra.":"Spectral.")~(s.size==2?"two_value":"block_value")~" "~add~" "~mul~" "~inv~" "~pow~cast_~" "~ha~" "~hm~" "~hi~" "~hp~hc~units~args~raws~" "~raw(s.minus)~totals~" "~hn~" "~check(0)~" "~check(1)~" (QSym.Spectral"~tag~"_1_2.DomainCertificate.domain_correct ξ) "~mat~" "~vec~" "~hmat~" "~hv~" "~exponent;
				}
			}
			code~="theorem spectral"~tag~spectralArgs~" : "~name(s.source)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ := "~proof~"\n";
			if(s.cubeZero||s.zeroRoot) code~="attribute [local semireducible] Value.add Value.mul\n";
		}
		foreach(j,s;result.sums){
			auto n=nodes[s.source],sort=elementSort(types[n.type]),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":"C";
			auto add=tensorOperation(types[n.type],TensorOp.add),mul=tensorOperation(types[n.type],TensorOp.mul),ha=sort==Sort.rational?"AffineRecurrence.addQ":"rfl",hm=sort==Sort.rational?"AffineRecurrence.mulQ":"rfl";
			auto field="natural",env="({ ξ with natural := fun i => if i = "~to!string(s.variable)~" then x else ξ.natural i })";
			string known(uint id,string en){
				auto prefix="QSym.BindingScalar"~to!string(id),actual=arena.sort(result.domains[id].input);
				auto hz=actual==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":actual==Sort.real_?"AffineRecurrence.zeroR":"AffineRecurrence.zeroC";
				auto proof="(Eq.trans (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct "~en~") ("~prefix~".ValueCertificate.refinement "~en~")) "~hz~")";
				return sort==Sort.rational&&actual==Sort.real_?"(Summation.rational_zero_of_real _ "~proof~")":proof;
			}
			auto initial=s.zero==uint.max?"":known(s.zero,"ξ"),step=known(s.step,env),minus="(n"~to!string(arena.number(Number(-1),sort).id)~".eval ξ)",hn=sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"Spectral.minus"~suffix;
			auto hs="(fun x => Spectral.checked_eq "~add~" "~mul~" "~ha~" "~hm~" "~minus~" _ _ "~hn~" "~step~")";
			auto f="(fun (x : ℕ) => "~name(nodes[n.a].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some x) ρ))",g="(fun (x : Option ℕ) => "~name(nodes[s.candidate].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) x ρ))";
			if(s.tail.length){
				auto pow="Functions.pow"~suffix~"N.apply",hp="Spectral.pow"~suffix;
				auto cast_="(fun n => Functions.castZQ.apply (Functions.castNZ.apply n))";
				if(sort==Sort.real_) cast_="(fun n => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n)))";
				if(sort==Sort.complex) cast_="(fun n => Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))))";
				string raw(Term t){ return "(n"~to!string(t.id)~".eval ξ)"; }
				string val(Term t){ return "("~raw(t)~".getD 0)"; }
				string total(Term t,uint k){ return "(Spectral.some_of_domain 0 "~raw(t)~" (QSym.BindingScalar"~to!string(k)~".DomainCertificate.domain_correct ξ))"; }
				string tree="Summation.Tail.nil",converges="True.intro",value="0";
				string rawTail=raw(arena.number(Number(0),sort)),ht=sort==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":"AffineRecurrence.zero"~suffix;
				foreach_reverse(k,p;s.tail){
					auto c=val(p.coefficient),q=val(p.ratio),degree=to!string(p.degree);
					tree="(Summation.Tail.cons "~c~" "~q~" "~degree~" "~tree~")";
					auto prefix="QSym.BindingScalar"~to!string(s.convergence[k]);
					converges="And.intro (Summation.norm_lt"~suffix~" "~raw(p.ratio)~" "~q~" "~raw(arena.real_(1))~" "~total(p.ratio,s.totals[2*k+1])~" AffineRecurrence.oneR (LinearRecurrence.known ("~prefix~".DomainCertificate.domain_correct ξ) ("~prefix~".ValueCertificate.refinement ξ))) ("~converges~")";
					ht="(Summation.Tail.cons_value "~add~" "~mul~" "~pow~" "~cast_~" "~ha~" "~hm~" "~hp~" RepeatedSpectra.cast"~suffix~" "~raw(p.coefficient)~" "~raw(p.ratio)~" "~rawTail~" "~c~" "~q~" "~value~" "~total(p.coefficient,s.totals[2*k])~" "~total(p.ratio,s.totals[2*k+1])~" "~ht~" "~degree~" x)";
					value="("~c~" * (x : "~(sort==Sort.rational?"ℚ":sort==Sort.real_?"ℝ":"ℂ")~")^"~degree~" * "~q~"^x + "~value~")";
					rawTail="("~add~" ("~mul~" ("~mul~" "~raw(p.coefficient)~" ("~pow~" ("~cast_~" (some x)) (some "~degree~"))) ("~pow~" "~raw(p.ratio)~" (some x))) "~rawTail~")";
				}
				code~="theorem summation"~to!string(j)~dimDecl~" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctxName(n.context)~") : "~name(s.source)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ := Summation.tail_solution "~f~" "~g~" "~tree~" ("~converges~") (fun x => "~ht~") "~add~" "~mul~" "~(sort==Sort.rational?"Summation.addQ":"Summation.add")~" (Summation.mul_eq "~mul~" "~hm~") "~minus~" "~hn~" "~hs~"\n";
				continue;
			}
			code~="theorem summation"~to!string(j)~dimDecl~" (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env "~ctxName(n.context)~") : "~name(s.source)~".eval ξ ρ = "~name(s.target)~".eval ξ ρ := Summation.range_solution_partial "~f~" "~g~" "~add~" "~(sort==Sort.rational?"Summation.addQ":"Summation.add")~" "~initial~" "~hs~" ("~name(n.b)~".eval ξ ρ)\n";
		}
		string proofName(uint id){ return "(p"~to!string(id)~dimArg~" γ)"; }
		foreach(i,p;result.proofs){
			auto n=nodes[p.from]; string proof;
			string sumZeroProof(){ auto sort=elementSort(types[n.type]); return sort==Sort.rational?"(congrArg some (div_one (0 : ℚ)))":sort==Sort.real_?"AffineRecurrence.zeroR":sort==Sort.complex?"AffineRecurrence.zeroC":"rfl"; }
			string sumRawZero(){ return "(n"~to!string(arena.number(Number(0),elementSort(types[n.type])).id)~".eval ξ)"; }
			final switch(p.rule){
				case BindingRule.sumMaskAnd:
					auto pred=nodes[n.a];
					proof=".ofEq (fun ξ ρ => SummationAlgebra.mask_and ("~name(pred.a)~".eval ξ ρ) ("~name(pred.b)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumNaturalBound:
					proof=".ofEq (fun ξ ρ => SummationAffine.natural_"~(arena.view(arena.at(n.data)).value==Builtin.ltN?"lt":"le")~" ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumAffineNatural:
					auto expr=p.extra?n.b:n.a,bound=p.extra?n.a:n.b;
					foreach(_;0..3)expr=nodes[expr].a;
					auto add=nodes[expr],mul=nodes[add.a],m=arena.number(arena.at(nodes[mul.a].data)).re.integer;
					proof=".ofEq (fun ξ ρ => SummationAffine.affineN ("~name(mul.a)~".eval ξ ρ) ("~name(add.b)~".eval ξ ρ) ("~name(mul.b)~".eval ξ ρ) ("~name(bound)~".eval ξ ρ) "~to!string(m)~" (of_decide_eq_true rfl) rfl (n"~to!string(arena.real_(-1).id)~".eval ξ) Spectral.minusR "~(arena.view(arena.at(n.data)).op==Op.le?"true":"false")~" "~(p.extra?"true":"false")~")";break;
				case BindingRule.sumPowerNatural:
					auto suffix=["Q","R","C"][arena.view(arena.at(n.data)).value-Builtin.powQZ];
					proof=".ofEq (fun ξ ρ => SummationPowers.natural"~suffix~" ("~name(n.a)~".eval ξ ρ) ("~name(nodes[n.b].a)~".eval ξ ρ))";break;
				case BindingRule.sumPowerNegative:
					auto suffix=["Q","R","C"][arena.view(arena.at(n.data)).value-Builtin.powQZ],exponent=nodes[n.b];
					auto offset=p.extra?exponent.b:exponent.a,product=nodes[p.extra?exponent.a:exponent.b],iv=nodes[product.b].a;
					auto m=-arena.number(arena.at(nodes[offset].data)).re.integer-1;
					proof=".ofEq (fun ξ ρ => SummationPowers.negative"~(p.extra?"Reverse":"")~suffix~" ("~name(n.a)~".eval ξ ρ) ("~name(iv)~".eval ξ ρ) "~to!string(m)~" ("~name(offset)~".eval ξ ρ) ("~name(product.a)~".eval ξ ρ) rfl rfl)";break;
				case BindingRule.addBottom:
					auto sort=elementSort(types[n.type]),add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					auto left=nodes[n.a].op==BoundOp.bottom;
					proof=".ofEq (fun ξ ρ => SummationMasks.add_none_"~(left?"left":"right")~" "~add~" "~ha~" ("~name(left?n.b:n.a)~".eval ξ ρ))";break;
				case BindingRule.sumExcludeZero:
					auto body=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm",hw=sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero";
					auto f="(fun (i : Option ℕ) => "~name(body.b)~".eval ξ (Binding.Env.cons (a := .scalar .natural) i ρ))";
					proof=".ofEq (fun ξ ρ => SummationMasks.exclude_zero "~w~" "~hw~" "~f~")";break;
				case BindingRule.sumExcludeOffset:
					auto body=nodes[nodes[n.a].a],sort=elementSort(types[n.type]);
					auto add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					auto f="(fun (i : Option ℕ) => "~name(body.b)~".eval ξ (Binding.Env.cons (a := .scalar .natural) i ρ))";
					proof=".ofEq (fun ξ ρ => SummationPrefix.exclude_offset norm "~add~" "~ha~" "~f~" ("~name(p.extra)~".eval ξ ρ))";break;
				case BindingRule.sumCastMask,BindingRule.sumCastAdd:
					auto child=nodes[n.a],suffix=["NZ","ZQ","QR","RC"][arena.view(arena.at(n.data)).value-Builtin.castNZ];
					proof=".ofEq (fun ξ ρ => SummationMasks.cast"~suffix~(p.rule==BindingRule.sumCastMask?"_mask":"_add")~" ("~name(child.a)~".eval ξ ρ) ("~name(child.b)~".eval ξ ρ))";break;
				case BindingRule.sumBoundedAdd:
					auto body=nodes[nodes[n.a].a],bounds=nodes[p.extra],sort=elementSort(types[n.type]);
					auto add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					auto w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm",hw=sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero";
					string fn(uint id){return "(fun (i : ℕ) => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))";}
					auto flags=arena.number(arena.at(nodes[nodes[nodes[bounds.b].b].a].data)).re.integer;
					proof=".ofEq (fun ξ ρ => SummationMasks.bounded_add "~w~" "~hw~" "~add~" "~ha~" "~fn(nodes[body.a].b)~" "~fn(nodes[body.b].b)~" ("~name(bounds.a)~".eval ξ ρ) ("~name(nodes[bounds.b].a)~".eval ξ ρ) "~(flags&1?"true":"false")~" "~(flags&2?"true":"false")~")";break;
				case BindingRule.sumDeltaZero:
					auto body=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),index=pool.view(type(at(n.a))).fields[0],ns=index==scalarType(Sort.natural);
					auto w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm",hw=sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero";
					auto f="(fun (i : "~(ns?"ℕ":"ℤ")~") => "~name(body.b)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") (some i) ρ))";
					proof=".ofEq (fun ξ ρ => SummationMasks.delta"~(ns?(p.extra==1?"N_nonzeroN":"N_zero"):"Z_zero")~" "~w~" "~hw~" "~f~")";break;
				case BindingRule.rangeAdd:
					auto body=nodes[nodes[n.a].a],sort=elementSort(types[n.type]);
					auto add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					string fn(uint id){return "(fun (i : ℕ) => "~name(id)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))";}
					proof=".ofEq (fun ξ ρ => SummationAlgebra.range_add "~add~" "~ha~" "~fn(body.a)~" "~fn(body.b)~" ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.rangeMaskLt,BindingRule.rangeMaskGe:
					auto body=nodes[nodes[n.a].a],ge=p.rule==BindingRule.rangeMaskGe;
					auto f="(fun (i : "~(ge?"Option ℕ":"ℕ")~") => "~name(body.b)~".eval ξ (Binding.Env.cons (a := .scalar .natural) "~(ge?"i":"(some i)")~" ρ))";
					proof=".ofEq (fun ξ ρ => SummationAlgebra.range_mask_"~(ge?"ge":"lt")~" "~f~" ("~name(n.b)~".eval ξ ρ) ("~name(p.extra)~".eval ξ ρ))";break;
				case BindingRule.sumMaskEqOffset,BindingRule.sumMaskNeOffset:
					auto equal=p.rule==BindingRule.sumMaskEqOffset,sort=elementSort(types[n.type]);
					auto iv=variable(context(at(n.a)),0),add=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					proof=".ofEq (fun ξ ρ => SummationAlgebra.mask_"~(equal?"eq_offset":"ne_offset_op "~add~" "~ha)~" ("~name(iv.id)~".eval ξ ρ) ("~name(p.extra)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumTail:
					auto body=nodes[nodes[n.a].a],pred=nodes[body.a],index=pool.view(type(at(n.a))).fields[0],sort=elementSort(types[n.type]);
					auto ns=index==scalarType(Sort.natural),lower=arena.view(arena.at(pred.data)).value==(ns?Builtin.leN:Builtin.leZ);
					auto w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : Option "~(ns?"ℕ":"ℤ")~") => "~name(body.b)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") i ρ))";
					proof=".ofEq (fun ξ ρ => SummationTails."~(ns?"lowerN":lower?"lowerZ":"upperZ")~" "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(p.extra)~".eval ξ ρ))";break;
				case BindingRule.sumRationalBound:
					proof=".ofEq (fun ξ ρ => SummationBounds.rational_"~(arena.view(arena.at(n.data)).value==Builtin.ltQ?"lt":"le")~" ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))";break;
				case BindingRule.sumRound:
					auto reverse=(p.extra&2)!=0,natural=(p.extra&4)==0,index=reverse?n.b:n.a,bound=reverse?n.a:n.b;
					index=nodes[nodes[index].a].a; if(natural) index=nodes[index].a;
					auto suffix=["lt","le","gt","ge"][p.extra&3];
					proof=".ofEq (fun ξ ρ => SummationBounds.round"~(natural?"N":"Z")~"_"~suffix~" ("~name(index)~".eval ξ ρ) ("~name(bound)~".eval ξ ρ))"; break;
				case BindingRule.rangeSolution:proof=".ofEq (summation"~to!string(p.extra)~dimArg~" γ)"; break;
				case BindingRule.rangeGeometric:
					auto sort=elementSort(types[n.type]),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":"C",leaf=types[n.type];
					auto add=tensorOperation(leaf,TensorOp.add),mul=tensorOperation(leaf,TensorOp.mul),inv=sort==Sort.rational?"Functions.invQ.apply":"Value.inv";
					auto ha=sort==Sort.rational?"AffineRecurrence.addQ":"rfl",hm=sort==Sort.rational?"AffineRecurrence.mulQ":"rfl",hi=sort==Sort.rational?"Spectral.invQ":"rfl";
					auto cast_="(fun n => Functions.castZQ.apply (Functions.castNZ.apply n))";
					if(sort==Sort.real_) cast_="(fun n => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n)))";
					if(sort==Sort.complex) cast_="(fun n => Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))))";
					auto minus="(n"~to!string(arena.number(Number(-1),sort).id)~".eval ξ)",hn=sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"Spectral.minus"~suffix;
					proof=".ofEq (fun ξ ρ => Summation.range_geometric_value "~add~" "~mul~" "~inv~" Functions.pow"~suffix~"N.apply "~cast_~" "~(sort==Sort.rational?"Functions.nonzeroQ.apply Summation.nonzeroQ":"Value.nonzero rfl")~" "~ha~" "~hm~" "~hi~" Spectral.pow"~suffix~" RepeatedSpectra.cast"~suffix~" "~sumRawZero()~" "~minus~" "~sumZeroProof()~" "~hn~" ("~name(p.extra)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.sumConstant:
					auto sort=elementSort(types[n.type]),index=pool.view(type(at(n.a))).fields[0];
					auto suffix=sort==Sort.natural?"N":sort==Sort.integer?"Z":sort==Sort.rational?"Q":"_norm";
					proof=".ofEq (fun ξ ρ => Summation.constant"~suffix~" (ι := "~(index==scalarType(Sort.natural)?"ℕ":"ℤ")~") ("~name(p.extra)~".eval ξ ρ) "~sumRawZero()~" "~sumZeroProof()~")"; break;
				case BindingRule.sumBounds:
					auto bounds=nodes[p.extra],sourceBody=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),index=pool.view(type(at(n.a))).fields[0];
					auto ns=index==scalarType(Sort.natural),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : "~(ns?"ℕ":"ℤ")~") => "~name(sourceBody.b)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") (some i) ρ))";
					auto flags=arena.number(arena.at(nodes[nodes[nodes[bounds.b].b].a].data)).re.integer;
					proof=".ofEq (fun ξ ρ => Summation.bounds"~(ns?"N":"Z")~" "~w~" "~f~" ("~name(bounds.a)~".eval ξ ρ) ("~name(nodes[bounds.b].a)~".eval ξ ρ) "~(flags&1?"true":"false")~" "~(flags&2?"true":"false")~")"; break;
				case BindingRule.sumShiftGeometric:
					auto args=nodes[p.extra],sort=elementSort(types[n.type]),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":"C";
					auto mul=sort==Sort.rational?"Functions.mulQ.apply":"Value.mul",hm=sort==Sort.rational?"AffineRecurrence.mulQ":"rfl";
					string raw(Term t){ return "(n"~to!string(t.id)~".eval ξ)"; }
					auto one=raw(arena.number(Number(1),sort)),minus=raw(arena.number(Number(-1),sort)),rOne=raw(arena.real_(1));
					auto ho=sort==Sort.rational?"(congrArg some (div_one (1 : ℚ)))":"AffineRecurrence.one"~suffix,hn=sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"Spectral.minus"~suffix;
					auto q="("~name(args.a)~".eval ξ ρ)",h="(Summation.geometric"~suffix~"_literals "~q~" "~one~" "~minus~(sort==Sort.real_?"":" "~rOne)~" "~ho~" "~hn~(sort==Sort.real_?"":" AffineRecurrence.oneR")~")";
					proof=".ofEq (fun ξ ρ => Summation.geometric_shift_guard Functions.pow"~suffix~"N.apply Spectral.pow"~suffix~" "~mul~" "~hm~" "~q~" ("~name(nodes[args.b].a)~".eval ξ ρ) _ _ "~h~")"; break;
				case BindingRule.sumTailNatural,BindingRule.sumTailStrict:
					auto sourceBody=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : Option ℕ) => "~name(sourceBody.b)~".eval ξ (Binding.Env.cons (a := .scalar .natural) i ρ))";
					proof=".ofEq (fun ξ ρ => Summation.tailN_value "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(p.extra)~".eval ξ ρ) "~(p.rule==BindingRule.sumTailStrict?"true":"false")~")"; break;
				case BindingRule.sumInterval:
					auto bounds=nodes[p.extra],sourceBody=nodes[nodes[n.a].a],sort=elementSort(types[n.type]),index=pool.view(type(at(n.a))).fields[0];
					auto ns=index==scalarType(Sort.natural),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : Option "~(ns?"ℕ":"ℤ")~") => "~name(sourceBody.b)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") i ρ))";
					proof=".ofEq (fun ξ ρ => Summation.interval_convert"~(ns?"N":"Z")~" "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(bounds.a)~".eval ξ ρ) ("~name(nodes[bounds.b].a)~".eval ξ ρ))"; break;
				case BindingRule.sumDelta,BindingRule.sumDeltaOffset:
					auto out_=nodes[p.to],sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm",index=pool.view(type(at(n.a))).fields[0];
					auto f="(fun (i : "~(index==scalarType(Sort.natural)?"ℕ":"ℤ")~") => "~name(nodes[out_.a].a)~".eval ξ (Binding.Env.cons (a := "~leanType(index)~") (some i) ρ))";
					proof=".ofEq (fun ξ ρ => Summation.delta"~(p.rule==BindingRule.sumDeltaOffset?"Z_offset":index==scalarType(Sort.natural)?"N":"Z")~" "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(p.rule==BindingRule.sumDeltaOffset?p.extra:out_.b)~".eval ξ ρ))"; break;
				case BindingRule.sumGeometric:
					auto sort=elementSort(types[n.type]),suffix=sort==Sort.rational?"Q":sort==Sort.real_?"R":"C";
					string raw(Term t){ return "(n"~to!string(t.id)~".eval ξ)"; }
					auto one=raw(arena.number(Number(1),sort)),minus=raw(arena.number(Number(-1),sort)),rOne=raw(arena.real_(1));
					auto ho=sort==Sort.rational?"(congrArg some (div_one (1 : ℚ)))":"AffineRecurrence.one"~suffix;
					auto hm=sort==Sort.rational?"(congrArg some (div_one (-1 : ℚ)))":"Spectral.minus"~suffix;
					proof=".ofEq (fun ξ ρ => Summation.geometric"~suffix~"_literals ("~name(p.extra)~".eval ξ ρ) "~one~" "~minus~(sort==Sort.real_?"":" "~rOne)~" "~ho~" "~hm~(sort==Sort.real_?"":" AffineRecurrence.oneR")~")"; break;
				case BindingRule.sumZero:
					auto sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					proof=".ofEq (fun ξ ρ => Summation.zero_literal "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~sumRawZero()~" "~sumZeroProof()~")"; break;
				case BindingRule.sumRange,BindingRule.sumRangeLe:
					auto out_=nodes[p.to],sort=elementSort(types[n.type]),w=sort==Sort.natural?"(fun n : ℕ => (n : ℝ))":"norm";
					auto f="(fun (i : ℕ) => "~name(nodes[out_.a].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))";
					proof=".ofEq (fun ξ ρ => Summation."~(p.rule==BindingRule.sumRangeLe?"range_convert_le":"range_convert")~" "~w~" "~(sort==Sort.natural?"Summation.nat_weight_zero":"norm_zero")~" "~f~" ("~name(p.rule==BindingRule.sumRangeLe?p.extra:out_.b)~".eval ξ ρ))"; break;
				case BindingRule.rangeZero:proof=".ofEq (fun ξ ρ => Summation.range_zero_literal ("~name(n.a)~".eval ξ ρ) rfl "~sumRawZero()~" "~sumZeroProof()~")"; break;
				case BindingRule.rangeStep:
					auto count=arena.number(arena.at(nodes[n.b].data)).re.integer;
					auto f="(fun (i : ℕ) => "~name(nodes[n.a].a)~".eval ξ (Binding.Env.cons (a := .scalar .natural) (some i) ρ))",sort=elementSort(types[n.type]);
					auto op=tensorOperation(types[n.type],TensorOp.add),ha=sort==Sort.natural?"Summation.addN":sort==Sort.integer?"Summation.addZ":sort==Sort.rational?"Summation.addQ":"Summation.add";
					proof=".ofEq (fun ξ ρ => Summation.range_step "~f~" "~to!string(count-1)~" "~op~" "~ha~")"; break;
				case BindingRule.rangeLift:
					proof=".ofEq (fun ξ ρ => Summation.range_"~(elementSort(types[n.type])==Sort.natural?"nat":"int")~"_lift ("~name(n.a)~".eval ξ ρ) ("~name(n.b)~".eval ξ ρ))"; break;
				case BindingRule.getScalarUndefined:
					proof="Tensor.getScalarUndefined "~name(n.a)~" n"~to!string(nodes[n.b].data)~" QSym.BindingScalar"~to!string(p.extra)~".DomainCertificate.domain_correct"; break;
				case BindingRule.getBottom:
					auto left=nodes[n.a].op==BoundOp.bottom;
					proof=".ofEq (fun ξ ρ => Tensor.get_none_"~(left?"left":"right")~" ("~name(left?n.b:n.a)~".eval ξ ρ))"; break;
				case BindingRule.getCons:
					auto index=arena.number(arena.at(nodes[n.b].data)).re.integer,cons=nodes[n.a];
					proof=".ofEq (fun ξ ρ => Tensor.get_cons_"~(index?"succ":"zero")~" ("~name(cons.a)~".eval ξ ρ) ("~name(cons.b)~".eval ξ ρ)"~(index?" "~to!string(index-1):"")~")"; break;
				case BindingRule.tensorSpectrumCast:
					auto source=nodes[p.from],power=nodes[source.a],lifted=nodes[p.extra],liftedPower=nodes[lifted.a];
					auto from=elementSort(typeLeaf(type(at(p.from)))),targetSort=elementSort(typeLeaf(type(at(p.extra)))),size=pool.view(type(at(p.from))).length;
					auto tag=(from==Sort.natural?"N":"Z")~(targetSort==Sort.real_?"R":"C"),hom="("~(from==Sort.natural?"Nat":"Int")~".castRingHom "~(targetSort==Sort.real_?"ℝ":"ℂ")~")";
					string raw(uint id){ return "("~name(id)~".eval ξ ρ)"; }
					string mapped(uint original,uint converted,uint depth){
						if(!depth) return "(IntegerSpectra.cast"~tag~" "~raw(original)~")";
						auto a=nodes[original],b=nodes[converted],f=depth==1?hom:"(fun v : Fin "~to!string(size)~" → _ => fun i => "~hom~" (v i))";
						if(a.op==BoundOp.vectorNil) return "(IntegerSpectra.map_nil "~f~")";
						return "(IntegerSpectra.map_cons "~f~" "~raw(a.a)~" "~raw(a.b)~" "~raw(b.a)~" "~raw(b.b)~" "~mapped(a.a,b.a,depth-1)~" "~mapped(a.b,b.b,depth)~")";
					}
					auto element=scalarType(targetSort),field=targetSort==Sort.real_?"R":"C";
					auto units=" "~tensorLiteral(element,0)~" "~tensorLiteral(element,1)~" (Option.some.inj AffineRecurrence.zero"~field~") (Option.some.inj AffineRecurrence.one"~field~")";
					proof=".ofEq (fun ξ ρ => IntegerSpectra.lift"~tag~" "~to!string(size-1)~units~" "~raw(power.a)~" "~raw(source.b)~" "~raw(power.b)~" "~raw(liftedPower.a)~" "~raw(lifted.b)~" "~mapped(power.a,liftedPower.a,2)~" "~mapped(source.b,lifted.b,1)~")"; break;
				case BindingRule.tensorSpectral:proof=".ofEq (fun ξ ρ => spectral"~to!string(p.extra)~dimArg~" γ ξ ρ)"; break;
				case BindingRule.tensorEval:proof=tensorEvaluationProof(p.from,p.to); break;
				case BindingRule.tensorPower:
					auto v=pool.view(types[n.type]),element=typeLeaf(types[n.type]),exponent=arena.number(arena.at(nodes[n.b].data)).re.integer;
					proof=".ofEq (fun ξ ρ => Tensor.matrixPowerValue_succ "~tensorOperation(element,TensorOp.add)~" "~tensorOperation(element,TensorOp.mul)~" "~tensorLiteral(element,0)~" "~tensorLiteral(element,1)~" "~v.dimension.lean~" ("~name(n.a)~".eval ξ ρ) "~to!string(exponent-1)~")"; break;
				case BindingRule.tensorDomain:
					auto child=nodes[n.a];
					proof=".ofEq (fun ξ ρ => TensorDomains.Binary.defined "~tensorDomainProof(child)~" ("~name(child.a)~".eval ξ ρ) ("~name(child.b)~".eval ξ ρ))"; break;
				case BindingRule.getDomain:
					auto child=nodes[n.a],index=arena.number(arena.at(nodes[child.b].data)).re.integer;
					proof=".ofEq (fun ξ ρ => TensorDomains.get "~to!string(pool.view(type(at(child.a))).length)~" "~to!string(index)~" (of_decide_eq_true rfl) ("~name(child.a)~".eval ξ ρ))"; break;
				case BindingRule.tensorDefined:
					auto child=nodes[n.a];
					proof=".ofEq (fun ξ ρ => Tensor."~(child.op==BoundOp.pair?"defined_pair":"defined_cons")~" ("~name(child.a)~".eval ξ ρ) ("~name(child.b)~".eval ξ ρ))"; break;
				case BindingRule.fixedRecurrence:proof=".ofEq (fun ξ ρ => solve"~to!string(p.from)~dimArg~" γ ξ ρ)"; break;
				case BindingRule.domainFixedTotal:proof=".ofEq (fun ξ ρ => "~(result.ranks[p.extra].iterations.length||result.ranks[p.extra].lower.output!=Term.init?"domainTotal"~to!string(p.extra)~dimArg~" γ ξ ρ":"Eq.trans (domainTotal"~to!string(p.extra)~dimArg~" γ ξ ρ) (congrArg some (Set.ext (fun _ => iff_of_true True.intro rfl)))")~")"; break;
				case BindingRule.refl:proof=".refl "~name(p.from); break;
				case BindingRule.trans:proof=".trans "~proofName(p.left)~" "~proofName(p.right); break;
				case BindingRule.beta:proof=".beta "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.seqScalar:proof=".seqScalar n"~to!string(nodes[n.a].data)~" "~name(n.b)~" (fun _ => ⟨_, rfl⟩)"; break;
				case BindingRule.seqLam:proof=".seqLam "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.seqSelf:proof=".seqSelf "~name(n.a); break;
				case BindingRule.shortCircuit:
					if(n.op==BoundOp.primitive&&nodes[n.a].op==BoundOp.scalar&&arena.view(arena.at(n.data)).op==Op.mask&&!arena.view(arena.at(nodes[n.a].data)).value){
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
					auto generic=n.op==BoundOp.finiteSum||n.op==BoundOp.summation||n.op==BoundOp.equal||n.op==BoundOp.typeEq||n.op==BoundOp.primitive||n.op==BoundOp.member||n.op==BoundOp.subset||n.op==BoundOp.domain||n.op==BoundOp.defined||n.op==BoundOp.holds||n.op==BoundOp.guard||n.op==BoundOp.pair||n.op==BoundOp.vectorCons||n.op==BoundOp.get||n.op==BoundOp.first||n.op==BoundOp.rest||n.op==BoundOp.tensor;
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
