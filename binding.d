module qsym.binding;
import qsym.ir;
import qsym.types:TypeId,TypeKind,TypePool;
import qsym.number:Number;
import qsym.table:Table;
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
enum BoundOp:ubyte{ scalar,variable,primitive,lambda,apply,sequence,global,set,member,domain,defined,holds,guard,subset }
struct BoundNode{
	BoundOp op;
	uint context,type,a=uint.max,b=uint.max,data;
}
private enum BindingRule:ubyte{
	refl,congr,beta,seqScalar,seqLam,seqSelf,trans,fold,seqTotal,seqGuard,domainLam,memberSet,
	definedTotal,definedGuardFalse,guardTrue,scalarDomain,scalarHolds,scalarSimplify,
	subsetRefl,subsetEmpty,subsetUniv,subsetUnivEmpty,definedMember,definedSubset,definedGuard,definedApp,domainGuardFalse,definedNot,
	guardAnd,pointwise,holdsGuard,setHolds
}
private struct BindingStep{ BindingRule rule; uint from,to,left=uint.max,right=uint.max,extra=uint.max; }
private struct ScalarDomain{ Term input; Result result,value; uint variable; Sort sort; uint[] path; BoundOp mode; }
struct BindingResult{
	BoundTerm input,output;
	bool exhausted;
	uint steps;
	private BindingStep[] proofs;
	private uint proof;
	private ScalarDomain[] domains;
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
		enforce(v.kind==TypeKind.function_||v.kind==TypeKind.set||v.kind>=TypeKind.boolean&&v.kind<=TypeKind.complex,"unsupported binding type");
		if(v.kind==TypeKind.function_||v.kind==TypeKind.set) foreach(f;v.fields) typeId(f);
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
			case BoundOp.scalar:return scalar(target,arena.at(n.data));
			case BoundOp.global:return global(target,types[n.type],n.data);
			case BoundOp.variable:assert(0,"variable requires substitution");
			case BoundOp.primitive:return primitive(arena.at(n.data),args);
			case BoundOp.lambda:return lambda(args[0]);
			case BoundOp.set:return set(args[0]);
			case BoundOp.member:return member(args[0],args[1]);
			case BoundOp.subset:return subset(args[0],args[1]);
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
			else if(n.op==BoundOp.lambda||n.op==BoundOp.set){
				uint[] lifted=[0]; foreach(index;indices) lifted~=index+1;
				auto body=rename(at(n.a),push(target,types[contexts[nodes[n.a].context].type]),lifted);
				result=n.op==BoundOp.lambda?lambda(body):set(body);
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
			else if(n.op==BoundOp.lambda||n.op==BoundOp.set){
				auto inner=push(target,types[contexts[nodes[n.a].context].type]);
				BoundTerm[] lifted=[variable(inner,0)]; uint[] indices;
				foreach(i;0..contexts[target.index].length) indices~=i+1;
				foreach(value;values) lifted~=rename(value,inner,indices);
				auto body=substitute(at(n.a),inner,lifted); result=n.op==BoundOp.lambda?lambda(body):set(body);
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
	BindingResult normalize(BoundTerm term,uint budget=4096,bool domains=false){
		check(term); uint steps; bool exhausted; BindingStep[] proofs; ScalarDomain[] scalarDomains;
		struct Result{ uint output,proof; }
		Table!(uint,Result) memo;
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
			return output==BoundTerm.init?output:node(binder).op==BoundOp.lambda?lambda(output):set(output);
		}
		Result visit(BoundTerm t,uint depth){
			enforce(depth<512,"binding normalization depth exceeded");
			auto old=memo.get(t.id,Result(uint.max,uint.max)); if(old.output!=uint.max) return old;
			auto n=node(t); Result result;
			if(n.a==uint.max) result=Result(t.id,emit(BindingRule.refl,t.id,t.id));
			else{
				auto x=visit(at(n.a),depth+1); BoundTerm[] args=[at(x.output)]; uint y=uint.max;
				if(n.b!=uint.max){ auto r=visit(at(n.b),depth+1); args~=at(r.output); y=r.proof; }
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
			if(current.op==BoundOp.apply&&nodes[current.a].op==BoundOp.lambda){
				if(steps<budget){ next=beta(at(nodes[current.a].a),at(current.b)); rule=BindingRule.beta; }
				else exhausted=true;
			}else if(current.op==BoundOp.sequence){
				if(current.a==current.b){ next=at(current.b); rule=BindingRule.seqSelf; }
				else if(totalScalar(at(current.a))){ next=at(current.b); rule=BindingRule.seqScalar; }
				else if(nodes[current.a].op==BoundOp.lambda){ next=at(current.b); rule=BindingRule.seqLam; }
				else if(domains){
					auto op=nodes[current.a].op;
					if(op==BoundOp.set||op==BoundOp.global||op==BoundOp.domain||op==BoundOp.defined||op==BoundOp.holds){ next=at(current.b); rule=BindingRule.seqTotal; }
					else{ next=guard(defined(at(current.a)),at(current.b)); rule=BindingRule.seqGuard; }
				}
				if(next!=BoundTerm.init&&steps>=budget){ next=BoundTerm.init; exhausted=true; }
			}
			if(domains&&next==BoundTerm.init){
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
					next=set(defined(at(nodes[current.a].a))); rule=BindingRule.domainLam;
				}else if(current.op==BoundOp.domain&&nodes[current.a].op==BoundOp.guard&&isTrue(nodes[current.a].a,false)){
					next=set(scalar(push(ctx,pool.view(types[current.type]).fields[0]),arena.boolean(false))); rule=BindingRule.domainGuardFalse;
				}else if(current.op==BoundOp.subset){
					if(current.a==current.b){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.subsetRefl; }
					else if(constantSet(current.a,false)){ next=sequence(at(current.b),scalar(ctx,arena.boolean(true))); rule=BindingRule.subsetEmpty; }
					else if(constantSet(current.b,true)){ next=sequence(at(current.a),scalar(ctx,arena.boolean(true))); rule=BindingRule.subsetUniv; }
					else if(constantSet(current.a,true)&&constantSet(current.b,false)){ next=scalar(ctx,arena.boolean(false)); rule=BindingRule.subsetUnivEmpty; }
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
					if(child.op==BoundOp.lambda||child.op==BoundOp.set||child.op==BoundOp.global||child.op==BoundOp.domain||child.op==BoundOp.defined||child.op==BoundOp.holds){
						next=scalar(ctx,arena.boolean(true)); rule=BindingRule.definedTotal;
					}else if(child.op==BoundOp.guard&&isTrue(child.a,false)){
						next=scalar(ctx,arena.boolean(false)); rule=BindingRule.definedGuardFalse;
					}else if(child.op==BoundOp.guard){
						next=both(holds(at(child.a)),defined(at(child.b))); rule=BindingRule.definedGuard;
					}else if(child.op==BoundOp.member||child.op==BoundOp.subset){
						next=both(defined(at(child.a)),defined(at(child.b))); rule=child.op==BoundOp.member?BindingRule.definedMember:BindingRule.definedSubset;
					}else if(child.op==BoundOp.primitive&&arena.view(arena.at(child.data)).op==Op.not_){
						next=defined(at(child.a)); rule=BindingRule.definedNot;
					}else if(child.op==BoundOp.apply){
						next=holds(member(domain(at(child.a)),at(child.b))); rule=BindingRule.definedApp;
					}
				}
				if((current.op==BoundOp.defined||current.op==BoundOp.holds)&&nodes[current.a].op==BoundOp.scalar&&steps<budget){
					auto source=arena.at(nodes[current.a].data),r=simplifyDomain(arena,source,[],Options(DensityMode.preserve,true));
					exhausted|=r.exhausted;
					extra=cast(uint)scalarDomains.length; scalarDomains~=ScalarDomain(source,r);
					next=scalar(ctx,current.op==BoundOp.defined?r.output:arena.and_(r.output,source));
					rule=current.op==BoundOp.defined?BindingRule.scalarDomain:BindingRule.scalarHolds;
				}
				if(steps>=budget){
					if(next!=BoundTerm.init){ next=BoundTerm.init; exhausted=true; }
					if(current.op==BoundOp.scalar&&!totalScalar(at(result.output))||
						(current.op==BoundOp.defined||current.op==BoundOp.holds)&&nodes[current.a].op==BoundOp.scalar) exhausted=true;
				}
			}
			if(next!=BoundTerm.init){
				++steps; auto step=emit(rule,result.output,next.id,uint.max,uint.max,extra),tail=visit(next,depth+1);
				auto rest=emit(BindingRule.trans,result.output,tail.output,step,tail.proof);
				result=Result(tail.output,emit(BindingRule.trans,t.id,tail.output,result.proof,rest));
			}
			memo.set(t.id,result); return result;
		}
		auto result=visit(term,0); return BindingResult(term,at(result.output),exhausted,steps,proofs,result.proof,scalarDomains);
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
	private string name(uint id){ return "(t"~to!string(id)~" γ)"; }
	private string valueOperation(BoundNode n){
		final switch(n.op){
			case BoundOp.primitive:return leanValueOperation(arena,arena.at(n.data));
			case BoundOp.member:return "Binding.memberValue";
			case BoundOp.subset:return "Binding.subsetValue";
			case BoundOp.domain:return "Binding.inputDomain";
			case BoundOp.defined:return "Binding.definedValue";
			case BoundOp.holds:return "Binding.holdsValue";
			case BoundOp.guard:return "Binding.guardValue";
			case BoundOp.scalar,BoundOp.variable,BoundOp.lambda,BoundOp.apply,BoundOp.sequence,BoundOp.global,BoundOp.set:assert(0);
		}
	}
	private string leanType(TypeId t){
		auto v=pool.view(t);
		if(v.kind==TypeKind.set) return "(.set "~leanType(v.fields[0])~")";
		if(v.kind==TypeKind.function_) return "(.arrow "~leanType(v.fields[0])~" "~leanType(v.fields[1])~")";
		foreach(s;[Sort.natural,Sort.integer,Sort.rational,Sort.real_,Sort.complex,Sort.boolean])
			if(t==scalarType(s)) return "(.scalar ."~leanSort(s)~")";
		throw new Exception("unsupported binding type");
	}
	string exportLean(BindingResult result,bool lowerResult=false){
		check(result.input); check(result.output); enforce(result.proof<result.proofs.length,"missing binding proof");
		auto lowered=lowerResult?lower(result.output):Term.init;
		string code="import QSym\n";
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
			code~="abbrev c"~to!string(i)~" : List Binding.Ty := ";
			code~=i==0?"[]\n":leanType(types[ctx.type])~" :: c"~to!string(ctx.parent)~"\n";
		}
		foreach(i,n;nodes) if(used[i]){
			string expr;
			final switch(n.op){
				case BoundOp.scalar:expr=".scalar n"~to!string(n.data); break;
				case BoundOp.variable:
					expr=".here"; foreach(j;0..n.data) expr="(.there "~expr~")";
					expr=".var "~expr; break;
				case BoundOp.primitive,BoundOp.member,BoundOp.subset,BoundOp.domain,BoundOp.defined,BoundOp.holds,BoundOp.guard:
					expr="."~(n.b==uint.max?"unary":"binary")~" "~valueOperation(n)~" "~name(n.a);
					if(n.b!=uint.max) expr~=" "~name(n.b); break;
				case BoundOp.lambda:expr=".lam "~name(n.a); break;
				case BoundOp.set:expr=".set "~name(n.a); break;
				case BoundOp.global:expr=".constant (some (γ "~leanType(types[n.type])~" "~to!string(n.data)~"))"; break;
				case BoundOp.apply:expr=".app "~name(n.a)~" "~name(n.b); break;
				case BoundOp.sequence:expr=".seq "~name(n.a)~" "~name(n.b); break;
			}
			code~="noncomputable def t"~to!string(i)~" (γ : Binding.Globals) : Binding.Expr c"~to!string(n.context)~" "~leanType(types[n.type])~" := "~expr~"\n";
		}
		string proofName(uint id){ return "(p"~to!string(id)~" γ)"; }
		foreach(i,p;result.proofs){
			auto n=nodes[p.from]; string proof;
			final switch(p.rule){
				case BindingRule.refl:proof=".refl "~name(p.from); break;
				case BindingRule.trans:proof=".trans "~proofName(p.left)~" "~proofName(p.right); break;
				case BindingRule.beta:proof=".beta "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.seqScalar:proof=".seqScalar n"~to!string(nodes[n.a].data)~" "~name(n.b)~" (fun _ => ⟨_, rfl⟩)"; break;
				case BindingRule.seqLam:proof=".seqLam "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.seqSelf:proof=".seqSelf "~name(n.a); break;
				case BindingRule.fold,BindingRule.seqTotal:proof=".ofEq (fun _ _ => rfl)"; break;
				case BindingRule.seqGuard:proof=".seqGuard "~name(n.a)~" "~name(n.b); break;
				case BindingRule.domainLam:proof=".domainLam "~name(nodes[n.a].a); break;
				case BindingRule.memberSet:proof=".memberSet "~name(nodes[n.a].a)~" "~name(n.b); break;
				case BindingRule.guardTrue:proof=".guardTrue "~name(n.b); break;
				case BindingRule.guardAnd:proof=".guardAnd "~name(n.a)~" "~name(nodes[n.b].a)~" "~name(nodes[n.b].b); break;
				case BindingRule.holdsGuard:proof=".holdsGuard "~name(nodes[n.a].a)~" "~name(nodes[n.a].b); break;
				case BindingRule.setHolds:proof=".setHolds "~name(n.a); break;
				case BindingRule.definedGuardFalse:proof=".definedGuardFalse "~name(nodes[n.a].b); break;
				case BindingRule.definedTotal:proof=".ofEq (fun _ _ => rfl)"; break;
				case BindingRule.subsetRefl:proof=".subsetRefl "~name(n.a); break;
				case BindingRule.subsetEmpty:proof=".subsetEmpty "~name(n.b); break;
				case BindingRule.subsetUniv:proof=".subsetUniv "~name(n.a); break;
				case BindingRule.subsetUnivEmpty:
					auto ty=pool.view(types[nodes[n.a].type]).fields[0],v=pool.view(ty);
					auto witness=v.kind==TypeKind.function_?"(fun _ => none)":v.kind==TypeKind.set?"∅":v.kind==TypeKind.boolean?"false":"0";
					proof=".subsetUnivEmpty (a := "~leanType(ty)~") "~witness; break;
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
					auto generic=n.op==BoundOp.primitive||n.op==BoundOp.member||n.op==BoundOp.subset||n.op==BoundOp.domain||n.op==BoundOp.defined||n.op==BoundOp.holds||n.op==BoundOp.guard;
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
			code~="theorem p"~to!string(i)~" (γ : Binding.Globals) : Binding.Reduction "~name(p.from)~" "~name(p.to)~" := "~proof~"\n";
		}
		code~="theorem reduction (γ : Binding.Globals) : Binding.Reduction "~name(result.input.id)~" "~name(result.output.id)~" := "~proofName(result.proof)~"\n";
		string left=name(result.input.id)~".eval ξ ρ",right=name(result.output.id)~".eval ξ ρ";
		code~="theorem sound (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env c"~to!string(node(result.input).context)~") : "~left~" = "~right~" := Binding.Reduction.sound (reduction γ) ξ ρ\n";
		code~="theorem domain (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env c"~to!string(node(result.input).context)~") : Value.Defined ("~left~") ↔ Value.Defined ("~right~") := Binding.Reduction.defined (reduction γ) ξ ρ\n";
		if(lowerResult){
			code~="theorem lowered (γ : Binding.Globals) (ξ : Env) (ρ : Binding.Env c0) : "~name(result.input.id)~".eval ξ ρ = n"~to!string(lowered.id)~".eval ξ := Eq.trans (sound γ ξ ρ) rfl\n";
			code~="#qsym_check_axioms lowered\n";
		}
		return code~"#qsym_check_axioms sound\n#qsym_check_axioms domain\nend QSym.BindingCertificate\n";
	}
}
