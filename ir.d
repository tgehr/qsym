module qsym.ir;

static assert(__VERSION__>=2112,"QSym requires the D 2.112 frontend or newer (tested with LDC 1.42.0).");

import std.exception:enforce;
import std.conv:to;
import qsym.buffer:Buffer;
import qsym.table:Table;
import qsym.multiset:Multisets;
public import qsym.number:BigInt,Rational,Number;

@safe:

public import qsym.builtins;
enum Op:ubyte{
	realLit,complexLit,boolLit,variable,add,mul,inv,nonzero,
	mask,conj,lebesgue,puncture,densityAt,forget,numberLit,pow,not_,and_,or_,lt,le,abs,builtin
}

/// Public handles carry ownership; internal edges are compact arena-local IDs.
/// Default handles are invalid. Handles from distinct arenas never alias.
struct Term{
	private Arena owner;
	private uint index=uint.max;
	uint id()const{ return index; }
	bool opEquals(Term other)const{
		return owner is other.owner&&index==other.index;
	}
}

/// A copy of this record is safe to inspect; it cannot mutate the arena.
struct Node{
	Op op;
	Sort sort;
	bool region;
	// Regions count distinct operands; a/b are only a binary compatibility view.
	uint arity;
	uint a=uint.max,b=uint.max;
	long value,imaginary;
	this(Op op,Sort sort,uint arity=0,uint a=uint.max,uint b=uint.max,long value=0,long imaginary=0,bool region=false){
		this.op=op; this.sort=sort; this.arity=arity; this.a=a; this.b=b;
		this.value=value; this.imaginary=imaginary; this.region=region;
	}
}
struct Operand{ Term term; uint count; }

final class Arena{
	private this(){ multisets=new Multisets; }
	private bool closed;
	private Buffer!Node nodes;
	private Table!(Node,uint,hash) table;
	private Number[] numbers;
	private Table!(string,uint) numberIndex;
	private Multisets multisets;
	private Table!(ulong,uint) rawRegions;
	private struct RegionKey{ Op op; Sort sort; uint operands; }
	private Table!(RegionKey,uint) regions;
	private Buffer!uint normalForms;

	private static size_t hash(Node n)pure nothrow @nogc{
		ulong h=14695981039346656037UL;
		ulong[8] values=[cast(ulong)n.op,cast(ulong)n.sort,cast(ulong)n.arity,
			cast(ulong)n.a,cast(ulong)n.b,cast(ulong)n.value,cast(ulong)n.imaginary,cast(ulong)n.region];
		foreach(v;values)
			h=(h^v)*1099511628211UL;
		// Mix high bits into the low bits used by a power-of-two table.
		h^=h>>32;
		return cast(size_t) h;
	}

	size_t length()const{ return nodes.length; }

	void check(Term t)const{
		enforce(!closed&&t.owner is this&&t.index<nodes.length,"closed arena, invalid or foreign term handle");
	}
	Node node(Term t)const{ check(t); return nodes[t.index]; }
	// A deterministic decomposition for algorithms and binary rule lemmas.
	// Stored nodes and the public child/operand traversal remain n-ary.
	Node view(Term t)const{
		auto n=node(t);
		if(n.region){ n.arity=2; n.value=0; n.region=false; }
		return n;
	}
	Sort sort(Term t)const{ return node(t).sort; }
	Term at(uint i){
		enforce(!closed&&i<nodes.length,"closed arena or node index out of range");
		return Term(this,i);
	}
	Term child(Term t,uint which){
		auto n=node(t);
		enforce(which<n.arity,"child index out of range");
		if(n.region) return at(multisets.entry(cast(uint)n.value,which).atom);
		return at(which==0?n.a:n.b);
	}
	Term viewChild(Term t,uint which){ auto n=view(t); enforce(which<n.arity,"child index out of range"); return at(which?n.b:n.a); }
	Operand[] operands(Term t){
		auto n=node(t); enforce(n.region,"counted operands require a sum or product");
		Operand[] result; foreach(c;multisets.entries(cast(uint)n.value)) result~=Operand(at(c.atom),c.count);
		return result;
	}
	package uint multiset(Term t,Op op){
		check(t); enforce(op==Op.add||op==Op.mul,"associative operation expected");
		ulong key(uint id){ return (cast(ulong)op<<32)|id; }
		uint[] pending=[t.id];
		while(pending.length){
			auto id=pending[$-1]; if(rawRegions.contains(key(id))){ --pending.length; continue; }
			auto atom=at(id),n=node(atom); uint result;
			if(n.op==op&&n.region) result=cast(uint)n.value;
			else if(n.op==op){
				if(!rawRegions.contains(key(n.a))){ pending~=n.a; continue; }
				if(!rawRegions.contains(key(n.b))){ pending~=n.b; continue; }
				result=multisets.merge(rawRegions.get(key(n.a),0),rawRegions.get(key(n.b),0));
			}else if(!isNumber(atom)||!(op==Op.add?number(atom).zero:number(atom).one)) result=multisets.single(id);
			rawRegions.set(key(id),result); --pending.length;
		}
		return rawRegions.get(key(t.id),0);
	}
	package size_t multisetSize(uint id){ return multisets.node(id).length; }
	package size_t multisetStorage(){ return multisets.length; }
	package Operand[] multisetTerms(uint id){
		Operand[] result; foreach(c;multisets.entries(id)) result~=Operand(at(c.atom),c.count); return result;
	}
	private uint bag(Term t,Op op){
		t=canonical(t); auto n=node(t);
		if(n.op==op&&n.region) return cast(uint)n.value;
		if(isNumber(t)&&(op==Op.add?number(t).zero:number(t).one)) return 0;
		return multisets.single(t.id);
	}
	private Term region(Op op,Sort sort,uint bag){
		if(!bag) return number(Number(op==Op.add?0:1),sort);
		auto b=multisets.node(bag);
		if(!b.mask&&b.right==1) return at(b.left);
		auto key=RegionKey(op,sort,bag),old=regions.get(key,uint.max);
		if(old!=uint.max) return at(old);
		auto left=b.mask?b.left:multisets.single(b.left,b.right&1?b.right-1:b.right/2);
		auto right=b.mask?b.right:multisets.single(b.left,b.right&1?1:b.right/2);
		auto l=region(op,sort,left),r=region(op,sort,right);
		auto result=intern(Node(op,sort,b.length,l.id,r.id,bag,0,true));
		regions.set(key,result.id); return result;
	}
	Term region(Op op,Sort sort,Operand[] terms){
		enforce((op==Op.add||op==Op.mul)&&(sort==Sort.real_||sort==Sort.complex),"real or complex associative operation expected");
		uint result;
		foreach(e;terms){ enforce(this.sort(e.term)==sort,"operand type mismatch"); result=multisets.merge(result,multisets.scale(bag(e.term,op),e.count)); }
		return region(op,sort,result);
	}

	private Term intern(Node n){
		enforce(!closed,"arena is closed");
		enforce(nodes.length<uint.max,"arena exceeds 32-bit node limit");
		auto found=table.get(n,uint.max);
		if(found!=uint.max) return Term(this,found);
		auto i=cast(uint) nodes.length;
		nodes.append(n);
		bool normalized=n.region||n.op!=Op.add&&n.op!=Op.mul&&
			(!n.arity||normalForms[n.a]==n.a+1)&&(n.arity<2||normalForms[n.b]==n.b+1);
		normalForms.append(normalized?i+1:0);
		table.set(n,i);
		return Term(this,i);
	}

	Term real_(long n){ return intern(Node(Op.realLit,Sort.real_,0,uint.max,uint.max,n)); }
	Term complex(long r,long i=0){
		return intern(Node(Op.complexLit,Sort.complex,0,uint.max,uint.max,r,i));
	}
	Term real_(Rational r){ return number(Number(r),Sort.real_); }
	Term complex(Rational r,Rational i=Rational.init){ return number(Number(r,i),Sort.complex); }
	Term number(Number v,Sort s){
		enforce(!closed,"arena is closed");
		enforce(numeric(s),"number requires a scalar type");
		enforce(s==Sort.complex||v.im.zero,"ordered number has an imaginary component");
		enforce(s!=Sort.natural&&s!=Sort.integer||v.re.integral,"integer literal required");
		enforce(s!=Sort.natural||v.re>=Rational(0),"negative natural literal");
		if((s==Sort.real_||s==Sort.complex)&&v.re.small&&v.im.small)
			return s==Sort.real_?real_(v.re.integer):complex(v.re.integer,v.im.integer);
		auto key=v.toString;
		auto i=numberIndex.get(key,uint.max);
		if(i==uint.max){
			enforce(numbers.length<uint.max,"number pool exceeds 32-bit limit");
			i=cast(uint)numbers.length; numbers~=v; numberIndex.set(key,i);
		}
		return intern(Node(Op.numberLit,s,0,uint.max,uint.max,i));
	}
	bool isNumber(Term t)const{ auto op=node(t).op; return op==Op.realLit||op==Op.complexLit||op==Op.numberLit; }
	Number number(Term t)const{
		return number(node(t));
	}
	Number number(Node n)const{
		enforce(n.op==Op.realLit||n.op==Op.complexLit||n.op==Op.numberLit,"expected a number");
		if(n.op==Op.numberLit) enforce(n.value>=0&&n.value<numbers.length,"invalid number index");
		return n.op==Op.numberLit?numbers[cast(size_t)n.value]:Number(n.value,n.imaginary);
	}
	Term natural_(long n){ return number(Number(n),Sort.natural); }
	Term integer(long n){ return number(Number(n),Sort.integer); }
	Term rational(long n,long d=1){ return number(Number(Rational(BigInt(n),BigInt(d))),Sort.rational); }
	Term boolean(bool b){ return intern(Node(Op.boolLit,Sort.boolean,0,uint.max,uint.max,b)); }
	Term variable(Sort s,uint i){
		enforce(numeric(s)||s==Sort.boolean,
			"only scalar variables are supported in this slice");
		return intern(Node(Op.variable,s,0,uint.max,uint.max,i));
	}
	private void scalar(Term a)const{
		auto s=sort(a);
		enforce(numeric(s),"numeric value expected");
	}
	private Term binary(Op op,Term a,Term b){
		scalar(a); scalar(b);
		enforce(sort(a)==sort(b),"scalar types differ; use an explicit embedding");
		return intern(Node(op,sort(a),2,a.id,b.id));
	}
	Term add(Term a,Term b,bool raw=false){
		scalar(a); enforce(sort(a)==sort(b),"scalar types differ");
		if(rank(sort(a))<rank(Sort.real_)) return call(builtin("add"~suffix(sort(a))),[a,b]);
		return raw?binary(Op.add,a,b):region(Op.add,sort(a),multisets.merge(bag(a,Op.add),bag(b,Op.add)));
	}
	Term mul(Term a,Term b,bool raw=false){
		scalar(a); enforce(sort(a)==sort(b),"scalar types differ");
		if(rank(sort(a))<rank(Sort.real_)) return call(builtin("mul"~suffix(sort(a))),[a,b]);
		return raw?binary(Op.mul,a,b):region(Op.mul,sort(a),multisets.merge(bag(a,Op.mul),bag(b,Op.mul)));
	}
	Term neg(Term a){ scalar(a); if(sort(a)==Sort.natural) a=castTo(a,Sort.integer); return mul(number(Number(-1),sort(a)),a); }
	Term sub(Term a,Term b){ enforce(sort(a)==sort(b),"scalar types differ"); b=neg(b); return add(castTo(a,sort(b)),b); }
	Term div(Term a,Term b){ enforce(sort(a)==sort(b),"scalar types differ"); b=inv(b); return mul(castTo(a,sort(b)),b); }
	Term inv(Term a){
		scalar(a); if(rank(sort(a))<rank(Sort.rational)) a=castTo(a,Sort.rational);
		return sort(a)==Sort.rational?call(Builtin.invQ,[a]):intern(Node(Op.inv,sort(a),1,a.id));
	}
	Term pow(Term a,uint n){ scalar(a); return intern(Node(Op.pow,sort(a),1,a.id,uint.max,n)); }
	Term abs(Term a){
		enforce(sort(a)==Sort.real_,"absolute value requires Real");
		return intern(Node(Op.abs,Sort.real_,1,a.id));
	}
	Term nonzero(Term a){
		scalar(a); return rank(sort(a))<rank(Sort.real_)?call(builtin("nonzero"~suffix(sort(a))),[a]):intern(Node(Op.nonzero,Sort.boolean,1,a.id));
	}
	Term equal(Term a,Term b){
		if(sort(a)==Sort.boolean&&sort(b)==Sort.boolean) return call(Builtin.eqB,[a,b]);
		return not_(nonzero(sub(a,b)));
	}
	Term not_(Term a){
		enforce(sort(a)==Sort.boolean,"not requires Bool");
		return intern(Node(Op.not_,Sort.boolean,1,a.id));
	}
	private Term logical(Op op,Term a,Term b){
		enforce(sort(a)==Sort.boolean&&sort(b)==Sort.boolean,"logical operation requires Bool");
		return intern(Node(op,Sort.boolean,2,a.id,b.id));
	}
	Term and_(Term a,Term b){ return logical(Op.and_,a,b); }
	Term or_(Term a,Term b){ return logical(Op.or_,a,b); }
	private Term comparison(Op op,Term a,Term b){
		enforce(sort(a)==Sort.real_&&sort(b)==Sort.real_,"ordering requires Real");
		return intern(Node(op,Sort.boolean,2,a.id,b.id));
	}
	Term lt(Term a,Term b){ return rank(sort(a))>=0&&rank(sort(a))<rank(Sort.real_)?call(builtin("lt"~suffix(sort(a))),[a,b]):comparison(Op.lt,a,b); }
	Term le(Term a,Term b){ return rank(sort(a))>=0&&rank(sort(a))<rank(Sort.real_)?call(builtin("le"~suffix(sort(a))),[a,b]):comparison(Op.le,a,b); }
	Term mask(Term p,Term a){
		enforce(sort(p)==Sort.boolean,"mask predicate must be Bool");
		scalar(a);
		return intern(Node(Op.mask,sort(a),2,p.id,a.id));
	}
	Term conj(Term a){
		enforce(sort(a)==Sort.complex,"conjugation requires Complex");
		return intern(Node(Op.conj,Sort.complex,1,a.id));
	}
	Term call(Builtin f,Term[] args){
		auto info=builtinInfo(f);
		enforce(args.length==info.args.length,"built-in arity mismatch");
		foreach(i,t;args) enforce(sort(t)==info.args[i],"built-in type mismatch: "~info.code);
		return intern(Node(Op.builtin,info.result,cast(ubyte)args.length,
			args.length?args[0].id:uint.max,args.length==2?args[1].id:uint.max,cast(long)f));
	}
	Term castTo(Term t,Sort target){
		enforce(promotes(sort(t),target),"invalid numeric embedding");
		while(sort(t)!=target){
			auto next=sort(t)==Sort.natural?Sort.integer:sort(t)==Sort.integer?Sort.rational:sort(t)==Sort.rational?Sort.real_:Sort.complex;
			t=call(builtin("cast"~suffix(sort(t))~suffix(next)),[t]);
		}
		return t;
	}
	Term lebesgue(){ return intern(Node(Op.lebesgue,Sort.density)); }
	Term puncture(Term d){
		enforce(sort(d)==Sort.density,"puncture requires a density representative");
		return intern(Node(Op.puncture,Sort.density,1,d.id));
	}
	/// Same-reference density disintegration, evaluated at x. Reference is λ.
	Term densityAt(Term d,Term x){
		enforce(sort(d)==Sort.density&&sort(x)==Sort.real_,
			"densityAt requires a tracked density and a real point");
		return intern(Node(Op.densityAt,Sort.real_,2,d.id,x.id));
	}
	Term forget(Term d){
		enforce(sort(d)==Sort.density,"forget requires a density representative");
		return intern(Node(Op.forget,Sort.measure,1,d.id));
	}

	/// Rebuilding rechecks every operand type and arena ownership.
	Term rebuild(Term original,Term[] cs){
		auto n=node(original);
		enforce(cs.length==n.arity,"wrong arity");
		if(n.region){ auto es=operands(original); foreach(i,ref e;es) e.term=cs[i]; return region(n.op,n.sort,es); }
		final switch(n.op){
			case Op.realLit,Op.complexLit,Op.boolLit,Op.variable,Op.lebesgue,Op.numberLit:
				return original;
			case Op.builtin:return call(cast(Builtin)n.value,cs);
			case Op.add:return add(cs[0],cs[1]);
			case Op.mul:return mul(cs[0],cs[1]);
			case Op.inv:return inv(cs[0]);
			case Op.pow:return pow(cs[0],cast(uint)n.value);
			case Op.abs:return abs(cs[0]);
			case Op.not_:return not_(cs[0]);
			case Op.and_:return and_(cs[0],cs[1]);
			case Op.or_:return or_(cs[0],cs[1]);
			case Op.lt:return lt(cs[0],cs[1]);
			case Op.le:return le(cs[0],cs[1]);
			case Op.nonzero:return nonzero(cs[0]);
			case Op.mask:return mask(cs[0],cs[1]);
			case Op.conj:return conj(cs[0]);
			case Op.puncture:return puncture(cs[0]);
			case Op.densityAt:return densityAt(cs[0],cs[1]);
			case Op.forget:return forget(cs[0]);
		}
	}
	Term viewRebuild(Term original,Term[] cs,bool raw=false){
		auto n=view(original); enforce(cs.length==n.arity,"wrong view arity");
		if(n.op==Op.add) return add(cs[0],cs[1],raw);
		if(n.op==Op.mul) return mul(cs[0],cs[1],raw);
		return rebuild(original,cs);
	}
	Term canonical(Term t){
		check(t); if(normalForms[t.id]) return at(normalForms[t.id]-1);
		uint[] pending=[t.id];
		while(pending.length){
			auto id=pending[$-1],n=nodes[id];
			if(normalForms[id]){ --pending.length; continue; }
			if(n.arity>=1&&!normalForms[n.a]){ pending~=n.a; continue; }
			if(n.arity==2&&!normalForms[n.b]){ pending~=n.b; continue; }
			Term[] cs; if(n.arity) cs~=at(normalForms[n.a]-1); if(n.arity==2) cs~=at(normalForms[n.b]-1);
			normalForms[id]=viewRebuild(at(id),cs).id+1; --pending.length;
		}
		return at(normalForms[t.id]-1);
	}

	/// Iterative left-to-right DFS: linear work, no recursion, and traversal
	/// independent of arena allocation order (including budget-limited runs).
	uint[] postorder(Term root){
		check(root); bool[] seen=new bool[nodes.length];
		struct Frame{ Term term; uint next; Operand[] terms; }
		Frame frame(Term t){ auto n=node(t); return Frame(t,0,n.region?operands(t):null); }
		Frame[] stack=[frame(root)]; uint[] result;
		while(stack.length){
			auto t=stack[$-1].term,n=node(t);
			if(stack[$-1].next<n.arity){
				auto i=stack[$-1].next++,c=n.region?stack[$-1].terms[i].term:at(i?n.b:n.a);
				if(!seen[c.id]) stack~=frame(c);
			}else{ seen[t.id]=true; result~=t.id; --stack.length; }
		}
		return result;
	}
	uint[] viewPostorder(Term root){
		check(root);
		bool[] seen=new bool[nodes.length];
		uint[] result,stack=[root.id];
		while(stack.length){
			auto id=stack[$-1],n=view(at(id));
			if(n.arity>=1&&!seen[n.a]){ stack~=n.a; continue; }
			if(n.arity==2&&!seen[n.b]){ stack~=n.b; continue; }
			seen[id]=true; result~=id; --stack.length;
		}
		return result;
	}

}

/// Noncopyable, scoped owner of an arena. Destruction invalidates handles and
/// releases its storage. Keep this owner alive through proof export. A foreign
/// host must also obey druntime's thread-registration and GC-root requirements.
struct Session{
	private Arena handle;
	@disable this(this);

	static Session open(){
		Session s;
		s.handle=new Arena;
		return s;
	}
	Arena arena(){
		enforce(handle !is null&&!handle.closed,"session is closed");
		return handle;
	}
	void close()nothrow{
		if(handle is null) return;
		handle.closed=true;
		handle.nodes=typeof(handle.nodes).init;
		handle.table=typeof(handle.table).init;
		handle.numbers=null;
		handle.numberIndex=typeof(handle.numberIndex).init;
		handle.multisets=null;
		handle.regions=typeof(handle.regions).init;
		handle.rawRegions=typeof(handle.rawRegions).init;
		handle.normalForms=typeof(handle.normalForms).init;
		handle=null;
	}
	~this()nothrow{ close(); }
}

string sortName(Sort s){
	final switch(s){
		case Sort.natural:return "Nat";
		case Sort.integer:return "Int";
		case Sort.rational:return "Rat";
		case Sort.real_:return "Real";
		case Sort.complex:return "Complex";
		case Sort.boolean:return "Bool";
		case Sort.density:return "Density";
		case Sort.measure:return "Measure";
	}
}

/// Bounded, nonrecursive diagnostic display preserves DAG sharing.
string dump(Arena a,Term root){
	string result;
	foreach(i;a.postorder(root)){
		auto t=a.at(i),n=a.node(t);
		result~="%"~to!string(i)~" : "~sortName(n.sort)~" = "~to!string(n.op);
		if(n.region) foreach(e;a.operands(t)) result~=" %"~to!string(e.term.id)~"*"~to!string(e.count);
		else{
			if(n.arity>=1) result~=" %"~to!string(n.a);
			if(n.arity==2) result~=" %"~to!string(n.b);
		}
		if(n.op==Op.realLit||n.op==Op.complexLit||n.op==Op.boolLit||n.op==Op.variable)
			result~=" "~to!string(n.value);
		if(n.op==Op.complexLit) result~=" "~to!string(n.imaginary)~"i";
		if(n.op==Op.numberLit) result~=" "~a.number(a.at(i)).toString;
		if(n.op==Op.pow) result~=" "~to!string(n.value);
		result~="\n";
	}
	return result;
}

unittest{
	import std.exception:assertThrown;
	auto sa=Session.open(); auto sb=Session.open();
	auto a=sa.arena,b=sb.arena;
	auto x=a.variable(Sort.real_,0);
	assert(x==a.variable(Sort.real_,0));
	assertThrown(a.add(x,b.real_(1)));
	assertThrown(a.add(x,a.complex(1)));
	assertThrown(a.node(Term.init));
	auto d=a.puncture(a.lebesgue());
	assertThrown(a.densityAt(a.forget(d),x));
	auto p=a.add(x,a.real_(0));
	auto q=a.mul(p,p);
	auto order=a.postorder(q);
	Table!(uint,uint) positions;
	foreach(j,i;order){
		auto t=a.at(i),n=a.node(t);
		foreach(k;0..n.arity) assert(positions.contains(a.child(t,k).id));
		assert(!positions.contains(i)); positions.set(i,cast(uint) j);
	}
	sa.close();
	assertThrown(a.node(x));
	assertThrown(a.real_(1));
}

unittest{
	import std.exception:assertThrown;
	auto session=Session.open(); auto a=session.arena;
	auto x=a.variable(Sort.real_,0),y=a.variable(Sort.real_,1),z=a.variable(Sort.real_,2);
	foreach(op;[Op.add,Op.mul]){
		Term join(Term l,Term r){ return op==Op.add?a.add(l,r):a.mul(l,r); }
		auto t=join(join(x,y),join(z,x));
		assert(t==join(z,join(x,join(y,x))));
		assert(a.node(t).region&&a.node(t).arity==3);
		assert(a.operands(t)==[Operand(x,2),Operand(y,1),Operand(z,1)]);
		assert(a.postorder(t).length==4);
		assert(a.rebuild(t,[y,z,x])==join(join(y,y),join(z,x)));
		auto copy=a.operands(t); copy[0].count=100;
		assert(a.operands(t)[0].count==2);
		auto raw=op==Op.add?a.add(z,a.add(y,x,true),true):a.mul(z,a.mul(y,x,true),true);
		assert(!a.node(raw).region&&a.canonical(raw)==join(x,join(y,z)));
		assert(a.canonical(a.inv(raw))==a.inv(join(x,join(y,z))));
		assertThrown(a.region(op,Sort.real_,[Operand(x,uint.max),Operand(x,1)]));
	}
	auto zero=a.real_(0),one=a.real_(1),undefined=a.inv(zero);
	assert(a.add(x,zero)==x&&a.mul(one,x)==x);
	assert(a.mul(zero,undefined)!=zero);
	assert(a.add(undefined,a.mul(a.real_(-1),undefined))!=zero);
	assert(a.region(Op.mul,Sort.real_,[Operand(undefined,0)])==one);
	auto c=a.variable(Sort.complex,0),d=a.variable(Sort.complex,1);
	assert(a.add(c,d)==a.add(d,c)&&a.mul(c,d)==a.mul(d,c));
}
