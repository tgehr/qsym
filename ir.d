module qsym.ir;

static assert(__VERSION__>=2112,"QSym requires the D 2.112 frontend or newer (tested with LDC 1.42.0).");

import std.exception:enforce;
import std.conv:to;
import qsym.buffer:Buffer;
import qsym.table:Table;
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
	ubyte arity;
	uint a=uint.max,b=uint.max;
	long value,imaginary;
}

final class Arena{
	private this(){}
	private bool closed;
	private Buffer!Node nodes;
	private Table!(Node,uint,hash) table;
	private Number[] numbers;
	private Table!(string,uint) numberIndex;

	private static size_t hash(Node n)pure nothrow @nogc{
		ulong h=14695981039346656037UL;
		ulong[7] values=[cast(ulong) n.op,cast(ulong) n.sort,cast(ulong) n.arity,
			cast(ulong) n.a,cast(ulong) n.b,cast(ulong) n.value,cast(ulong) n.imaginary];
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
	Sort sort(Term t)const{ return node(t).sort; }
	Term at(uint i){
		enforce(!closed&&i<nodes.length,"closed arena or node index out of range");
		return Term(this,i);
	}
	Term child(Term t,uint which){
		auto n=node(t);
		enforce(which<n.arity,"child index out of range");
		return at(which==0?n.a:n.b);
	}

	private Term intern(Node n){
		enforce(!closed,"arena is closed");
		enforce(nodes.length<uint.max,"arena exceeds 32-bit node limit");
		auto found=table.get(n,uint.max);
		if(found!=uint.max) return Term(this,found);
		auto i=cast(uint) nodes.length;
		nodes.append(n);
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
	Term add(Term a,Term b){
		scalar(a); enforce(sort(a)==sort(b),"scalar types differ");
		return rank(sort(a))<rank(Sort.real_)?call(builtin("add"~suffix(sort(a))),[a,b]):binary(Op.add,a,b);
	}
	Term mul(Term a,Term b){
		scalar(a); enforce(sort(a)==sort(b),"scalar types differ");
		return rank(sort(a))<rank(Sort.real_)?call(builtin("mul"~suffix(sort(a))),[a,b]):binary(Op.mul,a,b);
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

	/// Iterative left-to-right DFS: linear work, no recursion, and traversal
	/// independent of arena allocation order (including budget-limited runs).
	uint[] postorder(Term root){
		check(root);
		bool[] seen=new bool[nodes.length];
		uint[] result,stack=[root.id];
		while(stack.length){
			auto id=stack[$-1],n=nodes[id];
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
		auto n=a.node(a.at(i));
		result~="%"~to!string(i)~" : "~sortName(n.sort)~" = "~to!string(n.op);
		if(n.arity>=1) result~=" %"~to!string(n.a);
		if(n.arity==2) result~=" %"~to!string(n.b);
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
		auto n=a.node(a.at(i));
		if(n.arity>=1) assert(positions.contains(n.a));
		if(n.arity==2) assert(positions.contains(n.b));
		assert(!positions.contains(i)); positions.set(i,cast(uint) j);
	}
	sa.close();
	assertThrown(a.node(x));
	assertThrown(a.real_(1));
}
