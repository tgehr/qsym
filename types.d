module qsym.types;
import std.exception:enforce;
import std.conv:to;
import qsym.table:Table;
@safe:

enum Sort:ubyte{ real_,complex,boolean,density,measure,natural,integer,rational }

enum TypeKind:ubyte{
	unit,boolean,natural,integer,rational,real_,complex,
	uintBits,intBits,vector,tuple,array,function_,set,type_,pi
}
struct TypeId{
	private TypePool owner;
	private uint index=uint.max;
	@property uint id()const{ return index; }
	bool opEquals(TypeId rhs)const{ return owner is rhs.owner&&index==rhs.index; }
}
struct TypeView{
	TypeKind kind;
	ulong length;
	TypeId[] fields;
	Dimension dimension;
}

final class Dimension{
	string op;
	Dimension left,right;
	uint index=uint.max;
	immutable string key,text,lean;
	immutable ulong value;
	immutable bool constant;
	immutable string[] names;
	private this(string key,string text,string lean,ulong value,bool constant,const(string)[] names=[]){
		this.key=key; this.text=text; this.lean=lean; this.value=value; this.constant=constant; this.names=names.idup;
	}
	static Dimension literal(ulong n){ auto s=to!string(n); return new Dimension("#"~s,s,s,n,true); }
	static Dimension variable(string name,uint index){ return new Dimension("v"~to!string(index)~":"~name,name,"(δ "~to!string(index)~")",0,false,[name]); }
	static Dimension bound(uint index){ auto d=new Dimension("b"~to!string(index),"?"~to!string(index),"",0,false); d.index=index; return d; }
	Dimension map(Dimension delegate(uint) @safe f){
		if(index!=uint.max) return f(index);
		return op.length?binary(op,left.map(f),right.map(f)):this;
	}
	string format(string[] locals){
		if(index!=uint.max){ enforce(index<locals.length,"unbound dimension"); return locals[index]; }
		return op.length?"("~left.format(locals)~op~right.format(locals)~")":text;
	}
	static Dimension binary(string op,Dimension a,Dimension b){
		enforce(op=="+"||op=="*"||op=="^","invalid dimension operator");
		if(a.constant&&b.constant){
			if(op=="+"&&a.value<=ulong.max-b.value) return literal(a.value+b.value);
			if(op=="*"&&(!b.value||a.value<=ulong.max/b.value)) return literal(a.value*b.value);
			if(op=="^"&&b.value<=64){
				ulong n=1; bool fits=true;
				foreach(i;0..b.value){ if(a.value&&n>ulong.max/a.value){ fits=false; break; } n*=a.value; }
				if(fits) return literal(n);
			}
		}
		auto d=new Dimension("("~a.key~op~b.key~")","("~a.text~op~b.text~")","("~a.lean~op~b.lean~")",0,false,a.names~b.names);
		d.op=op; d.left=a; d.right=b; return d;
	}
}

final class TypePool{
	private TypeView[] nodes;
	private Table!(string,uint) table;
	private void check(TypeId t)const{
		enforce(t.owner is this&&t.index<nodes.length,"invalid or foreign type handle");
	}
	private TypeId intern(TypeKind k,ulong n,TypeId[] fs,Dimension dimension=null){
		string key=to!string(cast(ubyte) k)~":"~to!string(n);
		if(dimension !is null) key~="/"~dimension.key;
		foreach(f;fs){ check(f); key~=":"~to!string(f.index); }
		auto found=table.get(key,uint.max);
		if(found!=uint.max) return TypeId(this,found);
		enforce(nodes.length<uint.max,"type pool exhausted");
		auto id=cast(uint) nodes.length;
		nodes~=TypeView(k,n,fs.dup,dimension);
		table.set(key,id);
		return TypeId(this,id);
	}
	TypeView view(TypeId t){
		check(t); auto v=nodes[t.index]; v.fields=v.fields.dup; return v;
	}
	TypeId primitive(TypeKind k){
		enforce(k<=TypeKind.complex||k==TypeKind.type_,"not a primitive type");
		return intern(k,0,[]);
	}
	TypeId bits(bool signed_,ulong width){
		return intern(signed_?TypeKind.intBits:TypeKind.uintBits,width,[]);
	}
	TypeId vector(TypeId element,ulong length){
		return vector(element,Dimension.literal(length));
	}
	TypeId vector(TypeId element,Dimension length){
		check(element); enforce(length !is null,"missing vector dimension");
		return intern(TypeKind.vector,length.constant?length.value:ulong.max,[element],length);
	}
	TypeId tuple(TypeId[] fields){
		foreach(f;fields) check(f);
		if(!fields.length) return primitive(TypeKind.unit);
		bool uniform=true;
		foreach(f;fields) if(f!=fields[0]) uniform=false;
		if(uniform) return vector(fields[0],fields.length);
		foreach(f;fields){
			bool open; map(f,(uint i){ open=true; return Dimension.bound(i); });
			enforce(!open,"heterogeneous tuples with bound dimensions are not supported yet");
		}
		return intern(TypeKind.tuple,0,fields);
	}
	TypeId array(TypeId t){ return intern(TypeKind.array,0,[t]); }
	TypeId function_(TypeId a,TypeId b){ return intern(TypeKind.function_,0,[a,b]); }
	TypeId pi(TypeId a,TypeId b){
		if(!binds(b,0)) return function_(a,shift(b,-1));
		enforce(view(a).kind==TypeKind.natural,"dependent function parameters must currently be ℕ");
		return intern(TypeKind.pi,0,[a,b]);
	}
	TypeId map(TypeId t,Dimension delegate(uint) @safe f,uint depth=0){
		auto v=view(t); TypeId[] fields;
		foreach(i,field;v.fields) fields~=map(field,f,depth+(v.kind==TypeKind.pi&&i==1?1:0));
		auto d=v.dimension;
		if(d !is null) d=d.map((uint i)=>i<depth?Dimension.bound(i):f(i-depth).map((uint j)=>Dimension.bound(j+depth)));
		return v.kind==TypeKind.vector?vector(fields[0],d):intern(v.kind,v.length,fields);
	}
	TypeId shift(TypeId t,int amount){
		return map(t,(uint i){ enforce(cast(long)i+amount>=0,"dimension escapes its binder"); return Dimension.bound(cast(uint)(i+amount)); });
	}
	TypeId instantiate(TypeId body,Dimension value){ return map(body,(uint i)=>i?Dimension.bound(i-1):value); }
	bool binds(TypeId t,uint index){ bool found; map(t,(uint i){ found|=i==index; return Dimension.bound(i); }); return found; }
	bool dependent(TypeId t){
		auto v=view(t); if(v.kind==TypeKind.pi) return true;
		if(v.dimension !is null){ bool bound; v.dimension.map((uint i){ bound=true; return Dimension.bound(i); }); if(bound) return true; }
		foreach(f;v.fields) if(dependent(f)) return true; return false;
	}
	TypeId set(TypeId a){ return intern(TypeKind.set,0,[a]); }
}

unittest{
	import std.exception:assertThrown;
	auto p=new TypePool;
	auto r=p.primitive(TypeKind.real_),b=p.primitive(TypeKind.boolean);
	assert(p.tuple([r,r,r])==p.vector(r,3));
	assert(p.tuple([])==p.primitive(TypeKind.unit));
	assert(p.vector(r,0)!=p.vector(b,0));
	assert(p.tuple([r,b])!=p.vector(r,2));
	auto v=p.view(p.tuple([r,b])); v.fields[0]=b;
	assert(p.view(p.tuple([r,b])).fields[0]==r);
	assertThrown(p.array((new TypePool).primitive(TypeKind.real_)));
}
