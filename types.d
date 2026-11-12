module qsym.types;
import std.exception:enforce;
import std.conv:to;
import qsym.table:Table;
@safe:

enum Sort:ubyte{ real_,complex,boolean,density,measure,natural,integer,rational }

enum TypeKind:ubyte{
	unit,boolean,natural,integer,rational,real_,complex,
	uintBits,intBits,vector,tuple,array,function_,set,type_
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
}

/// Fixed-dimension type interning. Symbolic dimensions and Silq's effects are
/// intentionally not accepted until dependent typing is formalized.
final class TypePool{
	private TypeView[] nodes;
	private Table!(string,uint) table;
	private void check(TypeId t)const{
		enforce(t.owner is this&&t.index<nodes.length,"invalid or foreign type handle");
	}
	private TypeId intern(TypeKind k,ulong n,TypeId[] fs){
		string key=to!string(cast(ubyte) k)~":"~to!string(n);
		foreach(f;fs){ check(f); key~=":"~to!string(f.index); }
		auto found=table.get(key,uint.max);
		if(found!=uint.max) return TypeId(this,found);
		enforce(nodes.length<uint.max,"type pool exhausted");
		auto id=cast(uint) nodes.length;
		nodes~=TypeView(k,n,fs.dup);
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
		check(element);
		if(length==0) return primitive(TypeKind.unit);
		return intern(TypeKind.vector,length,[element]);
	}
	TypeId tuple(TypeId[] fields){
		foreach(f;fields) check(f);
		if(!fields.length) return primitive(TypeKind.unit);
		bool uniform=true;
		foreach(f;fields) if(f!=fields[0]) uniform=false;
		if(uniform) return vector(fields[0],fields.length);
		return intern(TypeKind.tuple,0,fields);
	}
	TypeId array(TypeId t){ return intern(TypeKind.array,0,[t]); }
	TypeId function_(TypeId a,TypeId b){ return intern(TypeKind.function_,0,[a,b]); }
	TypeId set(TypeId a){ return intern(TypeKind.set,0,[a]); }
}

unittest{
	import std.exception:assertThrown;
	auto p=new TypePool;
	auto r=p.primitive(TypeKind.real_),b=p.primitive(TypeKind.boolean);
	assert(p.tuple([r,r,r])==p.vector(r,3));
	assert(p.tuple([])==p.vector(r,0));
	assert(p.tuple([r,b])!=p.vector(r,2));
	auto v=p.view(p.tuple([r,b])); v.fields[0]=b;
	assert(p.view(p.tuple([r,b])).fields[0]==r);
	assertThrown(p.array((new TypePool).primitive(TypeKind.real_)));
}
