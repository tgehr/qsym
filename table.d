module qsym.table;
import util.hashtable:HashMap,Storage;
import std.traits:hasIndirections;

/// Value-only facade over tgehr/util. The pinned implementation is @system.
/// These three @trusted operations are the adapter's memory-safety boundary:
/// no entry pointer/reference escapes, keys are immutable strings or plain
/// values, and values are copied. Callers must not share a mutable map across
/// threads. Compact storage is sufficient because references never escape.
struct Table(K,V,alias hash=hashOf){
	static assert(!hasIndirections!K|| is(K==string),"keys must be values or immutable strings");
	static assert(!hasIndirections!V|| is(V==string),"values must be values or immutable strings");
	static assert(__traits(isPOD,K)&&__traits(isPOD,V),"custom lifetime hooks are unsupported");
	static assert(__traits(compiles,()@safe{
		K key;V value;
		auto h=hash(key);auto same=key==key;
		auto copy=value;copy=value;
	}),"key/hash/value operations must themselves be memory-safe");
	private alias Raw=HashMap!(K,V,(a,b)=>a==b,hash,Storage.compact);
	private Raw raw;
	@trusted bool contains(K key){ return key in raw; }
	@trusted V get(K key,V fallback){ return raw.get(key,fallback); }
	@trusted void set(K key,V value){ raw[key]=value; }
}

@safe unittest{
	auto t=Table!(uint,uint)();
	assert(!t.contains(1)); t.set(1,10); assert(t.get(1,0)==10);
	t.set(1,20); assert(t.get(1,0)==20);
	// Full equality must resolve collisions, regardless of hash quality.
	auto c=Table!(uint,uint,(uint _)=>size_t(0))();
	foreach(i;0..1000) c.set(i,i*2);
	foreach(i;0..1000) assert(c.get(i,uint.max)==i*2);
}
