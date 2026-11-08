module qsym.buffer;
import std.exception:enforce;
@safe:

/// Capacity-managed storage with explicit copying and no retained slices.
/// References to elements must not survive append; callers receive copies.
struct Buffer(T){
	private T[] storage;
	private size_t used;
	size_t length()const{ return used; }
	T opIndex(size_t i)const{
		enforce(i<used,"buffer index out of range");
		return storage[i];
	}
	void opIndexAssign(T value,size_t i){ enforce(i<used,"buffer index out of range"); storage[i]=value; }
	void append(T value){
		if(used==storage.length){
			size_t capacity=storage.length?storage.length*2:16;
			enforce(capacity>storage.length,"buffer capacity overflow");
			auto next=new T[capacity];
			next[0..used]=storage[0..used];
			storage=next;
		}
		storage[used++]=value;
	}
}
