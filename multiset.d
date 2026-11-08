module qsym.multiset;
import qsym.table:Table;
import core.bitop:bsr;
import std.exception:enforce;
@safe:

package struct Count{ uint atom,count; }

// Arena-local persistent counted multisets. Zero is the empty set; all other
// handles are hash-consed compressed tries of depth at most 32.
package final class Multisets{
	struct Node{ uint key,mask,left,right,length; }
	private Node[] nodes=[Node.init];
	private Table!(Node,uint) interned;
	private Table!(ulong,uint) unions;
	size_t length()const{ return nodes.length-1; }
	Node node(uint id)const{ enforce(id<nodes.length,"invalid multiset"); return nodes[id]; }
	private uint intern(Node n){
		auto old=interned.get(n,uint.max); if(old!=uint.max) return old;
		enforce(nodes.length<uint.max,"multiset pool exceeds 32-bit limit");
		auto id=cast(uint)nodes.length; nodes~=n; interned.set(n,id); return id;
	}
	uint single(uint atom,uint count=1){ return count?intern(Node(atom,0,atom,count,1)):0; }
	private uint branch(uint mask,uint left,uint right){
		if(!left) return right; if(!right) return left;
		auto l=node(left),r=node(right);
		return intern(Node(l.key,mask,left,right,l.length+r.length));
	}
	private bool contains(Node x,Node y){ return x.mask>y.mask&&!((x.key^y.key)&~(x.mask|(x.mask-1))); }
	uint merge(uint x,uint y){
		if(!x) return y; if(!y) return x;
		if(x>y){ auto t=x; x=y; y=t; }
		auto key=(cast(ulong)x<<32)|y,old=unions.get(key,uint.max);
		if(old!=uint.max) return old;
		auto l=node(x),r=node(y); uint result;
		if(!l.mask&&!r.mask&&l.key==r.key){
			enforce(r.right<=uint.max-l.right,"operand multiplicity exceeds 32-bit limit");
			result=single(l.key,l.right+r.right);
		}else if(l.mask==r.mask&&l.mask&&!((l.key^r.key)&~(l.mask|(l.mask-1))))
			result=branch(l.mask,merge(l.left,r.left),merge(l.right,r.right));
		else if(contains(l,r)) result=r.key&l.mask?
			branch(l.mask,l.left,merge(l.right,y)):branch(l.mask,merge(l.left,y),l.right);
		else if(contains(r,l)) result=l.key&r.mask?
			branch(r.mask,r.left,merge(x,r.right)):branch(r.mask,merge(x,r.left),r.right);
		else{
			auto mask=1u<<bsr(l.key^r.key);
			result=l.key&mask?branch(mask,y,x):branch(mask,x,y);
		}
		unions.set(key,result); return result;
	}
	uint scale(uint root,uint count){
		if(!count) return 0; if(count==1) return root;
		auto half=scale(root,count/2),result=merge(half,half);
		return count&1?merge(result,root):result;
	}
	Count entry(uint root,uint index)const{
		auto n=node(root); enforce(index<n.length,"operand index out of range");
		while(n.mask){
			auto left=node(n.left);
			if(index<left.length) n=left;
			else{ index-=left.length; n=node(n.right); }
		}
		return Count(n.left,n.right);
	}
	Count[] entries(uint root)const{
		Count[] result; uint[] pending;
		if(root) pending~=root;
		while(pending.length){
			auto n=node(pending[$-1]); --pending.length;
			if(n.mask) pending~=[n.right,n.left]; else result~=Count(n.left,n.right);
		}
		return result;
	}
}
