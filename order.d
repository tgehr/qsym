module qsym.order;
import qsym.ir;
import std.algorithm:sort;
@safe:

int compare(Arena a,Term x,Term y){
	x=a.canonical(x); y=a.canonical(y);
	Term[] left=[x],right=[y];
	while(left.length){
		x=left[$-1]; y=right[$-1]; --left.length; --right.length;
		if(x==y) continue;
		auto l=a.node(x),r=a.node(y);
		if(l.sort!=r.sort) return l.sort<r.sort?-1:1;
		if(l.op!=r.op) return l.op<r.op?-1:1;
		if(a.isNumber(x)){
			auto u=a.number(x),v=a.number(y),c=u.re.opCmp(v.re);
			if(c) return c;
			return u.im.opCmp(v.im);
		}
		if(l.region){
			auto ls=a.operands(x),rs=a.operands(y);
			if(ls.length!=rs.length) return ls.length<rs.length?-1:1;
			sort!((x,y)=>compare(a,x.term,y.term)<0)(ls);
			sort!((x,y)=>compare(a,x.term,y.term)<0)(rs);
			foreach(i,e;ls){
				auto c=compare(a,e.term,rs[i].term); if(c) return c;
				if(e.count!=rs[i].count) return e.count<rs[i].count?-1:1;
			}
			continue;
		}
		if(l.value!=r.value) return l.value<r.value?-1:1;
		if(l.arity==2){ left~=a.at(l.b); right~=a.at(r.b); }
		if(l.arity>=1){ left~=a.at(l.a); right~=a.at(r.a); }
	}
	return 0;
}
