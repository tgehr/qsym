module qsym.budget;
import qsym.ir:Number;
@safe:

package class Limit:Exception{ this(){ super("simplification budget exhausted"); } }
package final class Budget{
	size_t remaining,maxTerms,maxWords;
	bool exhausted;
	this(size_t work,size_t terms,size_t words){ remaining=work; maxTerms=terms; maxWords=words; }
	void spend(size_t n=1){ if(n>remaining) throw new Limit; remaining-=n; }
	Number calc(string op)(Number x,Number y){
		if(x.words>maxWords||y.words>maxWords) throw new Limit;
		spend(x.words+y.words);
		auto r=x.opBinary!op(y);
		if(r.words>maxWords) throw new Limit;
		return r;
	}
}
