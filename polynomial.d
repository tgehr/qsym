// Untrusted exact polynomial arithmetic. Accepted identities are replayed by
// explicit kernel-checked arithmetic certificates against the typed expression.
module qsym.polynomial;
import qsym.ir;
import qsym.budget:Budget,Limit;
import std.algorithm:sort;
@safe:

package alias Powers=immutable(uint)[]; // sorted (scalar variable term id, exponent) pairs
package alias Polynomial=Number[Powers];
package class Arithmetic {
 Arena arena;
 Budget budget;
 this(Arena a){arena=a;budget=new Budget(2_000_000,4096,512);}
 void put(ref Polynomial p,Powers powers,Number c){
  budget.spend();if(c.zero)return;
  c=budget.calc!"+"(p.get(powers,Number(0)),c);
  if(c.zero)p.remove(powers);else p[powers]=c;
  if(p.length>budget.maxTerms)throw new Limit;
 }
 Polynomial constant(Number n){Polynomial p;put(p,null,n);return p;}
 Polynomial add(Polynomial p,Polynomial q){
  auto r=p.dup;foreach(k,v;q)put(r,k,v);return r;
 }
 Polynomial mul(Polynomial p,Polynomial q){
  Polynomial r;
  foreach(k,c;p)foreach(l,d;q){
   budget.spend(k.length+l.length+1);uint[] powers;size_t i,j;
   while(i<k.length||j<l.length){
    if(j==l.length||i<k.length&&k[i]<l[j]){powers~=k[i..i+2];i+=2;}
    else if(i==k.length||l[j]<k[i]){powers~=l[j..j+2];j+=2;}
    else{if(k[i+1]>uint.max-l[j+1])throw new Limit;powers~=[k[i],k[i+1]+l[j+1]];i+=2;j+=2;}
   }
   put(r,powers.idup,budget.calc!"*"(c,d));
  }
  return r;
 }
 Polynomial power(Polynomial p,uint n){
  if(n>budget.remaining)throw new Limit;
  // Successor checks repeatedly contain (n+1)^k. Expand a binomial in
  // linear work instead of multiplying growing coefficient tables.
  Powers empty;
  if(p.length==2&&empty in p){
   auto b=p[empty];Powers key;Number a;
   foreach(k,c;p)if(k.length){key=k;a=c;}
   Number coefficient=Number(1),base=b;
   for(auto k=n;k;k>>=1){if(k&1)coefficient=budget.calc!"*"(coefficient,base);if(k>1)base=budget.calc!"*"(base,base);}
   Polynomial result;
   foreach(k;0..cast(ulong)n+1){
    uint[] exponents;
    if(k)for(size_t j;j<key.length;j+=2){
     if(key[j+1]>uint.max/k)throw new Limit;exponents~=[key[j],cast(uint)(key[j+1]*k)];
    }
    put(result,exponents.idup,coefficient);
    if(k<n)coefficient=budget.calc!"/"(budget.calc!"*"(coefficient,budget.calc!"*"(a,Number(n-cast(uint)k))),budget.calc!"*"(b,Number(cast(long)k+1)));
   }
   return result;
  }
  auto r=constant(Number(1));
  for(;n;n>>=1){if(n&1)r=mul(r,p);if(n>1)p=mul(p,p);}
  return r;
 }
 bool parse(Term t,out Polynomial p,uint depth=0){
  budget.spend();if(depth>128)throw new Limit;
  if(arena.isNumber(t)){p=constant(arena.number(t));return true;}
  auto n=arena.view(t);
  if(n.op==Op.variable&&numeric(n.sort)){put(p,[t.id,1].idup,Number(1));return true;}
  if(n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castRC)return parse(arena.viewChild(t,0),p,depth+1);
  bool add_=n.op==Op.add||n.op==Op.builtin&&(n.value==Builtin.addN||n.value==Builtin.addZ||n.value==Builtin.addQ);
  bool mul_=n.op==Op.mul||n.op==Op.builtin&&(n.value==Builtin.mulN||n.value==Builtin.mulZ||n.value==Builtin.mulQ);
  bool inv=n.op==Op.inv||n.op==Op.builtin&&n.value==Builtin.invQ;
  bool pow=n.op==Op.pow||n.op==Op.builtin&&n.value>=Builtin.powNN&&n.value<=Builtin.powCN;
  if(!add_&&!mul_&&!inv&&!pow)return false;
  Polynomial left,right;
  // Even a zero multiplier or exponent must not erase a partial operand.
  if(!parse(arena.viewChild(t,0),left,depth+1))return false;
  if(add_||mul_){
   if(!parse(arena.viewChild(t,1),right,depth+1))return false;
   p=add_?add(left,right):mul(left,right);return true;
  }
  if(inv){
   if(left.length!=1)return false;
   foreach(k,c;left){if(k.length||c.zero)return false;p=constant(budget.calc!"/"(Number(1),c));}
   return true;
  }
  uint exponent;
  if(n.op==Op.pow)exponent=cast(uint)n.value;
  else{
   auto e=arena.viewChild(t,1);
   if(!arena.isNumber(e))return false;
   auto q=arena.number(e).re;
   if(!q.small||q.integer<0||q.integer>uint.max)return false;
   exponent=cast(uint)q.integer;
  }
  p=power(left,exponent);return true;
 }
}

// This accepts only total ring expressions and inverses of nonzero numeric
// constants. In particular, cancellation cannot hide a pole or natural sub.
bool polynomialZero(Arena a,Term input){
 try{auto arithmetic=new Arithmetic(a);Polynomial p;return arithmetic.parse(input,p)&&!p.length;}
 catch(Limit e){return false;}
}

private bool quadraticCoefficients(Arithmetic arithmetic,Term expression,Term x,out Number[3] c){
 Polynomial p;
 if(!arithmetic.parse(expression,p))return false;
 foreach(powers,v;p){
  if(!v.im.zero||powers.length&&(powers.length!=2||powers[0]!=x.id||powers[1]>2))return false;
  c[powers.length?powers[1]:0]=v;
 }
 return !c[2].zero;
}

// The inverse branches of a nonconstant quadratic are h ± sqrt(t*y+u).
// Compute the three candidates here; the caller certifies t*f(x)+u=(x-h)^2.
bool rationalQuadraticInverse(Arena a,Term expression,Term x,out Rational centre,out Rational scale,out Rational offset){
 try{
  auto ar=new Arithmetic(a); Number[3] c;
  if(!quadraticCoefficients(ar,expression,x,c))return false;
  auto t=ar.budget.calc!"/"(Number(1),c[2]);
  auto h=ar.budget.calc!"/"(c[1],ar.budget.calc!"*"(Number(-2),c[2]));
  auto u=ar.budget.calc!"-"(ar.budget.calc!"*"(h,h),ar.budget.calc!"*"(t,c[0]));
  centre=h.re;scale=t.re;offset=u.re;return true;
 }catch(Limit e){return false;}
}

// Recover the rational affine square from its polynomial, regardless of how
// its products were expanded or ordered. The caller certifies the identity.
bool rationalAffineSquare(Arena a,Term expression,Term x,out Rational slope,out Rational offset){
 import qsym.elementary:Elementary;
 try{
  auto arithmetic=new Arithmetic(a);Number[3] c;
  if(!quadraticCoefficients(arithmetic,expression,x,c))return false;
  if(c[2].re<=Rational(0)||!(new Elementary(a,arithmetic.budget)).root(c[2].re,2,slope))return false;
  auto b=arithmetic.budget.calc!"/"(c[1],arithmetic.budget.calc!"*"(Number(2),Number(slope)));
  if(arithmetic.budget.calc!"*"(b,b)!=c[0])return false;
  offset=b.re;return true;
 }catch(Limit e){return false;}
}

Term polynomialAntidifference(Arena a,Term input,Term index){
 auto type=a.sort(input);
 if(type!=Sort.rational&&type!=Sort.real_&&type!=Sort.complex||a.sort(index)!=Sort.natural)return Term.init;
 try{
  auto arithmetic=new Arithmetic(a);Polynomial p;
  if(!arithmetic.parse(input,p))return Term.init;
  Number[][Powers] groups;uint degree;
  foreach(key,c;p){
   uint k;uint[] rest;
   for(size_t j;j<key.length;j+=2){if(key[j]==index.id)k=key[j+1];else rest~=key[j..j+2];}
   if(k>arithmetic.budget.remaining)throw new Limit;
   arithmetic.budget.spend(k+1);
   auto r=rest.idup,cs=groups.get(r,null);
   if(cs.length<=k)cs.length=k+1;
   cs[k]=arithmetic.budget.calc!"+"(cs[k],c);groups[r]=cs;
   if(k>degree)degree=k;
  }
  // Preserve the established compact forms and cheaper proofs of small sums.
  if(degree<4)return Term.init;
  // Keep exact rational polynomials in their smallest scalar field.
  // Widening every monomial separately makes the general normalizer prove
  // the same embedding contractions again after applying the primitive.
  auto representation=Sort.rational;
  foreach(key,cs;groups){
   foreach(c;cs)if(!c.im.zero)representation=Sort.complex;
   for(size_t j;j<key.length;j+=2)if(rank(a.sort(a.at(key[j])))>rank(representation))representation=a.sort(a.at(key[j]));
  }
  auto answer=a.number(Number(0),representation),x=a.castTo(index,representation);
  auto keys=groups.keys;
  sort!((x,y)=>x<y)(keys);
  foreach(key;keys){
   auto cs=groups[key].dup,primitive=new Number[cs.length+1];
   foreach_reverse(k;0..cs.length){
    auto c=arithmetic.budget.calc!"/"(cs[k],Number(cast(long)k+1));primitive[k+1]=c;
    if(c.zero)continue;
    auto choose=Number(1);
    foreach(j;0..k){
     cs[j]=arithmetic.budget.calc!"-"(cs[j],arithmetic.budget.calc!"*"(c,choose));
     choose=arithmetic.budget.calc!"/"(arithmetic.budget.calc!"*"(choose,Number(cast(long)k+1-cast(long)j)),Number(cast(long)j+1));
    }
   }
   auto factor=a.number(Number(1),representation);
   for(size_t j;j<key.length;j+=2)factor=a.mul(factor,a.pow(a.castTo(a.at(key[j]),representation),key[j+1]),true);
   foreach(k,c;primitive)if(!c.zero){
    auto term=a.mul(a.number(c,representation),a.pow(x,cast(uint)k),true);
    if(key.length)term=a.mul(factor,term,true);
    answer=a.add(answer,term,true);
   }
  }
  return a.castTo(answer,type);
 }catch(Limit e){return Term.init;}
}
