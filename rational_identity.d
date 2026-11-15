// Untrusted exact checking of masked rational/geometric identities. Every
// accepted identity is independently replayed against the original Expr in Lean.
module qsym.rational_identity;
import qsym.ir;
import qsym.polynomial:Arithmetic,Polynomial,Powers;
import qsym.budget:Limit;
@safe:

private struct Fraction { Polynomial numerator; uint[uint] denominator; }
private struct PowerAtom { Fraction base; Term exponent; uint id; }
private class Checker {
 Arena a; Arithmetic ring; Term[] conditions; Polynomial[] predicates,equalities,nonzeros,factors;
 PowerAtom[] atoms; uint branch; Fraction[uint] memo;
 this(Arena arena){a=arena;ring=new Arithmetic(a);}
 bool same(Polynomial p,Polynomial q){
  if(p.length!=q.length)return false;
  foreach(k,c;p){auto d=k in q;if(!d||*d!=c)return false;}return true;
 }
 Powers lead(Polynomial p){
  Powers result;bool first=true;
  foreach(k,c;p){
   size_t kd,rd;for(size_t j=1;j<k.length;j+=2)kd+=k[j];for(size_t j=1;j<result.length;j+=2)rd+=result[j];
   if(first||kd>rd||kd==rd&&k>result){result=k;first=false;}
  }return result;
 }
 bool divides(Powers x,Powers y,out Powers quotient){
  uint[] q;size_t i;
  for(size_t j;j<y.length;j+=2){
   if(i<x.length&&x[i]<y[j])return false;
   uint e=y[j+1];if(i<x.length&&x[i]==y[j]){if(x[i+1]>e)return false;e-=x[i+1];i+=2;}
   if(e)q~=[y[j],e];
  }
  if(i!=x.length)return false;quotient=q.idup;return true;
 }
 Polynomial scale(Polynomial p,Number c){return ring.mul(p,ring.constant(c));}
 Polynomial monic(Polynomial p){return p.length?scale(p,ring.budget.calc!"/"(Number(1),p[lead(p)])):p;}
 Polynomial reduce(Polynomial p){
  p=p.dup;bool changed=true;
  while(changed){
   changed=false;
   foreach(eq;equalities){
    auto key=lead(eq);if(!key.length)continue;
    Powers hit,quotient;bool found;
    foreach(k,c;p)if(divides(key,k,quotient)){hit=k;found=true;break;}
    if(!found)continue;
    Polynomial term;ring.put(term,quotient,ring.budget.calc!"/"(-p[hit],eq[key]));
    p=ring.add(p,ring.mul(eq,term));changed=true;break;
   }
  }return p;
 }
 bool nonzero(Polynomial p){
  p=reduce(p);if(!p.length)return false;
  if(p.length==1&&p.keys[0].length==0)return true;
  p=monic(p);foreach(q;nonzeros)if(same(p,monic(reduce(q))))return true;
  return false;
 }
 Fraction constant(Number n){return Fraction(ring.constant(n));}
 Fraction clean(Fraction f){f.numerator=reduce(f.numerator);if(!f.numerator.length)f.denominator=null;return f;}
 Polynomial multiplyFactors(Polynomial p,uint[uint] powers){foreach(k,e;powers)p=ring.mul(p,ring.power(factors[k],e));return p;}
 Fraction add(Fraction x,Fraction y){
  auto den=x.denominator.dup;foreach(k,e;y.denominator)if(den.get(k,0)<e)den[k]=e;
  auto left=x.numerator,right=y.numerator;
  foreach(k,e;den){
   auto l=x.denominator.get(k,0),r=y.denominator.get(k,0);
   if(e>l)left=ring.mul(left,ring.power(factors[k],e-l));
   if(e>r)right=ring.mul(right,ring.power(factors[k],e-r));
  }return clean(Fraction(ring.add(left,right),den));
 }
 Fraction mul(Fraction x,Fraction y){
  auto den=x.denominator.dup;
  foreach(k,e;y.denominator){auto old=den.get(k,0);if(e>uint.max-old)throw new Limit;den[k]=old+e;}
  return clean(Fraction(ring.mul(x.numerator,y.numerator),den));
 }
 Fraction power(Fraction x,uint n){
  uint[uint] den;foreach(k,e;x.denominator){if(n&&e>uint.max/n)throw new Limit;if(n)den[k]=e*n;}
  return clean(Fraction(ring.power(x.numerator,n),den));
 }
 bool inverse(Fraction x,out Fraction result){
  x=clean(x);if(!nonzero(x.numerator))return false;
  auto c=x.numerator[lead(x.numerator)],p=scale(x.numerator,ring.budget.calc!"/"(Number(1),c));
  result=Fraction(multiplyFactors(ring.constant(ring.budget.calc!"/"(Number(1),c)),x.denominator));
  if(p.length==1&&p.keys[0].length==0)return true;
  uint id=uint.max;foreach(i,f;factors)if(same(p,f)){id=cast(uint)i;break;}
  if(id==uint.max){id=cast(uint)factors.length;factors~=p;}result.denominator[id]=1;return true;
 }
 bool collect(Term t){
  foreach(id;a.viewPostorder(t)){
   auto v=a.at(id),n=a.view(v);
   if(n.op!=Op.nonzero&&!(n.op==Op.builtin&&(n.value==Builtin.nonzeroN||n.value==Builtin.nonzeroZ||n.value==Builtin.nonzeroQ)))continue;
   auto condition=a.viewChild(v,0);bool found;foreach(c;conditions)if(c==condition)found=true;
   if(found)continue;
   Fraction p;if(conditions.length>=6||!parse(condition,p)||p.denominator.length)return false;
   conditions~=condition;predicates~=p.numerator;
  }return true;
 }
 bool truth(Term t,out bool value){
  auto n=a.view(t);if(n.op==Op.boolLit){value=n.value!=0;return true;}
  if(n.op==Op.not_){if(!truth(a.viewChild(t,0),value))return false;value=!value;return true;}
  if(n.op==Op.nonzero||n.op==Op.builtin&&(n.value==Builtin.nonzeroN||n.value==Builtin.nonzeroZ||n.value==Builtin.nonzeroQ)){
   auto c=a.viewChild(t,0);foreach(i,v;conditions)if(c==v){value=(branch&(1u<<i))!=0;return true;}return false;
  }
  if(n.op==Op.and_||n.op==Op.or_){
   if(!truth(a.viewChild(t,0),value))return false;
   if(n.op==Op.and_&&!value||n.op==Op.or_&&value)return true;
   return truth(a.viewChild(t,1),value);
  }return false;
 }
 bool naturalPower(Fraction base,Term exponent,out Fraction result,uint depth){
  if(depth>128)throw new Limit;ring.budget.spend();
  // Canonical affine natural exponents keep q^(2*n) and (q^2)^n
  // together, including q=0 and the removable q^2=1 branch.
  Polynomial exponents;if(!ring.parse(exponent,exponents))return false;
  result=constant(Number(1));
  foreach(key,c;exponents){
   if(!c.im.zero||!c.re.small||c.re.integer<0||c.re.integer>uint.max)return false;
   auto scaled=power(base,cast(uint)c.re.integer);
   if(!key.length){result=mul(result,scaled);continue;}
   if(key.length!=2||key[1]!=1)return false;
   auto variable=a.at(key[0]);if(a.sort(variable)!=Sort.natural||a.view(variable).op!=Op.variable)return false;
   if(!scaled.denominator.length&&same(scaled.numerator,ring.constant(Number(1))))continue;
   uint id=uint.max;
   foreach(atom;atoms)if(atom.exponent==variable&&same(atom.base.numerator,scaled.numerator)&&atom.base.denominator==scaled.denominator){id=atom.id;break;}
   if(id==uint.max){id=uint.max-1-cast(uint)atoms.length;if(id<a.length)throw new Limit;atoms~=PowerAtom(scaled,variable,id);}
   Fraction factor;ring.put(factor.numerator,[id,1].idup,Number(1));result=mul(result,factor);
  }
  return true;
 }
 // Treat a strictly total scalar function as an opaque field element.
 // Its internal identities are not assumed; partial arguments are rejected.
 bool total(Term t,uint depth=0){
  ring.budget.spend();if(depth>128)throw new Limit;
  auto n=a.view(t);if(a.isNumber(t)||n.op==Op.variable)return true;
  if(n.op!=Op.add&&n.op!=Op.mul&&n.op!=Op.pow&&n.op!=Op.conj&&n.op!=Op.abs&&
     !(n.op==Op.builtin&&builtinInfo(cast(Builtin)n.value).total))return false;
  foreach(i;0..n.arity)if(!total(a.viewChild(t,i),depth+1))return false;
  return true;
 }
 bool parse(Term t,out Fraction result,uint depth=0,bool invert=false){
  ring.budget.spend();if(depth>128)throw new Limit;
  if(!invert)if(auto found=t.id in memo){result=*found;return true;}
  auto n=a.view(t);
  if(n.op==Op.mask){
   bool v;if(!truth(a.viewChild(t,0),v))return false;
   if(!v){result=constant(Number(0));return !invert;}
   return parse(a.viewChild(t,1),result,depth+1,invert);
  }
  if(n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castRC)return parse(a.viewChild(t,0),result,depth+1,invert);
  if(n.op==Op.inv||n.op==Op.builtin&&n.value==Builtin.invQ){
   Fraction x;if(!parse(a.viewChild(t,0),x,depth+1,true))return false;
   if(invert)return inverse(x,result);result=x;return true;
  }
  bool sum=n.op==Op.add||n.op==Op.builtin&&(n.value==Builtin.addN||n.value==Builtin.addZ||n.value==Builtin.addQ);
  bool product=n.op==Op.mul||n.op==Op.builtin&&(n.value==Builtin.mulN||n.value==Builtin.mulZ||n.value==Builtin.mulQ);
  if(sum||product){
   Fraction x,y;if(!parse(a.viewChild(t,0),x,depth+1,invert&&product)||!parse(a.viewChild(t,1),y,depth+1,invert&&product))return false;
   result=sum?add(x,y):mul(x,y);if(invert&&sum)return inverse(result,result);
  }else if(n.op==Op.pow){
   Fraction base;if(!parse(a.viewChild(t,0),base,depth+1,invert))return false;result=power(base,cast(uint)n.value);
  }else if(n.op==Op.builtin&&n.value>=Builtin.powNN&&n.value<=Builtin.powCN){
   Fraction base;if(!parse(a.viewChild(t,0),base,depth+1,invert))return false;
   if(!naturalPower(base,a.viewChild(t,1),result,depth+1))return false;
  }else{
   Polynomial p;if(!ring.parse(t,p)){if(!total(t))return false;ring.put(p,[t.id,1].idup,Number(1));}result=clean(Fraction(p));if(invert)return inverse(result,result);
  }
  if(!invert)memo[t.id]=result;return true;
 }
 bool check(Term t){
  if(!collect(t))return false;
  foreach(bits;0..1u<<conditions.length){
   branch=bits;equalities=null;nonzeros=null;factors=null;atoms=null;memo=null;
   foreach(i,p;predicates)if(bits&(1u<<i))nonzeros~=p;else if(p.length)equalities~=p;
   bool impossible;foreach(p;nonzeros)if(!reduce(p).length)impossible=true;
   foreach(p;equalities)if(p.length==1&&p.keys[0].length==0)impossible=true;
   if(impossible)continue;
   Fraction value;if(!parse(t,value)||value.numerator.length)return false;
  }return true;
 }
}

bool rationalIdentityZero(Arena a,Term input,out Term[] conditions){
 try{auto checker=new Checker(a);if(!checker.check(input))return false;conditions=checker.conditions;return true;}
 catch(Limit e){return false;}
}
