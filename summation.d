// Untrusted antidifference candidates. binding.d checks the zero and successor
// identities, including their domains, before using any candidate.
// Candidate search is bounded (degree 32, 32 geometric components); failure
// leaves the sum symbolic. Infinite results additionally need a checked
// absolutely summable polynomial-geometric tail.
module qsym.summation;
import qsym.ir;
import qsym.number;
import qsym.simplify;
@safe:
struct SumPrimitive { Term coefficient,ratio; uint degree; }
Term sumAntidifference(Arena a,Term input,Term index){ SumPrimitive[] tail; return sumAntidifference(a,input,index,tail); }
Term sumAntidifference(Arena a,Term input,Term index,ref SumPrimitive[] tail){
 auto sort=a.sort(input); if(sort!=Sort.rational&&sort!=Sort.real_&&sort!=Sort.complex) return Term.init;
 auto zero=a.number(Number(0),sort),one=a.number(Number(1),sort);
 Term clean(Term t){ auto r=simplify(a,t); return r.exhausted?t:a.isNumber(r.output)?a.number(a.number(r.output),sort):a.castTo(r.output,sort); }
 bool dependent(Term t){ foreach(id;a.viewPostorder(t)) if(id==index.id) return true; return false; }
 struct Part { Term ratio; Term[] p; }
 Part[] plus(Part[] x,Part[] y){
  foreach(q;y){ bool found; foreach(ref p;x) if(p.ratio==q.ratio){
   auto old=p.p.length; if(p.p.length<q.p.length){ p.p.length=q.p.length; p.p[old..$]=zero; }
   foreach(i,c;q.p) p.p[i]=clean(a.add(p.p[i],c)); found=true; break;
  } if(!found) x~=q; } return x;
 }
 Part[] times(Part[] x,Part[] y){
  Part[] result; if(x.length*y.length>32) return null;
  foreach(p;x) foreach(q;y){
   if(p.p.length+q.p.length>34) return null;
   auto cs=new Term[p.p.length+q.p.length-1]; cs[]=zero;
   foreach(i,c;p.p) foreach(j,d;q.p) cs[i+j]=clean(a.add(cs[i+j],a.mul(c,d)));
   result=plus(result,[Part(clean(a.mul(p.ratio,q.ratio)),cs)]);
  } return result;
 }
 Part[] parse(Term t,uint depth=0){
  if(depth>64) return null;
  if(!dependent(t)) return [Part(one,[a.castTo(t,sort)])];
  if(t==index) return [Part(one,[zero,one])];
  auto n=a.view(t);
  if(n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castRC) return parse(a.viewChild(t,0),depth+1);
  bool add=n.op==Op.add||n.op==Op.builtin&&(n.value==Builtin.addN||n.value==Builtin.addZ||n.value==Builtin.addQ);
  bool mul=n.op==Op.mul||n.op==Op.builtin&&(n.value==Builtin.mulN||n.value==Builtin.mulZ||n.value==Builtin.mulQ);
  if(add||mul){
   auto x=parse(a.viewChild(t,0),depth+1),y=parse(a.viewChild(t,1),depth+1);
   if(!x.length||!y.length) return null;
   return add?plus(x,y):times(x,y);
  }
  if(n.op==Op.pow){
   if(n.value>32) return null;
   auto base=parse(a.viewChild(t,0),depth+1); if(!base.length) return null;
   Part[] result=[Part(one,[one])]; foreach(i;0..n.value){ result=times(result,base); if(!result.length) break; } return result;
  }
  if(n.op==Op.builtin&&n.value>=Builtin.powNN&&n.value<=Builtin.powCN){
   auto base=a.viewChild(t,0),exponent=a.viewChild(t,1);
   if(exponent==index&&!dependent(base)) return [Part(clean(a.castTo(base,sort)),[one])];
   if(a.isNumber(exponent)&&a.number(exponent).re.small&&a.number(exponent).re.integer>=0&&a.number(exponent).re.integer<=32){
    auto parts=parse(base,depth+1); if(!parts.length) return null;
    Part[] result=[Part(one,[one])]; foreach(i;0..a.number(exponent).re.integer){ result=times(result,parts); if(!result.length) break; } return result;
   }
  }
  return null;
 }
 auto parts=parse(input); if(!parts.length) return Term.init;
 Term rat(Rational q){ return a.number(Number(q),sort); }
 Rational choose(uint n,uint k){ auto c=Rational(1); foreach(i;0..k) c=c*Rational(n-i)/Rational(i+1); return c; }
 auto x=a.castTo(index,sort),answer=zero;
 foreach(part;parts){
  auto cs=part.p.dup;
  while(cs.length>1&&a.isNumber(cs[$-1])&&a.number(cs[$-1]).zero) --cs.length;
  Term[] primitive;
  if(part.ratio==one){
   primitive=new Term[cs.length+1]; primitive[]=zero;
   foreach_reverse(k;0..cs.length){
    auto c=clean(a.mul(cs[k],rat(Rational(1)/Rational(k+1)))); primitive[k+1]=c;
    foreach(j;0..k) cs[j]=clean(a.sub(cs[j],a.mul(c,rat(choose(cast(uint)k+1,cast(uint)j)))));
   }
  }else{
   // A symbolic ratio is handled only when the domain/equality checker can
   // establish ratio != 1. No unchecked division or convergence is assumed.
   primitive=new Term[cs.length]; primitive[]=zero;
   auto inverse=a.inv(clean(a.sub(part.ratio,one)));
   foreach_reverse(k;0..cs.length){
    auto c=cs[k]; foreach(j;k+1..cs.length) c=clean(a.sub(c,a.mul(part.ratio,a.mul(primitive[j],rat(choose(cast(uint)j,cast(uint)k))))));
    primitive[k]=clean(a.mul(c,inverse));
   }
  }
  foreach(k,c;primitive) if(!a.isNumber(c)||!a.number(c).zero) tail~=SumPrimitive(c,part.ratio,cast(uint)k);
  auto poly=zero;
  foreach_reverse(c;primitive) poly=clean(a.add(a.mul(poly,x),c));
  if(part.ratio!=one){ auto power=a.call(sort==Sort.rational?Builtin.powQN:sort==Sort.real_?Builtin.powRN:Builtin.powCN,[part.ratio,index]); poly=clean(a.sub(a.mul(poly,power),primitive[0])); }
  if(!a.isNumber(part.ratio)){
   // The removable ratio=1 case must be masked before any division is used.
   auto coefficients=part.p.dup;
   auto integral=new Term[coefficients.length+1]; integral[]=zero;
   foreach_reverse(k;0..coefficients.length){
    auto c=clean(a.mul(coefficients[k],rat(Rational(1)/Rational(k+1)))); integral[k+1]=c;
    foreach(j;0..k) coefficients[j]=clean(a.sub(coefficients[j],a.mul(c,rat(choose(cast(uint)k+1,cast(uint)j)))));
   }
   auto atOne=zero; foreach_reverse(c;integral) atOne=clean(a.add(a.mul(atOne,x),c));
   auto equal=a.equal(part.ratio,one);
   poly=a.add(a.mask(equal,atOne),a.mask(a.not_(equal),poly));
  }
  answer=clean(a.add(answer,poly));
 }
 return answer;
}
