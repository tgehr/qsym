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

// Diagnostics for the bounded, untrusted search (not proof evidence).
struct AbelSearchStats { uint calls, parts, cycles, hits; bool exhausted; }

Term sumAbelAntidifference(Arena a,Term input,Term index){
 AbelSearchStats stats; return sumAbelAntidifference(a,input,index,stats);
}

// Discrete integration by parts:
//   Δ(P G) = P ΔG + (ΔP) G(n+1).
// Memoized unknown primitives close affine cycles such as
//   S(n) = n*n - S(n) - n.
// The table belongs to this invocation, so neither failures nor placeholders
// escape into another arena or another summation. As with the coefficient
// solver below, binding.d must check the ORIGINAL summand and its domain.
Term sumAbelAntidifference(Arena a,Term input,Term index,ref AbelSearchStats stats){
 stats=AbelSearchStats.init;
 auto sort=a.sort(input);
 if(sort!=Sort.rational&&sort!=Sort.real_&&sort!=Sort.complex||a.sort(index)!=Sort.natural) return Term.init;
 if(sort==Sort.rational){
  // Perform polynomial expansion in the scalar field representation, then
  // retain a rational candidate only if exact embedding contraction finds it.
  auto result=sumAbelAntidifference(a,a.castTo(input,Sort.real_),index,stats);
  if(result==Term.init) return result;
  auto options=Options.init; options.maxRewrites=256; options.maxAlgebraWork=8192;
  auto narrowed=simplify(a,result,options);
  if(narrowed.exhausted){ stats.exhausted=true; return Term.init; }
  if(a.sort(narrowed.output)>Sort.rational) return Term.init;
  return a.castTo(narrowed.output,Sort.rational);
 }
 auto zero=a.number(Number(0),sort),one=a.number(Number(1),sort),x=a.castTo(index,sort);
 auto options=Options.init; options.expandPowers=true; options.expandScalarEmbeddings=true;
 options.maxRewrites=256; options.maxAlgebraWork=8192;
 uint fresh; foreach(id;0..a.length){ auto n=a.node(a.at(cast(uint)id));
  if(n.op==Op.variable){ if(n.value>=uint.max-512) return Term.init; if(n.value>=fresh) fresh=cast(uint)n.value+1; }
 }
 struct Entry { Term input,token,result; bool active; }
 Entry[] memo;
 bool failed;
 bool contains(Term t,Term v){ foreach(id;a.viewPostorder(t)) if(id==v.id) return true; return false; }
 Term replace(Term t,Term v,Term value){
  Term[uint] seen;
  Term visit(Term t){
   if(t==v) return value;
   if(auto found=t.id in seen) return *found;
   auto n=a.view(t); Term[] args; foreach(i;0..n.arity) args~=visit(a.viewChild(t,i));
   return seen[t.id]=args.length?a.viewRebuild(t,args,true):t;
  }
  return visit(t);
 }
 Term clean(Term t){
  if(failed||t==Term.init) return Term.init;
  if(a.viewPostorder(t).length>4096){ failed=true; stats.exhausted=true; return Term.init; }
  auto r=simplify(a,t,options);
  if(r.exhausted){ failed=true; stats.exhausted=true; return Term.init; }
  return a.isNumber(r.output)?a.number(a.number(r.output),sort):a.castTo(r.output,sort);
 }
 bool operation(Term t,Op op,Builtin q){ auto n=a.view(t); return n.op==op||n.op==Op.builtin&&n.value==q; }
 bool plus(Term t){ return operation(t,Op.add,Builtin.addQ); }
 bool times(Term t){ return operation(t,Op.mul,Builtin.mulQ); }
 bool unknown(Term t){ foreach(e;memo) if(contains(t,e.token)) return true; return false; }
 Term shift(Term t){ return replace(t,index,a.add(index,a.natural_(1),true)); }
 uint polynomial(Term t){
  if(t==x) return 1;
  auto n=a.view(t);
  if(n.op==Op.pow&&a.viewChild(t,0)==x&&n.value>0&&n.value<=32) return cast(uint)n.value;
  if(n.op==Op.builtin&&n.value>=Builtin.powQN&&n.value<=Builtin.powCN&&a.viewChild(t,0)==x){
   auto e=a.viewChild(t,1);
   if(a.isNumber(e)&&a.number(e).re.small&&a.number(e).re.integer>0&&a.number(e).re.integer<=32) return cast(uint)a.number(e).re.integer;
  }
  return 0;
 }
 // Structural affine extraction rejects nonlinear or shifted unknowns; it
 // does not infer linearity merely by evaluating a token at zero and one.
 bool affine(Term t,Term token,out Term coefficient,out Term constant){
  if(t==token){ coefficient=one; constant=zero; return true; }
  if(!contains(t,token)){ coefficient=zero; constant=t; return true; }
  if(!plus(t)&&!times(t)) return false;
  Term c,d,e,f;
  auto l=a.viewChild(t,0),r=a.viewChild(t,1);
  if(!affine(l,token,c,d)||!affine(r,token,e,f)) return false;
  if(plus(t)){ coefficient=clean(a.add(c,e)); constant=clean(a.add(d,f)); }
  else{
   if(contains(l,token)&&contains(r,token)) return false;
   coefficient=clean(a.add(a.mul(c,f),a.mul(d,e))); constant=clean(a.mul(d,f));
  }
  return !failed;
 }
 Term integrate(Term raw,uint depth){
  if(failed) return Term.init;
  if(++stats.calls>384||depth>64){ failed=true; stats.exhausted=true; return Term.init; }
  auto t=clean(raw); if(failed) return Term.init;
  if(!contains(t,index)) return clean(a.mul(t,x));
  auto view=a.view(t);
  if(view.op==Op.builtin&&view.value==Builtin.castRC&&!unknown(t)){
   // The scalar simplifier may keep a real-valued polynomial inside its
   // complex embedding. Integrate that real expression without losing the
   // recursive search, then embed the candidate back into the target field.
   AbelSearchStats inner;
   auto result=sumAbelAntidifference(a,a.viewChild(t,0),index,inner);
   stats.calls+=inner.calls;stats.parts+=inner.parts;stats.cycles+=inner.cycles;stats.hits+=inner.hits;
   if(inner.exhausted||stats.calls>384){ failed=true; stats.exhausted=true; return Term.init; }
   return result==Term.init?result:a.castTo(result,sort);
  }
  if(plus(t)){
   auto l=integrate(a.viewChild(t,0),depth+1); if(l==Term.init) return Term.init;
   auto r=integrate(a.viewChild(t,1),depth+1); return r==Term.init?r:clean(a.add(l,r));
  }
  Term[] factors;
  void flatten(Term f){ if(times(f)){ flatten(a.viewChild(f,0)); flatten(a.viewChild(f,1)); }else factors~=f; }
  flatten(t);
  auto coefficient=one,rest=one; bool extracted;
  foreach(f;factors){ if(!contains(f,index)){ coefficient=a.mul(coefficient,f); extracted=true; }else rest=a.mul(rest,f); }
  if(extracted){
   auto g=integrate(rest,depth+1); return g==Term.init?g:clean(a.mul(coefficient,g));
  }
  foreach(e;memo) if(e.input==t){ ++stats.hits; return e.active?e.token:e.result; }
  size_t choice=factors.length;
  foreach(i,f;factors) if(polynomial(f)){ choice=i; break; }
  if(choice==factors.length){
   auto node=a.view(t);
   if(node.op==Op.builtin&&(node.value==Builtin.expR||node.value==Builtin.expC||node.value==Builtin.powerR||node.value==Builtin.powerC)){
    bool power=node.value==Builtin.powerR||node.value==Builtin.powerC;
    auto exponent=a.viewChild(t,power?1:0);
    if(power&&contains(a.viewChild(t,0),index)) return Term.init;
    auto delta=clean(a.sub(shift(exponent),exponent)); if(failed) return Term.init;
    if(!contains(delta,index)){
     auto ratio=clean(power?a.call(cast(Builtin)node.value,[a.viewChild(t,0),delta]):a.call(cast(Builtin)node.value,[delta]));
     if(failed) return Term.init;
     if(ratio==one) return clean(a.mul(t,x));
     return clean(a.div(t,a.sub(ratio,one)));
    }
   }
   // Base primitives are deliberately independent of Abel's recurrence.
   // The existing polynomial-geometric solver also handles ratio=0 and 1.
   return sumAntidifference(a,t,index);
  }
  auto slot=memo.length,token=a.variable(sort,fresh++);
  memo~=Entry(t,token,Term.init,true); ++stats.parts;
  auto p=factors[choice]; rest=one;
  foreach(i,f;factors) if(i!=choice) rest=a.mul(rest,f);
  auto g=integrate(rest,depth+1);
  // A scalar token stands for a primitive at n, not at n+1. Never shift an
  // unresolved primitive as though it were an index-independent constant.
  if(g==Term.init||unknown(g)){ failed=true; return Term.init; }
  auto difference=clean(a.sub(shift(p),p)); if(failed) return Term.init;
  auto residual=clean(a.mul(difference,shift(g))); if(failed) return Term.init;
  auto h=integrate(residual,depth+1); if(h==Term.init){ failed=true; return Term.init; }
  auto result=clean(a.sub(a.mul(p,g),h)); if(failed) return Term.init;
  if(contains(result,token)){
   Term c,d;
   if(!affine(result,token,c,d)){ failed=true; return Term.init; }
   auto divisor=clean(a.sub(one,c)); if(failed) return Term.init;
   // Do not turn a singular or index-dependent recurrence into a formula.
   if(contains(divisor,index)||unknown(divisor)||a.isNumber(divisor)&&a.number(divisor).zero){ failed=true; return Term.init; }
   result=clean(a.div(d,divisor)); if(failed||contains(result,token)) return Term.init;
   ++stats.cycles;
  }
  memo[slot].active=false; memo[slot].result=result;
  foreach(ref e;memo) if(e.result!=Term.init&&contains(e.result,token)){
   e.result=clean(replace(e.result,token,result)); if(failed) return Term.init;
  }
  return result;
 }
 auto result=integrate(input,0);
 if(failed||result==Term.init||unknown(result)) return Term.init;
 return clean(a.sub(result,replace(result,index,a.natural_(0))));
}

Term sumAntidifference(Arena a,Term input,Term index){ SumPrimitive[] tail; return sumAntidifference(a,input,index,tail); }
Term sumAntidifference(Arena a,Term input,Term index,ref SumPrimitive[] tail){
 auto sort=a.sort(input); if(sort!=Sort.rational&&sort!=Sort.real_&&sort!=Sort.complex) return Term.init;
 auto zero=a.number(Number(0),sort),one=a.number(Number(1),sort);
 auto search=Options.init; search.maxRewrites=256; search.maxAlgebraWork=8192;
 Term clean(Term t){ auto r=simplify(a,t,search); return r.exhausted?t:a.isNumber(r.output)?a.number(a.number(r.output),sort):a.castTo(r.output,sort); }
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
   auto e=a.view(exponent);
   if(!dependent(base)&&e.op==Op.builtin&&e.value==Builtin.addN){
    auto left=a.viewChild(exponent,0),right=a.viewChild(exponent,1);
    if(right==index){auto tmp=left;left=right;right=tmp;}
    if(left==index&&!dependent(right)){
     auto ratio=clean(a.castTo(base,sort)),power=sort==Sort.rational?Builtin.powQN:sort==Sort.real_?Builtin.powRN:Builtin.powCN;
     return [Part(ratio,[clean(a.call(power,[ratio,right]))])];
    }
   }
   if(!dependent(base)){
    auto ex=parse(exponent,depth+1);
    if(ex.length==1&&ex[0].ratio==one&&ex[0].p.length<=2){
     auto b=ex[0].p[0],c=ex[0].p.length==2?ex[0].p[1]:zero;
     if(a.isNumber(b)&&a.isNumber(c)&&a.number(b).re.integral&&a.number(c).re.integral&&a.number(b).re>=Rational(0)&&a.number(c).re>=Rational(0)){
      auto power=sort==Sort.rational?Builtin.powQN:sort==Sort.real_?Builtin.powRN:Builtin.powCN;
      auto q=a.castTo(base,sort);
      return [Part(clean(a.call(power,[q,a.number(a.number(c),Sort.natural)])),[clean(a.call(power,[q,a.number(a.number(b),Sort.natural)]))])];
     }
    }
   }
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
