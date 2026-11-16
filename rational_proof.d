// Native certificates for strict rational identities. All equations and pole
// obligations are checked by the kernel using compiled algebra lemmas.
module qsym.rational_proof;
import qsym.ir;
import qsym.polynomial:Polynomial,Powers;
import qsym.rational_identity:Checker,Fraction;
import qsym.algebra_proof:AlgebraExporter;
import std.algorithm:sort;
import std.array:replace;
import std.conv:to;
import std.exception:enforce;
@safe:

private struct Form { Polynomial numerator,denominator; string proof; }
private struct Reduction { Polynomial value; string proof; }
private struct NaturalValue { string value,proof; }
private class GuardProofs {
 string valuation;
 string[uint] proofs;
 Polynomial[uint] values;
}
private class Naturals {
 AlgebraExporter output;NaturalValue[uint] values;
 this(AlgebraExporter out_){output=out_;}
 NaturalValue get(Term t){
  if(auto old=t.id in values)return *old;
  auto a=output.a,n=a.view(t);enforce(n.sort==Sort.natural);string value,h;
  if(a.isNumber(t)){value=to!string(a.number(t).re.numerator);h="Numeric.calculate_sound ρ n"~to!string(t.id)~" "~value~" rfl";}
  else if(n.op==Op.variable){value="ρ.natural "~to!string(n.value);h="rfl";}
  else{
   auto x=get(a.viewChild(t,0));
   if(n.op==Op.pow){value=x.value~" ^ "~to!string(n.value);h="congrArg (fun a : Option ℕ => a.map (fun x => x ^ "~to!string(n.value)~")) "~x.proof;}
   else{
    enforce(n.op==Op.builtin&&(n.value==Builtin.addN||n.value==Builtin.mulN||n.value==Builtin.powNN),"unsupported natural exponent");
    auto y=get(a.viewChild(t,1)),op="Functions."~builtinInfo(cast(Builtin)n.value).code;
    value=op~".value "~x.value~" "~y.value;
    h="known_function2 "~op~" "~x.proof~" "~y.proof~" True.intro";
   }
  }
  auto name="naturalValue"~to!string(t.id),proof="naturalKnown"~to!string(t.id);
  output.code~="noncomputable def "~name~" (ρ : Env) : ℕ := "~value~"\n";
  output.code~="theorem "~proof~" (ρ : Env) : n"~to!string(t.id)~".eval ρ = some ("~name~" ρ) := "~h~"\n";
  auto result=NaturalValue("("~name~" ρ)","("~proof~" ρ)");values[t.id]=result;return result;
 }
}

private class Branch {
 AlgebraExporter output;
 Checker checker;
 Arena a;
 Term input;
 uint bits,serial;
 string valuation,prefix,parameters,arguments;
 string[string] saved;
 Reduction[string] reductions;
 Form[uint] forms;
 Form[string] powerForms;
 Naturals naturals;
 GuardProofs guards;
 Fraction[uint] parsed;
 string[uint] conditions;
 this(AlgebraExporter out_,Naturals naturalValues,Term source,uint branch,GuardProofs knownGuards=null){
  guards=knownGuards;
  output=out_;a=out_.a;input=source;bits=branch;prefix="branch"~to!string(branch)~"_";
  naturals=naturalValues;
  checker=new Checker(a);enforce(checker.collect(input),"unsupported rational conditions");
  checker.branch=bits;checker.memo=null;
  foreach(i,p;checker.predicates){
   if(bits&(1u<<i))checker.nonzeros~=p;else if(p.length)checker.equalities~=p;
   parameters~=" (h"~to!string(i)~" : value "~guardValuation()~" "~output.poly(p)~(bits&(1u<<i)?" ≠ 0)":" = 0)");
   arguments~=" h"~to!string(i);
  }
 }
 string guardValuation(){return guards is null?"(atoms ρ)":guards.valuation;}
 string poly(Polynomial p){return output.poly(p);}
 string val(Polynomial p){return "(value "~valuation~" "~poly(p)~")";}
 Polynomial one(){return checker.ring.constant(Number(1));}
 Polynomial den(Fraction f){return checker.multiplyFactors(one(),f.denominator);}
 string calculate(string expression,Polynomial result){auto checked=output.calculation(expression);enforce(checker.same(checked.value,result),"arithmetic result mismatch");return checked.proof;}
 string powered(Polynomial p,uint n){return replace(output.powered(p,n)," σ)"," "~valuation~")");}
 string save(string claim,string proof){
  if(auto old=claim in saved)return *old;
  auto name=prefix~to!string(serial++);
  output.code~="theorem "~name~" (ρ : Env)"~parameters~" : "~claim~" := "~proof~"\n";
  auto result="("~name~" ρ"~arguments~")";saved[claim]=result;return result;
 }
 void prepare(Term t){
  if(t.id in parsed)return;
  auto n=a.view(t);
  if(n.op==Op.mask){bool truth;enforce(checker.truth(a.viewChild(t,0),truth),"unknown rational guard");if(truth)prepare(a.viewChild(t,1));}
  else if(n.op==Op.add||n.op==Op.mul||n.op==Op.inv||n.op==Op.pow||n.op==Op.builtin&&
    (n.value>=Builtin.castNZ&&n.value<=Builtin.castRC||n.value==Builtin.invQ||
     n.value==Builtin.addN||n.value==Builtin.addZ||n.value==Builtin.addQ||
     n.value==Builtin.mulN||n.value==Builtin.mulZ||n.value==Builtin.mulQ||
     n.value>=Builtin.powNN&&n.value<=Builtin.powCN)){
   prepare(a.viewChild(t,0));
   if(n.arity==2&&!(n.op==Op.builtin&&n.value>=Builtin.powNN&&n.value<=Builtin.powCN))prepare(a.viewChild(t,1));
   if(n.op==Op.builtin&&n.value>=Builtin.powNN&&n.value<=Builtin.powCN)preparePower(parsed[n.a],a.viewChild(t,1));
  }
  Fraction f;enforce(checker.parse(t,f),"missing rational source certificate");parsed[t.id]=f;
 }
 bool constantNatural(Term t,out uint k){
  Polynomial p;if(!checker.ring.parse(t,p)||p.length>1)return false;
  if(!p.length){k=0;return true;}
  if(p.keys[0].length)return false;
  auto c=p.values[0];if(!c.im.zero||!c.re.small||c.re.integer<0||c.re.integer>uint.max)return false;
  k=cast(uint)c.re.integer;return true;
 }
 Term[uint] exponents;
 Term exponentNormal(Term t){
  if(auto old=t.id in exponents)return *old;
  Polynomial p;enforce(checker.ring.parse(t,p),"unsupported exponent normalization");
  auto keys=p.keys;sort(keys);auto result=a.natural_(0);
  foreach(key;keys){
   auto c=p[key];enforce(c.im.zero);
   enforce(c.re.small&&c.re.integer>=0&&c.re.integer<=uint.max);
   auto coefficient=a.natural_(cast(long)c.re.integer),term=coefficient;
   if(key.length){enforce(key.length==2&&key[1]==1);term=c.re.integer==1?a.at(key[0]):a.mul(coefficient,a.at(key[0]),true);}
   result=a.isNumber(result)&&a.number(result).zero?term:a.add(result,term,true);
  }
  output.expression(result);exponents[t.id]=result;exponents[result.id]=result;return result;
 }
 void preparePower(Fraction base,Term exponent){
  exponent=exponentNormal(exponent);
  Fraction result;enforce(checker.naturalPower(base,exponent,result,0));uint k;
  if(constantNatural(exponent,k)||a.view(exponent).op==Op.variable)return;
  auto n=a.view(exponent),plus=n.op==Op.add||n.op==Op.builtin&&n.value==Builtin.addN;
  if(plus){preparePower(base,a.viewChild(exponent,0));preparePower(base,a.viewChild(exponent,1));return;}
  auto product=n.op==Op.mul||n.op==Op.builtin&&n.value==Builtin.mulN;
  if(product){
   if(constantNatural(a.viewChild(exponent,0),k)){preparePower(checker.power(base,k),a.viewChild(exponent,1));return;}
   if(constantNatural(a.viewChild(exponent,1),k)){preparePower(checker.power(base,k),a.viewChild(exponent,0));return;}
  }
  if(n.op==Op.pow&&n.value==1){preparePower(base,a.viewChild(exponent,0));return;}
  throw new Exception("unsupported affine natural-power proof");
 }
 void atoms(){
  auto previous="atoms";
  foreach(j,atom;checker.atoms){
   auto p=poly(atom.base.numerator),q=poly(den(atom.base)),name=prefix~"atoms"~to!string(j);
   auto exponent=a.view(atom.exponent);enforce(exponent.op==Op.variable&&exponent.sort==Sort.natural);
   output.code~="noncomputable def "~name~" (ρ : Env) (i : ℕ) : ℂ := if i = "~to!string(atom.id)~" then (value ("~previous~" ρ) "~p~" / value ("~previous~" ρ) "~q~") ^ (ρ.natural "~to!string(exponent.value)~") else "~previous~" ρ i\n";
   previous=name;
  }
  valuation="("~previous~" ρ)";
 }
 string condition(size_t i){
  if(auto old=cast(uint)i in conditions)return *old;
  auto p=checker.predicates[i],name="h"~to!string(i);
  auto eq=save(val(p)~" = value "~guardValuation()~" "~poly(p),"rfl");
  auto proof=bits&(1u<<i)?"(fun h => "~name~" (Eq.trans (Eq.symm "~eq~") h))":"(Eq.trans "~eq~" "~name~")";
  auto result=save(val(p)~(bits&(1u<<i)?" ≠ 0":" = 0"),proof);conditions[cast(uint)i]=result;return result;
 }
 Reduction reduce(Polynomial source){
  auto key=poly(source);if(auto old=key in reductions)return *old;
  auto p=source.dup;string proof="rfl";bool changed=true;
  while(changed){
   changed=false;
   foreach(i,e;checker.predicates){
    if(bits&(1u<<i)||!e.length)continue;
    auto lead=checker.lead(e);if(!lead.length)continue;
    Powers hit,quotient;bool found;
    foreach(k,c;p)if(checker.divides(lead,k,quotient)){hit=k;found=true;break;}
    if(!found)continue;
    Polynomial term;checker.ring.put(term,quotient,checker.ring.budget.calc!"/"(-p[hit],e[lead]));
    auto next=checker.ring.add(p,checker.ring.mul(e,term));
    auto calculation=calculate("AlgebraCertificate.add "~poly(p)~" (AlgebraCertificate.mul "~poly(e)~" "~poly(term)~")",next);
    auto step="(reduce_checked "~valuation~" (p := "~poly(p)~") (e := "~poly(e)~") (t := "~poly(term)~") "~condition(i)~" "~calculation~")";
    proof=save(val(source)~" = "~val(next),"(Eq.trans "~proof~" "~step~")");p=next;changed=true;break;
   }
  }
  auto result=Reduction(p,proof);reductions[key]=result;return result;
 }
 string equal(Polynomial p,Polynomial q){
  auto difference=checker.ring.add(p,checker.ring.mul(checker.ring.constant(Number(-1)),q));
  auto normalized=reduce(difference);enforce(!normalized.value.length,"nonzero rational equality witness");
  auto h=calculate("AlgebraCertificate.add "~poly(p)~" (multiplyTerm [] "~output.coefficient(Number(-1))~" "~poly(q)~")",difference);
  return save(val(p)~" = "~val(q),"(equal_reduced "~valuation~" "~normalized.proof~" "~h~")");
 }
 string nonzero(Polynomial p){
  auto normalized=reduce(p),r=normalized.value;enforce(r.length,"zero rational denominator");
  if(r.length==1&&!r.keys[0].length){
   auto c=r.values[0];
   auto definition=output.compute("AlgebraCertificate.constant "~output.coefficient(c),poly(r));
   auto hn="(Eq.mp (congrArg (fun p => value "~valuation~" p ≠ 0) "~definition~") (nonzero_constant "~valuation~" (c := "~output.coefficient(c)~") (of_decide_eq_true rfl)))";
   return save(val(p)~" ≠ 0","(fun hz => "~hn~" (Eq.trans (Eq.symm "~normalized.proof~") hz))");
  }
  foreach(i,q;checker.predicates)if(bits&(1u<<i)){
   auto qr=reduce(q).value;if(!qr.length)continue;
   if(!checker.same(checker.monic(r),checker.monic(qr)))continue;
   auto c=checker.ring.budget.calc!"/"(r[checker.lead(r)],qr[checker.lead(qr)]),multiple=checker.scale(q,c);
   auto he=equal(p,multiple),calc=calculate("multiplyTerm [] "~output.coefficient(c)~" "~poly(q),multiple);
   return save(val(p)~" ≠ 0","(nonzero_multiple "~valuation~" (c := "~output.coefficient(c)~") "~he~" "~calc~" (of_decide_eq_true rfl) "~condition(i)~")");
  }
  throw new Exception("unproved rational denominator");
 }
 string denominator(Fraction f){
  auto p=one(),h=nonzero(p),keys=f.denominator.keys;sort(keys);
  foreach(id;keys){
   auto n=f.denominator[id],factor=checker.factors[id],power=checker.ring.power(factor,n);
   auto hp="(Powered.nonzero "~powered(factor,n)~" "~nonzero(factor)~")",next=checker.ring.mul(p,power);
   h=save(val(next)~" ≠ 0","(nonzero_mul "~valuation~" "~h~" "~hp~" "~calculate("AlgebraCertificate.mul "~poly(p)~" "~poly(power),next)~")");p=next;
  }
  return h;
 }
 Form commonDenominator(Form form,Fraction original,uint[uint] powers,Polynomial q,string hq){
  if(checker.same(form.denominator,q))return form;
  auto missing=powers.dup;
  foreach(k,e;original.denominator){enforce(missing.get(k,0)>=e);missing[k]-=e;}
  auto factor=checker.multiplyFactors(one(),missing),p=checker.ring.mul(form.numerator,factor);
  auto hn=calculate("AlgebraCertificate.mul "~poly(form.numerator)~" "~poly(factor),p);
  auto hd=calculate("AlgebraCertificate.mul "~poly(form.denominator)~" "~poly(factor),q);
  return Form(p,q,"(Fractional.rescale (l := "~poly(factor)~") "~form.proof~" "~hn~" "~hd~" "~hq~")");
 }
 Form canonical(Form raw,Fraction target){
  auto p=target.numerator,q=den(target);
  if(checker.same(p,raw.numerator)&&checker.same(q,raw.denominator))return raw;
  auto left=checker.ring.mul(raw.numerator,q),right=checker.ring.mul(p,raw.denominator);
  auto proof="(Fractional.change_checked (r := "~poly(p)~") (s := "~poly(q)~") "~raw.proof~" "~denominator(target)~" "~equal(left,right)~" "~calculate("AlgebraCertificate.mul "~poly(raw.numerator)~" "~poly(q),left)~" "~calculate("AlgebraCertificate.mul "~poly(p)~" "~poly(raw.denominator),right)~")";
  return Form(p,q,proof);
 }
 string ratio(Fraction base){return "("~val(base.numerator)~" / "~val(den(base))~")";}
 Form numericPower(Fraction base,uint k){
  auto p=base.numerator,q=den(base),h="(Fractional.ratio "~valuation~" "~poly(p)~" "~poly(q)~" "~denominator(base)~")";
  auto raw=Form(checker.ring.power(p,k),checker.ring.power(q,k),"(Fractional.powered "~h~" "~powered(p,k)~" "~powered(q,k)~")");
  return canonical(raw,checker.power(base,k));
 }
 string knownConstant(Term t,uint k){
  if(a.isNumber(t))return "rfl";
  auto h=output.prove(t),p=output.values[t.id],known=naturals.get(t);
  auto literal="(numericN (atoms ρ) ρ (.nat "~to!string(k)~") "~to!string(k)~" rfl)";
  auto equality="(Normalized.equal Nat.cast_injective "~h~" "~literal~")";
  return "(Option.some.inj (Eq.trans (Eq.symm "~known.proof~") "~equality~"))";
 }
 Form powerTerm(Fraction base,Term exponent){
  auto key=poly(base.numerator)~":"~poly(den(base))~":"~to!string(exponent.id);
  if(auto old=key in powerForms)return *old;
  auto canonicalExponent=exponentNormal(exponent);
  if(canonicalExponent!=exponent){
   auto raw=powerTerm(base,canonicalExponent),old=naturals.get(exponent),fresh=naturals.get(canonicalExponent);
   auto hp=output.prove(exponent),hq=output.prove(canonicalExponent);
   auto he="(Option.some.inj (Eq.trans (Eq.symm "~old.proof~") (Eq.trans (Normalized.equal Nat.cast_injective "~hp~" "~hq~") "~fresh.proof~")))";
   raw.proof=save("Fractional "~valuation~" embedC (some ("~ratio(base)~" ^ "~old.value~")) "~poly(raw.numerator)~" "~poly(raw.denominator),
    "Fractional.replaceValue "~raw.proof~" (congrArg (fun n : ℕ => "~ratio(base)~" ^ n) "~he~")");
   powerForms[key]=raw;return raw;
  }
  auto known=naturals.get(exponent),value=ratio(base),n=a.view(exponent);uint k;Form raw;
  if(constantNatural(exponent,k)){
   raw=numericPower(base,k);
   raw.proof="(Fractional.replaceValue "~raw.proof~" (congrArg (fun n : ℕ => "~value~" ^ n) "~knownConstant(exponent,k)~"))";
  }else if(checker.same(base.numerator,one())&&!base.denominator.length){
   raw=Form(one(),one(),"(powerOne "~valuation~" "~known.value~")");
  }else if(n.op==Op.variable){
   auto normalized=checker.power(base,1);uint id=uint.max;
   foreach(atom;checker.atoms)if(atom.exponent==exponent&&checker.same(atom.base.numerator,normalized.numerator)&&atom.base.denominator==normalized.denominator){id=atom.id;break;}
   enforce(id!=uint.max,"missing canonical power atom");Polynomial p;checker.ring.put(p,[id,1].idup,Number(1));
   raw=Form(p,one(),"(Fractional.ofNormalized (Normalized.atom "~valuation~" embedC ("~value~" ^ "~known.value~") "~to!string(id)~" rfl))");
  }else if(n.op==Op.add||n.op==Op.builtin&&n.value==Builtin.addN){
   auto x=powerTerm(base,a.viewChild(exponent,0)),y=powerTerm(base,a.viewChild(exponent,1));
   auto p=checker.ring.mul(x.numerator,y.numerator),q=checker.ring.mul(x.denominator,y.denominator);
   auto h="(Fractional.mul (u := "~poly(p)~") (v := "~poly(q)~") "~x.proof~" "~y.proof~" "~calculate("AlgebraCertificate.mul "~poly(x.numerator)~" "~poly(y.numerator),p)~" "~calculate("AlgebraCertificate.mul "~poly(x.denominator)~" "~poly(y.denominator),q)~")";
   raw=Form(p,q,"(Fractional.replaceValue "~h~" (pow_add "~value~" "~naturals.get(a.viewChild(exponent,0)).value~" "~naturals.get(a.viewChild(exponent,1)).value~"))");
  }else if(n.op==Op.mul||n.op==Op.builtin&&n.value==Builtin.mulN){
   bool left=constantNatural(a.viewChild(exponent,0),k);if(!left)enforce(constantNatural(a.viewChild(exponent,1),k));
   auto constant=a.viewChild(exponent,left?0:1),other=a.viewChild(exponent,left?1:0),scaled=checker.power(base,k);
   auto hk=numericPower(base,k),hn=powerTerm(scaled,other);
   raw=hn;raw.proof="(Fractional.powerScale "~hk.proof~" "~hn.proof~")";
   auto hc=knownConstant(constant,k),ov=naturals.get(other).value;
   auto he=left?"(congrArg (fun k : ℕ => k * "~ov~") "~hc~")":"(Eq.trans (congrArg (fun k : ℕ => "~ov~" * k) "~hc~") (Nat.mul_comm "~ov~" "~to!string(k)~"))";
   raw.proof="(Fractional.replaceValue "~raw.proof~" (congrArg (fun n : ℕ => "~value~" ^ n) "~he~"))";
  }else if(n.op==Op.pow&&n.value==1){
   raw=powerTerm(base,a.viewChild(exponent,0));
   raw.proof="(Fractional.replaceValue "~raw.proof~" (congrArg (fun n : ℕ => "~value~" ^ n) (pow_one "~naturals.get(a.viewChild(exponent,0)).value~")))";
  }else throw new Exception("unsupported natural exponent certificate");
  Fraction target;auto count=checker.atoms.length;enforce(checker.naturalPower(base,exponent,target,0)&&checker.atoms.length==count,"late rational power atom");
  auto result=canonical(raw,target);
  result.proof=save("Fractional "~valuation~" embedC (some ("~value~" ^ "~known.value~")) "~poly(result.numerator)~" "~poly(result.denominator),result.proof);
  powerForms[key]=result;return result;
 }
 string boolean(Term t){
  auto n=a.view(t);bool result;enforce(checker.truth(t,result));string h;
  if(n.op==Op.boolLit)h="rfl";
  else if(n.op==Op.not_)h="known_not "~boolean(a.viewChild(t,0));
  else if(n.op==Op.and_||n.op==Op.or_){
   bool left;enforce(checker.truth(a.viewChild(t,0),left));auto hl=boolean(a.viewChild(t,0));
   if(n.op==Op.and_&&!left||n.op==Op.or_&&left)h=(left?"known_or_true":"known_and_false")~" (n"~to!string(n.b)~".eval ρ) "~hl;
   else h=(left?"known_and_true":"known_or_false")~" "~hl~" "~boolean(a.viewChild(t,1));
  }else{
   auto c=a.viewChild(t,0);size_t i;while(i<checker.conditions.length&&checker.conditions[i]!=c)++i;enforce(i<checker.conditions.length);
   string normal;Polynomial p;
   if(guards is null){normal=output.prove(c);p=output.values[c.id];}
   else {normal=guards.proofs[c.id];p=guards.values[c.id];}
   auto aligned=save("Normalized "~valuation~" embed"~AlgebraExporter.field(a.sort(c))~" (n"~to!string(c.id)~".eval ρ) "~poly(p),"Normalized.valuation (τ := "~valuation~") "~normal~" rfl");
   auto injective=a.sort(c)==Sort.natural?"Nat.cast_injective":a.sort(c)==Sort.integer?"Int.cast_injective":a.sort(c)==Sort.rational?"Rat.cast_injective":a.sort(c)==Sort.real_?"Complex.ofReal_injective":"Function.injective_id";
   h=(result?"Normalized.nonzero_true ":"Normalized.nonzero_false "~injective~" ")~aligned~" "~condition(i);
   if(n.op==Op.builtin)h="Eq.trans ("~builtinInfo(cast(Builtin)n.value).code~"_eq (n"~to!string(c.id)~".eval ρ)) ("~h~")";
  }
  return save("n"~to!string(t.id)~".eval ρ = some "~(result?"true":"false"),h);
 }
 Form source(Term t){
  if(auto old=t.id in forms)return *old;
  auto n=a.view(t);Form raw;
  if(n.op==Op.mask){
   bool truth;enforce(checker.truth(a.viewChild(t,0),truth));auto hg=boolean(a.viewChild(t,0));
   if(truth){raw=source(a.viewChild(t,1));raw.proof="(Fractional.mask_true "~hg~" "~raw.proof~")";}
   else raw=Form(Polynomial.init,one(),"(Fractional.mask_false (σ := "~valuation~") (n"~to!string(n.a)~".eval ρ) (n"~to!string(n.b)~".eval ρ) "~hg~")");
  }else if(a.isNumber(t)||n.op==Op.variable||output.opaque(t)){
   auto h=output.prove(t),p=output.values[t.id];
   auto normal=save("Normalized "~valuation~" embed"~AlgebraExporter.field(n.sort)~" (n"~to!string(t.id)~".eval ρ) "~poly(p),"Normalized.valuation (τ := "~valuation~") "~h~" rfl");
   raw=Form(p,one(),"(Fractional.ofNormalized "~normal~")");
  }else{
   auto left=source(a.viewChild(t,0));
   if(n.op==Op.builtin&&n.value>=Builtin.castNZ&&n.value<=Builtin.castRC){raw=left;raw.proof="(Fractional."~builtinInfo(cast(Builtin)n.value).code~" "~left.proof~")";}
   else if(n.op==Op.inv||n.op==Op.builtin&&n.value==Builtin.invQ){
    auto target=parsed[t.id],q=den(target),lhs=checker.ring.mul(left.numerator,target.numerator),rhs=checker.ring.mul(left.denominator,q);
    auto hn=save(val(left.numerator)~" ≠ 0","(inverse_nonzero "~valuation~" (Fractional.denominator "~left.proof~") "~denominator(target)~" "~equal(lhs,rhs)~" "~calculate("AlgebraCertificate.mul "~poly(left.numerator)~" "~poly(target.numerator),lhs)~" "~calculate("AlgebraCertificate.mul "~poly(left.denominator)~" "~poly(q),rhs)~")");
    raw=Form(left.denominator,left.numerator,"("~(n.op==Op.inv?"fraction_inverse":"Fractional.inverseQ")~" "~left.proof~" "~hn~")");
   }
   else if(n.op==Op.pow){
    auto k=cast(uint)n.value;raw=Form(checker.ring.power(left.numerator,k),checker.ring.power(left.denominator,k),"(Fractional.powered "~left.proof~" "~powered(left.numerator,k)~" "~powered(left.denominator,k)~")");
   }else if(n.op==Op.builtin&&n.value>=Builtin.powNN&&n.value<=Builtin.powCN){
    auto exponent=a.viewChild(t,1),power=powerTerm(parsed[n.a],exponent),known=naturals.get(exponent);
    raw=power;raw.proof="(Fractional.totalPower Functions."~builtinInfo(cast(Builtin)n.value).code~" (fun _ _ => rfl) (fun _ _ => True.intro) "~left.proof~" "~known.proof~" "~power.proof~")";
   }else{
    auto right=source(a.viewChild(t,1));
    auto plus=n.op==Op.add||n.op==Op.builtin&&(n.value==Builtin.addN||n.value==Builtin.addZ||n.value==Builtin.addQ);
    auto av="(n"~to!string(n.a)~".eval ρ)",bv="(n"~to!string(n.b)~".eval ρ)";
    if(plus){
     auto lf=parsed[n.a],rf=parsed[n.b],powers=lf.denominator.dup;
     foreach(k,e;rf.denominator)if(powers.get(k,0)<e)powers[k]=e;
     auto common=Fraction(one(),powers),q=den(common),hq=denominator(common);
     left=commonDenominator(left,lf,powers,q,hq);right=commonDenominator(right,rf,powers,q,hq);
     auto p=checker.ring.add(left.numerator,right.numerator);
     auto h=n.op==Op.builtin?"Fractional.totalAddSame Functions."~builtinInfo(cast(Builtin)n.value).code~" (fun _ _ => rfl) (fun _ _ => True.intro)":"Fractional.add_same";
     h~=" (a := "~av~") (b := "~bv~") (u := "~poly(p)~") "~left.proof~" "~right.proof~" "~calculate("AlgebraCertificate.add "~poly(left.numerator)~" "~poly(right.numerator),p);
     raw=Form(p,q,"("~h~")");
    }else{
     auto p=checker.ring.mul(left.numerator,right.numerator),q=checker.ring.mul(left.denominator,right.denominator);
     auto h=n.op==Op.builtin?"Fractional.totalMul Functions."~builtinInfo(cast(Builtin)n.value).code~" (fun _ _ => rfl) (fun _ _ => True.intro)":"Fractional.mul";
     h~=" (a := "~av~") (b := "~bv~") (u := "~poly(p)~") (v := "~poly(q)~") "~left.proof~" "~right.proof~" "~calculate("AlgebraCertificate.mul "~poly(left.numerator)~" "~poly(right.numerator),p)~" "~calculate("AlgebraCertificate.mul "~poly(left.denominator)~" "~poly(right.denominator),q);
     raw=Form(p,q,"("~h~")");
    }
   }
  }
  auto result=canonical(raw,parsed[t.id]);
  result.proof=save("Fractional "~valuation~" embed"~AlgebraExporter.field(n.sort)~" (n"~to!string(t.id)~".eval ρ) "~poly(result.numerator)~" "~poly(result.denominator),result.proof);
  forms[t.id]=result;return result;
 }
 string run(){
  bool impossible;
  foreach(i,p;checker.predicates){
   if(bits&(1u<<i)){if(!checker.reduce(p).length)impossible=true;}
   else if(p.length==1&&!p.keys[0].length)impossible=true;
  }
  if(!impossible)prepare(input);
  atoms();string h;
  if(impossible){
   foreach(i,p;checker.predicates){
    if(bits&(1u<<i)){auto r=reduce(p);if(!r.value.length){h="False.elim ("~condition(i)~" "~r.proof~")";break;}}
    else if(p.length==1&&!p.keys[0].length){
     auto c=p.values[0],def_=output.compute("AlgebraCertificate.constant "~output.coefficient(c),poly(p));
     h="False.elim ((Eq.mp (congrArg (fun p => value "~valuation~" p ≠ 0) "~def_~") (nonzero_constant "~valuation~" (c := "~output.coefficient(c)~") (of_decide_eq_true rfl))) "~condition(i)~")";break;
    }
   }
  }else{
   auto value=source(input);enforce(!value.numerator.length,"nonzero rational result");
   auto injective=a.sort(input)==Sort.rational?"Rat.cast_injective":a.sort(input)==Sort.real_?"Complex.ofReal_injective":"Function.injective_id";
   h="Fractional.zero "~injective~" "~value.proof;
  }
  enforce(h.length,"missing rational branch proof");
  return save("n"~to!string(input.id)~".eval ρ = some 0",h);
 }
}

string exportRationalCertificate(Arena a,Term input,Term[] conditions){
 auto output=new AlgebraExporter(a,input,"QSym.RationalCertificate"),check=new Checker(a);
 enforce(check.collect(input)&&check.conditions==conditions,"rational condition mismatch");
 auto naturals=new Naturals(output);
 GuardProofs guards;
 if(!check.atoms.length)foreach(c;conditions)output.prove(c);
 else {
  // Certify guards before making any branch assumptions. Their canonical
  // power atoms have a shared interpretation in every subsequent branch.
  guards=new GuardProofs;
  auto global=new Branch(output,naturals,input,0);
  global.prefix="guard_";global.parameters=global.arguments="";
  global.checker.predicates=null;global.checker.equalities=null;global.checker.nonzeros=null;
  foreach(c;conditions){
   foreach(id;a.viewPostorder(c))enforce(a.view(a.at(id)).op!=Op.mask,"masked symbolic-power guard is not supported");
   global.prepare(c);
  }
  global.atoms();guards.valuation=global.valuation;
  foreach(i,c;conditions){
   auto form=global.source(c);
   enforce(check.same(form.numerator,check.predicates[i])&&check.same(form.denominator,global.one()),"rational guard normalization mismatch");
   guards.proofs[c.id]=global.save("Normalized "~global.valuation~" embed"~AlgebraExporter.field(a.sort(c))~" (n"~to!string(c.id)~".eval ρ) "~global.poly(form.numerator),"Fractional.toNormalized "~form.proof);
   guards.values[c.id]=form.numerator;
  }
 }
 string[] branches;
 foreach(bits;0..1u<<conditions.length)branches~=(new Branch(output,naturals,input,bits,guards)).run();
 string split(size_t i,uint bits){
  if(i==conditions.length)return branches[bits];
  return "(Classical.byCases (p := value "~(guards is null?"(atoms ρ)":guards.valuation)~" "~output.poly(check.predicates[i])~" = 0) (fun h"~to!string(i)~" => "~split(i+1,bits)~") (fun h"~to!string(i)~" => "~split(i+1,bits|(1u<<i))~"))";
 }
 output.code~="theorem zero (ρ : Env) : n"~to!string(input.id)~".eval ρ = some 0 := "~split(0,0)~"\n#qsym_check_axioms zero\nend QSym.RationalCertificate\n";
 return output.code;
}
