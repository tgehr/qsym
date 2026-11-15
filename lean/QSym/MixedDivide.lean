import QSym.DivideConquer

namespace QSym.MixedDivide
open scoped BigOperators

-- Padding terminal subproblems adds no cost. At depth j, every offset in
-- [0,2^j) occurs once, so the two rounded child sizes remain exact.
def charge (toll : ℕ → ℕ) (n : ℕ) := if 2≤n then toll n else 0

def level (toll : ℕ → ℕ) (n j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2^j), charge toll ((n+k)/2^j)

theorem sum_pairs (f : ℕ → ℕ) (m : ℕ) :
    (∑ k ∈ Finset.range (2*m), f k) = ∑ k ∈ Finset.range m, (f (2*k)+f (2*k+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    omega

theorem half_offset (n k d : ℕ) : (n+2*k)/(2*d) = (n/2+k)/d := by
  rw [← Nat.div_div_eq_div_mul]
  congr 1
  omega

theorem level_step (toll : ℕ → ℕ) (n j : ℕ) :
    level toll n (j+1) = level toll (n/2) j + level toll ((n+1)/2) j := by
  unfold level
  rw [pow_succ',sum_pairs,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [half_offset,show n+(2*k+1)=(n+1)+2*k by omega,half_offset]


theorem histogram (f : ℕ → ℕ) (n d : ℕ) (hd : 0<d) :
    (∑ k ∈ Finset.range d, f ((n+k)/d)) =
      (d-n%d)*f (n/d)+(n%d)*f (n/d+1) := by
  have hr := Nat.mod_lt n hd
  have split : d=(d-n%d)+n%d := by omega
  have left : (∑ k ∈ Finset.range (d-n%d), f ((n+k)/d))=(d-n%d)*f (n/d) := by
    have he : ∀ k ∈ Finset.range (d-n%d), (n+k)/d=n/d := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [Nat.add_div hd]
      have hklt : k<d := by omega
      rw [Nat.div_eq_of_lt hklt,Nat.mod_eq_of_lt hklt,if_neg (by omega)]
      omega
    simp only [Finset.sum_congr rfl (fun k hk => congrArg f (he k hk)),Finset.sum_const,Finset.card_range,smul_eq_mul]
  have right : (∑ k ∈ Finset.range (n%d), f ((n+((d-n%d)+k))/d))=(n%d)*f (n/d+1) := by
    have he : ∀ k ∈ Finset.range (n%d), (n+((d-n%d)+k))/d=n/d+1 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [Nat.add_div hd]
      have hklt : (d-n%d)+k<d := by omega
      rw [Nat.div_eq_of_lt hklt,Nat.mod_eq_of_lt hklt,if_pos (by omega)]
    simp only [Finset.sum_congr rfl (fun k hk => congrArg f (he k hk)),Finset.sum_const,Finset.card_range,smul_eq_mul]
  calc
    _ = ∑ k ∈ Finset.range ((d-n%d)+n%d), f ((n+k)/d) := congrArg (fun m => ∑ k ∈ Finset.range m, f ((n+k)/d)) split
    _ = _ := by rw [Finset.sum_range_add,left,right]

theorem level_small (toll : ℕ → ℕ) (n j : ℕ) (hn : n≤1) : level toll n j = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hp : 0<2^j := pow_pos (by decide : 0 < (2:ℕ)) _
  have hk' : k<2^j := Finset.mem_range.mp hk
  have hq : (n+k)/2^j < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  simp [charge,show ¬2≤(n+k)/2^j by omega]

def cost (seed : ℕ) (toll : ℕ → ℕ) (n h : ℕ) :=
  n*seed + ∑ j ∈ Finset.range h, level toll n j

theorem cost_small (seed : ℕ) (toll : ℕ → ℕ) (h : ℕ) : cost seed toll 1 h = seed := by
  simp [cost,level_small toll 1 _ (by omega)]

theorem cost_step (seed : ℕ) (toll : ℕ → ℕ) (n h : ℕ) (hn : 2≤n) :
    cost seed toll n (h+1) = cost seed toll (n/2) h + cost seed toll ((n+1)/2) h + toll n := by
  have hs : n/2+(n+1)/2=n := by omega
  simp only [cost,Finset.sum_range_succ',level_step,Finset.sum_add_distrib]
  have hz : level toll n 0=toll n := by simp [level,charge,hn]
  rw [hz]
  have hm : n*seed=(n/2)*seed+((n+1)/2)*seed := by rw [← Nat.add_mul,hs]
  rw [hm]
  omega

theorem solve_height (p : Recursion.Program ℕ ℕ ℕ) (seed : ℕ → ℕ) (toll : ℕ → ℕ)
    (hp : ∀ g n, p.eval g n = if n≤1 then some (seed n)
      else Value.add (Value.add (g (n/2)) (g ((n+1)/2))) (some (toll n)))
    (h n : ℕ) (hn : 0<n) (hh : n≤2^h) :
    FixedPoint.value p.functional n = some (cost (seed 1) toll n h) := by
  induction h generalizing n with
  | zero =>
    have he : n=1 := by simp at hh; omega
    subst n
    rw [← p.unfold,hp,if_pos (by omega),cost_small]
  | succ h ih =>
    by_cases he : n=1
    · subst n;rw [← p.unfold,hp,if_pos (by omega),cost_small]
    · have htwo : 2≤n := by omega
      have hpow : n≤2*2^h := by simpa [pow_succ'] using hh
      rw [← p.unfold,hp,if_neg (by omega),ih (n/2) (by omega) (by omega),ih ((n+1)/2) (by omega) (by omega),cost_step (seed 1) toll n h htwo]
      rfl

#qsym_check_axioms solve_height
inductive Expr where
  | constant (value : ℕ)
  | lower
  | upper
  | add (a b : Expr)

def Expr.low : Expr → ℕ
  | .constant _ | .upper => 0
  | .lower => 1
  | .add a b => a.low+b.low

def Expr.high : Expr → ℕ
  | .constant _ | .lower => 0
  | .upper => 1
  | .add a b => a.high+b.high

def Expr.offset : Expr → ℕ
  | .constant c => c
  | .lower | .upper => 0
  | .add a b => a.offset+b.offset

noncomputable def Expr.eval (x y : Option ℕ) : Expr → Option ℕ
  | .constant c => some c
  | .lower => x
  | .upper => y
  | .add a b => Functions.addN.apply (a.eval x y) (b.eval x y)

theorem Expr.eval_some (e : Expr) (x y : ℕ) :
    e.eval (some x) (some y)=some (e.low*x+e.high*y+e.offset) := by
  induction e <;> simp_all [eval,low,high,offset,AffineRecurrence.addN,Value.add] <;> ring

theorem offset_eq (e : Expr) : e.eval (some 0) (some 0)=some e.offset := by
  rw [e.eval_some];simp

noncomputable def step (inclusive reverse : Bool) (seed : ℕ → ℕ)
    (e : ℕ → Expr) (g : ℕ → Option ℕ) (n : ℕ) :=
  let p := DivideConquer.condition 2 inclusive n
  let yes := Value.mask p (some (seed n))
  let no := Value.mask (Value.not p) ((e n).eval
    ((Functions.divN.apply (some n) (some 2)).bind g)
    ((Functions.divN.apply (Functions.addN.apply (some n) (some 1)) (some 2)).bind g))
  if reverse then Functions.addN.apply no yes else Functions.addN.apply yes no

theorem step_eq (inclusive reverse : Bool) (seed : ℕ → ℕ)
    (e : ℕ → Expr) (g : ℕ → Option ℕ) (n : ℕ) :
    step inclusive reverse seed e g n = if n≤1 then some (seed n)
      else (e n).eval (g (n/2)) (g ((n+1)/2)) := by
  have ha : Functions.addN.apply (some n) (some 1)=some (n+1) := by simp [Functions.addN,Function2.apply]
  simp only [step,DivideConquer.condition_eq 2 (by omega),ha,
    DivideConquer.div_some _ 2 (by omega),Option.some_bind,AffineRecurrence.addN]
  by_cases hn : n≤1
  · have hn' : n<2 := by omega
    cases reverse <;> simp [hn,hn',Value.mask,Value.not,Value.add]
  · have hn' : ¬n<2 := by omega
    cases he : (e n).eval (g (n/2)) (g ((n+1)/2)) <;>
      cases reverse <;> simp [hn,hn',Value.mask,Value.not,Value.add,he]

theorem solve_expr_height (p : Recursion.Program ℕ ℕ ℕ) (inclusive reverse : Bool)
    (seed : ℕ → ℕ) (e : ℕ → Expr) (hl : ∀ n, (e n).low=1) (hr : ∀ n, (e n).high=1)
    (hp : ∀ g n, p.eval g n = step inclusive reverse seed e g n)
    (h n : ℕ) (hn : 0<n) (hh : n≤2^h) :
    FixedPoint.value p.functional n = some (cost (seed 1) (fun n => (e n).offset) n h) := by
  induction h generalizing n with
  | zero =>
    have he : n=1 := by simp at hh;omega
    subst n
    rw [← p.unfold,hp,step_eq,if_pos (by omega),cost_small]
  | succ h ih =>
    by_cases he : n=1
    · subst n;rw [← p.unfold,hp,step_eq,if_pos (by omega),cost_small]
    · have htwo : 2≤n := by omega
      have hpow : n≤2*2^h := by simpa [pow_succ'] using hh
      rw [← p.unfold,hp,step_eq,if_neg (by omega),
        ih (n/2) (by omega) (by omega),ih ((n+1)/2) (by omega) (by omega),
        Expr.eval_some,hl,hr,cost_step (seed 1) _ n h htwo]
      simp

noncomputable def result (s t : Option ℕ → Option ℕ) (n : ℕ) :=
  let lit (x : ℕ) := some x
  let h := Functions.addN.apply (Functions.logN.apply (lit 2) (lit n)) (lit 1)
  let levels := Summation.rangeValue (some (fun j =>
    let d := Functions.powNN.apply (lit 2) (lit j)
    let q := Functions.divN.apply (lit n) d
    let r := Functions.subN.apply (lit n) (Functions.mulN.apply q d)
    let charge (v : Option ℕ) := Value.mask (Functions.leN.apply (lit 2) v) (v.bind (fun x => t (some x)))
    Functions.addN.apply
      (Functions.mulN.apply (Functions.subN.apply d r) (charge q))
      (Functions.mulN.apply r (charge (Functions.addN.apply q (lit 1)))))) h
  let body := Functions.addN.apply (Functions.mulN.apply (lit n) (s (lit 1))) levels
  Functions.addN.apply
    (Value.mask (Functions.leN.apply (lit n) (lit 0)) (s (lit 0)))
    (Value.mask (Value.not (Functions.leN.apply (lit n) (lit 0))) body)

theorem result_eq (seed toll : ℕ → ℕ) (s t : Option ℕ → Option ℕ)
    (hs : ∀ n, s (some n)=some (seed n)) (ht : ∀ n, t (some n)=some (toll n)) (n : ℕ) :
    result s t n = some (if n=0 then seed 0 else cost (seed 1) toll n (Nat.log 2 n+1)) := by
  have hd (j : ℕ) : (2:ℕ)^j≠0 := pow_ne_zero _ (by omega)
  have hp (x j : ℕ) : Functions.powNN.apply (some x) (some j)=some (x^j) := by simp [Functions.powNN,Function2.apply]
  have ha (x y : ℕ) : Functions.addN.apply (some x) (some y)=some (x+y) := by simp [Functions.addN,Function2.apply]
  have hmul (x y : ℕ) : Functions.mulN.apply (some x) (some y)=some (x*y) := by simp [Functions.mulN,Function2.apply]
  have hrem (j : ℕ) : Functions.subN.apply (some n) (some (n/2^j*2^j))=some (n%2^j) := by
    simp [Functions.subN,Function2.apply,Nat.div_mul_le_self,Nat.mod_eq_sub_div_mul]
  have hdiff (j : ℕ) : Functions.subN.apply (some (2^j)) (some (n%2^j))=some (2^j-n%2^j) := by
    simp [Functions.subN,Function2.apply,Nat.le_of_lt (Nat.mod_lt n (pow_pos (by decide : 0 < (2:ℕ)) j))]
  simp only [result,DivideConquer.log_some 2 n (by omega),ha,hp,
    DivideConquer.div_some _ _ (hd _),hmul,hrem,hdiff,ha,Option.some_bind,hs,ht]
  have hm (q : ℕ) : Value.mask (Functions.leN.apply (some 2) (some q)) (some (toll q))=some (charge toll q) := by
    by_cases h : 2≤q <;> simp [Function2.apply,Functions.leN,Value.mask,charge,h]
  simp only [hm]
  by_cases hn : n=0 <;> simp [Summation.rangeValue,Summation.finite,Function2.apply,Functions.mulN,Functions.addN,
    Value.mask,Value.not,Functions.leN,cost,level,hn]
  apply Finset.sum_congr rfl
  intro j hj
  exact (histogram (charge toll) n (2^j) (pow_pos (by decide : 0 < (2:ℕ)) j)).symm

theorem solve_sum (p : Recursion.Program ℕ ℕ ℕ) (inclusive reverse : Bool)
    (seed : ℕ → ℕ) (e : ℕ → Expr) (hl : ∀ n, (e n).low=1) (hr : ∀ n, (e n).high=1)
    (hp : ∀ g n, p.eval g n = step inclusive reverse seed e g n)
    (s t : Option ℕ → Option ℕ) (hs : ∀ n, s (some n)=some (seed n))
    (ht : ∀ n, t (some n)=some ((e n).offset)) :
    FixedPoint.value p.functional = fun n => result s t n := by
  funext n
  rw [result_eq seed _ s t hs ht]
  by_cases hn : n=0
  · subst n;rw [← p.unfold,hp,step_eq,if_pos (by omega),if_pos rfl]
  · rw [if_neg hn]
    exact solve_expr_height p inclusive reverse seed e hl hr hp _ n (by omega)
      (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega) n))

#qsym_check_axioms solve_sum
end QSym.MixedDivide
