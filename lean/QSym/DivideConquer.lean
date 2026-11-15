import QSym.Summation
import QSym.AffineRecurrence
import QSym.AxiomCheck

namespace QSym.DivideConquer
open scoped BigOperators

-- The seed is evaluated at the actual terminal subproblem, not at a
-- hypothetical power-of-b boundary.
def formula (b c : ℕ) (seed toll : ℕ → ℕ) (n : ℕ) : ℕ :=
  c^(Nat.log b n) * seed (n / b^(Nat.log b n)) +
    ∑ j ∈ Finset.range (Nat.log b n), c^j * toll (n / b^j)

theorem formula_base (b c : ℕ) (seed toll : ℕ → ℕ) (n : ℕ) (hn : n<b) :
    formula b c seed toll n = seed n := by simp [formula, Nat.log_of_lt hn]

theorem quotient (n b j : ℕ) : n / b / b^j = n / b^(j+1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ', Nat.mul_comm]

theorem formula_step (b c : ℕ) (hb : 1<b) (seed toll : ℕ → ℕ) (n : ℕ) (hn : b≤n) :
    formula b c seed toll n = c * formula b c seed toll (n/b) + toll n := by
  have hl : Nat.log b n = Nat.log b (n/b)+1 := by
    rw [Nat.log]; simp [hn,hb]
  unfold formula
  rw [hl, Finset.sum_range_succ']
  simp only [pow_zero, Nat.div_one, one_mul]
  simp only [pow_succ', ← Nat.div_div_eq_div_mul, mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem solve (p : Recursion.Program ℕ ℕ ℕ) (b c : ℕ) (hb : 1<b)
    (seed toll : ℕ → ℕ)
    (hp : ∀ g n, p.eval g n = if n<b then some (seed n)
      else Value.add (Value.mul (some c) (g (n/b))) (some (toll n))) :
    FixedPoint.value p.functional = fun n => some (formula b c seed toll n) := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [← p.unfold, hp]
    by_cases hn : n<b
    · rw [if_pos hn, formula_base b c seed toll n hn]
    · have hbn : b≤n := Nat.le_of_not_gt hn
      rw [if_neg hn, ih (n/b) (Nat.div_lt_self (by omega) hb), formula_step b c hb seed toll n hbn]
      rfl

theorem div_some (n b : ℕ) (hb : b≠0) :
    Functions.divN.apply (some n) (some b) = some (n/b) := by
  simp [Functions.divN, Function2.apply, hb]
  rfl

theorem log_some (b n : ℕ) (hb : 1<b) :
    Functions.logN.apply (some b) (some n) = some (Nat.log b n) := by
  simp [Functions.logN, Function2.apply, hb]

noncomputable def result (b : ℕ) (c : Option ℕ)
    (seed toll : Option ℕ → Option ℕ) (n : ℕ) :=
  let l := Functions.logN.apply (some b) (some n)
  let atLevel (j : Option ℕ) := Functions.divN.apply (some n) (Functions.powNN.apply (some b) j)
  Functions.addN.apply
    (Functions.mulN.apply (Functions.powNN.apply c l)
      ((atLevel l).bind (fun x => seed (some x))))
    (Summation.rangeValue (some (fun j => Functions.mulN.apply
      (Functions.powNN.apply c (some j))
      ((atLevel (some j)).bind (fun x => toll (some x))))) l)

theorem result_eq (b c : ℕ) (hb : 1<b) (seed toll : ℕ → ℕ)
    (s t : Option ℕ → Option ℕ) (hs : ∀ n, s (some n)=some (seed n))
    (ht : ∀ n, t (some n)=some (toll n)) (n : ℕ) :
    result b (some c) s t n = some (formula b c seed toll n) := by
  have hpos (j : ℕ) : b^j≠0 := pow_ne_zero _ (by omega)
  have hp (x j : ℕ) : Functions.powNN.apply (some x) (some j)=some (x^j) := by simp [Functions.powNN,Function2.apply]
  simp only [result, log_some b n hb, hp, div_some _ _ (hpos _), Option.some_bind, hs, ht]
  simp [Summation.rangeValue, Summation.finite, formula, Function2.apply, Functions.mulN, Functions.addN]

#qsym_check_axioms solve

theorem some_of_domain {v : Option ℕ} (h : Domain.Correct v (some true)) : v=some (v.getD 0) := by
  have hd := h.iff.mpr rfl
  cases v <;> simp_all [Value.Defined]

noncomputable def condition (b : ℕ) (inclusive : Bool) (n : ℕ) :=
  if inclusive then Functions.leN.apply (some n) (some (b-1))
  else Functions.ltN.apply (some n) (some b)

theorem condition_eq (b : ℕ) (hb : 1<b) (inclusive : Bool) (n : ℕ) :
    condition b inclusive n = some (decide (n<b)) := by
  have h : n≤b-1 ↔ n<b := by omega
  cases inclusive <;> simp [condition,Function2.apply,Functions.leN,Functions.ltN,h]

noncomputable def step (b : ℕ) (inclusive reverse : Bool) (seed : ℕ → ℕ)
    (e : ℕ → AffineRecurrence.Expr ℕ) (g : ℕ → Option ℕ) (n : ℕ) :=
  let p := condition b inclusive n
  let yes := Value.mask p (some (seed n))
  let no := Value.mask (Value.not p)
    ((e n).eval Functions.addN.apply Functions.mulN.apply
      ((Functions.divN.apply (some n) (some b)).bind g))
  if reverse then Functions.addN.apply no yes else Functions.addN.apply yes no

theorem step_eq (b : ℕ) (hb : 1<b) (inclusive reverse : Bool) (seed : ℕ → ℕ)
    (e : ℕ → AffineRecurrence.Expr ℕ) (g : ℕ → Option ℕ) (n : ℕ) :
    step b inclusive reverse seed e g n = if n<b then some (seed n)
      else (e n).eval Value.add Value.mul (g (n/b)) := by
  simp only [step,condition_eq b hb,div_some n b (by omega),Option.some_bind,
    AffineRecurrence.addN,AffineRecurrence.mulN]
  by_cases hn : n<b
  · cases reverse <;> simp [hn,Value.mask,Value.not,Value.add]
  · cases he : (e n).eval Value.add Value.mul (g (n/b)) <;>
      cases reverse <;> simp [hn,Value.mask,Value.not,Value.add,he]

theorem solve_expr (p : Recursion.Program ℕ ℕ ℕ) (b c : ℕ) (hb : 1<b)
    (inclusive reverse : Bool) (seed : ℕ → ℕ) (e : ℕ → AffineRecurrence.Expr ℕ)
    (hc : ∀ n, (e n).coefficient=c)
    (hp : ∀ g n, p.eval g n = step b inclusive reverse seed e g n) :
    FixedPoint.value p.functional = fun n => some (formula b c seed (fun j => (e j).offset) n) := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [← p.unfold,hp,step_eq b hb]
    by_cases hn : n<b
    · rw [if_pos hn,formula_base b c seed _ n hn]
    · have hbn : b≤n := Nat.le_of_not_gt hn
      rw [if_neg hn,ih (n/b) (Nat.div_lt_self (by omega) hb),AffineRecurrence.Expr.eval_some,hc,
        formula_step b c hb seed _ n hbn]

theorem offset_eq (e : AffineRecurrence.Expr ℕ) :
    e.eval Functions.addN.apply Functions.mulN.apply (some 0)=some e.offset := by
  rw [AffineRecurrence.addN,AffineRecurrence.mulN,AffineRecurrence.Expr.eval_some];simp

theorem solve_sum (p : Recursion.Program ℕ ℕ ℕ) (b c : ℕ) (hb : 1<b)
    (inclusive reverse : Bool) (seed : ℕ → ℕ) (e : ℕ → AffineRecurrence.Expr ℕ)
    (hc : ∀ n, (e n).coefficient=c)
    (hp : ∀ g n, p.eval g n = step b inclusive reverse seed e g n)
    (co : Option ℕ) (hco : co=some c) (s t : Option ℕ → Option ℕ)
    (hs : ∀ n, s (some n)=some (seed n)) (ht : ∀ n, t (some n)=some ((e n).offset)) :
    FixedPoint.value p.functional = fun n => result b co s t n := by
  rw [hco,solve_expr p b c hb inclusive reverse seed e hc hp]
  funext n;exact (result_eq b c hb seed _ s t hs ht n).symm

#qsym_check_axioms solve_sum

end QSym.DivideConquer
