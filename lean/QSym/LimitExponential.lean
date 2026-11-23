import QSym.LimitStep
import QSym.DistributionInterval

/-! Limits at infinity of polynomials times exponentials of rational rate.
A decaying exponential dominates every polynomial, at `+∞` for a negative
rate and at `-∞` for a positive one. A factor may be a piecewise polynomial:
only its polynomial beyond the last cut matters, and where that is zero the
product vanishes whatever the exponential does. -/
namespace QSym.Limit
open Filter Topology
open QSym.Distribution.StepSource

private def polyReflect : List ℚ → List ℚ
  | [] => []
  | c :: p => c :: polyScale (-1) (polyReflect p)

private theorem polyEval_reflect (p : List ℚ) (x : ℝ) :
    polyEval (polyReflect p) x = polyEval p (-x) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [polyReflect, polyEval, polyEval_scale, ih]
    push_cast
    ring

theorem expPolynomial_tendsto_atBot (p : List ℚ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => polyEval p x * Real.exp (r * x)) atBot (𝓝 0) := by
  have h := (expPolynomial_tendsto (polyReflect p) (show -r < 0 by linarith)).comp
    tendsto_neg_atBot_atTop
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, polyEval_reflect, neg_neg]
  congr 2
  ring

/-- The polynomial times the exponential of this rate vanishes along the
filter. -/
def Vanishes (l : Filter ℝ) (p : List ℚ) (r : ℚ) : Prop :=
  Tendsto (fun x => polyEval p x * Real.exp ((r : ℝ) * x)) l (𝓝 0)

theorem decays_atTop {p : List ℚ} {r : ℚ} (hr : decide (r < 0) = true) : Vanishes atTop p r :=
  expPolynomial_tendsto p (by exact_mod_cast of_decide_eq_true hr)

theorem decays_atBot {p : List ℚ} {r : ℚ} (hr : decide (0 < r) = true) : Vanishes atBot p r :=
  expPolynomial_tendsto_atBot p (by exact_mod_cast of_decide_eq_true hr)

/-- The zero polynomial vanishes whatever the exponential does. -/
theorem vanishes_zero {l : Filter ℝ} {p : List ℚ} {r : ℚ} (hp : polyZero p = true) :
    Vanishes l p r := by
  have h : (fun x => polyEval p x * Real.exp ((r : ℝ) * x)) = fun _ => 0 := by
    funext x; rw [polyEval_zero hp, zero_mul]
  unfold Vanishes
  rw [h]
  exact tendsto_const_nhds

/-- Eventually along the filter a polynomial times the exponential of a
rational multiple of the variable. -/
def EventualExp (l : Filter ℝ) (v : ℝ → Option ℝ) (p : List ℚ) (r : ℚ) : Prop :=
  ∀ᶠ x in l, v x = some (polyEval p x * Real.exp ((r : ℝ) * x))

theorem EventualExp.of_global {l : Filter ℝ} {v : ℝ → Option ℝ} {p : List ℚ} {r : ℚ}
    (h : ExpPolynomial v p r) : EventualExp l v p r :=
  Eventually.of_forall h.equation

/-- A piecewise polynomial is a polynomial beyond its last cut. -/
theorem EventualExp.of_piece {l : Filter ℝ} {reg : Region} {v : ℝ → Option ℝ} {p : List ℚ}
    (ht : Tail l reg) (h : PolynomialOn reg.contains v p) : EventualExp l v p 0 :=
  ht.mono fun x hx => by rw [h.equation x hx]; simp

theorem EventualExp.mul {l : Filter ℝ} {v w : ℝ → Option ℝ} {p q : List ℚ} {r s : ℚ}
    (hv : EventualExp l v p r) (hw : EventualExp l w q s) :
    EventualExp l (fun x => Value.mul (v x) (w x)) (polyMul p q) (r + s) := by
  refine (hv.and hw).mono fun x hx => ?_
  show Value.mul (v x) (w x) = _
  rw [hx.1, hx.2]
  simp only [Value.mul, polyEval_mul, Rat.cast_add, add_mul, Real.exp_add, Option.some.injEq]
  ring

/-- The same with a scale that does not mention the variable. -/
def EventualScaled (l : Filter ℝ) (v : ℝ → Option ℝ) (c : Option ℝ) (p : List ℚ) (r : ℚ) :
    Prop :=
  ∀ᶠ x in l, v x = Value.mul c (some (polyEval p x * Real.exp ((r : ℝ) * x)))

theorem EventualScaled.constant (l : Filter ℝ) (c : Option ℝ) :
    EventualScaled l (fun _ => c) c [1] 0 :=
  Eventually.of_forall (scaled_constant c).equation

theorem EventualScaled.times {l : Filter ℝ} {v w : ℝ → Option ℝ} {c : Option ℝ}
    {p q : List ℚ} {r s : ℚ} (hv : EventualScaled l v c p r) (hw : EventualExp l w q s) :
    EventualScaled l (fun x => Value.mul (v x) (w x)) c (polyMul p q) (r + s) := by
  refine (hv.and hw).mono fun x hx => ?_
  show Value.mul (v x) (w x) = _
  rw [hx.1, hx.2]
  cases c <;>
    simp only [Value.mul, polyEval_mul, Rat.cast_add, add_mul, Real.exp_add, Option.some.injEq]
  ring

theorem EventualScaled.after {l : Filter ℝ} {v w : ℝ → Option ℝ} {c : Option ℝ}
    {p q : List ℚ} {r s : ℚ} (hw : EventualExp l w q s) (hv : EventualScaled l v c p r) :
    EventualScaled l (fun x => Value.mul (w x) (v x)) c (polyMul q p) (s + r) := by
  refine (hv.and hw).mono fun x hx => ?_
  show Value.mul (w x) (v x) = _
  rw [hx.1, hx.2]
  cases c <;>
    simp only [Value.mul, polyEval_mul, Rat.cast_add, add_mul, Real.exp_add, Option.some.injEq]
  ring

theorem EventualScaled.mul {l : Filter ℝ} {v w : ℝ → Option ℝ} {c d : Option ℝ}
    {p q : List ℚ} {r s : ℚ} (hv : EventualScaled l v c p r) (hw : EventualScaled l w d q s) :
    EventualScaled l (fun x => Value.mul (v x) (w x)) (Value.mul c d) (polyMul p q) (r + s) := by
  refine (hv.and hw).mono fun x hx => ?_
  show Value.mul (v x) (w x) = _
  rw [hx.1, hx.2]
  cases c <;> cases d <;>
    simp only [Value.mul, polyEval_mul, Rat.cast_add, add_mul, Real.exp_add, Option.some.injEq]
  ring

private theorem zero_literal {z : Option ℝ}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : z = some 0 := by
  rw [hz]; simp [Numeric.denote]

/-- A polynomial times an exponential that vanishes tends to zero. -/
theorem Exact.decay {l : Filter ℝ} {v : ℝ → Option ℝ} {p : List ℚ} {r : ℚ} {z : Option ℝ}
    (hv : EventualExp l v p r) (hd : Vanishes l p r)
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : Exact l v z := by
  rw [zero_literal hz]
  exact ⟨_, hv, hd⟩

/-- Under a scale that does not mention the variable the limit is the scale
times zero: it is zero where the scale is defined and undefined with it. -/
theorem Exact.scaled_decay {l : Filter ℝ} {v : ℝ → Option ℝ} {c : Option ℝ} {p : List ℚ}
    {r : ℚ} {z : Option ℝ} (hv : EventualScaled l v c p r) (hd : Vanishes l p r)
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : Exact l v (Value.mul c z) := by
  rw [zero_literal hz]
  cases c with
  | none => exact hv
  | some c =>
    refine ⟨fun x => c * (polyEval p x * Real.exp ((r : ℝ) * x)), hv, ?_⟩
    simpa using hd.const_mul c

end QSym.Limit
