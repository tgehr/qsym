import QSym.Limit
import QSym.DistributionInterval

/-! Limits at infinity of polynomials times exponentials of rational rate.
A decaying exponential dominates every polynomial, at `+∞` for a negative
rate and at `-∞` for a positive one. -/
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

/-- A polynomial times the exponential of this rate vanishes along the filter. -/
def Decays (l : Filter ℝ) (r : ℚ) : Prop :=
  ∀ p : List ℚ, Tendsto (fun x => polyEval p x * Real.exp ((r : ℝ) * x)) l (𝓝 0)

theorem decays_atTop {r : ℚ} (hr : decide (r < 0) = true) : Decays atTop r := fun p =>
  expPolynomial_tendsto p (by exact_mod_cast of_decide_eq_true hr)

theorem decays_atBot {r : ℚ} (hr : decide (0 < r) = true) : Decays atBot r := fun p =>
  expPolynomial_tendsto_atBot p (by exact_mod_cast of_decide_eq_true hr)

private theorem zero_literal {z : Option ℝ}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : z = some 0 := by
  rw [hz]; simp [Numeric.denote]

/-- A polynomial times a decaying exponential tends to zero. -/
theorem Exact.decay {l : Filter ℝ} {v : ℝ → Option ℝ} {p : List ℚ} {r : ℚ} {z : Option ℝ}
    (hv : ExpPolynomial v p r) (hd : Decays l r)
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : Exact l v z := by
  rw [zero_literal hz]
  exact ⟨_, Eventually.of_forall hv.equation, hd p⟩

/-- Under a scale that does not mention the variable the limit is the scale
times zero: it is zero where the scale is defined and undefined with it. -/
theorem Exact.scaled_decay {l : Filter ℝ} {v : ℝ → Option ℝ} {c : Option ℝ} {p : List ℚ}
    {r : ℚ} {z : Option ℝ} (hv : Scaled v c p r) (hd : Decays l r)
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : Exact l v (Value.mul c z) := by
  rw [zero_literal hz]
  cases c with
  | none => exact Eventually.of_forall fun x => by rw [hv.equation]; rfl
  | some c =>
    refine ⟨fun x => c * (polyEval p x * Real.exp ((r : ℝ) * x)),
      Eventually.of_forall fun x => by rw [hv.equation]; rfl, ?_⟩
    simpa using (hd p).const_mul c

end QSym.Limit
