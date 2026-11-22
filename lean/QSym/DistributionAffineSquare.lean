import QSym.DistributionSquareExpression
import QSym.DistributionAffineExpression

noncomputable section
namespace QSym.Distribution.GraphFibre

def squareInput (product : Bool) (x : Option ℝ) : Option ℝ :=
  if product then Value.mul x x else x.map (· ^ 2)

def signedSqrt (neg : Bool) (y : Option ℝ) : Option ℝ :=
  let s := Functions.sqrtR.apply y
  if neg then Value.mul (some ((-1 : ℤ) : ℝ)) s else s

variable (a b j : ℚ) {f i : ℝ → Option ℝ} {v : Option ℝ}
variable (ha : a ≠ 0) (hj : j = |a⁻¹|) (hf : StepSource.Affine f a b)
variable (hi : StepSource.Affine i a⁻¹ (-b/a)) (hv : v = some (j : ℝ))
variable (num den : ℚ) {u v' : Option ℝ} (hn : den ≠ 0) (hd : num = (2 * |a|)*den)
variable (hu : u = some (num : ℝ)) (hv' : v' = some (den : ℝ))

include ha hj hf hi hv hn hd hu hv' in
def affineSquareExpression (product : Bool) :
    SquareExpression (fun x => squareInput product (f x))
      (fun y => (signedSqrt (decide (0 < a)) y).bind i)
      (fun y => (signedSqrt (!(decide (0 < a))) y).bind i)
      (fun y => rationalInvMul den u v' (Functions.sqrtR.apply y)) (i ((0 : ℤ) : ℝ)) := by
  let c := affineExpression a b j ha hj hf hi hv
  let F := fun x => (c.f x)^2
  let D := fun x => (2*c.f x)*(a : ℝ)
  have diff (x : ℝ) : HasStrictDerivAt F (D x) x := by
    have pow : HasStrictDerivAt (fun t : ℝ => t^2) (2*c.f x) (c.f x) := by
      simpa using hasStrictDerivAt_pow 2 (c.f x)
    exact pow.comp x (c.branch.derivative x)
  refine ⟨F, D, ?_, diff, ?_⟩
  · intro x
    rw [hf.equation]
    cases product <;> simp [F, c, affineExpression, squareInput, Value.mul, pow_two]
  · intro y
    have inv (t : ℝ) : i t = some (c.root t) := c.inverse_eq (some t)
    have atRoot (t : ℝ) : D (c.root t) = (2*t)*(a : ℝ) := by simp [D, c.branch.inverse t]
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · exact ⟨[], squareCover_negative c.f hy, by
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hy, not_lt_of_ge hy.le]⟩
    · exact ⟨[c.root 0], squareCover_zero c.branch, by
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, inv, atRoot, Value.inv]⟩
    · have hs := Real.sqrt_pos.mpr hy
      have zero : (0 : ℝ) ≤ y := hy.le
      have s : Functions.sqrtR.apply (some y) = some (√y) := by
        simp [Function1.apply, Functions.sqrtR, zero]
      have J : rationalInvMul den u v' (some (√y)) = Value.inv (some ((2*|(a : ℝ)|)*√y)) := by
        rw [hu, hv', hd]
        push_cast
        exact rationalInvMul_some hn _ _
      have wp (t : ℝ) (ht : |t| = √y) : |D (c.root t)| = (2*|(a : ℝ)|)*√y := by
        rw [atRoot, abs_mul, abs_mul, ht, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring
      have n := wp (-√y) (by simp [abs_of_pos hs])
      have p := wp (√y) (abs_of_pos hs)
      rcases lt_or_gt_of_ne ha with neg | pos
      · have h : (a : ℝ) < 0 := by exact_mod_cast neg
        have order : c.root (√y) < c.root (-√y) := by
          change (√y-b)/(a : ℝ) < (-√y-b)/(a : ℝ)
          exact (div_lt_div_right_of_neg h).mpr (by linarith)
        refine ⟨_, squareCover_positive c.branch hy order (Or.inr ⟨rfl,rfl⟩), ?_⟩
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hy, signedSqrt, not_lt_of_gt neg,
          s, J, Value.mul, inv, n, p]
      · have h : 0 < (a : ℝ) := by exact_mod_cast pos
        have order : c.root (-√y) < c.root (√y) := by
          change (-√y-b)/(a : ℝ) < (√y-b)/(a : ℝ)
          exact (div_lt_div_iff_of_pos_right h).mpr (by linarith)
        refine ⟨_, squareCover_positive c.branch hy order (Or.inl ⟨rfl,rfl⟩), ?_⟩
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hy, signedSqrt, pos,
          s, J, Value.mul, inv, n, p]

end QSym.Distribution.GraphFibre
