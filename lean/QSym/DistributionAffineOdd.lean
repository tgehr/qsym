import QSym.DistributionOddPowerBridge

noncomputable section
namespace QSym.Distribution.GraphFibre

variable (a b j : ℚ) {f i : ℝ → Option ℝ} {v : Option ℝ}
variable (ha : a ≠ 0) (hj : j = |a⁻¹|) (hf : StepSource.Affine f a b)
variable (hi : StepSource.Affine i a⁻¹ (-b/a)) (hv : v = some (j : ℝ))

def affineExpression : BranchExpression (fun x => x.bind f) (fun y => y.bind i) (fun y => y.bind fun _ => v) where
  f x := (a : ℝ)*x+b
  root y := (y-b)/(a : ℝ)
  slope _ := (a : ℝ)
  branch := by
    have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    exact ⟨fun _ _ h => mul_left_cancel₀ hn (add_right_cancel h),
      fun y => by field_simp, affine_derivative _ _⟩
  forward_eq := hf.equation
  inverse_eq y := by
    cases y with
    | none => rfl
    | some y =>
      simp only [Option.some_bind, Option.map_some, hi.equation, Rat.cast_inv, Rat.cast_div, Rat.cast_neg]
      congr 1
      ring
  jac_eq y := by
    have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    cases y <;> simp [Value.inv, hn, hv, hj, abs_inv]

/-- Write a rational derivative coefficient as a quotient of integers, keeping
the denominator outside the partial reciprocal. This gives the frontend a
stable printed expression even when the coefficient is fractional. -/
def affineOddWeight (k : ℕ) (den : ℚ) (u v y : Option ℝ) : Option ℝ :=
  let w := Value.inv (Value.mul u ((oddRootValue k y).map (fun x => x ^ (oddDegree k - 1))))
  if den = 1 then w else Value.mul v w

private theorem scaled_inv (c z n : ℝ) (hn : n ≠ 0) :
    Value.mul (some n) (Value.inv (some ((c*n)*z))) = Value.inv (some (c*z)) := by
  by_cases hc : c = 0 <;> by_cases hz : z = 0 <;>
    simp [Value.inv, Value.mul, hc, hz, hn, mul_inv_rev]
  field_simp
  ring

variable (k : ℕ) (num den : ℚ) {u v' : Option ℝ}
variable (hn : den ≠ 0) (hd : num = (oddDegree k * |a|)*den)
variable (hu : u = some (num : ℝ)) (hv' : v' = some (den : ℝ))

include hn hd hu hv' in
def affineOddExpression :
    BranchExpression (fun x => (x.bind f).map (fun z => z ^ oddDegree k))
      (fun y => (oddRootValue k y).bind i) (affineOddWeight k den u v') := by
  let inner := affineExpression a b j ha hj hf hi hv
  let c := inner.comp (oddPowerExpression k)
  refine ⟨c.f, c.root, c.slope, c.branch, c.forward_eq, c.inverse_eq, ?_⟩
  intro y
  cases y with
  | none => simp [affineOddWeight, oddRootValue_eq, hu, hv', Value.mul, Value.inv]
  | some y =>
    change _ = Value.inv (some |oddSlope k (inner.f (inner.root (oddRoot k y))) * (a : ℝ)|)
    rw [inner.branch.inverse (oddRoot k y), abs_mul, abs_of_nonneg (oddSlope_nonneg k _),
      affineOddWeight, oddRootValue_eq, hu, hv', hd]
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs, Option.map_some]
    let z := (oddRoot k y) ^ (oddDegree k - 1)
    let c₀ := (oddDegree k : ℝ) * |(a : ℝ)|
    change (if den = 1 then Value.inv (some ((c₀*den)*z))
            else Value.mul (some (den : ℝ)) (Value.inv (some ((c₀*den)*z)))) = _
    have heq : oddSlope k (oddRoot k y) * |(a : ℝ)| = c₀*z := by unfold c₀ z oddSlope; ring
    rw [heq]
    split
    · rename_i he
      simp [he]
    · exact scaled_inv c₀ z den (by exact_mod_cast hn)

include ha hj hf hi hv hn hd hu hv' in
/-- For an affine source change followed by an odd power, the unique critical
source is the affine inverse at zero. The frontend checks the predicate there. -/
theorem affineOdd_chart_rule (p : ℝ → Option Bool) (hp : ∀ x, Value.Defined (p x))
    (h0 : (i ((0 : ℤ) : ℝ)).bind p = some false) :
    realPushforwardOnValue (some p) (some fun x => (f x).map (fun t => t ^ oddDegree k)) =
      weightValue (some fun y =>
        let z := oddRootValue k (some y)
        Value.mask ((z.bind i).bind p) (affineOddWeight k den u v' (some y))) lebesgueValue := by
  apply (affineOddExpression a b j ha hj hf hi hv k num den hn hd hu hv').chart_rule p hp
  intro x hz
  have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  change oddSlope k ((a : ℝ)*x+b) * a = 0 at hz
  have hx : (a : ℝ)*x+b = 0 := by
    by_contra h
    exact (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (oddDegree_pos k).ne') (pow_ne_zero _ h)) hn) hz
  have inv : i 0 = some x := by
    rw [hi.equation]
    congr 1
    push_cast
    field_simp
    linarith
  simpa [inv] using h0

end QSym.Distribution.GraphFibre
