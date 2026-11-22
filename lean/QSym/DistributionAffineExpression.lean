import QSym.DistributionBranchExpression
import QSym.DistributionStepSource

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
def rationalInvMul (den : ℚ) (u v z : Option ℝ) : Option ℝ :=
  let w := Value.inv (Value.mul u z)
  if den = 1 then w else Value.mul v w

private theorem scaled_inv (c z n : ℝ) (hn : n ≠ 0) :
    Value.mul (some n) (Value.inv (some ((c*n)*z))) = Value.inv (some (c*z)) := by
  by_cases hc : c = 0 <;> by_cases hz : z = 0 <;>
    simp [Value.inv, Value.mul, hc, hz, hn, mul_inv_rev]
  field_simp
  ring

theorem rationalInvMul_some {den : ℚ} (hn : den ≠ 0) (c z : ℝ) :
    rationalInvMul den (some (c*den)) (some (den : ℝ)) (some z) = Value.inv (some (c*z)) := by
  unfold rationalInvMul
  split
  · rename_i he
    simp [he, Value.mul]
  · exact scaled_inv c z den (by exact_mod_cast hn)

end QSym.Distribution.GraphFibre
