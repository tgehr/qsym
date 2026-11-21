import QSym.Binding
import QSym.Refinement

noncomputable section
namespace QSym.Distribution.GraphFibre

/-- The expression emitted by the frontend uses strict comparisons and the
partial real square root and inverse. Both atoms are retained. -/
def squareResult (y : Option ℝ) : Option (D ℝ) :=
  let z := some ((0 : ℤ) : ℝ)
  let s := Functions.sqrtR.apply y
  let w := Value.inv (Value.mul (some ((2 : ℤ) : ℝ)) s)
  Binding.conditionalValue (Value.lt z y)
    (addValue (scaleValue w (diracValue (Value.mul (some ((-1 : ℤ) : ℝ)) s)))
      (scaleValue w (diracValue s)))
    (Binding.conditionalValue (Value.lt y z) zeroValue none)

theorem square_rule (y : Option ℝ) : value (some (fun x => some (x^2))) y = squareResult y := by
  cases y with
  | none => rfl
  | some y =>
    change value (some (fun x => some (square x))) (some y) = _
    rw [value_total square (measurable_id.pow_const 2)]
    rcases lt_trichotomy y 0 with hn|rfl|hp
    · have h : fibre square y = some [] := by qsym_rule
      simp [h, squareResult, Binding.conditionalValue, Value.lt, hn, not_lt_of_ge hn.le,
        presentation, zeroValue]
    · have h : fibre square 0 = none := by qsym_rule
      simp [h, squareResult, Binding.conditionalValue, Value.lt]
    · have h : fibre square y = some [(-√y, jac y), (√y, jac y)] := by qsym_rule
      have hne : 2 * √y ≠ 0 := by positivity
      simp [h, presentation, squareResult, Binding.conditionalValue, Value.lt, hp, hp.le,
        Function1.apply, Functions.sqrtR, diracValue, scaleValue, addValue, Value.mul, Value.inv, hne, jac]

theorem square_mul_rule (y : Option ℝ) :
    value (some (fun x => Value.mul (some x) (some x))) y = squareResult y := by
  simpa [Value.mul, pow_two] using square_rule y

/-- Scalar marginal via a strict test on the source section. -/
def squareMass (y : Option ℝ) : Option ℝ :=
  let z := some ((0 : ℤ) : ℝ)
  Value.mask (Value.le z y) (Value.inv (Functions.sqrtR.apply y))

theorem square_mass_rule (y : Option ℝ) :
    marginal (some (fun x => some (x^2))) y = squareMass y := by
  cases y with
  | none => rfl
  | some y =>
    change marginal (some (fun x => some (square x))) (some y) = _
    rcases lt_trichotomy y 0 with hn|rfl|hp
    · have h : marginal (some (fun x => some (square x))) (some y) = some 0 := by qsym_rule
      simp [h, squareMass, Value.le, Value.mask, not_le_of_gt hn]
    · simpa [squareMass, Value.le, Value.mask, Value.inv, Function1.apply, Functions.sqrtR] using square_marginal_zero
    · have h : marginal (some (fun x => some (square x))) (some y) = some (√y)⁻¹ := by qsym_rule
      simp [h, squareMass, Value.le, Value.mask, hp.le, Functions.sqrtR,
        Function1.apply, Value.inv, (Real.sqrt_pos.mpr hp).ne']

theorem square_mul_mass_rule (y : Option ℝ) :
    marginal (some (fun x => Value.mul (some x) (some x))) y = squareMass y := by
  simpa [Value.mul, pow_two] using square_mass_rule y

end QSym.Distribution.GraphFibre
