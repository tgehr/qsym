import QSym.Binding
import QSym.Refinement

noncomputable section
namespace QSym.Distribution.GraphFibre

/-- Frontend expression for the signed real inverse. Cubing uses the existing
cube-root primitive. Higher degrees use real powers on nonnegative bases. -/
def oddRootValue (k : ℕ) (y : Option ℝ) : Option ℝ :=
  if k = 0 then Functions.cbrtR.apply y else
    let sign := Functions.castQR.apply (Functions.castZQ.apply (Functions.signR.apply y))
    let e := Value.inv (some ((oddDegree k : ℤ) : ℝ))
    Value.mul sign (Functions.powerR.apply (Value.abs y) e)

def oddWeightValue (k : ℕ) (y : Option ℝ) : Option ℝ :=
  Value.inv (Value.mul (some ((oddDegree k : ℤ) : ℝ))
    ((oddRootValue k y).map (fun x => x ^ (oddDegree k - 1))))

private theorem oddRootValue_eq (k : ℕ) (y : Option ℝ) : oddRootValue k y = y.map (oddRoot k) := by
  cases y with
  | none => by_cases hk : k = 0 <;> simp [oddRootValue, hk, Function1.apply, Value.mul]
  | some y =>
    by_cases hk : k = 0
    · subst k
      simp [oddRootValue, oddRoot, oddDegree, Function1.apply, Functions.cbrtR, one_div]
    · have hn : (0 : ℝ) < oddDegree k := Nat.cast_pos.mpr (oddDegree_pos k)
      have dom {x : ℝ} (hx : 0 ≤ x) : Functions.powerR.domain x (oddDegree k : ℝ)⁻¹ := by
        rcases hx.eq_or_lt with h | h
        · exact Or.inr (Or.inl ⟨h.symm, inv_nonneg.mpr hn.le⟩)
        · exact Or.inl h
      have eq : oddRootValue k (some y) =
          some ((if y < 0 then -1 else if 0 < y then 1 else 0) * |y| ^ (oddDegree k : ℝ)⁻¹) := by
        simp [oddRootValue, hk, Functions.signR, Functions.castZQ, Functions.castQR, Function1.apply,
          Value.mul, Value.inv, Value.abs, Function2.apply, hn.ne', dom (abs_nonneg y), Functions.powerR]
        split_ifs <;> norm_num <;> exact ‹¬ _› (dom (abs_nonneg y))
      rw [eq]
      rcases lt_trichotomy y 0 with h | rfl | h
      · simp [oddRoot, h, abs_of_neg h]
      · simp [oddRoot, Real.zero_rpow (inv_ne_zero hn.ne')]
      · simp [oddRoot, h, not_lt_of_gt h, abs_of_pos h]

private theorem oddWeightValue_some (k : ℕ) (y : ℝ) : oddWeightValue k (some y) = oddWeight k y := by
  simp [oddWeightValue, oddRootValue_eq, oddWeight, oddSlope, Value.mul]

theorem oddPower_fibre_rule (k : ℕ) (y : Option ℝ) :
    value (some fun x => some (x ^ oddDegree k)) y =
      scaleValue (oddWeightValue k y) (diracValue (oddRootValue k y)) := by
  cases y with
  | none => simp [oddWeightValue, oddRootValue_eq, Value.mul, Value.inv, scaleValue, value, atomsValue]
  | some y =>
    rw [value_total (fun x : ℝ => x ^ oddDegree k) (measurable_id.pow_const _), oddWeightValue_some, oddRootValue_eq]
    have fibreEq : fibre (fun x => x ^ oddDegree k) y =
        (oddWeight k y).map (fun w => [(oddRoot k y, w)]) := by qsym_rule
    rw [fibreEq]
    cases oddWeight k y <;> rfl

theorem oddPower_mass_rule (k : ℕ) (y : Option ℝ) :
    marginal (some fun x => some (x ^ oddDegree k)) y = oddWeightValue k y := by
  cases y with
  | none => simp [oddWeightValue, oddRootValue_eq, Value.mul, Value.inv, marginal, atomsValue]
  | some y =>
    rw [marginal, atomsValue_total (fun x : ℝ => x ^ oddDegree k) (measurable_id.pow_const _), oddWeightValue_some]
    have h : fibre (fun x => x ^ oddDegree k) y =
        (oddWeight k y).map (fun w => [(oddRoot k y, w)]) := by qsym_rule
    rw [h]
    cases oddWeight k y <;> simp [observe, Value.mul, Value.add]

theorem oddPower_masked_rule (k : ℕ) (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    (maskedKernel p (some fun x => some (x ^ oddDegree k))).bind (fun fn => y.bind fn) =
      scaleValue (Value.mask (p.bind fun pred => (oddRootValue k y).bind pred) (oddWeightValue k y))
        (diracValue (oddRootValue k y)) := by
  cases p with
  | none => rfl
  | some p =>
    rw [maskedKernel_total p (fun x : ℝ => x ^ oddDegree k) (measurable_id.pow_const _)]
    cases y with
    | none => simp [oddRootValue_eq, diracValue, scaleValue, Value.mask]
    | some y =>
      have h : maskedAtoms p (fun x => x ^ oddDegree k) y =
          (Value.mask (p (oddRoot k y)) (oddWeight k y)).map (fun w => [(oddRoot k y,w)]) := by qsym_rule
      simp only [Option.some_bind, h, oddRootValue_eq, Option.map_some, oddWeightValue_some]
      change _ = scaleValue (Value.mask (p (oddRoot k y)) (oddWeight k y)) (diracValue (some (oddRoot k y)))
      cases Value.mask (p (oddRoot k y)) (oddWeight k y) <;> rfl

theorem oddPower_density_rule (k : ℕ) (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    densityAtValue (realPushforwardOnValue p (some fun x => some (x ^ oddDegree k))) y =
      Value.mask (p.bind fun pred => (oddRootValue k y).bind pred) (oddWeightValue k y) := by
  cases p with
  | none => rfl
  | some p =>
    cases y with
    | none => rw [oddRootValue_eq]; rfl
    | some y =>
      rw [oddRootValue_eq, oddWeightValue_some]
      change _ = Value.mask (p (oddRoot k y)) (oddWeight k y)
      qsym_rule

theorem oddPower_chart_rule (k : ℕ) (p : ℝ → Option Bool) (hp : ∀ x, Value.Defined (p x))
    (h0 : p ((0 : ℤ) : ℝ) = some false) :
    realPushforwardOnValue (some p) (some fun x => some (x ^ oddDegree k)) =
      weightValue (some fun y => Value.mask ((oddRootValue k (some y)).bind p) (oddWeightValue k (some y)))
        lebesgueValue := by
  have hz : p 0 = some false := by simpa using h0
  have eq : realPushforwardOnValue (some p) (some fun x => some (x ^ oddDegree k)) =
      densityValue (some fun y => Value.mask (p (oddRoot k y)) (oddWeight k y)) := by qsym_rule
  rw [eq]
  simp [weightValue, weight, lebesgueValue, densityValue, oddRootValue_eq, oddWeightValue_some, Value.mul_one_left]

end QSym.Distribution.GraphFibre
