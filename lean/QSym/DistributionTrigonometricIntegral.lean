import QSym.DistributionCoordinatePeriodic
import QSym.DistributionGaussianSymbolic

noncomputable section
namespace QSym.Distribution.StepSource.HasPrimitive
open MeasureTheory Set

/-- Integrate an affine phase with partial coefficients. At zero frequency the
integrand is constant. A missing coefficient makes it missing throughout. -/
theorem parameters {w P} (h : HasPrimitive w P) (hw : w none = none) (hP : P none = none)
    (phase : Option ℝ → Option ℝ) {C A l u m : Option ℝ}
    (hf : Quadratic (fun x => phase (some x)) (some C) (some A) none) :
    let G := fun z => Value.mul (Value.inv A) (P (phase z))
    IntervalTerms l u m (fun x => w (phase (some x)))
      (Binding.conditionalValue (Value.nonzero A) (Value.add (G u) (Value.mul m (G l)))
        (Value.mul (w C) (Value.add u (Value.mul m l)))) := by
  dsimp only
  have eqn (x : ℝ) : phase (some x) = Value.add C (Value.mul A (some x)) := by
    rw [hf.equation]
    cases C <;> cases A <;> simp [coefValue, Value.mul, Value.add]
  rcases A with _ | a
  · apply IntervalTerms.undefined
    intro x
    rw [eqn]
    cases C <;> exact hw
  rcases C with _ | c
  · have src (x : ℝ) : w (phase (some x)) = none := by rw [eqn]; exact hw
    apply IntervalTerms.missing src
    intro i j hi hj hm
    subst hi hj hm
    by_cases ha : a = 0 <;>
      simp [Value.nonzero, Value.inv, ha, Binding.conditionalValue, eqn, Value.add, Value.mul, hw, hP]
  obtain ⟨g, H, src, out, cont, deriv⟩ := h
  have point (x : ℝ) : w (phase (some x)) = some (g (c+a*x)) := by rw [eqn]; exact src _
  by_cases ha : a = 0
  · subst a
    apply IntervalTerms.value (g := fun _ => g c) (fun x => by simpa using point x) continuous_const
    intro i j hi hj hm
    subst hi hj hm
    simp [Value.nonzero, Binding.conditionalValue, Value.add, Value.mul, src, intervalIntegral.integral_const]
    ring
  · apply IntervalTerms.value point (cont.comp (continuous_const.add (continuous_const.mul continuous_id)))
    intro i j hi hj hm
    subst hi hj hm
    have d (x : ℝ) : HasDerivAt (fun z : ℝ => a⁻¹*H (c+a*z)) (g (c+a*x)) x := by
      have p : HasDerivAt (fun z : ℝ => c+a*z) a x := by
        simpa using (((hasDerivAt_id x).const_mul a).const_add c)
      convert ((deriv _).comp x p).const_mul a⁻¹ using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => d x)
      ((cont.comp (continuous_const.add (continuous_const.mul continuous_id))).intervalIntegrable _ _)]
    simp [Value.nonzero, Value.inv, ha, Binding.conditionalValue, eqn, Value.add, Value.mul, out]
    ring

end QSym.Distribution.StepSource.HasPrimitive
