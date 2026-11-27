import QSym.DistributionWeightObservation
import QSym.DistributionSum
import QSym.SummationLinearity

noncomputable section
namespace QSym.Distribution

/-- A nonzero signed scalar preserves and reflects existence of all the
integrals and absolutely convergent sums in an observation. -/
theorem integrate_scale_test (d : D α) (c : ℝ) (hc : c ≠ 0) (f : α → Option ℝ) :
    integrate d (fun x => Value.mul (some c) (f x)) = Value.mul (some c) (integrate d f) := by
  induction d with
  | invalid | dirac => rfl
  | zero => simp [integrate, Value.mul]
  | density w v =>
    refine Eq.trans ?_ (partialIntegral_scale_nonzero MeasureTheory.volume c hc _)
    apply congrArg (partialIntegral MeasureTheory.volume)
    funext r
    cases hv : v r with
    | none => cases w r <;> rfl
    | some x => exact Value.mul_left_comm (w r) (some c) (f x)
  | add a b ha hb =>
    change Value.add _ _ = Value.mul (some c) (Value.add (integrate a f) (integrate b f))
    rw [ha, hb]
    cases integrate a f <;> cases integrate b f <;> simp [Value.add, Value.mul, mul_add]
  | scale r a ih =>
    change Value.mul (some r) _ = Value.mul (some c) (Value.mul (some r) (integrate a f))
    rw [ih, Value.mul_left_comm]
  | integral k ih =>
    exact (congrArg (partialIntegral MeasureTheory.volume) (funext ih)).trans
      (partialIntegral_scale_nonzero MeasureTheory.volume c hc _)
  | sum k ih =>
    refine (congrArg partialSum (funext ih)).trans ?_
    simpa only [partialSum_eq_value] using SummationLinearity.scale_nonzero c hc (fun i => integrate (k i) f)

theorem mass_weight_one (d : Option (D α)) (c : Option ℝ) (h : c = some 1) :
    massValue (weightValue (some (fun _ => c)) d) = massValue d := by
  subst c
  exact mass_weight_test _ _

theorem mass_weight_constant (d : Option (D α)) (q : ℚ) (hq : q ≠ 0)
    (c : Option ℝ) (h : c = some (q : ℝ)) :
    massValue (weightValue (some (fun _ => c)) d) = Value.mul c (massValue d) := by
  subst c
  rw [mass_weight_test]
  cases d with
  | none => rfl
  | some d =>
    have hn : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    simpa only [Value.mul_one_right] using integrate_scale_test d (q : ℝ) hn (fun _ => some 1)

end QSym.Distribution
