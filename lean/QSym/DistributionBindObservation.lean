import QSym.DistributionWeightObservation

noncomputable section
namespace QSym.Distribution

/-- Observe a sequential composition by testing the kernel in the original
source order. The source and kernel can both contain sums and integrals. -/
theorem integrate_bind (d : D α) (k : α → Option (D β)) (f : β → Option ℝ) :
    (bind d k).bind (fun b => integrate b f) =
      integrate d (fun x => (k x).bind (fun b => integrate b f)) := by
  induction d with
  | invalid | zero | dirac => rfl
  | density w v =>
    apply congrArg (partialIntegral MeasureTheory.volume)
    funext r
    exact (integrate_getD _ _).trans ((integrate_scaleValue _ _ _).trans
      (congrArg (Value.mul (w r)) (Option.bind_assoc ..)))
  | add a b ha hb => exact (integrate_addValue _ _ _).trans (congrArg₂ Value.add ha hb)
  | scale r d ih => exact (integrate_scaleValue _ _ _).trans (congrArg (Value.mul (some r)) ih)
  | integral k ih => exact congrArg (partialIntegral MeasureTheory.volume) (funext fun r => (integrate_getD _ _).trans (ih r))
  | sum k ih => exact congrArg partialSum (funext fun i => (integrate_getD _ _).trans (ih i))

theorem mass_bind_test (d : Option (D α)) (k : α → Option (D β)) :
    massValue (bindValue d (some k)) =
      massValue (weightValue (some (fun x => massValue (k x))) d) := by
  rw [mass_weight_test]
  cases d with
  | none => rfl
  | some d => exact integrate_bind d k (fun _ => some 1)

/-- A missing kernel function is strict even when the source is empty. -/
theorem mass_bind_kernel (d : Option (D α)) (k : Option (α → Option (D β))) :
    massValue (bindValue d k) = k.bind (fun _ => massValue (weightValue
      (some (fun x => massValue (k.bind (fun g => g x)))) d)) := by
  cases k with
  | none => cases d <;> rfl
  | some k => exact mass_bind_test d k

theorem FiniteFibre.Represents.bind_mass {d : Option (D ℝ)} {m : Option (FiniteFibre.Model ℝ)}
    (r : FiniteFibre.Represents d m) (k : Option (ℝ → Option (D β))) :
    massValue (bindValue d k) =
      k.bind (fun g => m.bind (fun p => FiniteFibre.pairing p (fun x => massValue (g x)))) := by
  cases k with
  | none => cases d <;> rfl
  | some k => exact (mass_bind_test d k).trans (r.weighted_mass _)

end QSym.Distribution
