import QSym.DistributionWeightObservation
import QSym.DistributionAtomRows

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

/-- Pair the output of an ordered bind with a strict partial test. The source
tests the weighted mass of each kernel result in its original order. -/
theorem mass_weight_bind (d : Option (D α)) (k : α → Option (D β)) (t : β → Option ℝ) :
    massValue (weightValue (some t) (bindValue d (some k))) =
      massValue (weightValue (some (fun x => massValue (weightValue (some t) (k x)))) d) := by
  simp only [mass_weight_test]
  cases d with
  | none => rfl
  | some d => exact integrate_bind d k t

theorem mass_weight_bind_values (d : Option (D α)) (k : Option (α → Option (D β)))
    (t : Option (β → Option ℝ)) :
    massValue (weightValue t (bindValue d k)) =
      t.bind (fun _ => k.bind (fun _ => massValue (weightValue
        (some (fun x => massValue (weightValue t (k.bind (fun g => g x))))) d))) := by
  cases t with
  | none => rfl
  | some t =>
    cases k with
    | none => cases d <;> rfl
    | some k => exact mass_weight_bind d k t

/-- Changing the real output chart preserves every total scalar observation. -/
theorem GraphFibre.realBind_weight_total (d : Option (D α)) (k : Option (α → Option (D ℝ)))
    (t : ℝ → Option ℝ) (ht : ∀ y, Value.Defined (t y)) :
    massValue (weightValue (some t) (GraphFibre.realBindValue d k)) =
      massValue (weightValue (some t) (bindValue d k)) := by
  rw [mass_weight_test, mass_weight_test]
  choose f hf using ht
  rw [funext hf]
  exact GraphFibre.realBind_total d k f

end QSym.Distribution
