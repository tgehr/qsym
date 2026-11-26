import QSym.DistributionCoordinateCorners

/-! The mass of a finite variation chart splits into lengths traversed at
jumps and the ordinary integral of the regular Jacobian. -/
noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.VariationChart
open Set Filter Topology

/-- Total length traversed at a jump. This vanishes at a continuous corner. -/
def jumpLength (g : ℝ → ℝ) (a : ℝ) := |Function.rightLim g a - Function.leftLim g a|

theorem mass_corner (a : ℝ) : massValue (corner a (some true)) = some 0 := by
  unfold corner
  rw [realPushforward_mass_total]
  have selected (x : ℝ) : Value.mask (if x = 0 then some true else some false) (some (1:ℝ)) =
      some (if x = 0 then 1 else 0) := by split <;> rfl
  simp only [Option.map_some, Int.cast_one]
  change massValue (weightValue (some fun x : ℝ => Value.mask
    (if x = 0 then some true else some false) (some (1:ℝ))) lebesgueValue) = some 0
  rw [funext selected]
  change partialIntegral MeasureTheory.volume (fun x : ℝ => some (((1:ℝ) * (if x = 0 then 1 else 0)) * 1)) = _
  rw [partialIntegral_congr_away _ (fun _ => some (0:ℝ)) [0] (fun _ => ⟨_,rfl⟩) (fun _ => ⟨_,rfl⟩)
    (fun x hx => by simp [hx 0 (by simp)])]
  simp [partialIntegral, Value.Defined]

theorem mass_atom (a : ℝ) (w : Option ℝ) : massValue (atom a w) = w := by
  by_cases h : w = some 1
  · subst w; simp [atom, mass_diracValue]
  · simp [atom, h, mass_scaleValue, mass_diracValue, Value.mul_one_right]

theorem mass_atCut (g : ℝ → ℝ) (a : ℝ) : massValue (atCut g a none) = some (jumpLength g a) := by
  by_cases h : Function.leftLim g a = Function.rightLim g a
  · simp [atCut, jumpLength, h, mass_corner]
  · simp [atCut, jumpLength, h, mass_atom]

private theorem mass_fold (g : ℝ → ℝ) (as : List ℝ) (z : Option (D ℝ)) :
    massValue (as.foldr (fun a d => addValue (atCut g a none) d) z) =
      Value.add (some (as.map (jumpLength g)).sum) (massValue z) := by
  induction as with
  | nil => cases h : massValue z <;> simp [h, Value.add]
  | cons a as ih =>
    rw [List.foldr_cons, mass_addValue, mass_atCut, ih]
    cases h : massValue z <;> simp [h, Value.add, add_assoc]

/-- The unguarded mass is the sum of all transformed jump lengths and the
ordinary mass of the absolute derivative. Divergence of that last term is retained. -/
theorem mass_present (c : VariationChart) :
    massValue (c.present none) = Value.add (some (c.cuts.map (jumpLength c.coord)).sum)
      (massValue (weightValue (some fun x => some |deriv c.coord x|) lebesgueValue)) :=
  mass_fold _ _ _

theorem mass_flat (c : VariationChart) (flat : ∀ x, deriv c.coord x = 0) :
    massValue (c.present none) = some (c.cuts.map (jumpLength c.coord)).sum := by
  rw [mass_present]
  simp only [flat, abs_zero]
  have hz : massValue (weightValue (some fun _ : ℝ => some 0) lebesgueValue) = some 0 := by
    change partialIntegral MeasureTheory.volume (fun _ : ℝ => some ((1 * (0 : ℝ)) * 1)) = _
    simp [partialIntegral, Value.Defined]
  simp [hz, Value.add]

end QSym.Distribution.GraphFibre.Coordinates.VariationChart
