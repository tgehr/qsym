import QSym.DistributionCoordinateCorners

/-! A query of an unrestricted variation coordinate only needs its intrinsic
cuts and the regular derivative at the point. A jump contributes the distance
between the two traces, whereas a continuous corner has zero atomic charge. -/
noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.VariationChart
open Classical Set Filter Topology

private def cutFibre (g : ℝ → ℝ) (a : ℝ) : RealDensityFibre :=
  ⟨|Function.rightLim g a - Function.leftLim g a|,
    if Function.leftLim g a = Function.rightLim g a then none else some 0⟩

theorem atom_fibre (a k x : ℝ) : ∃ d, atom a (some k) = some d ∧
    realFibre d x = ⟨if x = a then k else 0, some 0⟩ := by
  by_cases hk : k = 1
  · subst k; refine ⟨.dirac a, by simp [atom, diracValue], ?_⟩
    rfl
  · refine ⟨.scale k (.dirac a), by simp [atom, hk, diracValue, scaleValue], ?_⟩
    by_cases hx : x = a <;> simp [realFibre, RealDensityFibre.scale, Value.mul, hx]

private theorem cut_fibre (g : ℝ → ℝ) (a x : ℝ) : ∃ d, atCut g a none = some d ∧
    realFibre d x = if x = a then cutFibre g x else ⟨0, some 0⟩ := by
  unfold atCut
  by_cases traces : Function.leftLim g a = Function.rightLim g a
  · rw [if_pos traces]
    obtain ⟨d, hd, probe⟩ := corner_components a
    refine ⟨d, hd, ?_⟩
    obtain ⟨charge, weight⟩ := probe x
    cases h : realFibre d x with
    | mk c w =>
      rw [h] at charge weight
      by_cases hx : x = a <;> simp_all [cutFibre]
  · rw [if_neg traces]
    obtain ⟨d, hd, probe⟩ := atom_fibre a |Function.rightLim g a - Function.leftLim g a| x
    refine ⟨d, hd, ?_⟩
    by_cases hx : x = a <;> simp_all [cutFibre]

private theorem zero_add_fibre (f : RealDensityFibre) : (RealDensityFibre.mk 0 (some 0)).add f = f := by
  rcases f with ⟨c, w⟩
  cases w <;> simp [RealDensityFibre.add, Value.add]

private theorem fold_fibre (g : ℝ → ℝ) (as : List ℝ) (unique : as.Nodup) (x : ℝ)
    (w : ℝ → Option ℝ) : ∃ d, as.foldr (fun a v => addValue (atCut g a none) v)
        (weightValue (some w) lebesgueValue) = some d ∧
    realFibre d x = if x ∈ as then (cutFibre g x).add ⟨0, w x⟩ else ⟨0, w x⟩ := by
  induction as with
  | nil =>
    exact ⟨.density w some, by simp [weightValue, weight, lebesgueValue, densityValue, Value.mul_one_left],
      by simp [realFibre]⟩
  | cons a as ih =>
    obtain ⟨before, hb, eb⟩ := ih (List.nodup_cons.mp unique).2
    obtain ⟨atA, ha, ea⟩ := cut_fibre g a x
    refine ⟨.add atA before, by rw [List.foldr_cons, ha, hb]; rfl, ?_⟩
    change (realFibre atA x).add (realFibre before x) = _
    rw [ea, eb]
    by_cases hx : x = a
    · subst x
      simp [(List.nodup_cons.mp unique).1]
    · simp [hx, zero_add_fibre]

private theorem present_fibre (c : VariationChart) (x : ℝ) : ∃ d, c.present none = some d ∧
    realFibre d x = if x ∈ c.cuts then (cutFibre c.coord x).add ⟨0, some |deriv c.coord x|⟩
      else ⟨0, some |deriv c.coord x|⟩ :=
  fold_fibre _ _ c.sorted.nodup _ _

/-- The unguarded coordinate has precisely its jump lengths as atom weights. -/
theorem charge_present (c : VariationChart) (x : ℝ) :
    (c.present none).map (fun d => (realFibre d x).charge) =
      some (if x ∈ c.cuts then |Function.rightLim c.coord x - Function.leftLim c.coord x| else 0) := by
  obtain ⟨d, hd, hf⟩ := present_fibre c x
  by_cases hx : x ∈ c.cuts <;> simp [hd, hf, hx, cutFibre, RealDensityFibre.add]

/-- Density is missing at every intrinsic cut, even when its point mass is zero. -/
theorem density_present (c : VariationChart) (x : ℝ) :
    densityAtValue (c.present none) (some x) =
      if x ∈ c.cuts then none else some |deriv c.coord x| := by
  obtain ⟨d, hd, hf⟩ := present_fibre c x
  rw [hd]
  change (realFibre d x).density = _
  rw [hf]
  by_cases hx : x ∈ c.cuts
  · by_cases h : Function.leftLim c.coord x = Function.rightLim c.coord x
    · simp [hx, cutFibre, h, RealDensityFibre.add, RealDensityFibre.density, Value.add]
    · simp [hx, cutFibre, h, sub_ne_zero.mpr (Ne.symm h), RealDensityFibre.add, RealDensityFibre.density]
  · simp [hx, RealDensityFibre.density]

end QSym.Distribution.GraphFibre.Coordinates.VariationChart

namespace QSym.Distribution.GraphFibre.Coordinates
open Classical

theorem density_pieces {ι : Type} {gs : ι → ℝ → Option ℝ} {c : VariationChart}
    (display : Displays gs c) (x : ℝ) :
    densityAtValue (value (some gs)) (some x) =
      if x ∈ c.cuts then none else some |deriv c.coord x| := by
  rw [pieces_eq display, c.density_present]

end QSym.Distribution.GraphFibre.Coordinates
