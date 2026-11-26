import QSym.DistributionPolynomialGrid
import QSym.DistributionModelBridge
import QSym.Binding

noncomputable section
namespace QSym.Distribution.StepSource
open MeasureTheory

/-- A missing source value supplies a witness against pointwise definedness. -/
def MissingPoint (f : ℝ → Option ℝ) := ∃ x, f x = none

theorem MissingPoint.bottom : MissingPoint (fun _ => none) := ⟨0, rfl⟩

theorem MissingPoint.mul_left {f} (g : ℝ → Option ℝ) (hf : MissingPoint f) :
    MissingPoint (fun x => Value.mul (f x) (g x)) := by
  obtain ⟨x, hx⟩ := hf
  exact ⟨x, by simp [hx, Value.mul]⟩

theorem MissingPoint.mul_right (f : ℝ → Option ℝ) {g} (hg : MissingPoint g) :
    MissingPoint (fun x => Value.mul (f x) (g x)) := by
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, by change Value.mul (f x) (g x) = none; rw [hx]; cases f x <;> rfl⟩

theorem MissingPoint.add_left {f} (g : ℝ → Option ℝ) (hf : MissingPoint f) :
    MissingPoint (fun x => Value.add (f x) (g x)) := by
  obtain ⟨x, hx⟩ := hf
  exact ⟨x, by simp [hx, Value.add]⟩

theorem MissingPoint.add_right (f : ℝ → Option ℝ) {g} (hg : MissingPoint g) :
    MissingPoint (fun x => Value.add (f x) (g x)) := by
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, by change Value.add (f x) (g x) = none; rw [hx]; cases f x <;> rfl⟩

theorem MissingPoint.guard (p : ℝ → Option Bool) {f} (hf : MissingPoint f) :
    MissingPoint (fun x => Binding.guardValue (p x) (f x)) := by
  obtain ⟨x, hx⟩ := hf
  exact ⟨x, by simp [hx, Binding.guardValue]⟩

namespace MissingPoint

/-- An ordinary real density, possibly missing as a distribution. -/
def IsDensity (d : Option (D ℝ)) : Prop := ∃ f, d = densityValue f

/-- A missing distribution or a real density missing at a source point. -/
def InDensity (d : Option (D ℝ)) : Prop :=
  ∃ f, d = densityValue f ∧ ∃ x, f.bind (fun w => w x) = none

private theorem weight_density (w f : Option (ℝ → Option ℝ)) :
    weightValue w (densityValue f) = densityValue (do
      let g ← f
      let h ← w
      pure (fun x => Value.mul (g x) (h x))) := by
  cases f <;> cases w <;> rfl

theorem IsDensity.lebesgue : IsDensity lebesgueValue := ⟨_, rfl⟩

theorem IsDensity.weight (w : Option (ℝ → Option ℝ)) {d} (hd : IsDensity d) : IsDensity (weightValue w d) := by
  obtain ⟨f, rfl⟩ := hd
  exact ⟨_, weight_density w f⟩

theorem InDensity.of_weight {d} (hd : IsDensity d) {w} (hw : MissingPoint w) :
    InDensity (weightValue (some w) d) := by
  obtain ⟨f, rfl⟩ := hd
  obtain ⟨x, hx⟩ := hw
  refine ⟨_, weight_density (some w) f, x, ?_⟩
  cases f with
  | none => rfl
  | some f =>
    change Value.mul (f x) (w x) = none
    rw [hx]; cases f x <;> rfl

theorem InDensity.weight (w : Option (ℝ → Option ℝ)) {d} (hd : InDensity d) : InDensity (weightValue w d) := by
  obtain ⟨f, rfl, x, hx⟩ := hd
  refine ⟨_, weight_density w f, x, ?_⟩
  cases f with
  | none => rfl
  | some f =>
    change f x = none at hx
    cases w with
    | none => rfl
    | some w =>
      change Value.mul (f x) (w x) = none
      rw [hx]; rfl

theorem InDensity.mass {d} (hd : InDensity d) : massValue d = none := by
  obtain ⟨f, rfl, x, hx⟩ := hd
  rw [density_mass_bridge, Model.densityMassValue_eq]
  cases f with
  | none => rfl
  | some f =>
    change f x = none at hx
    change partialIntegral volume f = none
    apply if_neg
    intro v
    obtain ⟨y, hy⟩ := v.1 x
    rw [hx] at hy
    cases hy

theorem mass (p : DensityProgram) (h : MissingPoint p.density) : massValue p.presentation = none :=
  InDensity.mass ⟨some p.density, p.presentation_eq, h⟩

end MissingPoint

theorem quadratic_source {f p} (c b a : ℚ) (src : PolynomialOn (fun _ => True) f p)
    (shape : polyZero (polyAdd p (polyScale (-1) [c, 2*b, a])) = true) (x : ℝ) :
    f x = some ((c : ℝ) + 2*b*x + a*x^2) := by
  rw [src.equation x trivial]
  have hz := polyEval_zero shape x
  rw [polyEval_add, polyEval_scale] at hz
  simp [polyEval] at hz
  congr 1
  linarith

theorem MissingPoint.quadratic {f p} (c b a : ℚ) (src : PolynomialOn (fun _ => True) f p)
    (shape : polyZero (polyAdd p (polyScale (-1) [c, 2*b, a])) = true)
    (root : decide ((a ≠ 0 ∨ b ≠ 0) ∧ a*c ≤ b^2) = true) :
    MissingPoint (fun x => Value.inv (f x)) := by
  obtain ⟨nonconst, disc⟩ := of_decide_eq_true root
  have h : 0 ≤ (b : ℝ)^2 - a*c := sub_nonneg.mpr (by exact_mod_cast disc)
  have zero : ∃ x : ℝ, (c : ℝ) + 2*b*x + a*x^2 = 0 := by
    by_cases ha : a = 0
    · have hb : (b : ℝ) ≠ 0 := by exact_mod_cast nonconst.resolve_left (not_not_intro ha)
      refine ⟨-(c : ℝ)/(2*b), ?_⟩
      simp [ha]
      field_simp [hb]
      ring
    · have hn : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      refine ⟨(√((b : ℝ)^2 - a*c)-b)/a, ?_⟩
      field_simp [hn]
      nlinarith [Real.sq_sqrt h]
  obtain ⟨x, hx⟩ := zero
  exact ⟨x, by change Value.inv (f x) = none; rw [quadratic_source c b a src shape x, hx]; simp [Value.inv]⟩

end QSym.Distribution.StepSource
