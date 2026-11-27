import QSym.DistributionInverseCover
import QSym.DistributionMissingPoint

noncomputable section
namespace QSym.Distribution.GraphFibre
open StepSource MeasureTheory

/-- A missing parameter output survives arbitrary target weights. It obstructs
both strict pairing and the real chart's pointwise density observer. -/
def MissingOutput (d : Option (D ℝ)) : Prop :=
  d = none ∨ ∃ w f, d = some (.density w f) ∧ MissingPoint f

namespace MissingOutput

private theorem density_none {f : ℝ → Option ℝ} (h : MissingPoint f)
    (w : ℝ → Option ℝ) (y : ℝ) : densityAt (.density w f) y = none := by
  obtain ⟨x, hx⟩ := h
  have hi : f ≠ some := fun e => by simp [e] at hx
  have nh : ¬ ∀ t, Value.Defined (f t) := fun all => by
    obtain ⟨_, hv⟩ := all x
    rw [hx] at hv
    cases hv
  simp [densityAt, realFibre, hi, RealDensityFibre.density, chartDensity, nh]

theorem pushforward (p : Option (ℝ → Option Bool)) {f : ℝ → Option ℝ}
    (h : MissingPoint f) : MissingOutput (pushforwardOnValue p (some f)) := by
  cases p with
  | none => exact Or.inl rfl
  | some pred => exact Or.inr ⟨_, f, rfl, h⟩

theorem realPushforward (p : Option (ℝ → Option Bool)) {f : ℝ → Option ℝ}
    (h : MissingPoint f) : MissingOutput (realPushforwardOnValue p (some f)) := by
  cases p with
  | none => exact Or.inl rfl
  | some pred =>
    refine Or.inr ⟨fun x => Value.mask (pred x) (some 1), f, ?_, h⟩
    exact congrArg some (coordinates_of_missing_density (density_none h _ 0))

theorem weight (v : Option (ℝ → Option ℝ)) {d} (h : MissingOutput d) :
    MissingOutput (weightValue v d) := by
  rcases h with rfl | ⟨w, f, rfl, hf⟩
  · exact Or.inl (by cases v <;> rfl)
  · cases v with
    | none => exact Or.inl rfl
    | some v => exact Or.inr ⟨_, f, rfl, hf⟩

theorem pairing {d} (h : MissingOutput d) (t : ℝ → Option ℝ) :
    d.bind (fun a => integrate a t) = none := by
  rcases h with rfl | ⟨w, f, rfl, x, hx⟩
  · rfl
  · change partialIntegral volume (fun r => Value.mul (w r) ((f r).bind t)) = none
    apply if_neg
    intro valid
    obtain ⟨v, hv⟩ := valid.1 x
    change Value.mul (w x) ((f x).bind t) = some v at hv
    rw [hx] at hv
    cases hw : w x <;> simp [hw, Value.mul] at hv

theorem mass {d} (h : MissingOutput d) : massValue d = none :=
  pairing h (fun _ => some 1)

theorem density {d} (h : MissingOutput d) (y : Option ℝ) : densityAtValue d y = none := by
  rcases h with rfl | ⟨w, f, rfl, hf⟩
  · rfl
  · cases y with
    | none => rfl
    | some y => exact density_none hf w y

private theorem empty_map {ι : Type} {g : ι → ℝ → Option ℝ} (h : ∀ i y, g i y = none) :
    inverseCoverOutput g = fun _ => none :=
  inverseCoverOutput_eq (fun x y => by simp [h])

/-- An empty inverse relation gives an everywhere-missing forward map. -/
theorem emptyCover {ι : Type} {g : ι → ℝ → Option ℝ} (h : ∀ i y, g i y = none) :
    MissingOutput (Coordinates.value (some g)) := by
  rw [Coordinates.of_gap (fun i => h i 0)]
  rw [inverseCover_eq (f := fun _ => (none : Option ℝ)) (fun x y => by simp [h])]
  exact realPushforward _ MissingPoint.bottom

theorem emptyPart (p : Option (ℝ → Option Bool)) {ι : Type} {g : ι → ℝ → Option ℝ}
    (h : ∀ i y, g i y = none) : MissingOutput (Coordinates.restricted p (some g)) := by
  rw [Coordinates.restricted_of_gap (fun i => h i 0)]
  change MissingOutput (pushforwardOnValue p (some (inverseCoverOutput g)))
  rw [empty_map h]
  exact pushforward _ MissingPoint.bottom

theorem singleton : MissingOutput (Coordinates.value
    (Tensor.consValue (some fun _ : ℝ => (none : Option ℝ)) Tensor.nilValue)) := by
  apply emptyCover
  intro i y
  fin_cases i
  rfl

theorem singletonPart (p : Option (ℝ → Option Bool)) : MissingOutput (Coordinates.restricted p
    (Tensor.consValue (some fun _ : ℝ => (none : Option ℝ)) Tensor.nilValue)) := by
  apply emptyPart
  intro i y
  fin_cases i
  rfl

end MissingOutput
end QSym.Distribution.GraphFibre
