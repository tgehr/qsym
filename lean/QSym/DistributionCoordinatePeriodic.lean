import QSym.DistributionCoordinateInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid.VariationChange
open Set MeasureTheory Real

/-- An integral of a continuous periodic function needs just one cell and a
signed count of complete periods, including for endpoints below zero. -/
theorem periodic_primitive {g : ℝ → ℝ} {P : ℝ} (hP : 0 < P) (period : Function.Periodic g P)
    (hg : Continuous g) (cell : ℝ → ℝ) (hcell : ∀ u ∈ Icc 0 P, (∫ t in (0:ℝ)..u, g t) = cell u) (x : ℝ) :
    (∫ t in (0:ℝ)..x, g t) =
      (⌊x/P⌋ : ℤ) * cell P + cell (x - (⌊x/P⌋ : ℤ) * P) := by
  let m : ℤ := ⌊x/P⌋
  let u := x - (m:ℝ)*P
  have hlo : (m:ℝ)*P ≤ x := (le_div_iff₀ hP).mp (Int.floor_le _)
  have hhi : x < ((m:ℝ)+1)*P := (div_lt_iff₀ hP).mp (Int.lt_floor_add_one _)
  have hu : u ∈ Icc 0 P := by dsimp [u]; constructor <;> linarith
  have divided : u + m • P = x := by simp [u, zsmul_eq_mul]
  calc
    (∫ t in (0:ℝ)..x, g t) = (∫ t in (0:ℝ)..u, g t) + ∫ t in u..(u + m • P), g t := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _), divided]
    _ = cell u + (m:ℝ)*cell P := by
      rw [hcell u hu, period.intervalIntegral_add_zsmul_eq m u (fun a b => hg.intervalIntegrable a b),
        period.intervalIntegral_add_eq u 0, _root_.zero_add, hcell P ⟨hP.le, le_rfl⟩, zsmul_eq_mul]
    _ = _ := add_comm _ _

private def cosineVariation (x : ℝ) := (∫ t in (0:ℝ)..x, |Real.sin t|) - 1

private theorem cosineVariation_deriv (x : ℝ) : HasDerivAt cosineVariation |Real.sin x| x := by
  have h := Real.continuous_sin.abs
  exact (intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable 0 x)
    h.stronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt).sub_const 1

private theorem cosineVariation_smooth : ContDiff ℝ 1 cosineVariation :=
  contDiff_one_iff_deriv.mpr ⟨fun x => (cosineVariation_deriv x).differentiableAt,
    (show deriv cosineVariation = fun x => |Real.sin x| from funext fun x => (cosineVariation_deriv x).deriv) ▸
      Real.continuous_sin.abs⟩

private theorem cosineVariation_mono : Monotone cosineVariation :=
  monotone_of_hasDerivAt_nonneg cosineVariation_deriv (fun _ => abs_nonneg _)

private theorem cosineVariation_cell (x : ℝ) : cosineVariation x =
    2 * (⌊x/π⌋ : ℤ) - Real.cos (x - (⌊x/π⌋ : ℤ)*π) := by
  have period : Function.Periodic (fun t : ℝ => |Real.sin t|) π := fun u => by simp [Real.sin_add_pi]
  have cell (u : ℝ) (hu : u ∈ Icc 0 π) : (∫ t in (0:ℝ)..u, |Real.sin t|) = 1 - Real.cos u := by
    calc
      (∫ t in (0:ℝ)..u, |Real.sin t|) = ∫ t in (0:ℝ)..u, Real.sin t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hu.1] at ht
        exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (ht.2.trans hu.2))
      _ = _ := by simp [integral_cos, integral_sin]
  rw [cosineVariation, periodic_primitive Real.pi_pos period Real.continuous_sin.abs _ cell x]
  simp only [Real.cos_pi]
  ring

private def phase (sine : Bool) (v : Option ℝ) : Option ℝ :=
  if sine then Value.add v (Value.mul (some π) (Value.inv (some ((2:ℤ):ℝ)))) else v

/-- Unwrap the variation of a real cosine (or a sine shifted by a quarter
turn). Only ordinary scalar operations occur in the normalized expression. -/
def trigPrimitive (sine : Bool) (v : Option ℝ) : Option ℝ :=
  let u := phase sine v
  let cell := Functions.floorR.apply (Value.mul u (Value.inv (some π)))
  let k := Functions.castQR.apply (Functions.castZQ.apply cell)
  let minus := some ((-1:ℤ):ℝ)
  let parity := Functions.powRZ.apply minus cell
  let height := Value.mul parity (if sine then Functions.sinR.apply v else Functions.cosR.apply v)
  Value.add (Value.mul (some ((2:ℤ):ℝ)) k) (if sine then height else Value.mul minus height)

private theorem trigPrimitive_some (sine : Bool) (x : ℝ) :
    trigPrimitive sine (some x) = some (cosineVariation (if sine then x + π / 2 else x)) := by
  have cell (u : ℝ) : cosineVariation u = 2 * (⌊u/π⌋ : ℤ) - (-1 : ℝ)^⌊u/π⌋ * Real.cos u := by
    rw [cosineVariation_cell, Real.cos_sub_int_mul_pi]
  cases sine <;>
    simp [trigPrimitive, phase, Value.add, Value.mul, Value.inv, Real.pi_ne_zero,
      Functions.castQR, Functions.castZQ, Functions.floorR, Functions.powRZ, Function2.apply,
      Functions.cosR, Functions.sinR, Function1.apply, cell, Real.cos_add_pi_div_two, div_eq_mul_inv,
      sub_eq_add_neg]
  rw [← div_eq_mul_inv π 2, Real.cos_add_pi_div_two, mul_neg, neg_neg]


theorem cosine : VariationChange Real.cos cosineVariation Functions.cosR.apply (trigPrimitive false) := by
  refine ⟨Real.contDiff_cos, cosineVariation_smooth, cosineVariation_mono, ?_, ?_, trigPrimitive_some false⟩
  · intro x
    simp [(cosineVariation_deriv x).deriv, (Real.hasDerivAt_cos x).deriv]
  · intro x; simp [Functions.cosR, Function1.apply]

theorem sine : VariationChange Real.sin (fun x => cosineVariation (x + π/2)) Functions.sinR.apply (trigPrimitive true) := by
  refine ⟨Real.contDiff_sin, cosineVariation_smooth.comp (contDiff_id.add contDiff_const),
    cosineVariation_mono.comp (fun a b h => add_le_add_right h _), ?_, ?_, trigPrimitive_some true⟩
  · intro x
    have d := (cosineVariation_deriv (x + π/2)).comp x ((hasDerivAt_id x).add_const (π/2))
    simpa [Function.comp_def, Real.sin_add_pi_div_two, (Real.hasDerivAt_sin x).deriv] using d.deriv
  · intro x; simp [Functions.sinR, Function1.apply]

end QSym.Distribution.GraphFibre.Coordinates.Grid.VariationChange
