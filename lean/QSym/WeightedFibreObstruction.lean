import QSym.WeightedMarginal

/-! A globally measure-preserving parameter bijection need not preserve
pointwise fibre densities. Thus the quotient in `WeightedParameterSpace` cannot
admit an observer satisfying the unrestricted coordinate-projection rule.
This does not contradict its already-proved, bijective density-chart laws.
-/
noncomputable section
namespace QSym.WeightedParameter.FibreObstruction
open MeasureTheory Set

abbrev plane : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)

def box (a b x : ℝ) : ℝ := if a ≤ x ∧ x ≤ b then 1 else 0

theorem box_integrable (a b : ℝ) : Integrable (box a b) volume := by
  have hf : box a b = (Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext x; simp [box, Set.indicator, Set.mem_Icc]
  rw [hf]
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact integrableOn_const.mpr (Or.inr (by simp [Real.volume_Icc]))

theorem box_integral (a b : ℝ) (hab : a ≤ b) : (∫ y, box a b y) = b - a := by
  have hf : box a b = (Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext x; simp [box, Set.indicator, Set.mem_Icc]
  rw [hf]
  simp [integral_indicator_const, Real.volume_real_Icc_of_le hab]

/-- Double the latent parameter only on the output fibre `x = 0`. -/
def nullScale : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toEquiv :=
    { toFun := fun z => (z.1, if z.1 = 0 then 2 * z.2 else z.2)
      invFun := fun z => (z.1, if z.1 = 0 then (1 / 2) * z.2 else z.2)
      left_inv := by rintro ⟨x, y⟩; by_cases hx : x = 0 <;> simp [hx, ← mul_assoc]
      right_inv := by rintro ⟨x, y⟩; by_cases hx : x = 0 <;> simp [hx, ← mul_assoc] }
  measurable_toFun := measurable_fst.prodMk
    (Measurable.ite (measurable_fst (measurableSet_singleton 0))
      (measurable_const.mul measurable_snd) measurable_snd)
  measurable_invFun := measurable_fst.prodMk
    (Measurable.ite (measurable_fst (measurableSet_singleton 0))
      (measurable_const.mul measurable_snd) measurable_snd)

theorem nullScale_ae : (fun z => nullScale z) =ᵐ[plane] (fun z : ℝ × ℝ => z) := by
  have h0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  have h := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).ae h0
  filter_upwards [h] with z hz
  change (z.1, if z.1 = 0 then 2 * z.2 else z.2) = z
  simp [hz]

theorem nullScale_preserving :
    MeasurePreserving nullScale (plane) (plane) where
  measurable := nullScale.measurable
  map_eq := (Measure.map_congr nullScale_ae).trans Measure.map_id

def original : ParamKernel PUnit.{1} ℝ where
  space := ParameterSpace.real.prod ParameterSpace.real
  body := ⟨fun _ z => box (-1) 1 z.1 * box 0 1 z.2, fun _ z => z.1⟩

def rescaled : ParamKernel PUnit.{1} ℝ where
  space := ParameterSpace.real.prod ParameterSpace.real
  body := Kernel.pull nullScale.toEquiv original.body

def rescaledIso : ParamKernel.Iso rescaled original where
  coord := nullScale
  preserving := nullScale_preserving
  weight := fun _ _ => rfl
  value := fun _ _ => rfl

theorem same_quotient : Hom.ofKernel rescaled = Hom.ofKernel original :=
  Quotient.sound ⟨rescaledIso⟩

theorem original_integrable : Integrable (original.body.weight PUnit.unit) (plane) :=
  (box_integrable (-1) 1).mul_prod (box_integrable 0 1)

theorem rescaled_integrable : Integrable (rescaled.body.weight PUnit.unit) (plane) :=
  (nullScale_preserving.integrable_comp_emb nullScale.measurableEmbedding).mpr original_integrable

theorem original_mass :
    Kernel.integrate (plane) original.body PUnit.unit (fun _ => 1) = some 2 := by
  change finiteIntegral plane (fun z : ℝ × ℝ => (box (-1) 1 z.1 * box 0 1 z.2) * 1) = some 2
  simp only [mul_one]
  have hi : Integrable (fun z : ℝ × ℝ => box (-1) 1 z.1 * box 0 1 z.2) plane :=
    (box_integrable (-1) 1).mul_prod (box_integrable 0 1)
  rw [finiteIntegral, if_pos hi]
  rw [integral_prod_mul, box_integral (-1) 1 (by norm_num), box_integral 0 1 (by norm_num)]
  norm_num

theorem rescaled_mass :
    Kernel.integrate (plane) rescaled.body PUnit.unit (fun _ => 1) = some 2 := by
  exact (rescaledIso.observe_eq PUnit.unit (fun _ => 1)).trans original_mass

theorem original_fibre_zero :
    (∫ y : ℝ, original.body.weight PUnit.unit ((0 : ℝ), y)) = 1 := by
  simpa [original, box] using box_integral 0 1 (by norm_num)

theorem box_double (y : ℝ) : box 0 1 (2 * y) = box 0 (1 / 2) y := by
  have h : (0 ≤ 2 * y ∧ 2 * y ≤ 1) ↔ (0 ≤ y ∧ y ≤ 1 / 2) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [box, h]

theorem rescaled_fibre_zero :
    (∫ y : ℝ, rescaled.body.weight PUnit.unit ((0 : ℝ), y)) = 1 / 2 := by
  have h0 : box (-1) 1 0 = 1 := by norm_num [box]
  have hr : (fun y : ℝ => rescaled.body.weight PUnit.unit ((0 : ℝ), y)) = box 0 (1 / 2) := by
    funext y
    simp [rescaled, Kernel.pull, original, nullScale, box_double, h0]
  rw [hr]
  have h := box_integral 0 (1 / 2) (by norm_num)
  norm_num at h
  exact h

theorem original_rows :
    Fibre.IntegrableRows volume (fun x y : ℝ => original.body.weight PUnit.unit (x, y)) :=
  Fibre.rows_separable (box (-1) 1) (box_integrable 0 1)

theorem rescaled_row (x y : ℝ) :
    rescaled.body.weight PUnit.unit (x, y) =
      if x = 0 then box 0 (1 / 2) y else box (-1) 1 x * box 0 1 y := by
  have h0 : box (-1) 1 0 = 1 := by norm_num [box]
  by_cases hx : x = 0 <;> simp [rescaled, Kernel.pull, original, nullScale, hx, h0, box_double]

theorem rescaled_rows :
    Fibre.IntegrableRows volume (fun x y : ℝ => rescaled.body.weight PUnit.unit (x, y)) := by
  constructor
  intro x
  simp_rw [rescaled_row]
  by_cases hx : x = 0
  · simpa only [if_pos hx] using box_integrable 0 (1 / 2)
  · simpa only [if_neg hx] using (box_integrable 0 1).const_mul (box (-1) 1 x)

theorem original_nonnegative (z : ℝ × ℝ) : 0 ≤ original.body.weight PUnit.unit z := by
  have hn (a b t : ℝ) : 0 ≤ box a b t := by unfold box; split_ifs <;> norm_num
  exact mul_nonneg (hn _ _ _) (hn _ _ _)

theorem rescaled_nonnegative (z : ℝ × ℝ) : 0 ≤ rescaled.body.weight PUnit.unit z :=
  original_nonnegative (nullScale z)

/-- No function on the existing quotient can recover both of these pointwise
coordinate-fibre integrals, even for nonnegative, jointly integrable weights. -/
theorem no_quotient_fibre_observer :
    ¬ ∃ d : Trace ℝ → ℝ,
      d (Hom.ofKernel original) = (∫ y : ℝ, original.body.weight PUnit.unit ((0 : ℝ), y)) ∧
      d (Hom.ofKernel rescaled) = (∫ y : ℝ, rescaled.body.weight PUnit.unit ((0 : ℝ), y)) := by
  rintro ⟨d, hp, hq⟩
  rw [original_fibre_zero] at hp
  rw [same_quotient, rescaled_fibre_zero, hp] at hq
  norm_num at hq

end QSym.WeightedParameter.FibreObstruction
