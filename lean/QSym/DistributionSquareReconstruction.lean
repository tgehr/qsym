import QSym.DistributionMaskedGraph
import QSym.DistributionSquareIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set

/-- Integrate the two regular branches as a pair, so signed cancellation
cannot hide failure of integrability. At zero only the original source
observation's definedness is needed. The pointwise kernel is untouched. -/
def squareReconstructionRows (critical : Option ℝ) (kernel : ℝ → Option (D ℝ))
    (h : ℝ → ℝ → Option ℝ) (y : ℝ) : Option (ℝ × ℝ) :=
  if 0 < y then do
    let d ← kernel y
    let neg ← integrate d (fun x => if x < 0 then h x y else some 0)
    let pos ← integrate d (fun x => if 0 < x then h x y else some 0)
    return (neg, pos)
  else if y = 0 then critical.map (fun _ => 0) else some 0

private def inverseRows (g : ℝ → Option ℝ) (y : ℝ) : Option (ℝ × ℝ) :=
  if 0 < y then do
    let neg ← g (-√y)
    let pos ← g (√y)
    return (jac y * neg, jac y * pos)
  else if y = 0 then (g 0).map (fun _ => 0) else some 0

private theorem inverseRows_domain (g : ℝ → Option ℝ) :
    (∀ y, Value.Defined (inverseRows g y)) ↔ ∀ x, Value.Defined (g x) := by
  have regular (y : ℝ) (hy : 0 < y) : Value.Defined (inverseRows g y) ↔
      Value.Defined (g (-√y)) ∧ Value.Defined (g (√y)) := by
    cases hn : g (-√y) <;> cases hp : g (√y) <;> simp [inverseRows, hy, hn, hp, Value.Defined]
  have critical : Value.Defined (inverseRows g 0) ↔ Value.Defined (g 0) := by
    cases h : g 0 <;> simp [inverseRows, h, Value.Defined]
  constructor
  · intro hd x
    rcases lt_trichotomy x 0 with hn | rfl | hp
    · have h := ((regular (x^2) (sq_pos_of_ne_zero hn.ne)).mp (hd _)).1
      simpa only [Real.sqrt_sq_eq_abs, abs_of_neg hn, neg_neg] using h
    · exact critical.mp (hd _)
    · simpa only [Real.sqrt_sq hp.le] using ((regular (x^2) (sq_pos_of_pos hp)).mp (hd _)).2
  · intro hd y
    rcases lt_trichotomy y 0 with hn | rfl | hp
    · simp [inverseRows, not_lt_of_gt hn, hn.ne, Value.Defined]
    · exact critical.mpr (hd _)
    · exact (regular y hp).mpr ⟨hd _, hd _⟩

private theorem inverseRows_getD (g : ℝ → Option ℝ) (hd : ∀ x, Value.Defined (g x)) :
    (fun y => (inverseRows g y).getD 0) =
      (Ioi 0).indicator (fun y => (jac y * (g (-√y)).getD 0, jac y * (g (√y)).getD 0)) := by
  funext y
  by_cases hy : 0 < y
  · obtain ⟨a, ha⟩ := hd (-√y)
    obtain ⟨b, hb⟩ := hd (√y)
    simp [inverseRows, hy, indicator, mem_Ioi, ha, hb]
  · obtain ⟨a, ha⟩ := hd 0
    simp [inverseRows, hy, indicator, mem_Ioi, ha]

private theorem integrable_reflect (f : ℝ → ℝ) :
    IntegrableOn f (Iic 0) ↔ IntegrableOn (fun x => f (-x)) (Ioi 0) := by
  conv_lhs => rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  have m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
  rw [m.integrableOn_map_iff]
  simpa only [neg_preimage, neg_Iic, neg_zero, Function.comp_def] using
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun x => f (-x)) (b := (0 : ℝ)) (μ := volume))

private theorem inverseRows_integral (g : ℝ → Option ℝ) :
    partialIntegral volume g =
      (partialIntegral volume (inverseRows g)).map (fun v => v.1 + v.2) := by
  classical
  by_cases hd : ∀ x, Value.Defined (g x)
  · let f := fun x => (g x).getD 0
    let neg := fun y => jac y * f (-√y)
    let pos := fun y => jac y * f (√y)
    have row : (fun y => (inverseRows g y).getD 0) = (Ioi 0).indicator (fun y => (neg y, pos y)) :=
      inverseRows_getD g hd
    obtain ⟨hn, en⟩ := sqrt_changeOfVariables (fun x => f (-x))
    obtain ⟨hp, ep⟩ := sqrt_changeOfVariables f
    have branches : Integrable f ↔ IntegrableOn neg (Ioi 0) ∧ IntegrableOn pos (Ioi 0) := by
      rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union, integrable_reflect, hn, hp]
    have hi : Integrable f ↔ Integrable ((Ioi 0).indicator (fun y => (neg y, pos y))) := by
      rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn, integrable_prod]
      exact branches
    rw [partialIntegral, partialIntegral]
    simp only [hd, (inverseRows_domain g).mpr hd, row, implies_true, true_and]
    change (if Integrable f then _ else _) = _
    by_cases hf : Integrable f
    · rw [if_pos hf, if_pos (hi.mp hf), integral_indicator measurableSet_Ioi,
        integral_pair (branches.mp hf).1 (branches.mp hf).2]
      apply congrArg some
      change (∫ x, f x) = (∫ y in Ioi 0, neg y) + ∫ y in Ioi 0, pos y
      rw [← en, ← ep, integral_comp_neg_Ioi, neg_zero]
      exact (intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn).symm
    · rw [if_neg hf, if_neg (mt hi.mpr hf)]
      rfl
  · simp [partialIntegral, hd, mt (inverseRows_domain g).mp hd]

/-- A total source integrand reconstructs as a pair over the regular square
branches. The value at the single critical source has zero integral. -/
theorem square_pair_integral (g : ℝ → ℝ) :
    partialIntegral volume (fun x => some (g x)) =
      (partialIntegral volume (fun y => some (if 0 < y then
        (jac y * g (-√y), jac y * g (√y)) else (0, 0)))).map (fun v => v.1 + v.2) := by
  rw [inverseRows_integral]
  congr 2
  funext y
  by_cases hp : 0 < y <;> simp [inverseRows, hp]

private theorem masked_inverse_rows (p : ℝ → Option Bool) (h : ℝ → ℝ → Option ℝ) :
    inverseRows (fun x => Value.mul (Value.mask (p x) (some 1)) (h x (square x))) =
      squareReconstructionRows (Value.mul (Value.mask (p 0) (some 1)) (h 0 0))
        (fun y => (maskedKernel (some p) (some fun x => some (square x))).bind (fun k => k y)) h := by
  rw [maskedKernel_total p square (measurable_id.pow_const 2)]
  funext y
  by_cases hy : 0 < y
  · have hs := Real.sqrt_pos.mpr hy
    simp only [inverseRows, squareReconstructionRows, if_pos hy, Option.some_bind,
      masked_square_positive p hy, square, neg_sq, Real.sq_sqrt hy.le]
    cases hn : p (-√y) <;> cases hp : p (√y) <;> (repeat' casesm Bool) <;>
      cases ha : h (-√y) y <;> cases hb : h (√y) y <;>
      simp [presentation, integrate, hs, not_lt_of_gt hs, ha, hb, Value.mul, Value.add, Value.mask]
  · simp [inverseRows, squareReconstructionRows, hy, square]

/-- Exact reconstruction through the same pointwise kernel used by the
frontend. Both the mask and the joint test may be partial. -/
theorem masked_square_disintegrates (p : ℝ → Option Bool) (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mul (Value.mask (p x) (some 1)) (h x (square x))) =
      (partialIntegral volume (squareReconstructionRows
        (Value.mul (Value.mask (p 0) (some 1)) (h 0 0))
        (fun y => (maskedKernel (some p) (some fun x => some (square x))).bind (fun k => k y))
        h)).map (fun v => v.1 + v.2) := by
  rw [inverseRows_integral, masked_inverse_rows]

/-- Summing before integrating is sound as a refinement. Opposite,
nonintegrable coordinates can give a defined scalar integral. -/
private theorem integral_sum_refines (rows : ℝ → Option (ℝ × ℝ)) :
    Value.Refines ((partialIntegral volume rows).map (fun v => v.1 + v.2))
      (partialIntegral volume (fun y => (rows y).map (fun v => v.1 + v.2))) := by
  intro v hv
  cases hr : partialIntegral volume rows with
  | none => simp [hr] at hv
  | some z =>
    obtain ⟨hd, hi⟩ := (partialIntegral_defined_iff volume rows).mp ⟨z, hr⟩
    let f := fun y => (rows y).getD 0
    have hpair := integrable_prod.mp hi
    have total (y : ℝ) : Value.Defined ((rows y).map (fun t => t.1 + t.2)) := by
      obtain ⟨r, h⟩ := hd y
      exact ⟨r.1 + r.2, by simp [h]⟩
    have body : (fun y => ((rows y).map (fun t => t.1 + t.2)).getD 0) =
        fun y => (f y).1 + (f y).2 := by
      funext y
      obtain ⟨r, h⟩ := hd y
      simp [f, h]
    have eqz : (∫ y, f y) = z :=
      Option.some.inj ((partialIntegral_valid volume rows hd hi).symm.trans hr)
    rw [show (∫ y, f y) = (_, _) from integral_pair hpair.1 hpair.2] at eqz
    rw [partialIntegral, if_pos ⟨total, body ▸ hpair.1.add hpair.2⟩, body,
      integral_add hpair.1 hpair.2]
    simpa only [hr, Option.map_some, ← eqz] using hv

/-- The scalar form visits the same pointwise kernel on regular targets.
At the critical value the source supplies only a definedness check. -/
def squareRegularTest (critical : Option ℝ) (kernel : ℝ → Option (D ℝ))
    (h : ℝ → ℝ → Option ℝ) (y : ℝ) : Option ℝ :=
  if y = 0 then critical.map (fun _ => 0)
  else (kernel y).bind (fun d => integrate d (fun x => h x y))

private theorem sum_square_rows (p : ℝ → Option Bool) (h : ℝ → ℝ → Option ℝ) :
    (fun y => (squareReconstructionRows (Value.mul (Value.mask (p 0) (some 1)) (h 0 0))
      (fun y => (maskedKernel (some p) (some fun x => some (square x))).bind (fun k => k y)) h y).map
      (fun v => v.1 + v.2)) =
    squareRegularTest (Value.mul (Value.mask (p 0) (some 1)) (h 0 0))
      (fun y => (maskedKernel (some p) (some fun x => some (square x))).bind (fun k => k y)) h := by
  rw [maskedKernel_total p square (measurable_id.pow_const 2)]
  funext y
  rcases lt_trichotomy y 0 with hn | rfl | hp
  · simp [squareRegularTest, squareReconstructionRows, masked_square_negative p hn,
      not_lt_of_gt hn, hn.ne, presentation, integrate]
  · cases Value.mul (Value.mask (p 0) (some 1)) (h 0 0) <;>
      simp [squareRegularTest, squareReconstructionRows]
  · have hs := Real.sqrt_pos.mpr hp
    simp only [squareRegularTest, squareReconstructionRows, if_pos hp, if_neg hp.ne',
      Option.some_bind, masked_square_positive p hp]
    cases hn : p (-√y) <;> cases hpos : p (√y) <;> try rfl
    cases ha : h (-√y) y <;> cases hb : h (√y) y <;>
      simp [presentation, integrate, hs, not_lt_of_gt hs, ha, hb, Value.add, Value.mul]

theorem masked_square_regular_refines (p : ℝ → Option Bool) (h : ℝ → ℝ → Option ℝ) :
    Value.Refines
      (partialIntegral volume (fun x => Value.mul (Value.mask (p x) (some 1)) (h x (square x))))
      (partialIntegral volume (squareRegularTest (Value.mul (Value.mask (p 0) (some 1)) (h 0 0))
        (fun y => (maskedKernel (some p) (some fun x => some (square x))).bind (fun k => k y)) h)) := by
  rw [masked_square_disintegrates, ← sum_square_rows]
  exact integral_sum_refines _

/-- One integrable source half suffices to rule out hidden cancellation in
the scalar reconstruction. No totality or L¹ certificate is required on the
other half. -/
theorem masked_square_regular_eq (p : ℝ → Option Bool) (h : ℝ → ℝ → Option ℝ)
    (half : let f := fun x => (Value.mul (Value.mask (p x) (some 1)) (h x (square x))).getD 0
            IntegrableOn f (Iic 0) ∨ IntegrableOn f (Ioi 0)) :
    partialIntegral volume (fun x => Value.mul (Value.mask (p x) (some 1)) (h x (square x))) =
      partialIntegral volume (squareRegularTest (Value.mul (Value.mask (p 0) (some 1)) (h 0 0))
        (fun y => (maskedKernel (some p) (some fun x => some (square x))).bind (fun k => k y)) h) := by
  apply (masked_square_regular_refines p h).antisymm
  intro v hv
  rw [← sum_square_rows, ← masked_inverse_rows] at hv
  let g := fun x => Value.mul (Value.mask (p x) (some 1)) (h x (square x))
  let f := fun x => (g x).getD 0
  obtain ⟨hd, hi⟩ := (partialIntegral_defined_iff _ _).mp ⟨v, hv⟩
  have rowsTotal (y : ℝ) : Value.Defined (inverseRows g y) := by
    obtain ⟨z, hz⟩ := hd y
    cases hr : inverseRows g y with
    | none => change (inverseRows g y).map _ = some z at hz; simp [hr] at hz
    | some r => exact ⟨_, rfl⟩
  have rowValue := inverseRows_getD g ((inverseRows_domain g).mp rowsTotal)
  let neg := fun y => jac y * f (-√y)
  let pos := fun y => jac y * f (√y)
  have sum : (fun y => ((inverseRows g y).map (fun r => r.1 + r.2)).getD 0) =
      (Ioi 0).indicator (fun y => neg y + pos y) := by
    funext y
    obtain ⟨r, hr⟩ := rowsTotal y
    have eq := congrFun rowValue y
    by_cases hy : y ∈ Ioi (0 : ℝ) <;> simp [hr, Set.indicator, hy] at eq ⊢
    · rw [eq]
    · simp [eq]
  change Integrable (fun y => ((inverseRows g y).map (fun r => r.1 + r.2)).getD 0) at hi
  rw [sum, integrable_indicator_iff measurableSet_Ioi] at hi
  have both : IntegrableOn neg (Ioi 0) ∧ IntegrableOn pos (Ioi 0) := by
    rcases half with hn | hp
    · have hneg : IntegrableOn neg (Ioi 0) :=
        (sqrt_changeOfVariables (fun x => f (-x))).1.mp ((integrable_reflect f).mp hn)
      exact ⟨hneg, by simpa only [Pi.sub_def, add_sub_cancel_left] using hi.sub hneg⟩
    · have hpos : IntegrableOn pos (Ioi 0) := (sqrt_changeOfVariables f).1.mp hp
      exact ⟨by simpa only [Pi.sub_def, add_sub_cancel_right] using hi.sub hpos, hpos⟩
  have hrows : Integrable (fun y => (inverseRows g y).getD 0) := by
    rw [rowValue, integrable_indicator_iff measurableSet_Ioi]
    exact both.1.prodMk both.2
  obtain ⟨z, hz⟩ := (partialIntegral_defined_iff _ _).mpr ⟨rowsTotal, hrows⟩
  rw [inverseRows_integral]
  exact ((integral_sum_refines (inverseRows g)).eq_of_defined
    ⟨z.1 + z.2, by simp [hz]⟩).trans hv

end QSym.Distribution.GraphFibre
