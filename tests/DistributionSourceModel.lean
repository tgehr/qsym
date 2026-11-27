import QSym.DistributionIntegral
import QSym.DistributionMissingPoint
import QSym.DistributionModelBridge
import QSym.DistributionMaskedRootCover
import QSym.DistributionBindObservation
import QSym.DistributionTestScale
import QSym.DistributionQuadraticBand
import QSym.DistributionPushforwardObservation
import QSym.DistributionRootIntervalSource
import QSym.AxiomCheck

noncomputable section
namespace QSym.DistributionSourceTests
open MeasureTheory Distribution
open scoped ProbabilityTheory

theorem generic_interval (T : DensityIntegralTheory) (f : ℝ → Option ℝ)
    (a b c : ℝ) (points : List ℝ) (h : IntervalCertificate f a b c points) :
    T.mass f = some (c * (b - a)) := by qsym_rule

theorem generic_null_edit (T : DensityIntegralTheory) (f g : ℝ → Option ℝ)
    (points : List ℝ) (h : NullEditCertificate f g points) : T.mass f = T.mass g := by qsym_rule

theorem legacy_integral : partialIntegral volume
    (fun x : ℝ => some (if 0 ≤ x ∧ x ≤ 2 then (3 : ℝ) else 0)) = some 6 :=
  qsym_integral% [] (fun x : ℝ => some (if 0 ≤ x ∧ x ≤ 2 then (3 : ℝ) else 0)) 0 2 3 []

theorem legacy_ae : partialIntegral volume (fun x : ℝ => some (if x = 0 then 0 else (1 : ℝ))) =
    partialIntegral volume (fun _ : ℝ => some (1 : ℝ)) :=
  qsym_integral_ae% [] (fun x : ℝ => some (if x = 0 then 0 else (1 : ℝ)))
    (fun _ : ℝ => some (1 : ℝ)) [0]

def punctured : DensityProgram :=
  .weight (fun x => some (if -1 ≤ x ∧ x ≤ 1 then (-3 : ℝ) else 0))
    (.weight (fun x => some (if x ≠ 0 then (1 : ℝ) else 0)) .lebesgue)

def puncturedCertificate : IntervalCertificate punctured.density (-1) 1 (-3) [0] :=
  qsym_interval_certificate% [punctured] punctured.density (-1) 1 (-3) [0]

theorem signed_mass : massValue punctured.presentation = some (-6) :=
  qsym_density_integral% [punctured] punctured (-1) 1 (-3) [0]

theorem signed_variation : (∫ x, |(punctured.density x).getD 0|) = 6 := by
  have h := puncturedCertificate.variation
  norm_num at h
  exact h

theorem punctured_point : punctured.observeAt 0 = some 0 := by
  simp [DensityProgram.observeAt_eq, punctured, DensityProgram.density, Value.mul]

def puncturedLebesgue : DensityProgram :=
  .weight (fun x => some (if x ≠ 0 then (1 : ℝ) else 0)) .lebesgue

theorem scalar_null_edit : massValue puncturedLebesgue.presentation = massValue DensityProgram.lebesgue.presentation :=
  qsym_density_integral_ae% [puncturedLebesgue] puncturedLebesgue DensityProgram.lebesgue [0]

theorem density_null_edit_forbidden : puncturedLebesgue.observeAt 0 ≠ DensityProgram.lebesgue.observeAt 0 := by
  simp [DensityProgram.observeAt_eq, puncturedLebesgue, DensityProgram.density, Value.mul]

def hole : DensityProgram := .weight (fun x => if x = 0 then none else some (1 : ℝ)) .lebesgue

theorem hole_not_certified (a b c : ℝ) (points : List ℝ) :
    ¬ IntervalCertificate hole.density a b c points := by
  intro h
  have hd := h.total 0
  simp [hole, DensityProgram.density, Value.mul, Value.Defined] at hd

theorem hole_mass : hole.mass = none := by
  rw [DensityProgram.mass, Model.densityMassValue_eq]
  change partialIntegral volume hole.density = none
  apply if_neg
  intro h
  have hd := h.1 0
  simp [hole, DensityProgram.density, Value.mul, Value.Defined] at hd

-- Rule search must not manufacture a certificate, nor use a scalar null edit
-- to rewrite a pointwise density. The finishing equality uses the parameters.
example (p : DensityProgram) : p.mass = p.mass := by
  fail_if_success
    have bad : p.mass = some 0 := by qsym_distribution
  rfl

theorem wrong_interval_not_certified : ¬ IntervalCertificate punctured.density (-1) 1 17 [0] := by
  intro h
  have he := h.integrate
  rw [puncturedCertificate.integrate] at he
  norm_num at he

-- Source-shaped row certificates with genuinely varying bounds and signs.
-- Their absolute profiles discharge the joint capability compositionally.
abbrev twoAtoms : Measure Bool := Measure.dirac false + Measure.dirac true
def upper (b : Bool) : ℝ := if b then 2 else 1
def coefficient (b : Bool) : ℝ := if b then 3 else -2
def rows (p : Bool × ℝ) : Option ℝ :=
  some (if 0 ≤ p.2 ∧ p.2 ≤ upper p.1 then coefficient p.1 else 0)

def rowCertificate (b : Bool) : IntervalCertificate (fun y => rows (b, y)) 0
    (upper b) (coefficient b) [] where
  ordered := by cases b <;> norm_num [upper]
  total := fun _ => ⟨_, rfl⟩
  away := fun _ _ => rfl

theorem rows_capability : IntegrableEveryRow (ProbabilityTheory.Kernel.const Bool volume) rows :=
  IntervalCertificate.rows rowCertificate

theorem rows_measurable : Measurable (fun p => (rows p).getD 0) := by
  have hb : Measurable (fun p : Bool × ℝ => upper p.1) :=
    (measurable_of_finite upper).comp measurable_fst
  have hc : Measurable (fun p : Bool × ℝ => coefficient p.1) :=
    (measurable_of_finite coefficient).comp measurable_fst
  exact hc.ite ((measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd hb)) measurable_const

theorem joint_capability : Integrable (fun p => (rows p).getD 0)
    (twoAtoms ⊗ₘ ProbabilityTheory.Kernel.const Bool volume) := by
  apply IntervalCertificate.joint_integrable twoAtoms rowCertificate rows_measurable.aestronglyMeasurable
  simp [twoAtoms]

theorem dependent_source_mass : partialIntegral (twoAtoms ⊗ₘ ProbabilityTheory.Kernel.const Bool volume)
    rows = some 4 := by
  have hr := rows_capability
  have hi := joint_capability
  have h : partialIntegral (twoAtoms ⊗ₘ ProbabilityTheory.Kernel.const Bool volume) rows =
      partialIntegral twoAtoms (fun b => partialIntegral volume (fun y => rows (b, y))) := by qsym_rule
  rw [h]
  simp_rw [(rowCertificate _).integrate]
  norm_num [partialIntegral, Value.Defined, twoAtoms, upper, coefficient, integral_add_measure]

def interval : DensityProgram :=
  .weight (fun x => some (if 0 ≤ x ∧ x ≤ 2 then (1 : ℝ) else 0)) .lebesgue

def parameter (c : Option ℝ) : DensityProgram := .weight (fun _ => c) interval

theorem parameter_mass (c : Option ℝ) :
    massValue (parameter c).presentation = Value.mul c (some 2) :=
  qsym_density_factor% [parameter, interval] (parameter c) interval c 0 2 1 []

theorem parameter_point (c : Option ℝ) : (parameter c).observeAt 1 = c := by
  simp [DensityProgram.observeAt_eq, parameter, interval, DensityProgram.density,
    Value.mul_one_left]

theorem ordered_bind (p : DensityProgram) (k : ℝ → Option (D (ℕ → ℕ))) :
    massValue (bindValue p.presentation (some k)) =
      massValue (weightValue (some (fun x => massValue (k x))) p.presentation) :=
  model_mass_bind_density p k

theorem ordered_integral (k : ℝ → Option (D (D ℝ))) :
    massValue (integralValue (some k)) =
      massValue (weightValue (some (fun x => massValue (k x))) lebesgueValue) :=
  model_mass_integralValue k

theorem unbounded_inner : DensityProgram.lebesgue.mass = none := DensityProgram.lebesgue_mass

def zeroDensity : DensityProgram := .weight (fun _ => some 0) .lebesgue

theorem zero_density_mass : zeroDensity.mass = some 0 := by
  simp [DensityProgram.mass, Model.densityMassValue_eq, zeroDensity,
    DensityProgram.density, Value.mul, partialIntegral_zero]

theorem factoring_requires_finiteness :
    zeroDensity.mass ≠ Value.mul (some 0) DensityProgram.lebesgue.mass := by
  rw [zero_density_mass, unbounded_inner]
  simp [Value.mul]

def maskedParameter (c : Option ℝ) : DensityProgram :=
  .weight (fun x => Value.mask (some (decide (0 ≤ x ∧ x ≤ 2))) c) .lebesgue

def maskedCertificate (c : Option ℝ) :
    ParametricIntervalCertificate (maskedParameter c).density c 0 2 1 [] :=
  qsym_parametric_certificate% [maskedParameter] (maskedParameter c).density c 0 2 1 [] [c]

theorem masked_parameter_mass (c : Option ℝ) :
    massValue (maskedParameter c).presentation = Value.mul c (some 2) :=
  qsym_density_parametric% [maskedParameter] (maskedParameter c) c 0 2 1 [] [c]

def booleanMask (p : Option Bool) : DensityProgram :=
  .weight (fun x => Value.mask (some (decide (0 ≤ x ∧ x ≤ 2)))
    (Value.mask p (some (-3)))) .lebesgue

theorem boolean_mask_mass (p : Option Bool) :
    massValue (booleanMask p).presentation = Value.mul (Value.mask p (some (-3))) (some 2) :=
  qsym_density_parametric% [booleanMask] (booleanMask p) (Value.mask p (some (-3))) 0 2 1 [] [p]

def outerBooleanMask (p : Option Bool) : DensityProgram :=
  .weight (fun x => Value.mask p
    (Value.mask (some (decide (0 ≤ x ∧ x ≤ 2))) (some (-3)))) .lebesgue

theorem outer_boolean_mask_mass (p : Option Bool) :
    massValue (outerBooleanMask p).presentation = Value.mul (Value.mask p (some (-3))) (some 2) :=
  qsym_density_parametric% [outerBooleanMask] (outerBooleanMask p) (Value.mask p (some (-3))) 0 2 1 [] [p]

theorem masked_parameter_domain (c : Option ℝ) :
    (∀ x, Value.Defined ((maskedParameter c).density x)) ↔ Value.Defined c :=
  (maskedCertificate c).defined_iff

theorem masked_parameter_not_strict_density :
    (maskedParameter none).observeAt 3 ≠ Value.mul none (interval.observeAt 3) := by
  norm_num [DensityProgram.observeAt_eq, maskedParameter, DensityProgram.density, Value.mask, Value.mul]
  exact fun h => Option.noConfusion h

theorem empty_support_cannot_expose_failure (w : ℝ) (points : List ℝ) :
    ¬ ParametricIntervalCertificate (fun _ => some 0) none 0 0 w points := by
  intro h
  have := h.at_witness
  cases this

theorem masked_parameter_variation (r : ℝ) :
    (∫ x, |((maskedParameter (some r)).density x).getD 0|) = |r| * 2 := by
  simpa using ((maskedCertificate (some r)).specialize rfl).variation

def maskedBranch (p : Option Bool) (c : Option ℝ) : DensityProgram :=
  .weight (fun x => Value.mask p (Value.mask (some (decide (0 ≤ x ∧ x ≤ 2))) c)) .lebesgue

theorem masked_partial_branch (p : Option Bool) (c : Option ℝ) :
    massValue (maskedBranch p c).presentation = Value.mul (Value.mask p c) (some 2) :=
  qsym_density_parametric% [maskedBranch] (maskedBranch p c) (Value.mask p c) 0 2 1 [] [p, c]

theorem false_mask_hides_partial_branch : massValue (maskedBranch (some false) none).presentation = some 0 := by
  rw [masked_partial_branch]
  simp [Value.mask, Value.mul]

theorem null_hole_not_certified (w : ℝ) (points : List ℝ) :
    ¬ ParametricIntervalCertificate (fun x => if x = 0 then none else some 1)
      (some 1) (-1) 1 w points := by
  intro h
  have := h.total ⟨1, rfl⟩ 0
  simp [Value.Defined] at this

def singletonParameter (c : Option ℝ) : DensityProgram :=
  .weight (fun x => Value.mask (some (decide (x = 0))) c) .lebesgue

def singletonCertificate (c : Option ℝ) :
    NullSupportCertificate (singletonParameter c).density [-1, 0, 1] [0] :=
  qsym_null_support_certificate% [singletonParameter] (singletonParameter c).density [-1, 0, 1] [0] [c]

theorem singleton_mass (c : Option ℝ) : massValue (singletonParameter c).presentation =
    zeroOnProbes (singletonParameter c).density [-1, 0, 1] :=
  qsym_density_null_support% [singletonParameter] (singletonParameter c) [-1, 0, 1] [0] [c]

theorem singleton_defined_mass (r : ℝ) : massValue (singletonParameter (some r)).presentation = some 0 := by
  rw [singleton_mass]
  norm_num [zeroOnProbes, singletonParameter, DensityProgram.density, Value.mask, Value.mul]

theorem singleton_undefined_mass : massValue (singletonParameter none).presentation = none := by
  rw [singleton_mass]
  norm_num [zeroOnProbes, singletonParameter, DensityProgram.density, Value.mask, Value.mul]

theorem singleton_retains_density (c : Option ℝ) : (singletonParameter c).observeAt 0 = c := by
  simp [DensityProgram.observeAt_eq, singletonParameter, DensityProgram.density,
    Value.mask, Value.mul_one_left]

def disjointParameters (c d : Option ℝ) : DensityProgram :=
  .weight (fun x => Value.mask (some (decide (x = 1))) d) (singletonParameter c)

def disjointCertificate (c d : Option ℝ) :
    NullSupportCertificate (disjointParameters c d).density [-1, 0, 1/2, 1, 2] [0, 1] :=
  qsym_null_support_certificate% [disjointParameters, singletonParameter]
    (disjointParameters c d).density [-1, 0, 1/2, 1, 2] [0, 1] [c, d]

theorem disjoint_defined_iff (c d : Option ℝ) :
    (∀ x, Value.Defined ((disjointParameters c d).density x)) ↔
      Value.Defined c ∧ Value.Defined d := by
  rw [(disjointCertificate c d).defined_iff]
  simp only [List.forall_mem_cons, List.forall_mem_nil]
  cases c <;> cases d <;>
    norm_num [disjointParameters, singletonParameter, DensityProgram.density, Value.mask, Value.mul, Value.Defined]

theorem disjoint_undefined_mass : (disjointParameters (some 0) none).mass = none := by
  have h := disjointCertificate (some 0) none
  have he : (disjointParameters (some 0) none).mass =
      zeroOnProbes (disjointParameters (some 0) none).density [-1, 0, 1/2, 1, 2] := by qsym_rule
  rw [he]
  norm_num [zeroOnProbes, disjointParameters, singletonParameter, DensityProgram.density, Value.mask, Value.mul]

def emptyParameter (c : Option ℝ) : DensityProgram :=
  .weight (fun x => Value.mask (some (decide (x < 0)))
    (Value.mask (some (decide (1 < x))) c)) .lebesgue

theorem empty_parameter_mass (c : Option ℝ) : massValue (emptyParameter c).presentation = some 0 :=
  qsym_density_null_support% [emptyParameter] (emptyParameter c) [-1, 0, 1/2, 1, 2] [0, 1] [c]

theorem missing_null_probe_rejected :
    ¬ NullSupportCertificate (singletonParameter none).density [-1, 1] [0] := by
  intro h
  have hd : ∀ x ∈ ([-1, 1] : List ℝ), Value.Defined ((singletonParameter none).density x) := by
    norm_num [singletonParameter, DensityProgram.density, Value.mask, Value.mul, Value.Defined]
  have := h.total hd 0
  simp [singletonParameter, DensityProgram.density, Value.mask, Value.mul, Value.Defined] at this

-- Boundary probes alone miss a failure throughout an open cell.
theorem missing_cell_probe_rejected :
    ¬ NullSupportCertificate
      (fun x : ℝ => Value.mask (some (decide (0 < x ∧ x < 1))) (none : Option ℝ))
      [0, 1] [0, 1] := by
  intro h
  have hd : ∀ x ∈ ([0, 1] : List ℝ),
      Value.Defined (Value.mask (some (decide (0 < x ∧ x < 1))) (none : Option ℝ)) := by
    simp only [List.forall_mem_cons, List.forall_mem_nil]
    norm_num [Value.mask, Value.Defined]
  have := h.total hd (1/2)
  norm_num [Value.mask, Value.Defined] at this
  obtain ⟨v, hv⟩ := this
  cases hv

-- Ordered composition must not use the flattened zero integrand to hide an
-- infinite row, even though the outer density is everywhere zero.
theorem zero_does_not_hide_infinite_row :
    massValue (bindValue zeroDensity.presentation (some (fun _ => DensityProgram.lebesgue.presentation))) = none := by
  rw [DensityProgram.bind_mass_bridge]
  simp only [DensityProgram.mass_bridge, unbounded_inner, DensityProgram.observe,
    Model.densityMassValue_eq, zeroDensity, DensityProgram.density, Value.mul]
  simp [partialIntegral, Value.Defined]

-- Failure of one row at a null point also remains visible to the outer
-- integral; the pointwise requirement is stronger than almost-everywhere L1.
theorem null_row_is_not_erased :
    interval.observe (fun x => if x = 0 then none else some 1) = none := by
  rw [DensityProgram.observe, Model.densityMassValue_eq]
  change partialIntegral volume _ = none
  apply if_neg
  intro h
  have hd := h.1 0
  simp [Value.mul, Value.Defined] at hd

-- The rule prover may use a supplied finite-observation capability, but must
-- not invent one just because a factor is zero.
example (p : DensityProgram) : p.mass = p.mass := by
  fail_if_success
    have bad : (DensityProgram.weight (fun _ => some 0) p).mass = Value.mul (some 0) p.mass := by
      qsym_distribution
  rfl

#qsym_check_axioms IntervalCertificate.integrate
#qsym_check_axioms IntervalCertificate.integrable
#qsym_check_axioms IntervalCertificate.integral_value
#qsym_check_axioms IntervalCertificate.absolute
#qsym_check_axioms IntervalCertificate.variation
#qsym_check_axioms IntervalCertificate.rows
#qsym_check_axioms IntervalCertificate.joint_integrable
#qsym_check_axioms DensityProgram.presentation_eq
#qsym_check_axioms DensityProgram.mass_bridge
#qsym_check_axioms DensityProgram.observeAt_bridge
#qsym_check_axioms densityIntegralTheory
#qsym_check_axioms DensityProgram.mass_interval
#qsym_check_axioms DensityProgram.mass_null_edit
#qsym_check_axioms generic_interval
#qsym_check_axioms generic_null_edit
#qsym_check_axioms legacy_integral
#qsym_check_axioms legacy_ae
#qsym_check_axioms puncturedCertificate
#qsym_check_axioms signed_mass
#qsym_check_axioms signed_variation
#qsym_check_axioms punctured_point
#qsym_check_axioms scalar_null_edit
#qsym_check_axioms density_null_edit_forbidden
#qsym_check_axioms hole_not_certified
#qsym_check_axioms hole_mass
#qsym_check_axioms wrong_interval_not_certified
#qsym_check_axioms rowCertificate
#qsym_check_axioms rows_capability
#qsym_check_axioms rows_measurable
#qsym_check_axioms joint_capability
#qsym_check_axioms dependent_source_mass
#qsym_check_axioms Value.mul_assoc
#qsym_check_axioms Value.mul_comm
#qsym_check_axioms Value.mul_left_comm
#qsym_check_axioms DensityProgram.mass_factor
#qsym_check_axioms DensityProgram.observe_weight
#qsym_check_axioms DensityProgram.bind_mass_bridge
#qsym_check_axioms DensityProgram.integral_mass_bridge
#qsym_check_axioms model_mass_bind_density
#qsym_check_axioms model_mass_integralValue
#qsym_check_axioms parameter_mass
#qsym_check_axioms parameter_point
#qsym_check_axioms ordered_bind
#qsym_check_axioms ordered_integral
#qsym_check_axioms unbounded_inner
#qsym_check_axioms mass_lebesgue
#qsym_check_axioms zero_density_mass
#qsym_check_axioms factoring_requires_finiteness
#qsym_check_axioms ParametricIntervalCertificate.defined_iff
#qsym_check_axioms ParametricIntervalCertificate.specialize
#qsym_check_axioms ParametricIntervalCertificate.integrate
#qsym_check_axioms DensityProgram.mass_parametric
#qsym_check_axioms maskedCertificate
#qsym_check_axioms masked_parameter_mass
#qsym_check_axioms boolean_mask_mass
#qsym_check_axioms outer_boolean_mask_mass
#qsym_check_axioms masked_parameter_domain
#qsym_check_axioms masked_parameter_not_strict_density
#qsym_check_axioms empty_support_cannot_expose_failure
#qsym_check_axioms masked_parameter_variation
#qsym_check_axioms masked_partial_branch
#qsym_check_axioms false_mask_hides_partial_branch
#qsym_check_axioms null_hole_not_certified
#qsym_check_axioms zeroOnProbes_eq
#qsym_check_axioms Value.mul_bind_const
#qsym_check_axioms NullSupportCertificate.defined_iff
#qsym_check_axioms NullSupportCertificate.specialize
#qsym_check_axioms NullSupportCertificate.integrate
#qsym_check_axioms DensityProgram.mass_null_support
#qsym_check_axioms singletonCertificate
#qsym_check_axioms singleton_mass
#qsym_check_axioms singleton_defined_mass
#qsym_check_axioms singleton_undefined_mass
#qsym_check_axioms singleton_retains_density
#qsym_check_axioms disjointCertificate
#qsym_check_axioms disjoint_defined_iff
#qsym_check_axioms disjoint_undefined_mass
#qsym_check_axioms empty_parameter_mass
#qsym_check_axioms missing_null_probe_rejected
#qsym_check_axioms missing_cell_probe_rejected
#qsym_check_axioms zero_does_not_hide_infinite_row
#qsym_check_axioms null_row_is_not_erased

theorem empty_fibre_skips_missing_test :
    FiniteFibre.pairing (FiniteFibre.ofRows ([] : List (ℝ × ℝ))) (fun _ => none) = some 0 := by
  rw [FiniteFibre.pairing_rows]; rfl

theorem zero_weight_visits_point (x : ℝ) :
    FiniteFibre.pairing (FiniteFibre.ofRows [(x,0)]) (fun _ => none) = none := by
  rw [FiniteFibre.pairing_rows]; rfl

theorem cancelled_point_density (x w : ℝ) :
    FiniteFibre.density (FiniteFibre.ofRows [(x,w),(x,-w)]) x = some 0 := by
  simp [FiniteFibre.density, FiniteFibre.pairing_rows, Value.mul, Value.add]

theorem charged_point_density (x w : ℝ) (hw : w ≠ 0) :
    FiniteFibre.density (FiniteFibre.ofRows [(x,w)]) x = none := by
  simp [FiniteFibre.density, FiniteFibre.pairing_rows, Value.mul, Value.add, hw]

#qsym_check_axioms empty_fibre_skips_missing_test
#qsym_check_axioms zero_weight_visits_point
#qsym_check_axioms cancelled_point_density
#qsym_check_axioms charged_point_density
#qsym_check_axioms GraphFibre.RootCover.finite_model
#qsym_check_axioms GraphFibre.RootCover.masked_model
#qsym_check_axioms GraphFibre.RootCover.masked_mass
#qsym_check_axioms integrate_weight
#qsym_check_axioms mass_weight_push
#qsym_check_axioms mass_weight_push_values
#qsym_check_axioms GraphFibre.mass_weight_real_push_total
#qsym_check_axioms mass_weight_test
#qsym_check_axioms mass_two_weights
#qsym_check_axioms mass_weight_pair
#qsym_check_axioms FiniteFibre.Represents.weighted_mass
#qsym_check_axioms integrate_bind
#qsym_check_axioms mass_bind_test
#qsym_check_axioms mass_bind_kernel
#qsym_check_axioms FiniteFibre.Represents.bind_mass
#qsym_check_axioms mass_weight_bind
#qsym_check_axioms mass_weight_bind_values
#qsym_check_axioms GraphFibre.realBind_weight_total
#qsym_check_axioms integrate_scale_test
#qsym_check_axioms mass_weight_one
#qsym_check_axioms mass_weight_constant
#qsym_check_axioms GraphFibre.Coordinates.Quadratic.weighted_integral
#qsym_check_axioms GraphFibre.Coordinates.Quadratic.masked_chart
#qsym_check_axioms GraphFibre.Coordinates.Quadratic.masked_chart_source
#qsym_check_axioms GraphFibre.Coordinates.Quadratic.band_chart
#qsym_check_axioms GraphFibre.Coordinates.Quadratic.target_band_chart
/-- A finite edit at the singular endpoint retains its scalar integral. -/
theorem inverse_root_endpoint_edit :
    partialIntegral volume (fun y : ℝ => some (if y = 1 then 7 else
      if 0 < y ∧ y < 1 then -3 / √(1-y) else 0)) = some (-6:ℝ) := by
  calc
    _ = some ((2*(-3)/(-1:ℝ))*(√(-1*1+1)-√(-1*0+1))) := by
      apply RootInterval.integral (-1) 1 0 1 (-3) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) _ [1] (fun y => ⟨_,rfl⟩)
      intro y away
      simp [away 1 (by simp), sub_eq_add_neg, add_comm]
    _ = _ := by norm_num

#qsym_check_axioms RootInterval.Term.inverse
#qsym_check_axioms RootInterval.Term.left
#qsym_check_axioms RootInterval.Term.right
#qsym_check_axioms RootInterval.mass
#qsym_check_axioms RootInterval.mass_missing
#qsym_check_axioms RootInterval.exact_result
#qsym_check_axioms StepSource.MissingPoint.unary
#qsym_check_axioms Binding.mask_guard_implication
#qsym_check_axioms StepSource.MissingPoint.guard_false_at
#qsym_check_axioms StepSource.MissingPoint.affine_preimage
#qsym_check_axioms StepSource.MissingPoint.sqrt_negative_one
#qsym_check_axioms RootInterval.integral
#qsym_check_axioms inverse_root_endpoint_edit

end QSym.DistributionSourceTests
