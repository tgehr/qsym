import QSym.DistributionIntegral
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

end QSym.DistributionSourceTests
