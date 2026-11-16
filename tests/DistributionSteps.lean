import QSym.DistributionIntegral
import QSym.AxiomCheck

noncomputable section
namespace QSym.DistributionStepTests
open Distribution

def splitDensity (c d : Option ℝ) : DensityProgram := .weight
  (fun x => Value.add (Value.mask (Value.and (Value.lt (some 0) (some x)) (Value.lt (some x) (some 1))) c)
    (Value.mask (Value.and (Value.lt (some 1) (some x)) (Value.lt (some x) (some 2))) d)) .lebesgue

def cells : List StepCell := [⟨0, 1, 1/2⟩, ⟨1, 2, 3/2⟩]
def probes : List ℝ := [-1, 0, 1/2, 1, 3/2, 2, 3]

open StepSource
attribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv

private theorem affine0 : Affine (fun _ => some (0 : ℝ)) 0 0 := by
  exact affine_constant (some 0) 0 (by norm_num)
private theorem affine1 : Affine (fun _ => some (1 : ℝ)) 0 1 := by
  exact affine_constant (some 1) 1 (by norm_num)
private theorem affine2 : Affine (fun _ => some (2 : ℝ)) 0 2 := by
  exact affine_constant (some 2) 2 (by norm_num)

private theorem split_uniform (r : Region) (c d : Option ℝ) (s₀ s₁ s₂ s₃ : Sign)
    (hr : r.valid) (h₀ : signCheck r (-1) 0 s₀ = true)
    (h₁ : signCheck r 1 (-1) s₁ = true)
    (h₂ : signCheck r (-1) 1 s₂ = true)
    (h₃ : signCheck r 1 (-2) s₃ = true) : Uniform r (splitDensity c d).density :=
  uniform_binary Value.mul (uniform_const r (some 1))
    (uniform_binary Value.add
      (uniform_binary Value.mask
        (uniform_binary Value.and
          (uniform_lt (s := s₀) hr affine0 affine_variable h₀)
          (uniform_lt (s := s₁) hr affine_variable affine1 h₁)) (uniform_const r c))
      (uniform_binary Value.mask
        (uniform_binary Value.and
          (uniform_lt (s := s₂) hr affine1 affine_variable h₂)
          (uniform_lt (s := s₃) hr affine_variable affine2 h₃)) (uniform_const r d)))

def splitCertificate (c d : Option ℝ) :
    StepCertificate (splitDensity c d).density cells probes [0, 1, 2] := by
  have hl := split_uniform (.before 0) c d .positive .negative .positive .negative
    trivial rfl rfl rfl rfl
  have h₁ := split_uniform (.between 0 1) c d .negative .negative .positive .negative
    (of_decide_eq_true rfl) rfl rfl rfl rfl
  have h₂ := split_uniform (.between 1 2) c d .negative .positive .negative .negative
    (of_decide_eq_true rfl) rfl rfl rfl rfl
  have hr := split_uniform (.after 2) c d .negative .positive .negative .positive
    trivial rfl rfl rfl rfl
  have ht : Tail (splitDensity c d).density 0 [1, 2] :=
    .cons (of_decide_eq_true rfl) h₁ (.cons (of_decide_eq_true rfl) h₂ (.nil 2 hr))
  have zl : ZeroOrUndefined ((splitDensity c d).density (((0-1 : ℚ) : ℝ))) := by
    norm_num [splitDensity, DensityProgram.density, Value.lt, Value.and, Value.mask, Value.mul, Value.add, ZeroOrUndefined]
  have zr : ZeroOrUndefined ((splitDensity c d).density (lastProbe 0 [1, 2] : ℝ)) := by
    norm_num [lastProbe, splitDensity, DensityProgram.density, Value.lt, Value.and, Value.mask, Value.mul, Value.add, ZeroOrUndefined]
  convert grid_certificate hl ht zl zr using 1 <;>
    norm_num [gridCells, gridProbes, cells, probes]

theorem split_mass (c d : Option ℝ) : massValue (splitDensity c d).presentation =
    (zeroOnProbes (splitDensity c d).density probes).bind
      (fun _ => stepMass (splitDensity c d).density cells) := by
  rw [DensityProgram.mass_bridge]
  have h := splitCertificate c d
  qsym_rule

theorem split_defined_mass (r s : ℝ) : massValue (splitDensity (some r) (some s)).presentation = some (r + s) := by
  rw [split_mass]
  norm_num [splitDensity, cells, probes, zeroOnProbes, stepMass, DensityProgram.density, Value.lt, Value.and, Value.mask, Value.mul, Value.add]

theorem split_signed_mass : massValue (splitDensity (some (-3)) (some 2)).presentation = some (-1) := by
  convert split_defined_mass (-3) 2 using 1 <;> norm_num

theorem split_undefined_mass : massValue (splitDensity (some 0) none).presentation = none := by
  rw [split_mass]
  norm_num [splitDensity, cells, probes, zeroOnProbes, stepMass, DensityProgram.density, Value.lt, Value.and, Value.mask, Value.mul, Value.add]

theorem boundary_density_retained (r s : ℝ) : (splitDensity (some r) (some s)).observeAt 1 = some 0 := by
  norm_num [DensityProgram.observeAt_eq, splitDensity, DensityProgram.density, Value.lt, Value.and, Value.mask, Value.mul, Value.add]

theorem step_representation_not_pointwise :
    (splitDensity (some 1) (some 1)).density 1 ≠ some (stepValue (splitDensity (some 1) (some 1)).density cells 1) := by
  norm_num [splitDensity, cells, stepValue, DensityProgram.density, Value.lt, Value.and, Value.mask, Value.mul, Value.add]

theorem missing_boundary_rejected :
    ¬ StepCertificate (fun x : ℝ => if x = 1 then none else some 0)
      [⟨0, 2, 1/2⟩] [0, 1/2, 2] [1] := by
  intro h
  have hd : ∀ x ∈ ([0, 1/2, 2] : List ℝ), Value.Defined (if x = 1 then none else some (0 : ℝ)) := by
    simp only [List.forall_mem_cons, List.forall_mem_nil]
    norm_num [Value.Defined]
  have := h.total hd 1
  simp [Value.Defined] at this

theorem unbounded_tail_rejected :
    ¬ StepCertificate (fun _ : ℝ => some 1) [⟨0, 1, 1/2⟩] [1/2] [0, 1] := by
  intro h
  have := h.away (by simp [Value.Defined]) 2 (by norm_num)
  norm_num [stepValue] at this

theorem sample_domain_required (c : Option ℝ) :
    (∀ x, Value.Defined ((splitDensity c none).density x)) ↔ False := by
  constructor
  · intro h
    have := h (3/2)
    norm_num [splitDensity, DensityProgram.density, Value.lt, Value.and, Value.mask, Value.mul, Value.add, Value.Defined] at this
    obtain ⟨v, hv⟩ := this
    cases hv
  · exact False.elim

example (p : DensityProgram) : p.mass = p.mass := by
  fail_if_success
    have bad : p.mass = some 0 := by qsym_distribution
  rfl

-- Numeric witnesses preserve masks' short-circuit behavior and do not treat
-- unsupported or undefined values as successful numeric evaluations.
example : Numeric.calculate (.maskR (.bool false) (.invR (.real 0))) = some 0 := rfl
example : Numeric.calculate (.maskR (.bool true) (.invR (.real 0))) = none := rfl
example : Numeric.calculate (.not (.and (.bool true) (.bool false))) = some true := rfl
example : Numeric.calculate (.or (.bool false) (.bool true)) = some true := rfl
example : signCheck (.after 0) 1 0 .negative ≠ true := Bool.false_ne_true

#qsym_check_axioms Numeric.calculate_sound
#qsym_check_axioms StepSource.signCheck_sound
#qsym_check_axioms StepSource.KnownMass.value
#qsym_check_axioms DensityProgram.presentation_mass_grid_known
#qsym_check_axioms StepSource.grid_certificate
#qsym_check_axioms StepSource.grid_null_edit
#qsym_check_axioms DensityProgram.mass_grid
#qsym_check_axioms DensityProgram.presentation_mass_grid
#qsym_check_axioms DensityProgram.presentation_mass_grid_null_edit
#qsym_check_axioms step_integral
#qsym_check_axioms stepMass_eq
#qsym_check_axioms StepCertificate.defined_iff
#qsym_check_axioms StepCertificate.integrate
#qsym_check_axioms DensityProgram.mass_step
#qsym_check_axioms splitCertificate
#qsym_check_axioms split_mass
#qsym_check_axioms split_defined_mass
#qsym_check_axioms split_signed_mass
#qsym_check_axioms split_undefined_mass
#qsym_check_axioms boundary_density_retained
#qsym_check_axioms step_representation_not_pointwise
#qsym_check_axioms missing_boundary_rejected
#qsym_check_axioms unbounded_tail_rejected
#qsym_check_axioms sample_domain_required

end QSym.DistributionStepTests
