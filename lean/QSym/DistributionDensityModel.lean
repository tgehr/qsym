import QSym.Distribution
import QSym.DistributionModelLaws
import QSym.DistributionIntegralCertificate

/-! A source fragment with a proved interpretation in the reference-aware
model. A density program retains every point of its partial weight function.
Its presentation interpretation is only a compatibility boundary for the
current frontend. Integral certificates apply to observations of the program,
not to equality of programs or pointwise densities.
-/
noncomputable section
namespace QSym.Distribution

/-- The currently recognized source fragment: a real Lebesgue reference and
any finite chain of possibly partial weight functions. -/
inductive DensityProgram where
  | lebesgue
  | weight : (ℝ → Option ℝ) → DensityProgram → DensityProgram

namespace DensityProgram

def density : DensityProgram → ℝ → Option ℝ
  | .lebesgue => fun _ => some 1
  | .weight f p => fun x => Value.mul (p.density x) (f x)

def presentation : DensityProgram → Option (D ℝ)
  | .lebesgue => lebesgueValue
  | .weight f p => weightValue (some f) p.presentation

def mass (p : DensityProgram) : Option ℝ := Model.densityMassValue (some p.density)

def observeAt (p : DensityProgram) (x : ℝ) : Option ℝ :=
  Model.densityTestValue (some p.density) (some x)

theorem presentation_eq (p : DensityProgram) :
    p.presentation = densityValue (some p.density) := by
  induction p with
  | lebesgue => rfl
  | weight f p ih =>
    simp only [presentation, ih, weightValue, densityValue, Distribution.weight, Option.bind_some, Option.map_some]
    rfl

/-- A representation theorem for this source fragment, including all partial
weights. It does not require the eventual mass observation to be defined. -/
theorem mass_bridge (p : DensityProgram) : massValue p.presentation = p.mass := by
  rw [presentation_eq]
  unfold mass
  rw [Model.densityMassValue_eq]
  change partialIntegral _ (fun x => Value.mul (p.density x) (some 1)) = partialIntegral _ p.density
  simp only [Value.mul_one_right]

theorem observeAt_eq (p : DensityProgram) (x : ℝ) : p.observeAt x = p.density x := by
  exact Model.densityTestValue_eq _ _

theorem observeAt_bridge (p : DensityProgram) (x : ℝ) :
    densityAtValue p.presentation (some x) = p.observeAt x := by
  rw [presentation_eq, observeAt_eq]
  exact densityAt_density p.density x

end DensityProgram

/-- A replaceable observation interface. Implementations must prove both
laws on their model; certificates never add global axioms. -/
structure DensityIntegralTheory where
  mass : (ℝ → Option ℝ) → Option ℝ
  interval : ∀ f a b c points, IntervalCertificate f a b c points →
    mass f = some (c * (b - a))
  null_edit : ∀ f g points, NullEditCertificate f g points → mass f = mass g

def densityIntegralTheory : DensityIntegralTheory where
  mass := fun f => Model.densityMassValue (some f)
  interval := by
    intro f a b c points h
    rw [Model.densityMassValue_eq]
    exact h.integrate
  null_edit := by
    intro f g points h
    simp only [Model.densityMassValue_eq, Option.bind_some]
    exact partialIntegral_congr_away f g points h.source_total h.target_total h.away

theorem DensityProgram.mass_interval (p : DensityProgram) {a b c : ℝ} {points : List ℝ}
    (h : IntervalCertificate p.density a b c points) : p.mass = some (c * (b - a)) :=
  densityIntegralTheory.interval p.density a b c points h

theorem DensityProgram.mass_null_edit (p q : DensityProgram) {points : List ℝ}
    (h : NullEditCertificate p.density q.density points) : p.mass = q.mass :=
  densityIntegralTheory.null_edit p.density q.density points h

end QSym.Distribution
