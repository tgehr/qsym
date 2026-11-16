import QSym.DistributionDensityModel

/-! A finite interval observation with a possibly partial parameter.
Pointwise equality to a strictly weighted interval is deliberately not required:
an Iverson mask can hide an undefined parameter outside its support. Instead,
the certificate checks totality when the parameter is defined, a point that
exposes its failure, and the integral's value on the defined domain.
-/
noncomputable section
namespace QSym.Distribution

structure ParametricIntervalCertificate (f : ℝ → Option ℝ) (c : Option ℝ)
    (a b witness : ℝ) (points : List ℝ) : Prop where
  ordered : a ≤ b
  total : Value.Defined c → ∀ x, Value.Defined (f x)
  away : ∀ r, c = some r → ∀ x, (∀ p ∈ points, x ≠ p) →
    f x = some (if a ≤ x ∧ x ≤ b then r else 0)
  at_witness : f witness = c

namespace ParametricIntervalCertificate

theorem defined_iff {f c a b w points} (h : ParametricIntervalCertificate f c a b w points) :
    (∀ x, Value.Defined (f x)) ↔ Value.Defined c := by
  constructor
  · intro hd
    simpa only [h.at_witness] using hd w
  · exact h.total

def specialize {f c a b w points} (h : ParametricIntervalCertificate f c a b w points)
    {r : ℝ} (hr : c = some r) : IntervalCertificate f a b r points where
  ordered := h.ordered
  total := h.total ⟨r, hr⟩
  away := h.away r hr

theorem integrate {f c a b w points} (h : ParametricIntervalCertificate f c a b w points) :
    partialIntegral MeasureTheory.volume f = Value.mul c (some (b - a)) := by
  cases hc : c with
  | some r => exact (h.specialize hc).integrate
  | none =>
    change partialIntegral _ f = none
    apply if_neg
    intro hd
    have := h.defined_iff.mp hd.1
    simp [hc, Value.Defined] at this

end ParametricIntervalCertificate

theorem DensityProgram.mass_parametric (p : DensityProgram) {c a b w points}
    (h : ParametricIntervalCertificate p.density c a b w points) :
    p.mass = Value.mul c (some (b - a)) := by
  rw [DensityProgram.mass, Model.densityMassValue_eq]
  exact h.integrate

end QSym.Distribution
