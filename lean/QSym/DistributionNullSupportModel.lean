import QSym.DistributionDensityModel

/-! Zero mass does not imply that a strict observation is defined. These
certificates retain a finite set of pointwise domain tests, including points
of zero measure. The tests need not share a single witness or coefficient.
-/
noncomputable section
namespace QSym.Distribution
open Classical

theorem _root_.QSym.Value.mul_bind_const {α β : Type} [Mul α]
    (a b : Option α) (c : Option β) :
    (Value.mul a b).bind (fun _ => c) = a.bind (fun _ => b.bind (fun _ => c)) := by
  cases a <;> cases b <;> rfl

def zeroOnProbes (f : ℝ → Option ℝ) : List ℝ → Option ℝ
  | [] => some 0
  | x :: xs => (f x).bind (fun _ => zeroOnProbes f xs)

theorem zeroOnProbes_eq (f : ℝ → Option ℝ) (probes : List ℝ) :
    zeroOnProbes f probes =
      if ∀ x ∈ probes, Value.Defined (f x) then some 0 else none := by
  classical
  induction probes with
  | nil => simp [zeroOnProbes]
  | cons x xs ih => cases h : f x <;> simp [zeroOnProbes, h, ih, Value.Defined]

/-- The source proves that the finite probes detect every undefined point.
The almost-everywhere claim is used only after those probes have succeeded. -/
structure NullSupportCertificate (f : ℝ → Option ℝ) (probes points : List ℝ) : Prop where
  total : (∀ x ∈ probes, Value.Defined (f x)) → ∀ x, Value.Defined (f x)
  away : (∀ x ∈ probes, Value.Defined (f x)) →
    ∀ x, (∀ p ∈ points, x ≠ p) → f x = some 0

namespace NullSupportCertificate

theorem defined_iff {f probes points} (h : NullSupportCertificate f probes points) :
    (∀ x, Value.Defined (f x)) ↔ ∀ x ∈ probes, Value.Defined (f x) :=
  ⟨fun hf x _ => hf x, h.total⟩

def specialize {f probes points} (h : NullSupportCertificate f probes points)
    (hd : ∀ x ∈ probes, Value.Defined (f x)) : IntervalCertificate f 0 0 0 points where
  ordered := le_rfl
  total := h.total hd
  away := by simpa using h.away hd

theorem integrate {f probes points} (h : NullSupportCertificate f probes points) :
    partialIntegral MeasureTheory.volume f = zeroOnProbes f probes := by
  classical
  rw [zeroOnProbes_eq]
  split_ifs with hd
  · simpa using (h.specialize hd).integrate
  · apply if_neg
    intro hf
    exact hd (h.defined_iff.mp hf.1)

end NullSupportCertificate

theorem DensityProgram.mass_null_support (p : DensityProgram) {probes points}
    (h : NullSupportCertificate p.density probes points) :
    p.mass = zeroOnProbes p.density probes := by
  rw [DensityProgram.mass, Model.densityMassValue_eq]
  exact h.integrate

end QSym.Distribution
