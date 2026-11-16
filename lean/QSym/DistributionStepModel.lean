import QSym.DistributionNullSupportModel

/-! Finite step-function observations. The sampled interval values determine
the integral, while a separate finite list of probes checks the pointwise
domain, including boundaries of measure zero. No density is replaced by its
almost-everywhere step representation. -/
noncomputable section
namespace QSym.Distribution
open MeasureTheory
open Classical

structure StepCell where
  lower : ℝ
  upper : ℝ
  sample : ℝ

def stepValue (f : ℝ → Option ℝ) : List StepCell → ℝ → ℝ
  | [] => fun _ => 0
  | c :: cs => fun x =>
      (if c.lower ≤ x ∧ x ≤ c.upper then (f c.sample).getD 0 else 0) + stepValue f cs x

def stepTotal (f : ℝ → Option ℝ) : List StepCell → ℝ
  | [] => 0
  | c :: cs => (f c.sample).getD 0 * (c.upper - c.lower) + stepTotal f cs

def stepMass (f : ℝ → Option ℝ) : List StepCell → Option ℝ
  | [] => some 0
  | c :: cs => Value.add (Value.mul (f c.sample) (some (c.upper - c.lower))) (stepMass f cs)

theorem step_integral (f : ℝ → Option ℝ) (cells : List StepCell)
    (ho : ∀ c ∈ cells, c.lower ≤ c.upper) :
    Integrable (stepValue f cells) volume ∧ (∫ x, stepValue f cells x) = stepTotal f cells := by
  induction cells with
  | nil => simp [stepValue, stepTotal]
  | cons c cs ih =>
    have h : IntervalCertificate
        (fun x => some (if c.lower ≤ x ∧ x ≤ c.upper then (f c.sample).getD 0 else 0))
        c.lower c.upper ((f c.sample).getD 0) [] :=
      ⟨ho c (by simp), fun x => ⟨_, rfl⟩, fun _ _ => rfl⟩
    have hc : Integrable (fun x => if c.lower ≤ x ∧ x ≤ c.upper then (f c.sample).getD 0 else 0) volume := by
      simpa using h.integrable
    obtain ⟨hi, hv⟩ := ih (fun d hd => ho d (by simp [hd]))
    refine ⟨hc.add hi, ?_⟩
    simpa only [stepValue, stepTotal, integral_add hc hi, hv] using
      congrArg (fun v => v + stepTotal f cs) h.integral_value

theorem stepMass_eq (f : ℝ → Option ℝ) (cells : List StepCell)
    (hd : ∀ c ∈ cells, Value.Defined (f c.sample)) : stepMass f cells = some (stepTotal f cells) := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨r, hr⟩ := hd c (by simp)
    rw [stepMass, ih (fun d h => hd d (by simp [h]))]
    simp [stepTotal, hr, Value.mul, Value.add]

structure StepCertificate (f : ℝ → Option ℝ) (cells : List StepCell) (probes points : List ℝ) : Prop where
  ordered : ∀ c ∈ cells, c.lower ≤ c.upper
  total : (∀ x ∈ probes, Value.Defined (f x)) → ∀ x, Value.Defined (f x)
  away : (∀ x ∈ probes, Value.Defined (f x)) →
    ∀ x, (∀ p ∈ points, x ≠ p) → f x = some (stepValue f cells x)

namespace StepCertificate

theorem defined_iff {f cells probes points} (h : StepCertificate f cells probes points) :
    (∀ x, Value.Defined (f x)) ↔ ∀ x ∈ probes, Value.Defined (f x) :=
  ⟨fun hf x _ => hf x, h.total⟩

theorem integrate {f cells probes points} (h : StepCertificate f cells probes points) :
    partialIntegral volume f = (zeroOnProbes f probes).bind (fun _ => stepMass f cells) := by
  rw [zeroOnProbes_eq]
  split_ifs with hd
  · have he : (fun x => (f x).getD 0) =ᵐ[volume] stepValue f cells := by
      filter_upwards [ae_away points] with x hx
      simp only [h.away hd x hx, Option.getD_some]
    obtain ⟨hi, hv⟩ := step_integral f cells h.ordered
    rw [partialIntegral_valid volume f (h.total hd) ((integrable_congr he).mpr hi),
      integral_congr_ae he, hv, Option.some_bind, stepMass_eq f cells (fun c _ => h.total hd c.sample)]
  · change partialIntegral volume f = none
    apply if_neg
    intro hf
    exact hd (h.defined_iff.mp hf.1)

end StepCertificate

theorem DensityProgram.mass_step (p : DensityProgram) {cells probes points}
    (h : StepCertificate p.density cells probes points) :
    p.mass = (zeroOnProbes p.density probes).bind (fun _ => stepMass p.density cells) := by
  rw [DensityProgram.mass, Model.densityMassValue_eq]
  exact h.integrate

end QSym.Distribution
