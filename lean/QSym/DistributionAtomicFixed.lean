import QSym.Distribution
import Mathlib.Order.FixedPoints
import Mathlib.Analysis.SpecificLimits.Basic

/-! Increasing approximations to nonnegative atomic distributions. The order
compares the weight of each outcome. No measurable-space or countability
instance on the outcome type is required. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal
open OmegaCompletePartialOrder

abbrev Weights (α : Type) := α → ℝ≥0∞

/-- One round emits the seed and repeats with weight `r`. -/
def retryStep (seed : Weights α) (r : ℝ≥0∞) : Weights α →o Weights α where
  toFun k x := seed x + r * k x
  monotone' _ _ h x := add_le_add_left (mul_le_mul_left' (h x) r) (seed x)

theorem retryContinuous (b : Weights α) (r : ℝ≥0∞) : ωScottContinuous (retryStep b r) := by
  apply ωScottContinuous_iff_map_ωSup_of_orderHom.mpr
  intro chain
  funext x
  change b x + r * (⨆ n : ℕ, chain n x) = ⨆ n : ℕ, b x + r * chain n x
  rw [ENNReal.mul_iSup, ENNReal.add_iSup]

/-- Depth zero emits zero weight. The first n rounds contribute once each. -/
theorem iterate_retry (b : Weights α) (r : ℝ≥0∞) (n : ℕ) (x : α) :
    (retryStep b r)^[n] ⊥ x = ∑ i ∈ Finset.range n, r ^ i * b x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Finset.sum_range_succ']
    change b x + r * ((retryStep b r)^[n] ⊥ x) = _
    rw [ih, Finset.mul_sum]
    simp only [pow_succ', mul_assoc, pow_zero, one_mul, add_comm (b x)]

theorem lfp_retry (b : Weights α) (r : ℝ≥0∞) (x : α) :
    (retryStep b r).lfp x = (1-r)⁻¹ * b x := by
  rw [fixedPoints.lfp_eq_sSup_iterate _ (retryContinuous b r), iSup_apply]
  simp_rw [iterate_retry]
  rw [← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

/-- Stop with weight `1-r` and retry with weight `r`. Every outcome recovers
its original weight, including when the seed has arbitrary total mass. -/
theorem lfp_stop_or_retry (b : Weights α) (r : ℝ≥0∞) (hr : r < 1) :
    (retryStep (fun x => (1-r) * b x) r).lfp = b := by
  funext x
  have hfin : 1-r ≠ ∞ := ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top)
  rw [lfp_retry, ← mul_assoc, ENNReal.inv_mul_cancel (tsub_pos_of_lt hr).ne' hfin, one_mul]

def atom (a : α) : Weights α := by classical exact fun x => if x = a then 1 else 0

/-- Finite atomic presentations with nonnegative weights. -/
inductive Represents : D α → Weights α → Prop where
  | zero : Represents .zero (fun _ => 0)
  | dirac (a : α) : Represents (.dirac a) (atom a)
  | add : Represents d k → Represents e l → Represents (.add d e) (fun x => k x + l x)
  | scale (hr : 0 ≤ r) : Represents d k → Represents (.scale r d) (fun x => ENNReal.ofReal r * k x)

/-- Agreement with the existing scalar observer for every total nonnegative
test, including mass. -/
theorem Represents.pairing {d : D α} {k : Weights α} (h : Represents d k)
    (t : α → ℝ) (ht : ∀ x, 0 ≤ t x) :
    ∃ m : ℝ, integrate d (fun x => some (t x)) = some m ∧ 0 ≤ m ∧
      ∑' x, k x * ENNReal.ofReal (t x) = ENNReal.ofReal m := by
  classical
  induction h with
  | zero => exact ⟨0, rfl, le_rfl, by simp⟩
  | dirac a =>
    refine ⟨t a, rfl, ht a, ?_⟩
    rw [tsum_eq_single a (fun x hx => by simp [atom, hx])]
    simp [atom]
  | add hd he ih jh =>
    obtain ⟨v, hv, v0, kv⟩ := ih
    obtain ⟨w, hw, w0, lw⟩ := jh
    exact ⟨v+w, by simp [integrate, hv, hw, Value.add], add_nonneg v0 w0,
      by simp only [add_mul, ENNReal.tsum_add, kv, lw, ENNReal.ofReal_add v0 w0]⟩
  | scale hr hd ih =>
    obtain ⟨v, hv, v0, kv⟩ := ih
    exact ⟨_, by simp [integrate, hv, Value.mul], mul_nonneg hr v0,
      by simp only [mul_assoc, ENNReal.tsum_mul_left, kv, ENNReal.ofReal_mul hr]⟩

/-- Real atomic presentations have a defined zero regular part at every point.
A positive charge obstructs the density at precisely that point. -/
theorem Represents.realFibreAt {d : D ℝ} {k : Weights ℝ} (h : Represents d k) (x : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ k x = ENNReal.ofReal c ∧ realFibre d x = ⟨c, some 0⟩ := by
  classical
  induction h with
  | zero => exact ⟨0, le_rfl, by simp, rfl⟩
  | dirac a =>
    by_cases e : x = a
    · exact ⟨1, zero_le_one, by simp [atom, e], by simp [realFibre, e]⟩
    · exact ⟨0, le_rfl, by simp [atom, e], by simp [realFibre, e]⟩
  | add hd he ih jh =>
    obtain ⟨v, v0, kv, hv⟩ := ih
    obtain ⟨w, w0, lw, hw⟩ := jh
    exact ⟨v+w, add_nonneg v0 w0, by simp [kv, lw, ENNReal.ofReal_add v0 w0],
      by simp [realFibre, hv, hw, RealDensityFibre.add, Value.add]⟩
  | scale hr hd ih =>
    obtain ⟨v, v0, kv, hv⟩ := ih
    exact ⟨_, mul_nonneg hr v0, by simp [kv, ENNReal.ofReal_mul hr],
      by simp [realFibre, hv, RealDensityFibre.scale, Value.mul]⟩

theorem Represents.density {d : D ℝ} {k : Weights ℝ} (h : Represents d k) (x : ℝ) :
    densityAt d x = if k x = 0 then some 0 else none := by
  obtain ⟨c, h0, hk, hf⟩ := h.realFibreAt x
  have hz : ENNReal.ofReal c = 0 ↔ c = 0 := ENNReal.ofReal_eq_zero.trans ⟨fun h => le_antisymm h h0, fun h => h.le⟩
  simp only [densityAt, RealDensityFibre.density, hf, hk, hz]

/-- A convergent retry has a finite qsym presentation whenever its seed does. -/
theorem Represents.retry {d : D α} {k : Weights α} (h : Represents d k)
    {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Represents (.scale (1-r)⁻¹ d) (retryStep k (ENNReal.ofReal r)).lfp := by
  have hpos : 0 < 1-r := sub_pos.mpr h1
  convert h.scale (inv_nonneg.mpr hpos.le) using 1
  funext x
  rw [lfp_retry, ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_sub _ h0, ENNReal.ofReal_one]

/-- The finite unfoldings as ordinary qsym presentations. At depth zero a
partial probe observes zero before any outcome is visited. -/
def approximate (b : D α) (r : ℝ) : ℕ → D α
  | 0 => .zero
  | n+1 => .add b (.scale r (approximate b r n))

theorem Represents.approximate {d : D α} {k : Weights α} (h : Represents d k)
    {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    Represents (Atomic.approximate d r n) ((retryStep k (ENNReal.ofReal r))^[n] ⊥) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact h.add (ih.scale hr)

private theorem geometric_succ (r : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n+1), r^i = 1 + r * ∑ i ∈ Finset.range n, r^i := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ', add_comm]

/-- Each positive depth evaluates exactly the seed's partial probe, even for
a zero retry weight. This equality also holds for signed probes and seeds. -/
theorem integrate_approximate (b : D α) (r : ℝ) (t : α → Option ℝ) (n : ℕ) :
    integrate (approximate b r (n+1)) t =
      Value.mul (some (∑ i ∈ Finset.range (n+1), r^i)) (integrate b t) := by
  induction n with
  | zero =>
    cases h : integrate b t <;> simp [approximate, integrate, h, Value.mul, Value.add]
  | succ n ih =>
    change Value.add (integrate b t) (Value.mul (some r) (integrate (approximate b r (n+1)) t)) = _
    rw [ih, geometric_succ r (n+1)]
    cases h : integrate b t <;> simp [Value.mul, Value.add, add_mul, mul_assoc]

theorem approximate_defined (b : D α) (r : ℝ) (t : α → Option ℝ) (n : ℕ) :
    (integrate (approximate b r (n+1)) t).isSome =
      (integrate (.scale (1-r)⁻¹ b) t).isSome := by
  rw [integrate_approximate]
  cases h : integrate b t <;> simp [integrate, h, Value.mul]

open Filter Topology in
theorem approximate_limit (b : D α) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (t : α → Option ℝ)
    {v : ℝ} (hv : integrate b t = some v) :
    Tendsto (fun n : ℕ => (integrate (approximate b r (n+1)) t).getD 0) atTop
      (𝓝 ((1-r)⁻¹ * v)) := by
  have hnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hs := hasSum_geometric_of_norm_lt_one hnorm
  have lim := hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def, integrate_approximate, hv, Value.mul] using lim.mul_const v

end QSym.Distribution.Atomic
