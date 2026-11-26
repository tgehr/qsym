import QSym.DistributionAtomicIteration

/-! Least fixed points of state-indexed atomic kernels. One call emits a seed
and continues at the next state with a nonnegative weight. Only states reachable
from the query need a certificate for the evaluated body. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal
open OmegaCompletePartialOrder

abbrev Kernel (ι α : Type) := ι → Model α

def kernelStep (b : Kernel ι α) (r : ι → ℝ≥0∞) (next : ι → ι) : Kernel ι α →o Kernel ι α where
  toFun k x := strictRetryStep (b x) (r x) (k (next x))
  monotone' _ _ h x := (strictRetryStep (b x) (r x)).monotone (h (next x))

theorem kernel_continuous (b : Kernel ι α) (r : ι → ℝ≥0∞) (next : ι → ι) :
    ωScottContinuous (kernelStep b r next) := by
  apply ωScottContinuous_iff_map_ωSup_of_orderHom.mpr
  intro c
  funext x
  apply Prod.ext
  · funext y
    change (b x).1 y + r x * (⨆ n : ℕ, (c n (next x)).1 y) = ⨆ n : ℕ, (b x).1 y + r x * (c n (next x)).1 y
    rw [ENNReal.mul_iSup, ENNReal.add_iSup]
  · ext y
    change y ∈ (b x).2 ∪ (⨆ n : ℕ, (c n (next x)).2) ↔ y ∈ (⨆ n : ℕ, (b x).2 ∪ (c n (next x)).2)
    simp only [Set.iSup_eq_iUnion, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (h | ⟨n, h⟩)
      · exact ⟨0, Or.inl h⟩
      · exact ⟨n, Or.inr h⟩
    · rintro ⟨n, h | h⟩
      · exact Or.inl h
      · exact Or.inr ⟨n, h⟩

def reachWeight (r : ι → ℝ≥0∞) (next : ι → ι) : ℕ → ι → ℝ≥0∞
  | 0, _ => 1
  | n+1, x => r x * reachWeight r next n (next x)

theorem reachWeight_prod (r : ι → ℝ≥0∞) (next : ι → ι) (n : ℕ) (x : ι) :
    reachWeight r next n x = ∏ i ∈ Finset.range n, r (next^[i] x) := by
  induction n generalizing x with
  | zero => simp [reachWeight]
  | succ n ih =>
    rw [reachWeight, ih, Finset.prod_range_succ']
    exact mul_comm _ _

theorem reachWeight_const (r : ℝ≥0∞) (next : ι → ι) (n : ℕ) (x : ι) :
    reachWeight (fun _ => r) next n x = r^n := by
  simp [reachWeight_prod]

private theorem iterate_kernel_weights (b : Kernel ι α) (r : ι → ℝ≥0∞) (next : ι → ι) (n : ℕ) (x : ι) (y : α) :
    (((kernelStep b r next)^[n] ⊥) x).1 y = ∑ i ∈ Finset.range n, reachWeight r next i x * (b (next^[i] x)).1 y := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Finset.sum_range_succ']
    change (b x).1 y + r x * (((kernelStep b r next)^[n] ⊥) (next x)).1 y = _
    rw [ih, Finset.mul_sum]
    simp [reachWeight, Function.iterate_succ_apply, mul_assoc, add_comm]

theorem kernel_lfp_weight (b : Kernel ι α) (r : ι → ℝ≥0∞) (next : ι → ι) (x : ι) (y : α) :
    ((kernelStep b r next).lfp x).1 y = ∑' n : ℕ, reachWeight r next n x * (b (next^[n] x)).1 y := by
  rw [fixedPoints.lfp_eq_sSup_iterate _ (kernel_continuous b r next)]
  simp only [iSup_apply, Prod.fst_iSup]
  simp_rw [iterate_kernel_weights]
  rw [ENNReal.tsum_eq_iSup_nat]

private theorem iterate_kernel_visits (b : Kernel ι α) (r : ι → ℝ≥0∞) (next : ι → ι) (n : ℕ) (x : ι) (y : α) :
    y ∈ (((kernelStep b r next)^[n] ⊥) x).2 ↔ ∃ i < n, y ∈ (b (next^[i] x)).2 := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change y ∈ (b x).2 ∪ (((kernelStep b r next)^[n] ⊥) (next x)).2 ↔ _
    rw [Set.mem_union, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨0, Nat.zero_lt_succ _, h⟩
      · exact ⟨i+1, Nat.succ_lt_succ hi, by simpa [Function.iterate_succ_apply] using h⟩
    · rintro ⟨i, hi, h⟩
      cases i with
      | zero => exact Or.inl h
      | succ i => exact Or.inr ⟨i, Nat.lt_of_succ_lt_succ hi, by simpa [Function.iterate_succ_apply] using h⟩

theorem kernel_lfp_visits (b : Kernel ι α) (r : ι → ℝ≥0∞) (next : ι → ι) (x : ι) (y : α) :
    y ∈ ((kernelStep b r next).lfp x).2 ↔ ∃ n : ℕ, y ∈ (b (next^[n] x)).2 := by
  rw [fixedPoints.lfp_eq_sSup_iterate _ (kernel_continuous b r next)]
  rw [iSup_apply, Prod.snd_iSup]
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, iterate_kernel_visits]
  exact ⟨fun ⟨_, i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i+1, i, Nat.lt_succ_self _, h⟩⟩

def iterateKernel (body : (ι → Option (D α)) → ι → Option (D α)) : ℕ → ι → Option (D α)
  | 0 => fun _ => some .zero
  | n+1 => body (iterateKernel body n)

def kernelModelAt (body : (ι → Option (D α)) → ι → Option (D α)) (x : ι) : Option (Model α) :=
  limitModel (fun n => iterateKernel body n x)

/-- Undefined values at unrelated states do not affect the queried limit.
The source step may be partial away from the certified set. -/
theorem kernelModelAt_on (body : (ι → Option (D α)) → ι → Option (D α))
    (b : Kernel ι α) (r : ι → ℝ≥0∞) (next : ι → ι) (states : Set ι) (closed : Set.MapsTo next states states)
    (lift : ∀ x ∈ states, ∀ (k : ι → Option (D α)) d m, k (next x) = some d → Presents d m →
      ∃ e, body k x = some e ∧ Presents e (strictRetryStep (b x) (r x) m))
    {x : ι} (hx : x ∈ states) : kernelModelAt body x = some ((kernelStep b r next).lfp x) := by
  let g := kernelStep b r next
  have inc : ∀ n : ℕ, g^[n] ⊥ ≤ g^[n+1] ⊥ := by
    intro n
    induction n with
    | zero => exact bot_le
    | succ n ih => simpa only [Function.iterate_succ_apply'] using g.monotone ih
  have data : ∀ n a, a ∈ states → ∃ d, iterateKernel body n a = some d ∧ Presents d ((g^[n] ⊥) a) := by
    intro n
    induction n with
    | zero => exact fun _ _ => ⟨.zero, rfl, Represents.zero, visited_zero⟩
    | succ n ih =>
      intro a ha
      obtain ⟨d, hd, hm⟩ := ih (next a) (closed ha)
      obtain ⟨e, he, hk⟩ := lift a ha _ d _ hd hm
      exact ⟨e, he, by simpa only [Function.iterate_succ_apply'] using hk⟩
  have tr : Approximates (fun n => iterateKernel body n x) (fun n => (g^[n] ⊥) x) :=
    ⟨monotone_nat_of_le_succ (fun n => inc n x), fun n => data n x hx⟩
  rw [kernelModelAt, limitModel_eq tr, fixedPoints.lfp_eq_sSup_iterate _ (kernel_continuous b r next), iSup_apply]

end QSym.Distribution.Atomic
