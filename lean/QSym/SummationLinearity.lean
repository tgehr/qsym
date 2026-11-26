import QSym.SummationAlgebra

noncomputable section
namespace QSym.SummationLinearity
open Summation
variable {ι α : Type} [NormedAddCommGroup α]

private theorem norm_add (f g : ι → α) (hf : Summable (fun i => ‖f i‖))
    (hg : Summable (fun i => ‖g i‖)) : Summable (fun i => ‖f i+g i‖) :=
  (hf.add hg).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)

theorem add_known (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b)))
    (f g : ι → Option α) (hknown : (value norm (some f)).isSome) :
    value norm (some (fun i => op (f i) (g i))) = op (value norm (some f)) (value norm (some g)) := by
  classical
  have hop' : op = Value.add := by funext a b; rw [hop,Summation.add]
  subst op
  have hf : (∀ i, (f i).isSome) ∧ Summable (fun i => ‖(f i).getD 0‖) ∧ Summable (fun i => (f i).getD 0) := by
    by_contra h; simp [value,h] at hknown
  by_cases hg : ∀ i, (g i).isSome
  · have he (i : ι) : (Value.add (f i) (g i)).getD 0 = (f i).getD 0 + (g i).getD 0 := by
      have hfi0 := hf.1 i; have hgi0 := hg i
      cases hfi : f i <;> cases hgi : g i <;> simp_all [Value.add]
    have ht : ∀ i, (Value.add (f i) (g i)).isSome := by
      intro i; have hfi0 := hf.1 i; have hgi0 := hg i
      cases hfi : f i <;> cases hgi : g i <;> simp_all [Value.add]
    have hs : Summable (fun i => (f i).getD 0 + (g i).getD 0) ↔ Summable (fun i => (g i).getD 0) := by
      constructor
      · intro h; simpa using h.sub hf.2.2
      · exact hf.2.2.add
    have hn : Summable (fun i => ‖(f i).getD 0 + (g i).getD 0‖) ↔ Summable (fun i => ‖(g i).getD 0‖) := by
      constructor
      · intro h
        have hneg : Summable (fun i => ‖-((f i).getD 0)‖) := by simpa using hf.2.1
        simpa using norm_add (fun i => -((f i).getD 0)) (fun i => (f i).getD 0 + (g i).getD 0) hneg h
      · exact norm_add _ _ hf.2.1
    simp only [value,Option.bind,if_pos hf]
    simp only [ht,hg,true_and,he,hn,hs]
    split_ifs with h
    · simp only [Value.add,Option.bind,Option.map_some,Option.some.injEq]
      exact hf.2.2.tsum_add h.2.2
    · rfl
  · have ht : ¬ ∀ i, (Value.add (f i) (g i)).isSome := by
      intro h; apply hg; intro i
      have hi := h i
      cases hfi : f i <;> cases hgi : g i <;> simp_all [Value.add]
    simp only [value,Option.bind,if_neg (not_and_of_not_left _ ht),if_neg (not_and_of_not_left _ hg),if_pos hf]
    rfl

theorem add_known_right (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b)))
    (f g : ι → Option α) (hknown : (value norm (some g)).isSome) :
    value norm (some (fun i => op (f i) (g i))) = op (value norm (some f)) (value norm (some g)) := by
  have hc (a b : Option α) : op a b = op b a := by cases a <;> cases b <;> simp [hop,_root_.add_comm]
  simp_rw [hc (f _) (g _)]
  rw [add_known op hop g f hknown, hc]

/-- A nonzero constant preserves and reflects absolute convergence, even for
partial summands. A zero multiplier still checks each term and need not
reflect divergence. -/
theorem scale_nonzero {K : Type} [NormedDivisionRing K] (c : K) (hc : c ≠ 0) (f : ι → Option K) :
    value norm (some (fun i => Value.mul (some c) (f i))) = Value.mul (some c) (value norm (some f)) := by
  classical
  have ht (i : ι) : (Value.mul (some c) (f i)).isSome = (f i).isSome := by
    cases f i <;> rfl
  have hv (i : ι) : (Value.mul (some c) (f i)).getD 0 = c * (f i).getD 0 := by
    cases f i <;> simp [Value.mul]
  simp only [value, Option.bind, ht, hv, norm_mul, summable_mul_left_iff (norm_ne_zero_iff.mpr hc),
    summable_mul_left_iff hc, tsum_mul_left]
  split <;> rfl

theorem mul_missing {R : Type} [Mul R] (op : Option R → Option R → Option R)
    (hm : op = Value.mul) (left : Bool) (x : Option R) :
    (if left then op none x else op x none) = none := by
  subst op; cases left <;> cases x <;> rfl

theorem distribute {R : Type} [Semiring R]
    (add mul : Option R → Option R → Option R) (ha : add = Value.add) (hm : mul = Value.mul)
    (a b c : Option R) (reverse : Bool) :
    (if reverse then mul c (add a b) else mul (add a b) c) =
    add (if reverse then mul c a else mul a c) (if reverse then mul c b else mul b c) := by
  rw [ha,hm]
  cases a <;> cases b <;> cases c <;> cases reverse <;> simp [Value.add,Value.mul,mul_add,add_mul]

/-- One failed strict guard witnesses that the whole partial sum is missing. -/
theorem missing_guard {R : Type} [AddCommMonoid R] [TopologicalSpace R] [T2Space R] (weight : R → ℝ)
    (p : ι → Option Bool) (f : ι → Option R) (i : ι) (hi : p i = some false) :
    value weight (some (fun j => Binding.guardValue (p j) (f j))) = none :=
  undefined_term weight _ i (by rw [hi]; rfl)

theorem range_missing_guard {R : Type} [AddCommMonoid R] [TopologicalSpace R] [T2Space R]
    (p : ℕ → Option Bool) (f : ℕ → Option R) (i : ℕ) (hi : p i = some false)
    (n : ℕ) (lt : i < n) {bound : Option ℕ} (hb : bound = some n) :
    rangeValue (some (fun j => Binding.guardValue (p j) (f j))) bound = none := by
  subst bound
  have h : ¬ ∀ j ∈ Finset.range n, (Binding.guardValue (p j) (f j)).isSome = true := by
    intro h
    simpa [hi, Binding.guardValue] using h i (Finset.mem_range.mpr lt)
  simp only [rangeValue, Option.bind, finite, if_neg h]

theorem undefined_bound {R : Type} [AddCommMonoid R]
    (f : Option (ℕ → Option R)) (n : Option ℕ) (h : Domain.Correct n (some false)) :
    rangeValue f n = none := by
  cases n with
  | none => cases f <;> rfl
  | some n => simp [Domain.Correct] at h

end QSym.SummationLinearity
