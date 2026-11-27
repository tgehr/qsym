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

/-- A zero coefficient annihilates every row exactly when the ratio is
present. A nonzero coefficient can pass through the convergence check. -/
theorem factor_geometric {K : Type} [NormedField K] (left : Bool) (c r : Option K)
    (power : ℕ → Option K) (hp : ∀ n, power n = r.map (fun x => x^n)) :
    value norm (some (fun n => if left then Value.mul c (power n) else Value.mul (power n) c)) =
      r.bind (fun _ => Value.mask (Value.nonzero c) (Value.mul c (value norm (some power)))) := by
  have rows : (fun n => if left then Value.mul c (power n) else Value.mul (power n) c) =
      (fun n => Value.mul c (power n)) := by
    funext n
    cases left <;> cases c <;> cases power n <;> simp [Value.mul, mul_comm]
  rw [rows]
  cases r with
  | none =>
    apply undefined_term norm _ 0
    rw [hp]
    cases c <;> rfl
  | some r =>
    cases c with
    | none => exact undefined_term norm _ 0 rfl
    | some c =>
      by_cases hc : c = 0
      · subst c
        have zeroRow : (fun n => Value.mul (some (0 : K)) (power n)) = (fun _ => some 0) := by
          funext n; rw [hp]; simp [Value.mul]
        rw [zeroRow]
        simpa [Value.nonzero, Value.mask] using (Summation.zero (ι := ℕ) norm (norm_zero : ‖(0 : K)‖ = 0))
      · rw [scale_nonzero c hc]
        simp [hc, Value.nonzero, Value.mask]

theorem factor_geometricR (left : Bool) (c r : Option ℝ) :
    value norm (some (fun n : ℕ => if left then Value.mul c (Functions.powRN.apply r (some n))
      else Value.mul (Functions.powRN.apply r (some n)) c)) =
    r.bind (fun _ => Value.mask (Value.nonzero c) (Value.mul c
      (value norm (some (fun n : ℕ => Functions.powRN.apply r (some n)))))) :=
  factor_geometric left c r _ (fun n => by cases r <;> simp [Functions.powRN, Function2.apply])

theorem factor_geometricC (left : Bool) (c r : Option ℂ) :
    value norm (some (fun n : ℕ => if left then Value.mul c (Functions.powCN.apply r (some n))
      else Value.mul (Functions.powCN.apply r (some n)) c)) =
    r.bind (fun _ => Value.mask (Value.nonzero c) (Value.mul c
      (value norm (some (fun n : ℕ => Functions.powCN.apply r (some n)))))) :=
  factor_geometric left c r _ (fun n => by cases r <;> simp [Functions.powCN, Function2.apply])

theorem factor_geometricQ (left : Bool) (c r : Option ℚ) :
    value norm (some (fun n : ℕ => if left then Functions.mulQ.apply c (Functions.powQN.apply r (some n))
      else Functions.mulQ.apply (Functions.powQN.apply r (some n)) c)) =
    r.bind (fun _ => Value.mask (Functions.nonzeroQ.apply c) (Functions.mulQ.apply c
      (value norm (some (fun n : ℕ => Functions.powQN.apply r (some n)))))) := by
  have mul : Functions.mulQ.apply = Value.mul := by
    funext a b; cases a <;> cases b <;> simp [Function2.apply, Functions.mulQ, Value.mul]
  rw [Summation.nonzeroQ, mul]
  exact factor_geometric left c r _ (fun n => by cases r <;> simp [Functions.powQN, Function2.apply])

private theorem cast_power (q : Option ℚ) (i : ℕ) :
    Functions.castQR.apply (Functions.powQN.apply q (some i)) = Functions.powRN.apply (Functions.castQR.apply q) (some i) := by
  cases q <;> simp [Functions.castQR, Functions.powQN, Functions.powRN, Function1.apply, Function2.apply]

theorem factor_geometricQR (left : Bool) (c : Option ℝ) (q : Option ℚ) :
    let power := fun i : ℕ => Functions.castQR.apply (Functions.powQN.apply q (some i))
    value norm (some (fun i => if left then Value.mul c (power i) else Value.mul (power i) c)) =
      (Functions.castQR.apply q).bind (fun _ => Value.mask (Value.nonzero c) (Value.mul c (value norm (some power)))) := by
  dsimp only
  simp_rw [cast_power]
  exact factor_geometricR left c (Functions.castQR.apply q)

theorem geometricQR_literals (q : Option ℚ) (one minus : Option ℝ) (ho : one = some 1) (hm : minus = some (-1)) :
    value norm (some (fun n : ℕ => Functions.castQR.apply (Functions.powQN.apply q (some n)))) =
      Binding.guardValue (Value.lt (Value.abs (Functions.castQR.apply q)) one)
        (Value.inv (Value.add one (Value.mul minus (Functions.castQR.apply q)))) := by
  simp_rw [cast_power]
  exact geometricR_literals (Functions.castQR.apply q) one minus ho hm

end QSym.SummationLinearity
