import QSym.Summation

namespace QSym.Summation
attribute [local instance] Classical.propDecidable
variable {α : Type} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]

theorem reindex {ι κ : Type} (weight : α → ℝ) (hw : weight 0=0)
    (f : ι → Option α) (e : κ → ι) (he : Function.Injective e)
    (hz : ∀ i ∉ Set.range e, f i=some 0) :
    value weight (some f)=value weight (some (fun i => f (e i))) := by
  have ht : (∀ i, (f i).isSome) ↔ ∀ i, (f (e i)).isSome := by
    constructor
    · intro h i; exact h (e i)
    · intro h i
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j,rfl⟩ := hi; exact h j
      · simp [hz i hi]
  have hzero : ∀ i ∉ Set.range e, (f i).getD 0=0 := by
    intro i hi; simp [hz i hi]
  have hweight : ∀ i ∉ Set.range e, weight ((f i).getD 0)=0 := by
    intro i hi; rw [hzero i hi,hw]
  have hs := he.summable_iff hzero
  have ha := he.summable_iff hweight
  have heq := he.tsum_eq (fun i hi => by
    by_contra hn
    exact hi (hzero i hn))
  change (if (∀ i, (f i).isSome) ∧ Summable (fun i => weight ((f i).getD 0)) ∧
    Summable (fun i => (f i).getD 0) then some (∑' i, (f i).getD 0) else none) =
    (if (∀ i, (f (e i)).isSome) ∧ Summable (fun i => weight ((f (e i)).getD 0)) ∧
    Summable (fun i => (f (e i)).getD 0) then some (∑' i, (f (e i)).getD 0) else none)
  rw [ht,← ha,← hs,← heq]
  rfl

theorem tail_nat (weight : α → ℝ) (hw : weight 0=0) (f : ℕ → Option α) (l : ℕ) :
    value weight (some (fun i => if l ≤ i then f i else some 0))=
      value weight (some (fun i => f (i+l))) := by
  have he : Function.Injective (fun i : ℕ => i+l) := fun _ _ h => Nat.add_right_cancel h
  have hz : ∀ i ∉ Set.range (fun j : ℕ => j+l),
      (if l ≤ i then f i else some 0)=some 0 := by
    intro i hi
    have h : ¬l ≤ i := by
      intro hl; exact hi ⟨i-l,Nat.sub_add_cancel hl⟩
    simp [h]
  simpa using reindex weight hw (fun i => if l ≤ i then f i else some 0) _ he hz

theorem tailN (weight : α → ℝ) (hw : weight 0=0) (f : ℕ → Option α) (l : Option ℕ) :
    value weight (some (fun i => Value.mask (Functions.leN.apply l (some i)) (f i)))=
      l.bind (fun l => value weight (some (fun i => f (i+l)))) := by
  cases l with
  | none =>
    apply undefined_term weight _ 0
    simp [Function2.apply,Value.mask]
  | some l =>
    have hp : (fun i => Value.mask (Functions.leN.apply (some l) (some i)) (f i)) =
        (fun i => if l ≤ i then f i else some 0) := by
      funext i; by_cases h : l ≤ i <;> simp [Function2.apply,Functions.leN,Value.mask,h]
    simpa only [hp,Option.bind_some] using tail_nat weight hw f l

theorem tailN_strict (weight : α → ℝ) (hw : weight 0=0) (f : ℕ → Option α) (l : Option ℕ) :
    value weight (some (fun i => Value.mask (Functions.ltN.apply l (some i)) (f i)))=
      l.bind (fun l => value weight (some (fun i => f (i+(l+1))))) := by
  cases l with
  | none =>
    apply undefined_term weight _ 0
    simp [Function2.apply,Value.mask]
  | some l =>
    have hp : (fun i => Value.mask (Functions.ltN.apply (some l) (some i)) (f i)) =
        (fun i => if l+1 ≤ i then f i else some 0) := by
      funext i; by_cases h : l < i <;> simp [Function2.apply,Functions.ltN,Value.mask,Nat.succ_le_iff,h]
    simpa only [hp,Option.bind_some] using tail_nat weight hw f (l+1)

theorem tailN_value (weight : α → ℝ) (hw : weight 0=0)
    (f : Option ℕ → Option α) (l : Option ℕ) (strict : Bool) :
    value weight (some (fun i => Value.mask
      ((if strict then Functions.ltN else Functions.leN).apply l (some i)) (f (some i)))) =
    l.bind (fun _ => value weight (some (fun i => f
      (Functions.addN.apply (some i) (if strict then Functions.addN.apply l (some 1) else l))))) := by
  cases strict <;> cases l with
  | none =>
    apply undefined_term weight _ 0
    simp [Function2.apply,Value.mask]
  | some l =>
    first
    | simpa [Function2.apply,Functions.addN] using tailN weight hw (fun i => f (some i)) (some l)
    | simpa [Function2.apply,Functions.addN] using tailN_strict weight hw (fun i => f (some i)) (some l)

section Geometric
variable {K : Type} [NormedField K]

theorem geometric_shift (q : K) (k : ℕ) :
    value norm (some (fun i : ℕ => some (q^(i+k))))=
      Value.mul (some (q^k)) (value norm (some (fun i : ℕ => some (q^i)))) := by
  by_cases h : ‖q‖<1
  · have ha : Summable (fun i : ℕ => ‖q^(i+k)‖) := by
      simpa only [pow_add,norm_mul,norm_pow,mul_comm] using
        (summable_geometric_of_norm_lt_one (by simpa using h : ‖‖q‖‖<1)).mul_left (‖q‖^k)
    have hs : HasSum (fun i : ℕ => q^(i+k)) (q^k*(1-q)⁻¹) := by
      simpa only [pow_add,mul_comm] using (hasSum_geometric_of_norm_lt_one h).mul_left (q^k)
    rw [of_hasSum norm _ _ _ (fun _ => rfl) ha hs,geometric,if_pos h]
    rfl
  · have hn : ¬ Summable (fun i : ℕ => q^(i+k)) := by
      rw [summable_nat_add_iff]
      simpa only [summable_geometric_iff_norm_lt_one] using h
    rw [geometric,if_neg h]
    simp [value,hn,Value.mul]

theorem geometric_shift_value
    (pow : Option K → Option ℕ → Option K) (hp : pow=Spectral.power)
    (mul : Option K → Option K → Option K) (hm : mul=Value.mul)
    (q : Option K) (k : Option ℕ) :
    value norm (some (fun i : ℕ => pow q (Functions.addN.apply (some i) k)))=
      mul (pow q k) (value norm (some (fun i : ℕ => pow q (some i)))) := by
  subst pow;subst mul
  cases q with
  | none =>
    rw [undefined_term norm _ 0 rfl]
    rfl
  | some q =>
    cases k with
    | none =>
      rw [undefined_term norm _ 0 (by simp [Spectral.power,Function2.apply])]
      rfl
    | some k =>
      simpa [Spectral.power,Function2.apply,Functions.addN] using geometric_shift q k

theorem geometric_shift_guard
    (pow : Option K → Option ℕ → Option K) (hp : pow=Spectral.power)
    (mul : Option K → Option K → Option K) (hm : mul=Value.mul)
    (q : Option K) (k : Option ℕ) (p : Option Bool) (v : Option K)
    (h : value norm (some (fun i : ℕ => pow q (some i)))=Binding.guardValue p v) :
    value norm (some (fun i : ℕ => pow q (Functions.addN.apply (some i) k)))=
      Binding.guardValue p (mul (pow q k) v) := by
  rw [geometric_shift_value pow hp mul hm,h,hm]
  cases p with
  | none => simp [Binding.guardValue,Value.mul]
  | some p => cases p <;> simp [Binding.guardValue,Value.mul]
end Geometric

end QSym.Summation
