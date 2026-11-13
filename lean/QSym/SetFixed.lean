import QSym.Binding
import Mathlib.Order.FixedPoints

namespace QSym.SetFixed
open OmegaCompletePartialOrder
attribute [local instance] Classical.propDecidable

inductive Predicate (α : Type) where
  | pure : (α → Prop) → Predicate α
  | call : (α → Option α) → Predicate α
  | both : Predicate α → Predicate α → Predicate α
  | either : Predicate α → Predicate α → Predicate α

def Predicate.eval (s : Set α) (x : α) : Predicate α → Prop
  | .pure p => p x
  | .call a => ∃ y, a x = some y ∧ y ∈ s
  | .both a b => a.eval s x ∧ b.eval s x
  | .either a b => a.eval s x ∨ b.eval s x

theorem Predicate.monotone (p : Predicate α) : Monotone (fun s => {x | p.eval s x}) := by
  intro s t h x
  induction p with
  | pure p => exact id
  | call a => exact fun ⟨y, hy, hs⟩ => ⟨y, hy, h hs⟩
  | both a b ia ib => exact fun h => ⟨ia h.1, ib h.2⟩
  | either a b ia ib => exact Or.imp ia ib

def Predicate.hom (p : Predicate α) : Set α →o Set α := ⟨fun s => {x | p.eval s x}, p.monotone⟩
def Predicate.least (p : Predicate α) : Set α := p.hom.lfp

theorem Predicate.unfold (p : Predicate α) (x : α) : p.eval p.least x ↔ x ∈ p.least :=
  Iff.of_eq (congrArg (fun s : Set α => x ∈ s) p.hom.map_lfp)

theorem least_domain (p : Recursion.Program α β β) (d : Predicate α)
    (h : ∀ g x, Value.Defined (p.eval g x) ↔ d.eval {y | Value.Defined (g y)} x) :
    {x | Value.Defined (FixedPoint.value p.functional x)} = d.least := by
  classical
  apply le_antisymm
  · have step (g : α → Part β) (x : α) :
        (p.functional g x).Dom ↔ d.eval {y | (g y).Dom} x := by
      have hc := p.toOption_continuous x g
      change (p.continuous x g).Dom ↔ _
      have hd (v : Part β) : Value.Defined v.toOption ↔ v.Dom := by
        simp only [Value.Defined, Part.toOption_eq_some_iff, Part.dom_iff_mem]
      rw [← hd, hc, h]
      have hs : {y | Value.Defined (g y).toOption} = {y | (g y).Dom} := Set.ext (fun y => hd _)
      rw [hs]
    have ha : ∀ n x, (FixedPoint.approx p.functional n x).Dom → x ∈ d.least := by
      intro n
      induction n with
      | zero => intro x hx; exact False.elim hx
      | succ n ih =>
        intro x hx
        have he : FixedPoint.approx p.functional (n+1) = p.functional (FixedPoint.approx p.functional n) :=
          Function.iterate_succ_apply' _ _ _
        rw [he, step] at hx
        exact (d.unfold x).mp (d.monotone (fun y hy => ih y hy) hx)
    intro x hx
    obtain ⟨n, hn⟩ := (FixedPoint.defined_value_iff p.functional x).mp hx
    exact ha n x hn
  · apply d.hom.lfp_le
    intro x hx
    change Value.Defined (FixedPoint.value p.functional x)
    rw [← p.unfold x]
    exact (h _ x).mpr hx

theorem Predicate.total_nat (d : Predicate ℕ) (h : ∀ n, d.eval {m | m < n} n) : d.least = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih => exact (d.unfold n).mp (d.monotone (fun m hm => ih m hm) (h n))

theorem Predicate.least_nat_of_closed (d : Predicate ℕ) (s : Set ℕ)
    (hl : ∀ n, n ∈ s → d.eval {m | m < n ∧ m ∈ s} n)
    (hu : ∀ n, d.eval s n → n ∈ s) : d.least = s := by
  apply le_antisymm (d.hom.lfp_le hu)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    exact (d.unfold n).mp (d.monotone (fun m hm => ih m hm.1 hm.2) (hl n hn))

theorem Predicate.total_measure (d : Predicate α) (r : α → ℝ) (b e : ℝ) (he : 0 < e)
    (h : ∀ x, d.eval {y | b < r x ∧ r y + e ≤ r x} x) : d.least = Set.univ := by
  have bounded : ∀ n : ℕ, ∀ x, r x ≤ b + n * e → x ∈ d.least := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simp only [Nat.cast_zero, zero_mul, add_zero] at hx
      apply (d.unfold x).mp
      exact d.monotone (fun y hy => False.elim (not_lt_of_ge hx hy.1)) (h x)
    | succ n ih =>
      intro x hx
      apply (d.unfold x).mp
      apply d.monotone (fun y hy => ih y ?_) (h x)
      push_cast at hx
      linarith [hy.2]
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt ((r x - b) / e)
  apply bounded n x
  have := (div_lt_iff₀ he).mp hn
  linarith

theorem Predicate.start_least (d : Predicate α) :
    {x : α | (some false : Option Bool) = some true} ⊆ d.least := by simp

theorem Predicate.step_least (d : Predicate α) {s t : Set α} (hs : s ⊆ d.least)
    (h : ∀ x, x ∈ t ↔ d.eval s x) : t ⊆ d.least :=
  fun x hx => (d.unfold x).mp (d.monotone hs ((h x).mp hx))

theorem Predicate.least_of_stable (d : Predicate α) (s : Set α) (hs : s ⊆ d.least)
    (h : ∀ x, d.eval s x ↔ x ∈ s) : d.least = s :=
  le_antisymm (d.hom.lfp_le (fun x hx => (h x).mp hx)) hs

theorem defined_bind (a : Option α) (g : α → Option β) :
    Value.Defined (a.bind g) ↔ ∃ y, a = some y ∧ Value.Defined (g y) := by
  cases a <;> simp [Value.Defined]

theorem defined_total1 (f : Function1 α β) (ht : ∀ x, f.domain x) (a : Option α) :
    Value.Defined (f.apply a) ↔ Value.Defined a := by
  cases a <;> simp [Value.Defined, Function1.apply, ht]

theorem defined_total2 (f : Function2 α β γ) (ht : ∀ x y, f.domain x y) (a : Option α) (b : Option β) :
    Value.Defined (f.apply a b) ↔ Value.Defined a ∧ Value.Defined b := by
  cases a <;> cases b <;> simp [Value.Defined, Function2.apply, ht]

theorem defined_sequence (a : Option α) (b : Option β) :
    Value.Defined (a.bind (fun _ => b)) ↔ Value.Defined a ∧ Value.Defined b := by
  cases a <;> cases b <;> simp [Value.Defined]

theorem defined_guard (p : Option Bool) (a : Option α) :
    Value.Defined (Binding.guardValue p a) ↔ p = some true ∧ Value.Defined a := by
  cases p with
  | none => simp [Binding.guardValue, Value.Defined]
  | some p => cases p <;> simp [Binding.guardValue, Value.Defined]

def Test (b : Option Bool) (p : Prop) : Prop := (b = some true ↔ p) ∧ Value.Defined b

theorem Test.refine {a b : Option Bool} {p : Prop} (h : Test a p) (hr : Value.Refines a b) : Test b p :=
  hr.eq_of_defined h.2 ▸ h

theorem call_test {a : Option α} {d b : Option Bool} (p : α → Option Bool)
    (ha : Domain.Correct a d) (hp : ∀ x, Value.Defined (p x))
    (hb : ∀ x, a = some x → b = p x) :
    Test (Value.and d b) (∃ x, a = some x ∧ p x = some true) := by
  cases a with
  | none => change d = some false at ha; rw [ha]; simp [Test, Value.and, Value.Defined]
  | some a =>
    have hd : d = some true := ha
    rw [hd, hb a rfl]
    simpa [Test, Value.and] using (And.intro Iff.rfl (hp a) : Test (p a) (p a = some true))

theorem pure_rank {a : Option α} {d : Option Bool} (h : Domain.Correct a d) : Test d (Value.Defined a) :=
  ⟨h.iff.symm, h.total⟩

theorem call_rank {a : Option ℕ} {d : Option Bool} (n : ℕ) (h : Domain.Correct a d) :
    Test (Value.and d (Functions.ltN.apply a (some n))) (∃ y, a = some y ∧ y < n) := by
  cases a with
  | none => change d = some false at h; rw [h]; simp [Test, Value.and, Value.Defined]
  | some a => simp_all [Test, Domain.Correct, Value.and, Function2.apply, Functions.ltN, Value.Defined]

theorem call_rank_test {a : Option ℕ} {d b : Option Bool} (n : ℕ) (p : ℕ → Option Bool)
    (ha : Domain.Correct a d) (hp : ∀ x, Value.Defined (p x))
    (hb : ∀ x, a = some x → b = p x) :
    Test (Value.and d (Value.and (Functions.ltN.apply a (some n)) b))
      (∃ y, a = some y ∧ y < n ∧ p y = some true) := by
  cases a with
  | none => change d = some false at ha; rw [ha]; simp [Test, Value.and, Value.Defined]
  | some a =>
    change d = some true at ha
    rw [ha, hb a rfl]
    obtain ⟨v,hv⟩ := hp a
    rw [hv]
    by_cases h : a < n <;> cases v <;> simp [Test, Value.and, Function2.apply, Functions.ltN, Value.Defined, h, hv]

theorem call_measure {a : Option ℝ} {d : Option Bool} (x c b e : ℝ) (h : Domain.Correct a d) :
    Test (Value.and d (Value.and (Value.lt (some b) (Value.mul (some c) (some x)))
      (Value.le (Value.add (Value.mul (some c) a) (some e)) (Value.mul (some c) (some x)))))
      (∃ y, a = some y ∧ b < c * x ∧ c * y + e ≤ c * x) := by
  cases a with
  | none => change d = some false at h; rw [h]; simp [Test, Value.and, Value.Defined]
  | some a =>
    change d = some true at h
    rw [h]
    by_cases hb : b < c * x <;> by_cases he : c * a + e ≤ c * x <;>
      simp [Test, Value.and, Value.lt, Value.le, Value.mul, Value.add, Value.Defined, hb, he]

theorem positive_step (e : ℝ)
    (h : Value.Refines (Value.lt (some ((0 : ℤ) : ℝ)) (some e)) (some true)) : 0 < e := by
  simpa [Value.Refines, Value.lt] using h

theorem true_rank {p d : Option Bool} (h : Domain.Correct p d) : Test (Value.and d p) (p = some true) := by
  cases p with
  | none => change d = some false at h; rw [h]; simp [Test, Value.and, Value.Defined]
  | some p => cases p <;> simp_all [Test, Domain.Correct, Value.and, Value.Defined]

theorem false_rank {p d : Option Bool} (h : Domain.Correct p d) : Test (Value.and d (Value.not p)) (p = some false) := by
  cases p with
  | none => change d = some false at h; rw [h]; simp [Test, Value.and, Value.Defined]
  | some p => cases p <;> simp_all [Test, Domain.Correct, Value.and, Value.not, Value.Defined]

theorem mask_test {p dp b : Option Bool} {q : Prop} (hp : Domain.Correct p dp) (hb : Test b q) :
    Test (Value.and dp (Value.or (Value.not p) b)) (p = some false ∨ (p = some true ∧ q)) := by
  obtain ⟨b, rfl⟩ := hb.2
  cases p with
  | none => change dp = some false at hp; rw [hp]; simp [Test, Value.and, Value.Defined]
  | some p => cases p <;> cases b <;> simp_all [Test, Domain.Correct, Value.and, Value.or, Value.not, Value.Defined]

theorem or_test {p dp b : Option Bool} {q : Prop} (hp : Domain.Correct p dp) (hb : Test b q) :
    Test (Value.and dp (Value.or p b)) (p = some true ∨ (p = some false ∧ q)) := by
  obtain ⟨b, rfl⟩ := hb.2
  cases p with
  | none => change dp = some false at hp; rw [hp]; simp [Test, Value.and, Value.Defined]
  | some p => cases p <;> cases b <;> simp_all [Test, Domain.Correct, Value.and, Value.or, Value.Defined]

theorem both_rank {p q : Option Bool} {a b : Prop} (hp : Test p a) (hq : Test q b) : Test (Value.and p q) (a ∧ b) := by
  obtain ⟨u, rfl⟩ := hp.2
  obtain ⟨v, rfl⟩ := hq.2
  cases u <;> cases v <;> simp_all [Test, Value.and, Value.Defined]

theorem either_rank {p q : Option Bool} {a b : Prop} (hp : Test p a) (hq : Test q b) : Test (Value.or p q) (a ∨ b) := by
  obtain ⟨u, rfl⟩ := hp.2
  obtain ⟨v, rfl⟩ := hq.2
  cases u <;> cases v <;> simp_all [Test, Value.or, Value.Defined]

theorem implies_test {p q : Option Bool} {a b : Prop} (hp : Test p a) (hq : Test q b) :
    Test (Value.or (Value.not p) q) (a → b) := by
  obtain ⟨u,rfl⟩ := hp.2
  obtain ⟨v,rfl⟩ := hq.2
  cases u <;> cases v <;> simp_all [Test, Value.or, Value.not, Value.Defined]

theorem rank_true {b : Option Bool} {p : Prop} (h : Test b p) (hr : Value.Refines b (some true)) : p :=
  h.1.mp (hr.eq_of_defined h.2)

theorem domain_univ (p : Recursion.Program ℕ β β) (d : Predicate ℕ) (f : Option (ℕ → Option β))
    (hf : f = some (FixedPoint.value p.functional))
    (hd : ∀ g x, Value.Defined (p.eval g x) ↔ d.eval {y | Value.Defined (g y)} x)
    (hr : ∀ n, d.eval {m | m < n} n) : Binding.inputDomain f = some Set.univ := by
  rw [hf]
  have he := (least_domain p d hd).trans (d.total_nat hr)
  simp only [Binding.inputDomain, Option.some_bind]
  congr 1
  convert he using 1
  ext x
  exact Option.isSome_iff_exists

theorem domain_set (p : Recursion.Program α β β) (d : Predicate α) (f : Option (α → Option β))
    (hf : f = some (FixedPoint.value p.functional))
    (hd : ∀ g x, Value.Defined (p.eval g x) ↔ d.eval {y | Value.Defined (g y)} x)
    (s : Set α) (hs : d.least = s) : Binding.inputDomain f = some s := by
  rw [hf]
  have he := (least_domain p d hd).trans hs
  simp only [Binding.inputDomain, Option.some_bind]
  congr 1
  convert he using 1
  ext x
  exact Option.isSome_iff_exists

end QSym.SetFixed
