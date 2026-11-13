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

theorem pure_rank {a : Option α} {d : Option Bool} (h : Domain.Correct a d) : Test d (Value.Defined a) :=
  ⟨h.iff.symm, h.total⟩

theorem call_rank {a : Option ℕ} {d : Option Bool} (n : ℕ) (h : Domain.Correct a d) :
    Test (Value.and d (Functions.ltN.apply a (some n))) (∃ y, a = some y ∧ y < n) := by
  cases a with
  | none => change d = some false at h; rw [h]; simp [Test, Value.and, Value.Defined]
  | some a => simp_all [Test, Domain.Correct, Value.and, Function2.apply, Functions.ltN, Value.Defined]

theorem true_rank {p d : Option Bool} (h : Domain.Correct p d) : Test (Value.and d p) (p = some true) := by
  cases p with
  | none => change d = some false at h; rw [h]; simp [Test, Value.and, Value.Defined]
  | some p => cases p <;> simp_all [Test, Domain.Correct, Value.and, Value.Defined]

theorem false_rank {p d : Option Bool} (h : Domain.Correct p d) : Test (Value.and d (Value.not p)) (p = some false) := by
  cases p with
  | none => change d = some false at h; rw [h]; simp [Test, Value.and, Value.Defined]
  | some p => cases p <;> simp_all [Test, Domain.Correct, Value.and, Value.not, Value.Defined]

theorem both_rank {p q : Option Bool} {a b : Prop} (hp : Test p a) (hq : Test q b) : Test (Value.and p q) (a ∧ b) := by
  obtain ⟨u, rfl⟩ := hp.2
  obtain ⟨v, rfl⟩ := hq.2
  cases u <;> cases v <;> simp_all [Test, Value.and, Value.Defined]

theorem either_rank {p q : Option Bool} {a b : Prop} (hp : Test p a) (hq : Test q b) : Test (Value.or p q) (a ∨ b) := by
  obtain ⟨u, rfl⟩ := hp.2
  obtain ⟨v, rfl⟩ := hq.2
  cases u <;> cases v <;> simp_all [Test, Value.or, Value.Defined]

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

end QSym.SetFixed
