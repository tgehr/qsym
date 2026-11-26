import QSym.DistributionMixture
import QSym.Summation

/-! Sums of presentations indexed by ℤ.

`sumValue` is a request, like an integral node: `∑ i, δ i` is the counting
measure on ℤ and has no finite mass. A scalar observation of a sum is the scalar
sum of the observations of its terms, with the semantics of scalar summation:
every term is defined and the series converges absolutely. Weighting and
composition act on the terms. All laws are equalities of presentations or of
partial scalars and include the missing operands.
-/
namespace QSym.Distribution

theorem partialSum_eq_value (f : ℤ → Option ℝ) :
    partialSum f = Summation.value norm (some f) := by
  classical
  unfold partialSum Summation.value
  simp only [Option.some_bind]

/-- The mass of a sum is the scalar sum of the masses of its terms. -/
theorem mass_sumValue {α : Type} (k : ℤ → Option (D α)) :
    massValue (sumValue (some k)) = Summation.value norm (some (fun i => massValue (k i))) := by
  rw [← partialSum_eq_value]
  change partialSum (fun i => integrate ((k i).getD .invalid) _) = partialSum (fun i => massValue (k i))
  congr 1
  funext i
  cases k i <;> rfl

/-- A weight acts on every term. The copy `f'` of the weight below the index
binder is the weight itself; a missing weight makes the result missing. -/
theorem weight_sumValue {α : Type} (f : Option (α → Option ℝ)) (f' : ℤ → Option (α → Option ℝ))
    (k : ℤ → Option (D α)) (hf : ∀ i, f' i = f) :
    weightValue f (sumValue (some k)) =
      f.bind (fun _ => sumValue (some (fun i => weightValue (f' i) (k i)))) := by
  obtain rfl : f' = fun _ => f := funext hf
  cases f with
  | none => rfl
  | some g =>
    change some (Presentation.sum _) = some (Presentation.sum _)
    congr 2
    funext i
    beta_reduce
    cases k i <;> rfl

/-- Composition acts on every term. -/
theorem bind_sumValue {α β : Type} (k : ℤ → Option (D α)) (g : Option (α → Option (D β)))
    (g' : ℤ → Option (α → Option (D β))) (hg : ∀ i, g' i = g) :
    bindValue (sumValue (some k)) g =
      g.bind (fun _ => sumValue (some (fun i => bindValue (k i) (g' i)))) := by
  obtain rfl : g' = fun _ => g := funext hg
  cases g with
  | none => rfl
  | some h =>
    change some (Presentation.sum _) = some (Presentation.sum _)
    congr 2
    funext i
    beta_reduce
    cases k i <;> rfl

/-! Sums indexed by ℕ. -/

/-- A series over ℤ that vanishes at negative indices is the series over ℕ,
with the same definedness and absolute convergence. -/
theorem partialSum_nat (m : ℕ → Option ℝ) :
    partialSum (fun i : ℤ => if 0 ≤ i then m i.toNat else some 0) = Summation.value norm (some m) := by
  classical
  let a : ℕ → ℝ := fun n => (m n).getD 0
  let A : ℤ → ℝ := fun i => if 0 ≤ i then a i.toNat else 0
  have key : (fun i : ℤ => (if 0 ≤ i then m i.toNat else some 0).getD 0) = A := by
    funext i
    by_cases h : 0 ≤ i <;> simp [A, a, h]
  have hA : ∀ i ∉ Set.range (Nat.cast : ℕ → ℤ), A i = 0 := by
    intro i hi
    have : ¬ 0 ≤ i := fun h => hi ⟨i.toNat, Int.toNat_of_nonneg h⟩
    simp [A, this]
  have hcomp : A ∘ (Nat.cast : ℕ → ℤ) = a := by
    funext n
    simp [A]
  have hdef : (∀ i : ℤ, (if 0 ≤ i then m i.toNat else some 0).isSome) ↔ ∀ n, (m n).isSome := by
    constructor
    · intro h n
      simpa using h (n : ℤ)
    · intro h i
      by_cases hi : 0 ≤ i <;> simp [hi, h]
  have hs : Summable A ↔ Summable a := by
    rw [← hcomp]
    exact (Nat.cast_injective.summable_iff hA).symm
  have hn : Summable (fun i => ‖A i‖) ↔ Summable (fun n => ‖a n‖) := by
    have hc : (fun i => ‖A i‖) ∘ (Nat.cast : ℕ → ℤ) = fun n => ‖a n‖ := by
      funext n
      simp [A]
    rw [← hc]
    exact (Nat.cast_injective.summable_iff (fun i hi => by simp [hA i hi])).symm
  have ht : ∑' i, A i = ∑' n, a n := by
    rw [← hcomp]
    exact (Nat.cast_injective.tsum_eq (fun i hi => by
      by_contra h
      exact hi (hA i h))).symm
  unfold partialSum Summation.value
  have key' : ∀ i : ℤ, (if 0 ≤ i then m i.toNat else some 0).getD 0 = A i := fun i => congrFun key i
  simp only [Option.some_bind, key']
  by_cases h : (∀ n, (m n).isSome) ∧ Summable (fun n => ‖a n‖) ∧ Summable a
  · rw [if_pos ⟨hdef.mpr h.1, hn.mpr h.2.1, hs.mpr h.2.2⟩, if_pos h, ht]
  · rw [if_neg (fun g => h ⟨hdef.mp g.1, hn.mp g.2.1, hs.mp g.2.2⟩), if_neg h]

theorem mass_sumNatValue {α : Type} (k : ℕ → Option (D α)) :
    massValue (sumNatValue (some k)) = Summation.value norm (some (fun n => massValue (k n))) := by
  rw [← partialSum_nat]
  change partialSum (fun i => integrate (if 0 ≤ i then (k i.toNat).getD .invalid else .zero) _) = _
  congr 1
  funext i
  by_cases h : 0 ≤ i
  · rw [if_pos h, if_pos h]
    cases k i.toNat <;> rfl
  · rw [if_neg h, if_neg h]
    simp [integrate]

theorem weight_sumNatValue {α : Type} (f : Option (α → Option ℝ)) (f' : ℕ → Option (α → Option ℝ))
    (k : ℕ → Option (D α)) (hf : ∀ n, f' n = f) :
    weightValue f (sumNatValue (some k)) =
      f.bind (fun _ => sumNatValue (some (fun n => weightValue (f' n) (k n)))) := by
  obtain rfl : f' = fun _ => f := funext hf
  cases f with
  | none => rfl
  | some g =>
    change some (Presentation.sum _) = some (Presentation.sum _)
    congr 2
    funext i
    beta_reduce
    by_cases h : 0 ≤ i
    · rw [if_pos h, if_pos h]
      cases k i.toNat <;> rfl
    · rw [if_neg h, if_neg h]
      rfl

theorem bind_sumNatValue {α β : Type} (k : ℕ → Option (D α)) (g : Option (α → Option (D β)))
    (g' : ℕ → Option (α → Option (D β))) (hg : ∀ n, g' n = g) :
    bindValue (sumNatValue (some k)) g =
      g.bind (fun _ => sumNatValue (some (fun n => bindValue (k n) (g' n)))) := by
  obtain rfl : g' = fun _ => g := funext hg
  cases g with
  | none => rfl
  | some h =>
    change some (Presentation.sum _) = some (Presentation.sum _)
    congr 2
    funext i
    beta_reduce
    by_cases hi : 0 ≤ i
    · rw [if_pos hi, if_pos hi]
      cases k i.toNat <;> rfl
    · rw [if_neg hi, if_neg hi]
      rfl

namespace GraphFibre

theorem realBind_sumNatValue {α : Type} (k : ℕ → Option (D α)) (g : Option (α → Option (D ℝ)))
    (g' : ℕ → Option (α → Option (D ℝ))) (hg : ∀ n, g' n = g) :
    realBindValue (sumNatValue (some k)) g =
      g.bind (fun _ => sumNatValue (some (fun n => realBindValue (k n) (g' n)))) := by
  obtain rfl : g' = fun _ => g := funext hg
  cases g with
  | none => rfl
  | some h =>
    change some (Presentation.sum _) = some (Presentation.sum _)
    congr 2
    funext i
    beta_reduce
    by_cases hi : 0 ≤ i
    · rw [if_pos hi, if_pos hi]
      cases k i.toNat <;> rfl
    · rw [if_neg hi, if_neg hi]
      rfl


theorem realBind_sumValue {α : Type} (k : ℤ → Option (D α)) (g : Option (α → Option (D ℝ)))
    (g' : ℤ → Option (α → Option (D ℝ))) (hg : ∀ i, g' i = g) :
    realBindValue (sumValue (some k)) g =
      g.bind (fun _ => sumValue (some (fun i => realBindValue (k i) (g' i)))) := by
  obtain rfl : g' = fun _ => g := funext hg
  cases g with
  | none => rfl
  | some h =>
    change some (Presentation.sum _) = some (Presentation.sum _)
    congr 2
    funext i
    beta_reduce
    cases k i <;> rfl

end GraphFibre
end QSym.Distribution
