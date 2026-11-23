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

namespace GraphFibre

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
