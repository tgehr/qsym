import QSym.Limit
import QSym.DistributionStepSource

/-! Terms that are eventually constant because the variable has passed every
cut of their guards: the last cell of a step grid reaches the end of the line. -/
namespace QSym.Limit
open Filter
open QSym.Distribution.StepSource

/-- The region contains the end of the line the filter looks at. -/
def Tail (l : Filter ℝ) (r : Region) : Prop := ∀ᶠ x in l, r.contains x

theorem tail_after (c : ℚ) : Tail atTop (.after c) := eventually_gt_atTop (c : ℝ)

theorem tail_before (c : ℚ) : Tail atBot (.before c) := eventually_lt_atBot (c : ℝ)

/-- Constancy on such a region gives the value at its sample eventually. -/
theorem Eventual.step {β : Type} {l : Filter ℝ} {r : Region} {p : ℝ → β} {v g : β}
    (ht : Tail l r) (s : ℚ) (hs : r.sample = s) (hu : Uniform r p) (hv : p (s : ℝ) = v)
    (hg : g = v) : Eventual l p g := by
  subst hs hg
  exact ht.mono fun x hx => (hu x hx).trans hv

end QSym.Limit
