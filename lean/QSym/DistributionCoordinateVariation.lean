import QSym.DistributionBranch
import QSym.DistributionGraph
import Mathlib.Topology.Order.LeftRightLim

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates
open Classical Set Filter Topology

/-- A finite decomposition whose cuts are intrinsic to the displayed function.
Requiring an endpoint to equal one of its traces leaves isolated spikes outside
this class. Regular open pieces need only be locally C¹. -/
structure VariationChart where
  coord : ℝ → ℝ
  cuts : List ℝ
  sorted : cuts.Sorted (· < ·)
  exceptional : ∀ x, x ∈ cuts ↔ ¬ DifferentiableAt ℝ coord x
  regular : ∀ x ∉ cuts, ContDiffAt ℝ 1 coord x
  limits : ∀ x ∈ cuts, ∃ l r, Tendsto coord (𝓝[<] x) (𝓝 l) ∧
    Tendsto coord (𝓝[>] x) (𝓝 r) ∧ (coord x = l ∨ coord x = r)

namespace VariationChart

theorem ext_coord {a b : VariationChart} (h : a.coord = b.coord) : a = b := by
  cases a with | mk f as sa ea ra la =>
  cases b with | mk g bs sb eb rb lb =>
  cases h
  have eq := sa.eq_of_mem_iff sb (fun x => (ea x).trans (eb x).symm)
  cases eq
  rfl

def smooth (g : ℝ → ℝ) (h : ContDiff ℝ 1 g) : VariationChart where
  coord := g
  cuts := []
  sorted := List.Pairwise.nil
  exceptional x := by simp [h.differentiable le_rfl x]
  regular x _ := h.contDiffAt
  limits _ hx := False.elim (List.not_mem_nil hx)

/-- A zero-mass chart with one active critical parameter. Its pointwise
density is missing at a, while every total test pairs to zero. -/
def corner (a : ℝ) (active : Option Bool) : Option (D ℝ) :=
  realPushforwardOnValue (some fun s => if s = 0 then active else some false)
    (some fun s => some (s^2 + a))

def atom (a : ℝ) (w : Option ℝ) :=
  if w = some 1 then diracValue (some a) else scaleValue w (diracValue (some a))

/-- The source of a jump traverses the interval between the one-sided
coordinate values. Restricting that source integrates the predicate there. -/
def atCut (g : ℝ → ℝ) (a : ℝ) (p : Option (ℝ → Option Bool)) : Option (D ℝ) :=
  let l := Function.leftLim g a
  let r := Function.rightLim g a
  if l = r then corner a (p.elim (some true) (fun q => q (g a)))
  else atom a (p.elim (some |r-l|) (fun q => branchIntegral (uIcc l r)
    (fun z => Value.mask (q z) (some 1))))

/-- Source-checkable one-sided limits determine the entire cut contribution,
including a restriction through the interior of a jump. -/
theorem atCut_of_limits {g : ℝ → ℝ} {a l r : ℝ} (hl : Tendsto g (𝓝[<] a) (𝓝 l))
    (hr : Tendsto g (𝓝[>] a) (𝓝 r)) (p : Option (ℝ → Option Bool)) :
    atCut g a p = if l = r then corner a (p.elim (some true) (fun q => q (g a)))
      else atom a (p.elim (some |r-l|) (fun q => branchIntegral (uIcc l r)
        (fun z => Value.mask (q z) (some 1)))) := by
  rw [atCut, leftLim_eq_of_tendsto (NeBot.ne inferInstance) hl,
    rightLim_eq_of_tendsto (NeBot.ne inferInstance) hr]

def present (c : VariationChart) (p : Option (ℝ → Option Bool)) : Option (D ℝ) :=
  let regular := weightValue (some fun x => p.elim (some |deriv c.coord x|)
    (fun q => Value.mask (q (c.coord x)) (some |deriv c.coord x|))) lebesgueValue
  c.cuts.foldr (fun a d => addValue (atCut c.coord a p) d) regular

/-- Regular pieces form a density even with a partial source predicate. The
only remaining construction obligations are the individual cuts. -/
theorem present_isSome_iff (c : VariationChart) (p : Option (ℝ → Option Bool)) :
    (c.present p).isSome = true ↔ ∀ a ∈ c.cuts, (atCut c.coord a p).isSome = true := by
  let regular := weightValue (some fun x => p.elim (some |deriv c.coord x|)
    (fun q => Value.mask (q (c.coord x)) (some |deriv c.coord x|))) lebesgueValue
  change (c.cuts.foldr (fun a d => addValue (atCut c.coord a p) d) regular).isSome = true ↔ _
  have add (a b : Option (D ℝ)) : (addValue a b).isSome = true ↔ a.isSome = true ∧ b.isSome = true := by
    cases a <;> cases b <;> simp [addValue]
  induction c.cuts with
  | nil => simp [regular, weightValue, weight, lebesgueValue, densityValue]
  | cons x xs ih => simp only [List.foldr_cons, add, ih, List.forall_mem_cons]

theorem present_isSome (c : VariationChart) : (c.present none).isSome = true := by
  apply (c.present_isSome_iff none).2
  intro x _
  by_cases h : Function.leftLim c.coord x = Function.rightLim c.coord x
  · rw [atCut, if_pos h]
    rfl
  · rw [atCut, if_neg h]
    unfold atom
    split <;> rfl

end VariationChart
end QSym.Distribution.GraphFibre.Coordinates
