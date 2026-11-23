import QSym.DistributionBranch

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set Classical

/-- A coordinate g is used only on its certified target domain. Its right
inverse law makes it injective there. Different sheets may share targets. -/
structure InverseSheet (f : ℝ → ℝ) where
  target : Set ℝ
  point : ℝ → ℝ
  slope : ℝ → ℝ
  measurable : MeasurableSet target
  rightInv : ∀ y ∈ target, f (point y) = y
  derivWithin : ∀ y ∈ target, HasDerivWithinAt point (slope y) target y

namespace InverseSheet
variable {f : ℝ → ℝ} (b : InverseSheet f)

def source := b.point '' b.target

theorem injOn : InjOn b.point b.target := fun x hx y hy eq =>
  (b.rightInv x hx).symm.trans ((congrArg f eq).trans (b.rightInv y hy))

private theorem continuousOn : ContinuousOn b.point b.target :=
  fun y hy => (b.derivWithin y hy).continuousWithinAt

theorem measurableSource : MeasurableSet b.source :=
  b.measurable.image_of_continuousOn_injOn b.continuousOn b.injOn

/-- On an open regular branch the inverse Jacobian is the reciprocal of the
forward Jacobian at the selected root. -/
theorem reciprocal {y d : ℝ} (hy : y ∈ b.target) (neighbourhood : b.target ∈ nhds y)
    (hf : HasDerivAt f d (b.point y)) : |b.slope y| = |d|⁻¹ := by
  have hc := hf.comp y ((b.derivWithin y hy).hasDerivAt neighbourhood)
  have he : f ∘ b.point =ᶠ[nhds y] id :=
    Filter.mem_of_superset neighbourhood (fun z hz => b.rightInv z hz)
  have prod : d * b.slope y = 1 := (hc.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id y)
  have eq : b.slope y = d⁻¹ := eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans prod)
  rw [eq, abs_inv]

/-- The guard is evaluated before the joint test. An earlier sheet may
already have consumed the same source point. -/
def contribution (remaining : Set ℝ) (h : ℝ → ℝ → Option ℝ) :=
  partialIntegral volume (fun y => if y ∈ b.target ∧ b.point y ∈ remaining then
    (h (b.point y) y).map (|b.slope y| * ·) else some 0)

/-- Split off one inverse coordinate as an ordinary target Lebesgue integral.
The residual is still expressed in source coordinates. -/
theorem split (remaining : Set ℝ) (hm : MeasurableSet remaining) (h : ℝ → ℝ → Option ℝ) :
    branchIntegral remaining (fun x => h x (f x)) = Value.add (b.contribution remaining h)
      (branchIntegral (remaining \ b.source) (fun x => h x (f x))) := by
  let active := b.target ∩ b.point ⁻¹' remaining
  have sub : active ⊆ b.target := inter_subset_left
  have m : MeasurableSet active := by
    have ext := b.continuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const b.measurable
    convert b.measurable.inter (ext hm) using 1
    ext y
    by_cases hy : y ∈ b.target <;> simp [active, hy]
  have partition : remaining = (b.point '' active) ∪ (remaining \ b.source) := by
    ext x
    constructor
    · intro hx
      by_cases hi : x ∈ b.source
      · obtain ⟨y,hy,rfl⟩ := hi
        exact Or.inl ⟨y,⟨hy,hx⟩,rfl⟩
      · exact Or.inr ⟨hx,hi⟩
    · rintro (⟨y,hy,rfl⟩ | hx)
      · exact hy.2
      · exact hx.1
  have dis : Disjoint (b.point '' active) (remaining \ b.source) :=
    disjoint_left.mpr fun _ hx hr => hr.2 (image_mono sub hx)
  conv_lhs => rw [partition]
  rw [branchIntegral_union dis.aedisjoint (hm.diff b.measurableSource).nullMeasurableSet]
  apply congrArg (fun v => Value.add v _)
  rw [branchIntegral_image m (b.injOn.mono sub) (fun y hy => (b.derivWithin y (sub hy)).mono sub)]
  let row := fun y => if y ∈ b.target ∧ b.point y ∈ remaining then
    (h (b.point y) y).map (|b.slope y| * ·) else some 0
  change _ = partialIntegral volume row
  rw [← branchIntegral_eq_full m row (fun y hy => if_neg hy)]
  apply branchIntegral_congr m
  intro y hy
  have hr : b.point y ∈ remaining := hy.2
  simp [row, hy.1, hr, b.rightInv y hy.1, smul_eq_mul]

/-- Remove covered source points after each step. All unhandled points,
including critical sets of positive measure, keep their original graph. -/
def sum (remaining : Set ℝ) (h : ℝ → ℝ → Option ℝ) : List (InverseSheet f) → Option ℝ
  | [] => branchIntegral remaining (fun x => h x (f x))
  | b :: bs => Value.add (b.contribution remaining h) (sum (remaining \ b.source) h bs)

theorem reconstruct (bs : List (InverseSheet f)) (remaining : Set ℝ)
    (hm : MeasurableSet remaining) (h : ℝ → ℝ → Option ℝ) :
    branchIntegral remaining (fun x => h x (f x)) = sum remaining h bs := by
  induction bs generalizing remaining with
  | nil => rfl
  | cons b bs ih =>
    rw [b.split remaining hm, sum, ← ih _ (hm.diff b.measurableSource)]

end InverseSheet
end QSym.Distribution.GraphFibre
