import QSym.DistributionRootCover

noncomputable section
namespace QSym.Distribution.GraphFibre
open Set

theorem squareCover_negative (f : ℝ → ℝ) {y : ℝ} (hy : y < 0) :
    RootCover univ (fun x => (f x)^2) y [] := by
  exact ⟨by simp [List.Sorted], fun x => by simp [ne_of_gt (lt_of_lt_of_le hy (sq_nonneg (f x)))]⟩

variable {f i d : ℝ → ℝ} (inner : GlobalInverseBranch f i d)
include inner

theorem squareCover_zero : RootCover univ (fun x => (f x)^2) 0 [i 0] := by
  have c : RootCover univ square 0 [0] := ⟨by simp [List.Sorted], fun x => by simp [square]⟩
  simpa [square] using c.precomp inner (zs := [i 0]) (by simp [List.Sorted]) (by simp)

/-- The two source half-lines can have opposite orientations. Supply the
sorted pair of pulled-back roots in the order required by the fibre model. -/
theorem squareCover_positive {y l r : ℝ} (hy : 0 < y) (order : l < r)
    (roots : (l = i (-√y) ∧ r = i (√y)) ∨ (l = i (√y) ∧ r = i (-√y))) :
    RootCover univ (fun x => (f x)^2) y [l,r] := by
  have h := square_positive_roots hy
  have c : RootCover univ square y [-√y,√y] :=
    ⟨h.sorted, fun x => by simpa only [mem_univ, true_and] using h.complete x⟩
  have mem : ∀ x, x ∈ [l,r] ↔ x ∈ [-√y,√y].map i := by
    rcases roots with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [or_comm]
  simpa [square] using c.precomp inner (zs := [l,r]) (by simp [List.Sorted, order]) mem

end QSym.Distribution.GraphFibre
