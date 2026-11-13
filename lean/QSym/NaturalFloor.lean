import QSym.Functions

namespace QSym.NaturalFloor

theorem exact {x : ℝ} {n : ℕ} (hl : (n : ℝ)≤x) (hu : x<(n : ℝ)+1) :
    Nat.floor x=n :=
  (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans hl)).mpr ⟨hl,hu⟩

end QSym.NaturalFloor
