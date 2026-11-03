import QSym.Value

/-! A finite Dirac model for the next IR extension. These are actual vectors,
not generalized position eigenvectors. No quantum rewrite is enabled in D yet. -/
namespace QSym.Quantum
abbrev Ket (n : ℕ) := Fin n → ℂ
abbrev Operator (m n : ℕ) := Fin m → Fin n → ℂ

noncomputable def basis {n : ℕ} (x : Fin n) : Ket n := fun y => if y = x then 1 else 0
noncomputable def inner {n : ℕ} (v w : Ket n) : ℂ := ∑ i, star (v i) * w i
noncomputable def outer {m n : ℕ} (v : Ket m) (w : Ket n) : Operator m n :=
  fun y x => v y * star (w x)
noncomputable def apply {m n : ℕ} (a : Operator m n) (v : Ket n) : Ket m :=
  fun y => ∑ x, a y x * v x

theorem basis_inner {n : ℕ} (x y : Fin n) :
    inner (basis x) (basis y) = if x = y then 1 else 0 := by
  classical
  simp [inner, basis, eq_comm]

-- Continuous parameters can index ordinary, finite-dimensional states.
-- This is an unnormalized phase family, so no normalization is implicit.
noncomputable def phaseFamily (θ : ℝ) : Ket 2 :=
  fun j => if j = 0 then 1 else Complex.exp ((θ : ℂ) * Complex.I)

-- The user's Fourier matrix, deliberately without the 1/sqrt(n) normalization.
noncomputable def fourier (n : ℕ) : Operator n n := fun y x =>
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x.val : ℂ) * (y.val : ℂ) / (n : ℂ))

end QSym.Quantum
