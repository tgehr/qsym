import QSym.Functions

namespace QSym.RadicalRecovery

theorem inverse_of_product {K : Type*} [Field K] (x y : K) (h : x*y=1) : x⁻¹=y := by
  have hx : x≠0 := by intro hx; simp [hx] at h
  apply mul_left_cancel₀ hx
  rw [mul_inv_cancel₀ hx, h]

end QSym.RadicalRecovery
