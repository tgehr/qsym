import QSym.Numeric

noncomputable section
namespace QSym.Distribution.StepSource

/-- A partial value that is not zero where it is defined. -/
def Nonvanishing (c : Option ℝ) : Prop := ∀ s, c = some s → s ≠ 0

theorem Nonvanishing.inv (c : Option ℝ) : Nonvanishing (Value.inv c) := by
  intro s hs
  rcases c with _ | v
  · cases hs
  · by_cases hv : v = 0
    · simp [Value.inv, hv] at hs
    · have he : (some v⁻¹ : Option ℝ) = some s := by simpa [Value.inv, hv] using hs
      rw [← Option.some.inj he]
      exact inv_ne_zero hv

theorem Nonvanishing.literal {c : Option ℝ} (q : ℚ)
    (h : c = some (Numeric.denote (s := .real) q)) (hq : decide (q ≠ 0) = true) :
    Nonvanishing c := by
  intro s hs
  rw [h] at hs
  rw [← Option.some.inj hs]
  have hr : (q : ℝ) ≠ 0 := by exact_mod_cast of_decide_eq_true hq
  simpa [Numeric.denote] using hr

theorem Nonvanishing.pi {c : Option ℝ} (h : c = some Functions.pi) : Nonvanishing c := by
  intro s hs
  rw [h] at hs
  rw [← Option.some.inj hs]
  exact Real.pi_pos.ne'

theorem Nonvanishing.mul {a b : Option ℝ} (ha : Nonvanishing a) (hb : Nonvanishing b) :
    Nonvanishing (Value.mul a b) := by
  intro s hs
  rcases a with _ | x
  · cases hs
  · rcases b with _ | y
    · cases hs
    · rw [← Option.some.inj hs]
      exact mul_ne_zero (ha x rfl) (hb y rfl)

end QSym.Distribution.StepSource
