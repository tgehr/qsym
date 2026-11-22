import QSym.DistributionInverseBranch
import QSym.FunctionOrder

noncomputable section
namespace QSym.Distribution.GraphFibre

def oddDegree (k : ℕ) := 2*k+3

def oddRoot (k : ℕ) (y : ℝ) : ℝ :=
  let t := (oddDegree k : ℝ)⁻¹
  if y < 0 then -((-y)^t) else y^t

theorem oddDegree_odd (k : ℕ) : Odd (oddDegree k) := ⟨k+1, by unfold oddDegree; omega⟩
theorem oddDegree_pos (k : ℕ) : 0 < oddDegree k := by unfold oddDegree; omega

theorem oddRoot_pow (k : ℕ) (y : ℝ) : (oddRoot k y) ^ oddDegree k = y := by
  have hn : (oddDegree k : ℝ) ≠ 0 := by exact_mod_cast (oddDegree_pos k).ne'
  have positive (z : ℝ) (hz : 0 ≤ z) : (z ^ (oddDegree k : ℝ)⁻¹) ^ oddDegree k = z := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz, inv_mul_cancel₀ hn, Real.rpow_one]
  by_cases hy : y < 0
  · simp [oddRoot, hy, (oddDegree_odd k).neg_pow, positive _ (neg_nonneg.mpr hy.le)]
  · simp [oddRoot, hy, positive _ (le_of_not_gt hy)]

def oddSlope (k : ℕ) (x : ℝ) := (oddDegree k : ℝ) * x ^ (oddDegree k - 1)

theorem oddPowerBranch (k : ℕ) :
    GlobalInverseBranch (fun x => x ^ oddDegree k) (oddRoot k) (oddSlope k) :=
  ⟨(oddDegree_odd k).pow_injective, oddRoot_pow k, hasStrictDerivAt_pow _⟩

theorem oddSlope_nonneg (k : ℕ) (x : ℝ) : 0 ≤ oddSlope k x := by
  have he : Even (oddDegree k - 1) := ⟨k+1, by unfold oddDegree; omega⟩
  exact mul_nonneg (Nat.cast_nonneg _) (he.pow_nonneg x)

def oddWeight (k : ℕ) (y : ℝ) := Value.inv (some (oddSlope k (oddRoot k y)))

theorem oddPower_fibre (k : ℕ) (y : ℝ) :
    fibre (fun x => x ^ oddDegree k) y = (oddWeight k y).map (fun w => [(oddRoot k y, w)]) := by
  rw [← fibreOn_univ, (oddPowerBranch k).fibreOn_eq]
  by_cases hz : oddSlope k (oddRoot k y) = 0 <;> simp [oddWeight, Value.inv, hz, abs_of_nonneg (oddSlope_nonneg k _)]

theorem oddPower_masked (k : ℕ) (p : ℝ → Option Bool) (y : ℝ) :
    maskedAtoms p (fun x => x ^ oddDegree k) y =
      (Value.mask (p (oddRoot k y)) (oddWeight k y)).map (fun w => [(oddRoot k y,w)]) := by
  simpa only [oddWeight, abs_of_nonneg (oddSlope_nonneg k _)] using (oddPowerBranch k).maskedAtoms_eq p y

/-- The active inverse point determines the pushforward density. This also
handles a partial predicate and a predicate that excludes a critical root. -/
theorem oddPower_density (k : ℕ) (p : ℝ → Option Bool) (y : ℝ) :
    densityAtValue (realPushforwardOnValue (some p) (some fun x => some (x ^ oddDegree k))) (some y) =
      Value.mask (p (oddRoot k y)) (oddWeight k y) := by
  simpa only [oddWeight, abs_of_nonneg (oddSlope_nonneg k _)] using (oddPowerBranch k).density_eq p y

/-- If the source predicate is total and excludes zero, the whole pushforward
admits ordinary Lebesgue coordinates. Transport uses the forward derivative
on the entire source, including the excluded critical point. -/
theorem oddPower_chart (k : ℕ) (p : ℝ → Option Bool) (hp : ∀ x, Value.Defined (p x))
    (h0 : p 0 = some false) :
    realPushforwardOnValue (some p) (some fun x => some (x ^ oddDegree k)) =
      densityValue (some fun y => Value.mask (p (oddRoot k y)) (oddWeight k y)) := by
  have critical (x : ℝ) (hz : oddSlope k x = 0) : p x = some false := by
    by_contra h
    have hx : x ≠ 0 := fun h' => h (h' ▸ h0)
    exact (mul_ne_zero (Nat.cast_ne_zero.mpr (oddDegree_pos k).ne') (pow_ne_zero _ hx)) hz
  simpa only [oddWeight, abs_of_nonneg (oddSlope_nonneg k _)] using
    (oddPowerBranch k).lebesgueChart p hp critical

end QSym.Distribution.GraphFibre
