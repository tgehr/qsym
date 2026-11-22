import QSym.DistributionGraphModel
import QSym.Integration

noncomputable section
namespace QSym.Distribution.GraphFibre
open Set Classical MeasureTheory

def sourceWeight (s : Set ℝ) (x : ℝ) : ℝ := if x ∈ s then 1 else 0

/-- The existing source integral multiplies a partial test strictly by the
Iverson weight. Keep this observer on the source coordinates even when the
pointwise target density has a simpler formula. -/
def pushforwardTest (s : Set ℝ) (f : ℝ → ℝ) (t : ℝ → Option ℝ) : Option ℝ :=
  partialIntegral volume (fun x => Value.mul (some (sourceWeight s x)) (t (f x)))

theorem pushforwardTest_total {s : Set ℝ} (hs : MeasurableSet s) (f k : ℝ → ℝ)
    (hk : IntegrableOn (fun x => k (f x)) s) :
    pushforwardTest s f (fun y => some (k y)) = some (∫ x in s, k (f x)) := by
  let g := s.indicator (fun x => k (f x))
  have body : (fun x => Value.mul (some (sourceWeight s x)) (some (k (f x)))) =
      fun x => some (g x) := by
    funext x
    by_cases hx : x ∈ s <;> simp [sourceWeight, hx, g, indicator, Value.mul]
  rw [pushforwardTest, body, partialIntegral_valid]
  · simp [g, integral_indicator hs]
  · intro x
    exact ⟨g x, rfl⟩
  · exact hk.integrable_indicator hs

theorem square_injOn_positiveSource {s : Set ℝ} (hs : s ⊆ Ioi 0) : InjOn square s := by
  intro x hx z hz he
  simpa only [square, Real.sqrt_sq (le_of_lt (hs hx)), Real.sqrt_sq (le_of_lt (hs hz))] using
    congrArg Real.sqrt he

/-- A subset of the positive half-line selects at most one inverse branch.
The certificate is pointwise, so removing a singleton from the source removes
its inverse branch at the corresponding target. -/
theorem square_fibreOn_positiveSource {s : Set ℝ} (hs : s ⊆ Ioi 0) (y : ℝ) :
    fibreOn s square y = some (if √y ∈ s then [(√y, jac y)] else []) := by
  classical
  have root {x : ℝ} (hx : x ∈ s) (he : square x = y) : √y = x := by
    rw [← he, square, Real.sqrt_sq (le_of_lt (hs hx))]
  by_cases hy : √y ∈ s
  · rw [if_pos hy]
    have hp : 0 < √y := hs hy
    have eq : square (√y) = y := Real.sq_sqrt (Real.sqrt_pos.mp hp).le
    have hd : HasStrictDerivAt square (2 * √y) (√y) := by
      simpa [square] using hasStrictDerivAt_pow 2 (√y)
    simpa only [eq, abs_mul, abs_of_pos hp, abs_of_pos (by norm_num : (0 : ℝ) < 2), jac, one_div] using
      fibreOn_of_injOn (square_injOn_positiveSource hs) hy hd (by positivity)
  · rw [if_neg hy]
    apply fibreOn_of_notMem_image
    rintro ⟨x, hx, he⟩
    exact hy ((root hx he).symm ▸ hx)

def marginalOn (s : Set ℝ) (f : ℝ → ℝ) (y : ℝ) : Option ℝ :=
  (fibreOn s f y).bind (fun atoms => observe atoms (fun _ => some 1))

theorem marginalOn_id (s : Set ℝ) (y : ℝ) : marginalOn s id y = some (sourceWeight s y) := by
  classical
  by_cases h : y ∈ s
  · have roots : RegularRootList id (fun x => x ∈ s ∧ id x = y) [y] := by
      constructor
      · simp [List.Sorted]
      · intro x
        simp only [List.mem_singleton, id_eq, iff_and_self]
        exact fun e => e ▸ h
      · intro x _
        simpa using And.intro (hasStrictDerivAt_id x) (one_ne_zero : (1 : ℝ) ≠ 0)
    simp [marginalOn, fibreOn_of_regular roots, observe, sourceWeight, h, Value.mul, Value.add]
  · have roots : RegularRootList id (fun x => x ∈ s ∧ id x = y) [] := by
      constructor
      · simp [List.Sorted]
      · intro x
        simp only [List.not_mem_nil, id_eq, false_iff]
        rintro ⟨hx, rfl⟩
        exact h hx
      · simp
    simp [marginalOn, fibreOn_of_regular roots, observe, sourceWeight, h]

theorem square_marginalOn_positiveSource {s : Set ℝ} (hs : s ⊆ Ioi 0) (y : ℝ) :
    marginalOn s square y = some (if √y ∈ s then jac y else 0) := by
  rw [marginalOn, square_fibreOn_positiveSource hs]
  split <;> simp [observe, Value.add, Value.mul]

theorem square_marginalOn_openUnit (y : ℝ) :
    marginalOn (Ioo 0 1) square y = some (if 0 < y ∧ y < 1 then jac y else 0) := by
  rw [square_marginalOn_positiveSource (fun _ hx => hx.1)]
  simp [mem_Ioo, Real.sqrt_pos, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]

end QSym.Distribution.GraphFibre
