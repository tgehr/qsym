import QSym.DistributionRestrictedGraph
import Mathlib.MeasureTheory.Function.Jacobian

/-! Change of variables for one real graph branch. Branch integration tests
definedness on the selected source. A strict Iverson-weighted integral over
the whole line can additionally inspect values outside that source. -/
noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory Set

open Classical in
def branchIntegral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (s : Set ℝ) (g : ℝ → Option E) : Option E :=
  if (∀ x ∈ s, Value.Defined (g x)) ∧ IntegrableOn (fun x => (g x).getD 0) s then
    some (∫ x in s, (g x).getD 0) else none

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {s r : Set ℝ} {f d : ℝ → ℝ}

theorem branchIntegral_univ (g : ℝ → Option E) : branchIntegral univ g = partialIntegral volume g := by
  classical
  unfold branchIntegral partialIntegral
  apply ite_congr
  · simp [integrableOn_univ]
  · intro _
    rw [setIntegral_univ]
  · exact fun _ => rfl

theorem branchIntegral_congr (hs : MeasurableSet s) {g k : ℝ → Option E} (h : EqOn g k s) :
    branchIntegral s g = branchIntegral s k := by
  classical
  have body : EqOn (fun x => (g x).getD 0) (fun x => (k x).getD 0) s :=
    fun x hx => congrArg (fun v : Option E => v.getD 0) (h hx)
  have dom : (∀ x ∈ s, Value.Defined (g x)) ↔ ∀ x ∈ s, Value.Defined (k x) := by
    constructor <;> intro hg x hx <;> simpa only [h hx] using hg x hx
  exact ite_congr (propext (and_congr dom (integrableOn_congr_fun body hs)))
    (fun _ => congrArg some (setIntegral_congr_fun hs body)) (fun _ => rfl)

/-- Combine source branches even if their target images overlap. Absolute
integrability is checked on each branch before adding its signed result. A
shared source boundary of measure zero can be included in both domains. -/
theorem branchIntegral_union (hdis : AEDisjoint volume s r) (hr : NullMeasurableSet r volume)
    (g : ℝ → Option E) :
    branchIntegral (s ∪ r) g = Value.add (branchIntegral s g) (branchIntegral r g) := by
  classical
  let k := fun x => (g x).getD 0
  let valid := fun t => (∀ x ∈ t, Value.Defined (g x)) ∧ IntegrableOn k t
  have both : valid (s ∪ r) ↔ valid s ∧ valid r := by
    unfold valid
    rw [integrableOn_union]
    constructor
    · rintro ⟨h, hs, hr'⟩
      exact ⟨⟨fun x hx => h x (Or.inl hx), hs⟩, fun x hx => h x (Or.inr hx), hr'⟩
    · rintro ⟨⟨hs, is⟩, ⟨ht, it⟩⟩
      exact ⟨fun x hx => hx.elim (hs x) (ht x), is, it⟩
  change (if valid (s ∪ r) then some (∫ x in s ∪ r, k x) else none) =
    Value.add (if valid s then some (∫ x in s, k x) else none)
      (if valid r then some (∫ x in r, k x) else none)
  simp only [both]
  by_cases hs : valid s <;> by_cases ht : valid r <;> simp [hs, ht, Value.add]
  exact integral_union_ae hdis hr hs.2 ht.2

omit [CompleteSpace E] in
/-- Transport finite integrability in both directions as well as the integral.
The payload may be a tuple of signed tests. -/
theorem branch_changeOfVariables (hs : MeasurableSet s) (hi : InjOn f s)
    (hd : ∀ x ∈ s, HasDerivWithinAt f (d x) s x) (g : ℝ → E) :
    (IntegrableOn g (f '' s) ↔ IntegrableOn (fun x => |d x| • g (f x)) s) ∧
    (∫ y in f '' s, g y) = ∫ x in s, |d x| • g (f x) :=
  ⟨integrableOn_image_iff_integrableOn_abs_deriv_smul hs hd hi g,
   integral_image_eq_integral_abs_deriv_smul hs hd hi g⟩

/-- Pull a partial probe back through one branch. A zero derivative still
tests the probe at that point. No inverse or nonvanishing hypothesis is needed. -/
theorem branchIntegral_image (hs : MeasurableSet s) (hi : InjOn f s)
    (hd : ∀ x ∈ s, HasDerivWithinAt f (d x) s x) (g : ℝ → Option E) :
    branchIntegral (f '' s) g = branchIntegral s (fun x => (g (f x)).map (|d x| • ·)) := by
  classical
  have dom : (∀ y ∈ f '' s, Value.Defined (g y)) ↔
      ∀ x ∈ s, Value.Defined ((g (f x)).map (|d x| • ·)) := by
    simp only [Set.forall_mem_image]
    apply forall_congr'
    intro x
    apply forall_congr'
    intro _
    cases g (f x) <;> simp [Value.Defined]
  have body (x : ℝ) : ((g (f x)).map (|d x| • ·)).getD 0 = |d x| • (g (f x)).getD 0 := by
    cases g (f x) <;> simp
  obtain ⟨hint, heq⟩ := branch_changeOfVariables hs hi hd (fun y => (g y).getD 0)
  unfold branchIntegral
  simp_rw [body]
  exact ite_congr (propext (and_congr dom hint)) (fun _ => congrArg some heq) (fun _ => rfl)

/-- A branch with zero, defined values off its support integrates over the whole line. -/
theorem branchIntegral_eq_full (hs : MeasurableSet s) (g : ℝ → Option E)
    (hz : ∀ x ∉ s, g x = some 0) : branchIntegral s g = partialIntegral volume g := by
  classical
  have dom : (∀ x ∈ s, Value.Defined (g x)) ↔ ∀ x, Value.Defined (g x) :=
    ⟨fun h x => if hx : x ∈ s then h x hx else ⟨0, hz x hx⟩, fun h x _ => h x⟩
  let k := fun x => (g x).getD 0
  have ind : s.indicator k = k := by
    funext x
    by_cases hx : x ∈ s <;> simp [k, indicator, hx, hz]
  have hint := integrable_indicator_iff (μ := volume) (f := k) hs
  have heq := integral_indicator (μ := volume) (f := k) hs
  rw [ind] at hint heq
  exact ite_congr (propext (and_congr dom hint.symm))
    (fun _ => congrArg some heq.symm) (fun _ => rfl)

/-- Reconstruct a graph from its unnormalized pointwise fibres on one regular
injective branch, for any partial signed joint test. -/
theorem injectiveBranch_disintegrates (hs : MeasurableSet s) (hi : InjOn f s)
    (hd : ∀ x ∈ s, HasStrictDerivAt f (d x) x) (hn : ∀ x ∈ s, d x ≠ 0)
    (h : ℝ → ℝ → Option ℝ) :
    branchIntegral s (fun x => h x (f x)) = partialIntegral volume (fun y =>
      (fibreOn s f y).bind (fun atoms => observe atoms (fun x => h x y))) := by
  let k := fun y => (fibreOn s f y).bind (fun atoms => observe atoms (fun x => h x y))
  have pull (x : ℝ) (hx : x ∈ s) : (k (f x)).map (|d x| • ·) = h x (f x) := by
    dsimp only [k]
    rw [fibreOn_of_injOn hi hx (hd x hx) (hn x hx)]
    cases he : h x (f x) <;>
      simp [observe, Value.mul, Value.add, he, smul_eq_mul, ← mul_assoc, abs_ne_zero.mpr (hn x hx)]
  have hwithin := fun x hx => (hd x hx).hasDerivAt.hasDerivWithinAt (s := s)
  have hm : MeasurableSet (f '' s) := hs.image_of_continuousOn_injOn
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) hi
  change _ = partialIntegral volume k
  rw [← branchIntegral_eq_full hm k (fun y hy => by simp [k, fibreOn_of_notMem_image hy, observe]),
    branchIntegral_image hs hi hwithin]
  exact branchIntegral_congr hs (fun x hx => (pull x hx).symm)

open Classical in
/-- Strict weighting by an Iverson factor still probes every excluded source
point. Once those probes are defined, regular fibres reconstruct the result. -/
theorem injectiveBranch_disintegrates_masked (hs : MeasurableSet s) (hi : InjOn f s)
    (hd : ∀ x ∈ s, HasStrictDerivAt f (d x) x) (hn : ∀ x ∈ s, d x ≠ 0)
    (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mul (some (sourceWeight s x)) (h x (f x))) =
      if ∀ x ∉ s, Value.Defined (h x (f x)) then
        partialIntegral volume (fun y => (fibreOn s f y).bind (fun atoms => observe atoms (fun x => h x y)))
      else none := by
  let g := fun x => Value.mul (some (sourceWeight s x)) (h x (f x))
  by_cases ho : ∀ x ∉ s, Value.Defined (h x (f x))
  · have hz (x : ℝ) (hx : x ∉ s) : g x = some 0 := by
      obtain ⟨v, hv⟩ := ho x hx
      simp [g, hv, sourceWeight, hx, Value.mul]
    rw [if_pos ho, ← injectiveBranch_disintegrates hs hi hd hn h, ← branchIntegral_eq_full hs g hz]
    apply branchIntegral_congr hs
    intro x hx
    simp [g, sourceWeight, hx, Value.mul_one_left]
  · rw [if_neg ho, partialIntegral, if_neg]
    intro valid
    apply ho
    intro x _
    obtain ⟨v, hv⟩ := valid.1 x
    cases he : h x (f x) with
    | none => simp [he, Value.mul] at hv
    | some v => exact ⟨v, rfl⟩

open Classical in
/-- A null exceptional set contributes exactly the strict source-domain guard.
Its values need no derivative or inverse and are queried pointwise. -/
theorem branchIntegral_remove_null (hr : r ⊆ s) (hae : s =ᵐ[volume] r) (g : ℝ → Option E) :
    branchIntegral s g = if ∀ x ∈ s \ r, Value.Defined (g x) then branchIntegral r g else none := by
  by_cases he : ∀ x ∈ s \ r, Value.Defined (g x)
  · rw [if_pos he]
    have dom : (∀ x ∈ s, Value.Defined (g x)) ↔ ∀ x ∈ r, Value.Defined (g x) :=
      ⟨fun h x hx => h x (hr hx), fun h x hx => if hxr : x ∈ r then h x hxr else he x ⟨hx, hxr⟩⟩
    simp only [branchIntegral, dom, IntegrableOn, Measure.restrict_congr_set hae]
  · rw [if_neg he, branchIntegral, if_neg]
    exact fun h => he fun x hx => h.1 x hx.1

open Classical in
/-- Reconstruct on regular fibres and check the omitted source points, including
critical points that have zero mass but can carry an undefined probe. -/
theorem injectiveBranch_disintegrates_ae (hr : r ⊆ s) (hae : s =ᵐ[volume] r)
    (hm : MeasurableSet r) (hi : InjOn f r) (hd : ∀ x ∈ r, HasStrictDerivAt f (d x) x)
    (hn : ∀ x ∈ r, d x ≠ 0) (h : ℝ → ℝ → Option ℝ) :
    branchIntegral s (fun x => h x (f x)) =
      if ∀ x ∈ s \ r, Value.Defined (h x (f x)) then
        partialIntegral volume (fun y => (fibreOn r f y).bind (fun atoms => observe atoms (fun x => h x y)))
      else none := by
  rw [branchIntegral_remove_null hr hae, injectiveBranch_disintegrates hm hi hd hn]

end QSym.Distribution.GraphFibre
