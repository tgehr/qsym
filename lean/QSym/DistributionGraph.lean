import QSym.DistributionRestrictedGraph
import QSym.Distribution

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory

theorem bind_masked_dirac_test (s : Set ℝ) (f : ℝ → ℝ) (t : ℝ → Option ℝ) :
    (bindValue lebesgueValue (some (fun x =>
      scaleValue (some (sourceWeight s x)) (diracValue (some (f x)))))).bind
      (fun d => integrate d t) = pushforwardTest s f t := by
  unfold pushforwardTest
  apply congrArg (partialIntegral volume)
  funext x
  change Value.mul (some 1) (Value.mul _ (t (f x))) = Value.mul _ (t (f x))
  cases t (f x) <;> simp [Value.mul]

/-- Pairing the native restricted chart with any partial test agrees with
the source-space integral, including tests undefined outside the image. -/
theorem pushforwardOn_test (s : Set ℝ) [DecidablePred (· ∈ s)] (f : ℝ → ℝ)
    (t : ℝ → Option ℝ) :
    (pushforwardOnValue (some (fun x => some (decide (x ∈ s)))) (some (fun x => some (f x)))).bind
      (fun d => integrate d t) = pushforwardTest s f t := by
  apply congrArg (partialIntegral volume)
  funext x
  by_cases h : x ∈ s <;> simp [pushforwardOnValue, Value.mask, sourceWeight, h]

theorem mass_pushforwardOn_total (p : Option (ℝ → Option Bool)) (f : ℝ → ℝ) :
    massValue (pushforwardOnValue p (some (fun x => some (f x)))) =
      massValue (weightValue (p.map (fun pred x => Value.mask (pred x) (some ((1 : ℤ) : ℝ)))) lebesgueValue) := by
  rw [Int.cast_one]
  cases p with
  | none => rfl
  | some p =>
    apply congrArg (partialIntegral volume)
    funext x
    change Value.mul _ (some 1) = Value.mul (Value.mul (some 1) _) (some 1)
    rw [Value.mul_one_left]
    rfl

theorem chartDensity_sourceWeight (s : Set ℝ) (f : ℝ → ℝ) (hf : Measurable f) (y : ℝ) :
    chartDensity (fun x => some (sourceWeight s x)) (fun x => some (f x)) y = marginalOn s f y := by
  classical
  have active : {x | some (sourceWeight s x) ≠ some 0} = s := by
    ext x
    by_cases h : x ∈ s <;> simp [sourceWeight, h]
  simp only [chartDensity, Value.Defined, Option.some.injEq, exists_eq', implies_true,
    Option.getD_some, true_and, if_pos hf, active, marginalOn]
  cases h : fibreOn s f y with
  | none => rfl
  | some atoms =>
    simp only [Option.some_bind]
    apply observe_congr
    intro a ha
    simp [sourceWeight, fibreOn_mem h ha]

/-- Both observations of a restricted graph are determined by its parameters.
For a total measurable map the pointwise observer uses exactly its active
finite regular fibre, including when the output chart is the identity. -/
theorem pushforwardOn_density (s : Set ℝ) [DecidablePred (· ∈ s)] (f : ℝ → ℝ)
    (hf : Measurable f) (y : ℝ) :
    densityAtValue (pushforwardOnValue (some (fun x => some (decide (x ∈ s))))
      (some (fun x => some (f x)))) (some y) = marginalOn s f y := by
  classical
  have weight : (fun x => Value.mask (some (decide (x ∈ s))) (some (1 : ℝ))) =
      fun x => some (sourceWeight s x) := by
    funext x
    by_cases hx : x ∈ s <;> simp [Value.mask, sourceWeight, hx]
  change densityAt (.density _ (fun x => some (f x))) y = _
  rw [weight]
  by_cases hi : (fun x => some (f x)) = some
  · have he : f = id := funext (fun x => Option.some.inj (congrFun hi x))
    subst f
    rw [hi, marginalOn_id, densityAt_density]
  · simp [densityAt, realFibre, hi, RealDensityFibre.density, chartDensity_sourceWeight s f hf]

/-- Embed a weighted fibre in the current frontend distribution type. -/
def presentation : List (ℝ × ℝ) → D ℝ
  | [] => .zero
  | [(a,c)] => .scale c (.dirac a)
  | (a,c) :: b :: rest => .add (.scale c (.dirac a)) (presentation (b :: rest))

theorem integrate_presentation (atoms : List (ℝ × ℝ)) (test : ℝ → Option ℝ) :
    integrate (presentation atoms) test = observe atoms test := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    obtain ⟨x,c⟩ := atom
    cases rest with
    | nil => cases h : test x <;> simp [presentation, integrate, observe, Value.mul, Value.add, h]
    | cons a rest =>
      change Value.add _ (integrate (presentation (a :: rest)) test) = Value.add _ _
      rw [ih]
      rfl

def value (g : Option (ℝ → Option ℝ)) (y : Option ℝ) : Option (D ℝ) :=
  (atomsValue g y).map presentation

theorem value_total (f : ℝ → ℝ) (hf : Measurable f) (y : ℝ) :
    value (some (fun x => some (f x))) (some y) = (fibre f y).map presentation := by
  rw [value, atomsValue_total f hf]

theorem mass_eq_marginal (g : Option (ℝ → Option ℝ)) (y : Option ℝ) :
    massValue (value g y) = marginal g y := by
  unfold value marginal
  cases atomsValue g y with
  | none => rfl
  | some atoms => exact integrate_presentation atoms _

theorem square_test {y : ℝ} (hy : 0 < y) (test : ℝ → Option ℝ) :
    (fibre square y).bind (fun atoms => integrate (presentation atoms) test) =
      Value.add (Value.mul (some (jac y)) (test (-√y))) (Value.mul (some (jac y)) (test (√y))) := by
  simpa only [integrate_presentation] using square_observe hy test

end QSym.Distribution.GraphFibre
