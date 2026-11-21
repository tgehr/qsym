import QSym.DistributionRestrictedGraph
import QSym.Distribution
import QSym.RefinementBase

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

/-- Pairing the restricted parameter chart with any partial test agrees with
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

/-- Both observations of the source chart are determined by its parameters.
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

/-- A real chart is eligible for Lebesgue coordinates only if its retained
density exists at every point and reconstructs all total real tests, with the
same finite-integrability domain. -/
structure LebesgueChart (d : D ℝ) (w : ℝ → Option ℝ) : Prop where
  density : densityAt d = w
  total : ∀ y, Value.Defined (w y)
  reconstruct : ∀ t : ℝ → ℝ, integrate d (fun y => some (t y)) =
    integrate (.density w some) (fun y => some (t y))

/-- Partial tests on a regular real distribution use its target coordinates,
as on any other ordinary Lebesgue density. A missing pointwise value keeps
the parameter chart, even if a density exists almost everywhere. -/
def inLebesgueCoordinates (d : D ℝ) : D ℝ := by
  classical
  exact if LebesgueChart d (densityAt d) then .density (densityAt d) some else d

theorem inLebesgueCoordinates_of_chart {d w} (h : LebesgueChart d w) :
    inLebesgueCoordinates d = .density w some := by
  rw [inLebesgueCoordinates, h.density, if_pos h]

theorem coordinates_of_missing_density {d : D ℝ} {y : ℝ} (hy : densityAt d y = none) :
    inLebesgueCoordinates d = d := by
  unfold inLebesgueCoordinates
  apply if_neg
  intro h
  have := h.total y
  simp [hy, Value.Defined] at this

theorem coordinates_density (d : D ℝ) : densityAt (inLebesgueCoordinates d) = densityAt d := by
  unfold inLebesgueCoordinates
  split
  · funext y
    exact densityAt_density _ _
  · rfl

theorem coordinates_test (d : D ℝ) (t : ℝ → ℝ) :
    integrate (inLebesgueCoordinates d) (fun y => some (t y)) = integrate d (fun y => some (t y)) := by
  unfold inLebesgueCoordinates
  split
  · rename_i h
    exact (h.reconstruct t).symm
  · rfl

/-- A defined answer in target coordinates is also the original parameter
answer, even for a test supplied as a partial function. -/
theorem coordinates_partial (d : D ℝ) (t : ℝ → Option ℝ) :
    Value.Refines (integrate (inLebesgueCoordinates d) t) (integrate d t) := by
  classical
  intro a ha
  unfold inLebesgueCoordinates at ha
  split at ha
  · rename_i h
    let body := fun y => Value.mul (densityAt d y) (t y)
    change partialIntegral volume body = some a at ha
    have defined := ((partialIntegral_defined_iff _ _).mp ⟨a, ha⟩).1
    have he : t = fun y => some ((t y).getD 0) := by
      funext y
      cases ht : t y with
      | some v => rfl
      | none =>
        have hd := defined y
        cases hw : densityAt d y <;> simp [body, ht, hw, Value.mul, Value.Defined] at hd
    exact ((congrArg (integrate d) he).trans ((h.reconstruct _).trans
      (congrArg (integrate (.density (densityAt d) some)) he.symm))).trans ha
  · exact ha

theorem coordinates_identity (w : ℝ → Option ℝ) :
    inLebesgueCoordinates (.density w some) = .density w some := by
  unfold inLebesgueCoordinates
  split
  · rw [show densityAt (.density w some) = w from funext (densityAt_density w)]
  · rfl

def realPushforwardOnValue (p : Option (ℝ → Option Bool)) (v : Option (ℝ → Option ℝ)) :=
  (pushforwardOnValue p v).map inLebesgueCoordinates

theorem realPushforward_identity (p : ℝ → Option Bool) :
    realPushforwardOnValue (some p) (some some) =
      weightValue (some (fun y => Value.mask (p y) (some ((1 : ℤ) : ℝ)))) lebesgueValue := by
  simp [realPushforwardOnValue, pushforwardOnValue, coordinates_identity, weightValue,
    lebesgueValue, densityValue, weight, Value.mul_one_left]

theorem realPushforward_mass_total (p : Option (ℝ → Option Bool)) (f : ℝ → ℝ) :
    massValue (realPushforwardOnValue p (some (fun x => some (f x)))) =
      massValue (weightValue (p.map (fun pred x => Value.mask (pred x) (some ((1 : ℤ) : ℝ)))) lebesgueValue) := by
  rw [← mass_pushforwardOn_total]
  unfold realPushforwardOnValue massValue
  cases pushforwardOnValue p (some (fun x => some (f x))) with
  | none => rfl
  | some d => exact coordinates_test d (fun _ => 1)

/-- Auxiliary parameterization for the square substitution proof. -/
def positiveJacobian (x : ℝ) : ℝ := if 0 < x then 2 * x else 0

def squareParameters : Option (D ℝ) :=
  some (.density (fun x => some (positiveJacobian x)) (fun x => some (square x)))

/-- The target chart recovers the source presentation exactly. This allows the
change of variables underneath any distribution operation, even a strict bind. -/
theorem square_positiveSource_parameters (s : Set ℝ) [DecidablePred (· ∈ s)]
    (hs : s ⊆ Set.Ioi 0) :
    pushforwardOnValue (some (fun x => some (decide (x ∈ s)))) (some (fun x => some (square x))) =
      weightValue (some (marginalOn s square)) squareParameters := by
  apply congrArg (fun w => some (Presentation.density w (fun x => some (square x))))
  funext x
  change Value.mask (some (decide (x ∈ s))) (some 1) =
    Value.mul (some (positiveJacobian x)) (marginalOn s square (square x))
  rw [square_marginalOn_positiveSource hs]
  by_cases hx : 0 < x
  · rw [show √(square x) = x by exact Real.sqrt_sq hx.le]
    by_cases h : x ∈ s
    · simp [h, hx, Value.mask, Value.mul, positiveJacobian, jac, square, Real.sqrt_sq hx.le, hx.ne']
      field_simp
      ring
    · simp [h, Value.mask, Value.mul]
  · have hn : x ∉ s := fun h => hx (hs h)
    simp [hn, hx, Value.mask, Value.mul, positiveJacobian]

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
