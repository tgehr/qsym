import QSym.Binding
import QSym.Refinement

noncomputable section
namespace QSym.Distribution.GraphFibre

/-- The expression emitted by the frontend uses strict comparisons and the
partial real square root and inverse. Both atoms are retained. -/
def squareResult (y : Option ℝ) : Option (D ℝ) :=
  let z := some ((0 : ℤ) : ℝ)
  let s := Functions.sqrtR.apply y
  let w := Value.inv (Value.mul (some ((2 : ℤ) : ℝ)) s)
  Binding.conditionalValue (Value.lt z y)
    (addValue (scaleValue w (diracValue (Value.mul (some ((-1 : ℤ) : ℝ)) s)))
      (scaleValue w (diracValue s)))
    (Binding.conditionalValue (Value.lt y z) zeroValue none)

theorem square_rule (y : Option ℝ) : value (some (fun x => some (x^2))) y = squareResult y := by
  cases y with
  | none => rfl
  | some y =>
    change value (some (fun x => some (square x))) (some y) = _
    rw [value_total square (measurable_id.pow_const 2)]
    rcases lt_trichotomy y 0 with hn|rfl|hp
    · have h : fibre square y = some [] := by qsym_rule
      simp [h, squareResult, Binding.conditionalValue, Value.lt, hn, not_lt_of_ge hn.le,
        presentation, zeroValue]
    · have h : fibre square 0 = none := by qsym_rule
      simp [h, squareResult, Binding.conditionalValue, Value.lt]
    · have h : fibre square y = some [(-√y, jac y), (√y, jac y)] := by qsym_rule
      have hne : 2 * √y ≠ 0 := by positivity
      simp [h, presentation, squareResult, Binding.conditionalValue, Value.lt, hp, hp.le,
        Function1.apply, Functions.sqrtR, diracValue, scaleValue, addValue, Value.mul, Value.inv, hne, jac]

theorem square_mul_rule (y : Option ℝ) :
    value (some (fun x => Value.mul (some x) (some x))) y = squareResult y := by
  simpa [Value.mul, pow_two] using square_rule y

/-- Scalar marginal via a strict test on the source section. -/
def squareMass (y : Option ℝ) : Option ℝ :=
  let z := some ((0 : ℤ) : ℝ)
  Value.mask (Value.le z y) (Value.inv (Functions.sqrtR.apply y))

theorem square_mass_rule (y : Option ℝ) :
    marginal (some (fun x => some (x^2))) y = squareMass y := by
  cases y with
  | none => rfl
  | some y =>
    change marginal (some (fun x => some (square x))) (some y) = _
    rcases lt_trichotomy y 0 with hn|rfl|hp
    · have h : marginal (some (fun x => some (square x))) (some y) = some 0 := by qsym_rule
      simp [h, squareMass, Value.le, Value.mask, not_le_of_gt hn]
    · simpa [squareMass, Value.le, Value.mask, Value.inv, Function1.apply, Functions.sqrtR] using square_marginal_zero
    · have h : marginal (some (fun x => some (square x))) (some y) = some (√y)⁻¹ := by qsym_rule
      simp [h, squareMass, Value.le, Value.mask, hp.le, Functions.sqrtR,
        Function1.apply, Value.inv, (Real.sqrt_pos.mpr hp).ne']

theorem square_mul_mass_rule (y : Option ℝ) :
    marginal (some (fun x => Value.mul (some x) (some x))) y = squareMass y := by
  simpa [Value.mul, pow_two] using square_mass_rule y

/-- The frontend's strict predicate and its masked Jacobian. -/
def openUnitPredicate (y : Option ℝ) : Option Bool :=
  Value.and (Value.lt (some ((0 : ℤ) : ℝ)) y) (Value.lt y (some ((1 : ℤ) : ℝ)))

private theorem openUnitPredicate_some (y : ℝ) :
    openUnitPredicate (some y) = some (decide (y ∈ Set.Ioo (0 : ℝ) 1)) := by
  by_cases h : 0 < y <;> simp [openUnitPredicate, Value.lt, Value.and, Set.mem_Ioo, h]

theorem mass_total_graph (p : Option (ℝ → Option Bool)) (f : ℝ → Option ℝ)
    (hf : ∀ x, Value.Defined (f x)) :
    massValue (realPushforwardOnValue p (some f)) =
      massValue (weightValue (p.map (fun pred x => Value.mask (pred x) (some ((1 : ℤ) : ℝ)))) lebesgueValue) := by
  choose g hg using hf
  rw [funext hg]
  qsym_rule

/-- A pointwise domain proof supplies the weight and output of every row.
The graph still uses the original functions at every parameter. -/
private theorem total_masked_chart (p : ℝ → Option Bool) (f : ℝ → Option ℝ)
    (hp : ∀ x, Value.Defined (p x)) (hf : ∀ x, Value.Defined (f x)) :
    ∃ (w g : ℝ → ℝ),
      (∀ x, Value.mask (p x) (some ((1 : ℤ) : ℝ)) = some (w x)) ∧
      (∀ x, f x = some (g x)) ∧
      realPushforwardOnValue (some p) (some f) =
        some (inLebesgueCoordinates (.density (fun x => some (w x)) (fun x => some (g x)))) := by
  choose b hb using hp
  choose g hg using hf
  let w (x : ℝ) : ℝ := if b x then 1 else 0
  have hw (x : ℝ) : Value.mask (p x) (some ((1 : ℤ) : ℝ)) = some (w x) := by
    rw [hb x]
    cases h : b x <;> simp [Value.mask, w, h]
  refine ⟨w, g, hw, hg, ?_⟩
  change some (inLebesgueCoordinates (.density (fun x => Value.mask (p x) (some 1)) f)) = _
  simp only [Int.cast_one] at hw
  rw [funext hw, funext hg]

theorem bind_total_graph (p : ℝ → Option Bool) (f : ℝ → Option ℝ)
    (hp : ∀ x, Value.Defined (p x)) (hf : ∀ x, Value.Defined (f x)) :
    realBindValue lebesgueValue (some fun x =>
      scaleValue (Value.mask (p x) (some ((1 : ℤ) : ℝ))) (diracValue (f x))) =
      realPushforwardOnValue (some p) (some f) := by
  obtain ⟨w, g, hw, hg, h⟩ := total_masked_chart p f hp hf
  rw [h]
  simp only [hw, hg]
  qsym_rule

theorem integral_total_graph (p : ℝ → Option Bool) (f : ℝ → Option ℝ)
    (hp : ∀ x, Value.Defined (p x)) (hf : ∀ x, Value.Defined (f x)) :
    realIntegralValue (some fun x =>
      scaleValue (Value.mask (p x) (some ((1 : ℤ) : ℝ))) (diracValue (f x))) =
      realPushforwardOnValue (some p) (some f) := by
  obtain ⟨w, g, hw, hg, h⟩ := total_masked_chart p f hp hf
  rw [h]
  simp only [hw, hg]
  qsym_rule

theorem weighted_bind_total_graph (p : ℝ → Option Bool) (f : ℝ → Option ℝ)
    (hp : ∀ x, Value.Defined (p x)) (hf : ∀ x, Value.Defined (f x)) :
    realBindValue (weightValue (some fun x => Value.mask (p x) (some ((1 : ℤ) : ℝ))) lebesgueValue)
      (some fun x => diracValue (f x)) = realPushforwardOnValue (some p) (some f) := by
  obtain ⟨w, g, hw, hg, h⟩ := total_masked_chart p f hp hf
  rw [h]
  simp only [hw, hg]
  qsym_rule

private theorem openUnit_total (x : ℝ) : Value.Defined (openUnitPredicate (some x)) :=
  ⟨_, openUnitPredicate_some x⟩

theorem bind_openUnit_graph (f : ℝ → ℝ) :
    realBindValue lebesgueValue (some fun x =>
      scaleValue (Value.mask (openUnitPredicate (some x)) (some ((1 : ℤ) : ℝ))) (diracValue (some (f x)))) =
      realPushforwardOnValue (some fun x => openUnitPredicate (some x)) (some fun x => some (f x)) :=
  bind_total_graph _ _ openUnit_total (fun x => ⟨f x, rfl⟩)

theorem integral_openUnit_graph (f : ℝ → ℝ) :
    realIntegralValue (some fun x =>
      scaleValue (Value.mask (openUnitPredicate (some x)) (some ((1 : ℤ) : ℝ))) (diracValue (some (f x)))) =
      realPushforwardOnValue (some fun x => openUnitPredicate (some x)) (some fun x => some (f x)) :=
  integral_total_graph _ _ openUnit_total (fun x => ⟨f x, rfl⟩)

theorem weighted_bind_openUnit_graph (f : ℝ → ℝ) :
    realBindValue (weightValue (some fun x => Value.mask (openUnitPredicate (some x)) (some ((1 : ℤ) : ℝ)))
      lebesgueValue) (some fun x => diracValue (some (f x))) =
      realPushforwardOnValue (some fun x => openUnitPredicate (some x)) (some fun x => some (f x)) :=
  weighted_bind_total_graph _ _ openUnit_total (fun x => ⟨f x, rfl⟩)

def openUnitDensity (y : Option ℝ) : Option ℝ :=
  Value.mask (openUnitPredicate y)
    (Value.inv (Value.mul (some ((2 : ℤ) : ℝ)) (Functions.sqrtR.apply y)))

private theorem openUnit_coefficient (y : ℝ) :
    marginalOn (Set.Ioo 0 1) square y = openUnitDensity (some y) := by
  have coef : marginalOn (Set.Ioo 0 1) square y = some (if 0 < y ∧ y < 1 then jac y else 0) := by
    qsym_rule
  rw [coef]
  by_cases h : 0 < y ∧ y < 1
  · have hn : 2 * √y ≠ 0 := by have := h.1; positivity
    simp [openUnitDensity, openUnitPredicate_some, Set.mem_Ioo, h, Value.mask, Functions.sqrtR,
      Function1.apply, h.1.le, Value.inv, Value.mul, hn, jac]
  · simp [openUnitDensity, openUnitPredicate_some, Set.mem_Ioo, h, Value.mask]

theorem square_openUnit_chart :
    realPushforwardOnValue (some (fun x => openUnitPredicate (some x))) (some (fun x => some (x^2))) =
      weightValue (some (fun y => openUnitDensity (some y))) lebesgueValue := by
  have hs : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi 0 := fun _ h => h.1
  have changeChart :
      realPushforwardOnValue (some (fun x => some (decide (x ∈ Set.Ioo (0 : ℝ) 1))))
        (some (fun x => some (square x))) =
      densityValue (some (marginalOn (Set.Ioo 0 1) square)) := by qsym_rule
  have identityWeight (w : ℝ → Option ℝ) : weightValue (some w) lebesgueValue = densityValue (some w) := by
    simp [weightValue, lebesgueValue, densityValue, weight, Value.mul_one_left]
  rw [identityWeight]
  simpa only [openUnitPredicate_some, funext openUnit_coefficient, square] using changeChart

theorem square_mul_openUnit_chart :
    realPushforwardOnValue (some (fun x => openUnitPredicate (some x))) (some (fun x => Value.mul (some x) (some x))) =
      weightValue (some (fun y => openUnitDensity (some y))) lebesgueValue := by
  simpa [pow_two, Value.mul] using square_openUnit_chart

theorem square_openUnit_rule (y : Option ℝ) :
    densityAtValue (realPushforwardOnValue (some (fun x => openUnitPredicate (some x)))
      (some (fun x => some (x^2)))) y = openUnitDensity y := by
  rw [square_openUnit_chart, density_weight_lebesgueValue]
  cases y <;> rfl

theorem square_mul_openUnit_rule (y : Option ℝ) :
    densityAtValue (realPushforwardOnValue (some (fun x => openUnitPredicate (some x)))
      (some (fun x => Value.mul (some x) (some x)))) y = openUnitDensity y := by
  simpa [pow_two, Value.mul] using square_openUnit_rule y

/-- A stronger outer Iverson guard absorbs a repeated inner restriction,
including for partial tests and predicates. -/
theorem weight_mask_absorb (p q : ℝ → Option Bool) (f : ℝ → Option ℝ) :
    let w := some (fun x => Value.mask (Value.and (p x) (q x)) (f x))
    weightValue w (weightValue (some (fun x => Value.mask (p x) (some ((1 : ℤ) : ℝ)))) lebesgueValue) =
      weightValue w lebesgueValue := by
  apply congrArg (fun w => some (Presentation.density w some))
  funext x
  simp only [Option.some_bind, Value.mul_one_left, Int.cast_one]
  cases hp : p x with
  | none => rfl
  | some b =>
    cases b
    · simp [Value.and, Value.mask, Value.mul]
    · exact Value.mul_one_left _

theorem openUnit_chart_mass {w : Option (ℝ → Option ℝ)}
    (hw : some (fun y => openUnitDensity (some y)) = w) :
    massValue (weightValue w lebesgueValue) = some ((1 : ℤ) : ℝ) := by
  rw [← hw, ← square_openUnit_chart]
  rw [realPushforward_mass_total, ← mass_pushforwardOn_total]
  simp only [openUnitPredicate_some]
  change (pushforwardOnValue _ (some (fun x => some (square x)))).bind _ = _
  rw [pushforwardOn_test, pushforwardTest_total measurableSet_Ioo square (fun _ => 1)]
  · simp [Real.volume_Ioo, MeasureTheory.measureReal_def]
  · exact MeasureTheory.integrableOn_const.mpr (Or.inr (by simp [Real.volume_Ioo]))

end QSym.Distribution.GraphFibre
