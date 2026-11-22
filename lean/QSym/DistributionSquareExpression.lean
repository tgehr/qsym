import QSym.DistributionSquareCover
import QSym.Binding

noncomputable section
namespace QSym.Distribution.GraphFibre

private abbrev Rows := List (ℝ × Option ℝ)

def squareCases {α : Type} (y : Option ℝ) (pos neg crit : Option α) : Option α :=
  Binding.conditionalValue (Value.lt (some ((0 : ℤ) : ℝ)) y) pos
    (Binding.conditionalValue (Value.lt y (some ((0 : ℤ) : ℝ))) neg crit)

def squareRows (l r w : Option ℝ → Option ℝ) (z y : Option ℝ) : Option Rows :=
  squareCases y (do return [(← l y, w y), (← r y, w y)]) (some []) (z.map fun x => [(x, none)])

/-- Expression-level evidence that the source-ordered rows enumerate an
entire fibre. A missing weight records a critical root, whose predicate is
inspected separately by each observer. -/
structure SquareExpression (F : ℝ → Option ℝ) (l r w : Option ℝ → Option ℝ) (z : Option ℝ) where
  f : ℝ → ℝ
  slope : ℝ → ℝ
  forward : ∀ x, F x = some (f x)
  derivative : ∀ x, HasStrictDerivAt f (slope x) x
  covers : ∀ y, ∃ xs, RootCover Set.univ f y xs ∧ squareRows l r w z (some y) =
    some (xs.map fun x => (x, Value.inv (some |slope x|)))

namespace SquareExpression
variable {F : ℝ → Option ℝ} {l r w : Option ℝ → Option ℝ} {z : Option ℝ}
private theorem mapM_map {α β γ : Type} (xs : List α) (f : α → β) (g : β → Option γ) :
    (xs.map f).mapM g = xs.mapM (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.mapM_cons, ih]

variable (c : SquareExpression F l r w z)
include c

private theorem measurable_f : Measurable c.f :=
  (continuous_iff_continuousAt.mpr fun x => (c.derivative x).continuousAt).measurable

private theorem atoms (y : Option ℝ) :
    atomsValue (some F) y = (squareRows l r w z y).bind
      (fun rows => rows.mapM fun a => a.2.map (a.1, ·)) := by
  rw [funext c.forward]
  cases y with
  | none => simp [atomsValue, squareRows, squareCases, Binding.conditionalValue, Value.lt]
  | some y =>
    obtain ⟨xs, cover, rows⟩ := c.covers y
    rw [atomsValue_total _ c.measurable_f, rows, cover.atoms _ (fun x _ => c.derivative x)]
    simp [mapM_map]

private theorem maskedAtomsAt (p : ℝ → Option Bool) (y : ℝ) :
    maskedAtoms p c.f y = (squareRows l r w z (some y)).bind
      (fun rows => rows.mapM fun a => (Value.mask (p a.1) a.2).map (a.1, ·)) := by
  obtain ⟨xs, cover, rows⟩ := c.covers y
  rw [rows, cover.masked p _ (fun x _ _ => c.derivative x)]
  simp [mapM_map]

private theorem densityAt (p : ℝ → Option Bool) (y : ℝ) :
    densityAtValue (realPushforwardOnValue (some p) (some F)) (some y) =
      (squareRows l r w z (some y)).bind (fun rows => rows.foldr
        (fun a acc => Value.add (Value.mask (p a.1) a.2) acc) (some 0)) := by
  obtain ⟨xs, cover, rows⟩ := c.covers y
  rw [funext c.forward, cover.density p c.measurable_f _ (fun x _ _ => c.derivative x), rows]
  simp [List.foldr_map, Function.comp_def]

/-- Eliminate the two finite rows into the usual distribution operations. -/
theorem fibre_rule (y : Option ℝ) : value (some F) y =
    squareCases y (addValue (scaleValue (w y) (diracValue (l y))) (scaleValue (w y) (diracValue (r y))))
      zeroValue none := by
  rw [value, c.atoms]
  cases y with
  | none => rfl
  | some y =>
    rcases lt_trichotomy y 0 with hn | rfl | hp
    · simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hn, not_lt_of_ge hn.le, presentation, zeroValue]
    · cases hz : z <;> simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hz, List.mapM_cons]
    · cases hl : l (some y) <;> cases hr : r (some y) <;> cases hw : w (some y) <;>
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hp, hl, hr, hw, List.mapM_cons, presentation,
          scaleValue, addValue, diracValue]

theorem mass_rule (y : Option ℝ) : marginal (some F) y =
    squareCases y (Value.add (w y) (w y)) (some ((0 : ℤ) : ℝ)) none := by
  rw [marginal, c.atoms]
  cases y with
  | none => rfl
  | some y =>
    rcases lt_trichotomy y 0 with hn | rfl | hp
    · simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hn, not_lt_of_ge hn.le, observe]
    · cases hz : z <;> simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hz, List.mapM_cons]
    · obtain ⟨xs, _, h⟩ := c.covers y
      cases hl : l (some y) <;> cases hr : r (some y) <;> cases hw : w (some y) <;>
        simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hp, hl, hr, hw, observe, List.mapM_cons,
          Value.add, Value.mul] at h ⊢

theorem masked_rule (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    (maskedKernel p (some F)).bind (fun k => y.bind k) =
      p.bind fun _ => squareCases y
        (addValue
          (scaleValue (Value.mask (p.bind fun pred => (l y).bind pred) (w y)) (diracValue (l y)))
          (scaleValue (Value.mask (p.bind fun pred => (r y).bind pred) (w y)) (diracValue (r y))))
        zeroValue (Binding.conditionalValue (p.bind fun pred => z.bind pred) none
          (scaleValue (some ((0 : ℤ) : ℝ)) (diracValue z))) := by
  cases p with
  | none => rfl
  | some p =>
    rw [funext c.forward, maskedKernel_total p _ c.measurable_f]
    cases y with
    | none => rfl
    | some y =>
      simp only [Option.some_bind]
      rw [c.maskedAtomsAt p]
      rcases lt_trichotomy y 0 with hn | rfl | hp
      · simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hn, not_lt_of_ge hn.le, presentation, zeroValue]
      · cases hz : z with
        | none => simp [squareRows, squareCases, Value.lt, Binding.conditionalValue, hz]
        | some t =>
          cases h : p t with
          | none => simp [squareRows, squareCases, Value.lt, Binding.conditionalValue, h, hz, List.mapM_cons, Value.mask]
          | some b => cases b <;> simp [squareRows, squareCases, Value.lt, Binding.conditionalValue, h, hz,
              List.mapM_cons, Value.mask, presentation, scaleValue, diracValue]
      · cases hl : l (some y) <;> cases hr : r (some y) <;>
          simp [squareRows, squareCases, Value.lt, Binding.conditionalValue, hp, hl, hr, List.mapM_cons, scaleValue, addValue, diracValue]
        rename_i x t
        cases Value.mask (p x) (w (some y)) <;> cases Value.mask (p t) (w (some y)) <;> rfl

theorem density_rule (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    densityAtValue (realPushforwardOnValue p (some F)) y =
      p.bind fun _ => squareCases y
        (Value.add (Value.mask (p.bind fun pred => (l y).bind pred) (w y))
          (Value.mask (p.bind fun pred => (r y).bind pred) (w y))) (some ((0 : ℤ) : ℝ))
        (Binding.conditionalValue (p.bind fun pred => z.bind pred) none (some ((0 : ℤ) : ℝ))) := by
  cases p with
  | none => rfl
  | some p =>
    cases y with
    | none => rfl
    | some y =>
      rw [c.densityAt p]
      rcases lt_trichotomy y 0 with hn | rfl | hp
      · simp [squareRows, squareCases, Binding.conditionalValue, Value.lt, hn, not_lt_of_ge hn.le]
      · cases hz : z with
        | none => simp [squareRows, squareCases, Value.lt, Binding.conditionalValue, hz]
        | some t => cases h : p t with
          | none => simp [squareRows, squareCases, Value.lt, Binding.conditionalValue, h, hz, Value.mask, Value.add]
          | some b => cases b <;> simp [squareRows, squareCases, Value.lt, Binding.conditionalValue, h, hz, Value.mask, Value.add]
      · have add_missing (u : Option ℝ) : Value.add u none = none := by cases u <;> rfl
        have mask_missing (u : Option ℝ) : Value.mask none u = none := rfl
        cases hl : l (some y) <;> cases hr : r (some y) <;>
          simp [squareRows, squareCases, Value.lt, Binding.conditionalValue, hp, hl, hr,
            Value.add_zero_right, mask_missing, add_missing]
        all_goals rfl

end SquareExpression
end QSym.Distribution.GraphFibre
