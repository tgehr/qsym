import QSym.DistributionGraph

noncomputable section
namespace QSym.Distribution.GraphFibre

/-- A single real output and its signed coefficient. A zero coefficient still
retains the output needed by a strict partial test. -/
def atomRow : D ℝ → Option (ℝ × ℝ)
  | .dirac y => some (1, y)
  | .scale c d => (atomRow d).map (fun a => (c * a.1, a.2))
  | _ => none

private theorem atomRow_test {d : D ℝ} {a : ℝ × ℝ} (h : atomRow d = some a)
    (t : ℝ → Option ℝ) : integrate d t = Value.mul (some a.1) (t a.2) := by
  induction d generalizing a with
  | dirac y =>
    obtain rfl : (1, y) = a := Option.some.inj h
    exact (Value.mul_one_left _).symm
  | scale c d ih =>
    cases hd : atomRow d with
    | none => simp [atomRow, hd] at h
    | some b =>
      obtain rfl : (c * b.1, b.2) = a := by simpa [atomRow, hd] using h
      change Value.mul (some c) (integrate d t) = _
      rw [ih hd]
      cases t b.2 <;> simp [Value.mul, mul_assoc]
  | invalid | zero | add | density | integral => simp [atomRow] at h

/-- Interpret a real integral of point masses as one weighted parameter space.
The fallback retains the ordered integral when any row is missing or contains
a more general distribution. -/
def realIntegralRows (rows : ℝ → D ℝ) : D ℝ := by
  classical
  exact if ∀ r, (atomRow (rows r)).isSome then
    let a := fun r => (atomRow (rows r)).getD (0, 0)
    inLebesgueCoordinates (.density (fun r => some (a r).1) (fun r => some (a r).2))
  else .integral rows

theorem realIntegralRows_of_atoms (rows : ℝ → D ℝ) (w f : ℝ → ℝ)
    (h : ∀ r, atomRow (rows r) = some (w r, f r)) :
    realIntegralRows rows = inLebesgueCoordinates (.density (fun r => some (w r)) (fun r => some (f r))) := by
  simp [realIntegralRows, h]

theorem realIntegralRows_of_missing {rows : ℝ → D ℝ} {r : ℝ} (h : atomRow (rows r) = none) :
    realIntegralRows rows = .integral rows := by
  have hn : ¬∀ s, (atomRow (rows s)).isSome := fun hall => by simpa [h] using hall r
  simp [realIntegralRows, hn]

/-- Before choosing coordinates the recovered parameter space agrees with
the ordered integral on every partial test, even at zero-weight rows. -/
private theorem atomRows_test {rows : ℝ → D ℝ} {w f : ℝ → ℝ}
    (h : ∀ r, atomRow (rows r) = some (w r, f r)) (t : ℝ → Option ℝ) :
    integrate (.density (fun r => some (w r)) (fun r => some (f r))) t = integrate (.integral rows) t := by
  apply congrArg (partialIntegral MeasureTheory.volume)
  funext r
  exact (atomRow_test (h r) t).symm

private theorem row_getD {rows : ℝ → D ℝ} (h : ∀ r, (atomRow (rows r)).isSome) (r : ℝ) :
    atomRow (rows r) = some ((atomRow (rows r)).getD (0, 0)) := by
  cases hr : atomRow (rows r) with
  | some a => rfl
  | none => simpa [hr] using h r

theorem realIntegralRows_total (rows : ℝ → D ℝ) (t : ℝ → ℝ) :
    integrate (realIntegralRows rows) (fun y => some (t y)) =
      integrate (.integral rows) (fun y => some (t y)) := by
  unfold realIntegralRows
  split
  · rename_i h
    rw [coordinates_test]
    exact atomRows_test (row_getD h) _
  · rfl

theorem realIntegralRows_partial (rows : ℝ → D ℝ) (t : ℝ → Option ℝ) :
    Value.Refines (integrate (realIntegralRows rows) t) (integrate (.integral rows) t) := by
  unfold realIntegralRows
  split
  · rename_i h
    rw [← atomRows_test (row_getD h) t]
    exact coordinates_partial _ _
  · exact fun _ ha => ha

def realIntegralValue (k : Option (ℝ → Option (D ℝ))) : Option (D ℝ) :=
  k.map (fun f => realIntegralRows (fun r => (f r).getD .invalid))

/-- A real-valued bind uses the row interpreter of a real integral for every
parameter chart of its source, including charts below sums and scalings. Atoms,
zero and ordered integrals retain their usual bind. -/
def realBind {α : Type} : D α → (α → Option (D ℝ)) → Option (D ℝ)
  | .density w v, k => some (realIntegralRows (fun r => (scaleValue (w r) ((v r).bind k)).getD .invalid))
  | .add a b, k => addValue (realBind a k) (realBind b k)
  | .scale r a, k => scaleValue (some r) (realBind a k)
  | .invalid, _ => none
  | .zero, _ => some .zero
  | .dirac a, k => k a
  | .integral f, k => some (.integral (fun r => (bind (f r) k).getD .invalid))

def realBindValue {α : Type} (d : Option (D α)) (k : Option (α → Option (D ℝ))) : Option (D ℝ) := do
  realBind (← d) (← k)

private theorem add_test {β : Type} (x y : Option (D β)) (f : β → Option ℝ) :
    (addValue x y).bind (fun a => integrate a f) =
      Value.add (x.bind (fun a => integrate a f)) (y.bind (fun a => integrate a f)) := by
  cases x with
  | none => rfl
  | some a =>
    cases y with
    | some b => rfl
    | none =>
      change none = Value.add (integrate a f) none
      cases integrate a f <;> rfl

private theorem scale_test {β : Type} (r : ℝ) (x : Option (D β)) (f : β → Option ℝ) :
    (scaleValue (some r) x).bind (fun a => integrate a f) =
      Value.mul (some r) (x.bind (fun a => integrate a f)) := by
  cases x <;> rfl

theorem realBind_test {α : Type} (d : D α) (k : α → Option (D ℝ)) (t : ℝ → ℝ) :
    (realBind d k).bind (fun a => integrate a (fun y => some (t y))) =
      (bind d k).bind (fun a => integrate a (fun y => some (t y))) := by
  induction d with
  | density w v => exact realIntegralRows_total _ t
  | add a b iha ihb =>
    change (addValue (realBind a k) (realBind b k)).bind _ = (addValue (bind a k) (bind b k)).bind _
    rw [add_test, add_test, iha, ihb]
  | scale r a ih =>
    change (scaleValue (some r) (realBind a k)).bind _ = (scaleValue (some r) (bind a k)).bind _
    rw [scale_test, scale_test, ih]
  | invalid | zero | dirac | integral => rfl

theorem realBind_total {α : Type} (d : Option (D α)) (k : Option (α → Option (D ℝ))) (t : ℝ → ℝ) :
    (realBindValue d k).bind (fun a => integrate a (fun y => some (t y))) =
      (bindValue d k).bind (fun a => integrate a (fun y => some (t y))) := by
  cases d with
  | none => rfl
  | some d =>
    cases k with
    | none => rfl
    | some k => exact realBind_test d k t

theorem realBind_mass {α : Type} (d : Option (D α)) (k : Option (α → Option (D ℝ))) :
    massValue (realBindValue d k) = massValue (bindValue d k) :=
  realBind_total d k (fun _ => 1)

theorem realIntegral_mass (k : Option (ℝ → Option (D ℝ))) :
    massValue (realIntegralValue k) = massValue (integralValue k) := by
  cases k with
  | none => rfl
  | some k => exact realIntegralRows_total _ (fun _ => 1)

/-- The real integral and both placements of a source weight build the same
parameter chart for any total signed weight and total output. -/
theorem realIntegral_dirac (w f : ℝ → ℝ) :
    realIntegralValue (some fun x => scaleValue (some (w x)) (diracValue (some (f x)))) =
      some (inLebesgueCoordinates (.density (fun x => some (w x)) (fun x => some (f x)))) := by
  apply congrArg some
  apply realIntegralRows_of_atoms
  intro x
  simp [scaleValue, diracValue, atomRow]

theorem realBind_dirac (w f : ℝ → ℝ) :
    realBindValue lebesgueValue (some fun x => scaleValue (some (w x)) (diracValue (some (f x)))) =
      some (inLebesgueCoordinates (.density (fun x => some (w x)) (fun x => some (f x)))) := by
  apply congrArg some
  apply realIntegralRows_of_atoms
  intro x
  simp [scaleValue, diracValue, atomRow]

theorem realBind_weight_dirac (w f : ℝ → ℝ) :
    realBindValue (weightValue (some fun x => some (w x)) lebesgueValue)
      (some fun x => diracValue (some (f x))) =
      some (inLebesgueCoordinates (.density (fun x => some (w x)) (fun x => some (f x)))) := by
  simp only [weightValue, lebesgueValue, densityValue, Option.some_bind, weight, Value.mul_one_left]
  apply congrArg some
  apply realIntegralRows_of_atoms
  intro x
  simp [scaleValue, diracValue, atomRow, Value.mul]

end QSym.Distribution.GraphFibre
