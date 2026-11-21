import QSym.Integration
import QSym.RealDensityFibre

/-! Non-recursive, intensional distribution presentations. No quotient by equality
of measures is taken. Integral nodes retain their integrands; they are requests,
not assertions that an integral exists. The finite scalar observer below checks
definedness and integrability. In particular these are not Schwartz distributions,
and no multiplication of arbitrary distributions or general disintegration is
postulated. `α` needs no measurable-space instance merely to form a presentation.
-/
namespace QSym.Distribution

inductive Presentation (α : Type) where
  | invalid : Presentation α
  | zero : Presentation α
  | dirac : α → Presentation α
  | density : (ℝ → Option ℝ) → (ℝ → Option α) → Presentation α
  | add : Presentation α → Presentation α → Presentation α
  | scale : ℝ → Presentation α → Presentation α
  | integral : (ℝ → Presentation α) → Presentation α

abbrev D := Presentation

def diracValue {α : Type} (x : Option α) : Option (D α) := x.map .dirac
def zeroValue {α : Type} : Option (D α) := some .zero
def addValue {α : Type} (x y : Option (D α)) : Option (D α) := do
  return .add (← x) (← y)
def scaleValue {α : Type} (r : Option ℝ) (d : Option (D α)) : Option (D α) := do
  return .scale (← r) (← d)

def densityValue (f : Option (ℝ → Option ℝ)) : Option (D ℝ) :=
  f.map (fun w => .density w some)

def lebesgueValue : Option (D ℝ) := densityValue (some (fun _ => some 1))

/-- Weighting retains pointwise weights, including their definedness. -/
def weight (f : α → Option ℝ) : D α → Option (D α)
  | .invalid => none
  | .zero => some .zero
  | .dirac x => (f x).map (fun r => .scale r (.dirac x))
  | .density w v => some (.density (fun r => Value.mul (w r) ((v r).bind f)) v)
  | .add a b => addValue (weight f a) (weight f b)
  | .scale r d => scaleValue (some r) (weight f d)
  | .integral k => some (.integral (fun r => (weight f (k r)).getD .invalid))

def weightValue {α : Type} (f : Option (α → Option ℝ))
    (d : Option (D α)) : Option (D α) := do
  weight (← f) (← d)

/-- Plain scalar multiplication on a Dirac agrees with a constant weight, including partial operands. -/
theorem constant_weight_dirac {α : Type} (r : Option ℝ) (a : Option α) :
    weightValue (some (fun _ => r)) (diracValue a) = scaleValue r (diracValue a) := by
  cases a <;> cases r <;> rfl

def integralValue {α : Type} (k : Option (ℝ → Option (D α))) : Option (D α) :=
  k.map (fun f => .integral (fun r => (f r).getD .invalid))

/-- Composition of presentations. Continuous-source composition remains an
explicit integral request; no change-of-variables or Fubini law is assumed. -/
def bind (d : D α) (k : α → Option (D β)) : Option (D β) :=
  match d with
  | .invalid => none
  | .zero => some .zero
  | .dirac a => k a
  | .density w v => some (.integral (fun r => (scaleValue (w r) ((v r).bind k)).getD .invalid))
  | .add a b => addValue (bind a k) (bind b k)
  | .scale r a => scaleValue (some r) (bind a k)
  | .integral f => some (.integral (fun r => (bind (f r) k).getD .invalid))

def bindValue {α β : Type} (d : Option (D α))
    (k : Option (α → Option (D β))) : Option (D β) := do
  bind (← d) (← k)

/-- Finite scalar integration. Unknown or invalid mathematics returns `none`. -/
noncomputable def integrate (d : D α) (f : α → Option ℝ) : Option ℝ :=
  match d with
  | .invalid => none
  | .zero => some 0
  | .dirac x => f x
  | .density w v => partialIntegral MeasureTheory.volume
      (fun r => Value.mul (w r) ((v r).bind f))
  | .add a b => Value.add (integrate a f) (integrate b f)
  | .scale r a => Value.mul (some r) (integrate a f)
  | .integral k => partialIntegral MeasureTheory.volume
      (fun r => integrate (k r) f)

noncomputable def massValue {α : Type} (d : Option (D α)) : Option ℝ :=
  d.bind (fun a => integrate a (fun _ => some 1))

/-- Interpret the supported finite atomic part before deciding whether it
obstructs the query. General pushforwards and integral nodes retain their
old partial observer. In particular we never infer a density by integrating
the singleton charges of a continuum of atoms. -/
noncomputable def realFibre (d : D ℝ) (x : ℝ) : RealDensityFibre := by
  classical
  exact match d with
  | .invalid => ⟨0, none⟩
  | .zero => ⟨0, some 0⟩
  | .dirac a => ⟨if x = a then 1 else 0, some 0⟩
  | .density w v => ⟨0, if v = some then w x else none⟩
  | .add a b => (realFibre a x).add (realFibre b x)
  | .scale r a => (realFibre a x).scale r
  | .integral k => ⟨0, partialIntegral MeasureTheory.volume
      (fun r => (realFibre (k r) x).density)⟩

noncomputable def densityAt (d : D ℝ) (x : ℝ) : Option ℝ :=
  (realFibre d x).density

noncomputable def densityAtValue (d : Option (D ℝ)) (x : Option ℝ) : Option ℝ := do
  densityAt (← d) (← x)

@[simp] theorem densityAt_density (w : ℝ → Option ℝ) (x : ℝ) :
    densityAt (.density w some) x = w x := by simp [densityAt, realFibre, RealDensityFibre.density]

@[simp] theorem densityAt_dirac (a x : ℝ) :
    densityAt (.dirac a) x = (if x = a then none else some 0) := by
  by_cases h : x = a <;> simp [densityAt, realFibre, RealDensityFibre.density, h]

theorem weighted_lebesgue_density (f : ℝ → Option ℝ) (x : ℝ) :
    densityAtValue (weightValue (some f) lebesgueValue) (some x) = f x := by
  simp [densityAtValue, weightValue, weight, lebesgueValue, densityValue, Value.mul]
  cases f x <;> simp

theorem punctured_at_zero :
    densityAtValue (weightValue (some (fun x => some (if x = 0 then 0 else 1)))
      lebesgueValue) (some 0) = some 0 := by
  rw [weighted_lebesgue_density]; simp

theorem integrate_dirac (a : α) (f : α → Option ℝ) : integrate (.dirac a) f = f a := rfl

theorem mass_dirac (a : α) : massValue (diracValue (some a)) = some 1 := rfl

theorem mass_zeroValue : massValue (zeroValue (α := α)) = some ((0 : ℤ) : ℝ) := by
  simp [massValue, zeroValue, integrate]

theorem mass_addValue (a b : Option (D α)) :
    massValue (addValue a b) = Value.add (massValue a) (massValue b) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | some b => rfl
    | none =>
      change none = Value.add (integrate a (fun _ => some 1)) none
      cases integrate a (fun _ => some 1) <;> rfl

theorem mass_scaleValue (r : Option ℝ) (a : Option (D α)) :
    massValue (scaleValue r a) = Value.mul r (massValue a) := by
  cases r <;> cases a <;> rfl

theorem mass_diracValue (a : Option α) :
    massValue (diracValue a) = a.bind (fun _ => some ((1 : ℤ) : ℝ)) := by
  cases a <;> simp [massValue, diracValue, integrate]

theorem mass_weight_diracValue (f : Option (α → Option ℝ)) (a : Option α) :
    massValue (weightValue f (diracValue a)) = f.bind (fun g => a.bind g) := by
  cases f with
  | none => rfl
  | some f =>
    cases a with
    | none => rfl
    | some a =>
      cases h : f a <;>
        simp [weightValue, diracValue, weight, massValue, integrate, Value.mul, h]

theorem density_lebesgueValue (x : Option ℝ) :
    densityAtValue lebesgueValue x = x.bind (fun _ => some ((1 : ℤ) : ℝ)) := by
  cases x <;> simp [densityAtValue, lebesgueValue, densityValue]

theorem density_weight_lebesgueValue (f : Option (ℝ → Option ℝ)) (x : Option ℝ) :
    densityAtValue (weightValue f lebesgueValue) x = f.bind (fun g => x.bind g) := by
  cases f with
  | none => rfl
  | some f =>
    cases x with
    | none => rfl
    | some x => exact weighted_lebesgue_density f x

end QSym.Distribution
