import QSym.Distribution
import QSym.DistributionMixedReal

/-! Finite signed atomic sheets and one identity-coordinate Lebesgue sheet.
A repeated location is a distinct integration parameter. A partial test must
be defined on every atomic sheet, even when the net charge there is zero. -/
noncomputable section
namespace QSym.Distribution
open MeasureTheory

structure FiniteMixedReal where
  atoms : List (ℝ × ℝ)  -- (location, signed coefficient)
  weight : ℝ → Option ℝ

namespace FiniteMixedReal

def atomicObserve (atoms : List (ℝ × ℝ)) (f : ℝ → Option ℝ) (tail : Option ℝ) : Option ℝ :=
  atoms.foldr (fun (a, c) rest => Value.add (Value.mul (some c) (f a)) rest) tail

def observe (m : FiniteMixedReal) (f : ℝ → Option ℝ) : Option ℝ :=
  atomicObserve m.atoms f (partialIntegral volume (fun x => Value.mul (m.weight x) (f x)))

private theorem count_succ {n : ℕ} (f : Fin (n+1) → Option ℝ) :
    partialIntegral Measure.count f = Value.add (f 0)
      (partialIntegral Measure.count (fun i : Fin n => f i.succ)) := by
  classical
  simp only [partialIntegral, Integrable.of_finite, and_true, integral_count]
  simp only [Fin.forall_fin_succ, Fin.sum_univ_succ]
  cases h : f 0 <;> by_cases ht : ∀ i : Fin n, Value.Defined (f i.succ) <;>
    simp only [Value.Defined] at ht <;> simp [ht, h, Value.Defined, Value.add]

private theorem atomicObserve_count (atoms : List (ℝ × ℝ)) (f : ℝ → Option ℝ) (tail : Option ℝ) :
    atomicObserve atoms f tail = Value.add
      (partialIntegral Measure.count (fun i : Fin atoms.length =>
        Value.mul (some (atoms.get i).2) (f (atoms.get i).1))) tail := by
  induction atoms with
  | nil => simp [atomicObserve, partialIntegral, Value.add_zero_left]
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    change Value.add (Value.mul (some c) (f a)) (atomicObserve rest f tail) =
      Value.add (partialIntegral Measure.count (_ : Fin (rest.length+1) → Option ℝ)) tail
    rw [ih, count_succ]
    have assoc (u v t : Option ℝ) : Value.add u (Value.add v t) = Value.add (Value.add u v) t := by
      cases u <;> cases v <;> cases t <;> simp [Value.add, add_assoc]
    exact assoc _ _ _

/-- Weighted integration on the parameter space Fin n ⊕ ℝ with counting
measure on the atomic indices and volume on the retained coordinate. -/
theorem observe_parameterSpace (m : FiniteMixedReal) (f : ℝ → Option ℝ) :
    m.observe f = partialIntegral
      ((Measure.count : Measure (Fin m.atoms.length)).map Sum.inl + (volume : Measure ℝ).map Sum.inr)
      (Sum.elim (fun i => Value.mul (some (m.atoms.get i).2) (f (m.atoms.get i).1))
        (fun x => Value.mul (m.weight x) (f x))) := by
  rw [observe, partialIntegral_sum, atomicObserve_count]

def charge (atoms : List (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (atoms.map (fun (a, c) => if x = a then c else 0)).sum

theorem atomicObserve_singleton (atoms : List (ℝ × ℝ)) (x : ℝ) :
    atomicObserve atoms (fun y => some (if x = y then 1 else 0)) (some 0) =
      some (charge atoms x) := by
  induction atoms with
  | nil => rfl
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    change Value.add (Value.mul (some c) (some (if x = a then 1 else 0)))
      (atomicObserve rest (fun y => some (if x = y then 1 else 0)) (some 0)) = _
    rw [ih]
    by_cases h : x = a <;> simp [Value.add, Value.mul, charge, h]

def fibre (m : FiniteMixedReal) (x : ℝ) : RealDensityFibre := ⟨charge m.atoms x, m.weight x⟩

theorem fibre_perm {as bs : List (ℝ × ℝ)} (h : as.Perm bs) (w : ℝ → Option ℝ) (x : ℝ) :
    (FiniteMixedReal.mk as w).fibre x = (FiniteMixedReal.mk bs w).fibre x := by
  unfold fibre charge
  rw [(h.map _).sum_eq]

theorem observe_perm {as bs : List (ℝ × ℝ)} (h : as.Perm bs) (w f : ℝ → Option ℝ) :
    (FiniteMixedReal.mk as w).observe f = (FiniteMixedReal.mk bs w).observe f := by
  unfold observe atomicObserve
  apply h.foldr_eq'
  intro x _ y _ t
  have comm (u v : Option ℝ) : Value.add v (Value.add u t) = Value.add u (Value.add v t) := by
    cases u <;> cases v <;> cases t <;> simp [Value.add, add_left_comm]
  exact comm _ _

/-- A canonical source representation, used solely for the compatibility theorems. -/
def presentation (m : FiniteMixedReal) : D ℝ :=
  m.atoms.foldr (fun (a,c) rest => .add (.scale c (.dirac a)) rest) (.density m.weight some)

theorem observe_bridge (m : FiniteMixedReal) (f : ℝ → Option ℝ) :
    integrate m.presentation f = m.observe f := by
  obtain ⟨atoms,w⟩ := m
  induction atoms with
  | nil => rfl
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    exact congrArg (Value.add (Value.mul (some c) (f a))) ih

theorem fibre_bridge (m : FiniteMixedReal) (x : ℝ) :
    realFibre m.presentation x = m.fibre x := by
  obtain ⟨atoms,w⟩ := m
  induction atoms with
  | nil => simp [presentation, realFibre, fibre, charge]
  | cons ac rest ih =>
    obtain ⟨a,c⟩ := ac
    change ((realFibre (.scale c (.dirac a)) x).add (realFibre (presentation ⟨rest,w⟩) x)) = _
    rw [ih]
    by_cases h : x = a <;>
      simp [realFibre, RealDensityFibre.add, RealDensityFibre.scale, fibre, charge,
        Value.mul, Value.add_zero_left, h]

theorem densityAt_bridge (m : FiniteMixedReal) (x : ℝ) :
    densityAt m.presentation x = (if charge m.atoms x = 0 then m.weight x else none) := by
  rw [densityAt, fibre_bridge]
  rfl

end FiniteMixedReal

def AtomPlusDensity.toFinite (m : AtomPlusDensity) : FiniteMixedReal :=
  ⟨[(m.atom, 1)], m.weight⟩

theorem AtomPlusDensity.observe_toFinite (m : AtomPlusDensity) (f : ℝ → Option ℝ) :
    m.toFinite.observe f = m.observe f := by
  rw [AtomPlusDensity.observe_eq]
  simp [toFinite, FiniteMixedReal.observe, FiniteMixedReal.atomicObserve, Value.mul_one_left]

theorem AtomPlusDensity.density_toFinite (m : AtomPlusDensity) (x : ℝ) :
    (m.toFinite.fibre x).density = m.densityAt x := by
  rw [AtomPlusDensity.densityAt_eq]
  by_cases h : x = m.atom <;>
    simp [toFinite, FiniteMixedReal.fibre, FiniteMixedReal.charge, RealDensityFibre.density, h]

end QSym.Distribution
