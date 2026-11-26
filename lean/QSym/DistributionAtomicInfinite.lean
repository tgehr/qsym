import QSym.DistributionAtomicProbes
import Mathlib.Analysis.SpecificLimits.Normed

/-! A countable sum of copies of one Dirac represents an infinite atomic
weight. A finite signed probe of that outcome exists precisely when it is
defined there and equals zero. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal Classical

def infiniteAtom (a : α) : D α := .sum (fun _ : ℤ => .dirac a)

def infiniteModel (a : α) : Model α := (fun x => ⊤ * atom a x, {a})

theorem Represents.finite_weight {d : D α} {k : Weights α} (hd : Represents d k) (x : α) : k x ≠ ⊤ := by
  induction hd with
  | zero => exact ENNReal.zero_ne_top
  | dirac a => by_cases h : x=a <;> simp [atom, h]
  | add _ _ ih jh => exact ENNReal.add_ne_top.mpr ⟨ih, jh⟩
  | scale _ _ ih => exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ih

theorem constant_partialSum (v : Option ℝ) :
    partialSum (fun _ => v) = if v = some 0 then some 0 else none := by
  classical
  cases v with
  | none => simp [partialSum]
  | some v => by_cases h : v=0 <;> simp [partialSum, h, summable_const_iff]

theorem integrate_infiniteAtom (a : α) (t : α → Option ℝ) :
    integrate (infiniteAtom a) t = if t a = some 0 then some 0 else none :=
  constant_partialSum (t a)

@[simp] theorem visited_infiniteAtom (a : α) : visited (infiniteAtom a) = {a} := by
  classical
  ext x
  by_cases h : a=x <;> simp [visited, integrate_infiniteAtom, h, eq_comm]

/-- This presentation and the series of actual per-round emissions have the
same finite observation, including at a missing or a negative test value. -/
theorem infiniteAtom_geometric (a : α) (t : α → Option ℝ) {c r : ℝ} (hc : 0 < c) (hr : 1 ≤ r) :
    integrate (infiniteAtom a) t = (t a).bind fun v =>
      if Summable (fun n : ℕ => r^n * (c*v)) then some (∑' n : ℕ, r^n * (c*v)) else none := by
  classical
  rw [integrate_infiniteAtom]
  cases t a with
  | none => rfl
  | some v =>
    by_cases h : v=0
    · simp [h, summable_zero]
    · have diverges : ¬ Summable (fun n : ℕ => r^n * (c*v)) := by
        rw [summable_mul_right_iff (mul_ne_zero hc.ne' h), summable_geometric_iff_norm_lt_one,
          Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hr)]
        exact not_lt.mpr hr
      simp [h, diverges]

theorem density_infiniteAtom (a x : ℝ) :
    densityAt (infiniteAtom a) x = if x=a then none else some 0 := by
  classical
  by_cases h : x=a <;> simp [infiniteAtom, densityAt, realFibre, RealDensityFibre.density, h,
    summable_const_iff, constant_partialSum]

/-- The infinite weight obstructs the Lebesgue density exactly at the atom. -/
theorem density_constant_dirac_series (p x : Option ℝ) :
    densityAtValue (sumValue (some (fun _ : ℤ => diracValue p))) x = densityAtValue (diracValue p) x := by
  cases x with
  | none => cases p <;> rfl
  | some x =>
    cases p with
    | some a => exact (density_infiniteAtom a x).trans (densityAt_dirac a x).symm
    | none => simp [densityAtValue, sumValue, diracValue, densityAt, realFibre, RealDensityFibre.density, constant_partialSum]

/-- For two infinite atoms, moving addition through a countable sum can
change a signed probe. The weights and even all nonnegative partial probes
agree. Any extension to mixed infinite supports must account for this. -/
theorem infinite_mixed_signed :
    ∃ d e : D Bool, visited d = visited e ∧
      (∀ t : Bool → Option ℝ, (∀ a v, t a = some v → 0 ≤ v) → integrate d t = integrate e t) ∧
      ∃ t : Bool → Option ℝ, integrate d t ≠ integrate e t := by
  let d : D Bool := .sum (fun _ => .add (.dirac false) (.dirac true))
  let e : D Bool := .add (infiniteAtom false) (infiniteAtom true)
  have together (t : Bool → Option ℝ) :
      integrate d t = if Value.add (t false) (t true) = some 0 then some 0 else none :=
    constant_partialSum _
  have apart (t : Bool → Option ℝ) :
      integrate e t = if t false = some 0 ∧ t true = some 0 then some 0 else none := by
    change Value.add (integrate (infiniteAtom false) t) (integrate (infiniteAtom true) t) = _
    rw [integrate_infiniteAtom, integrate_infiniteAtom]
    by_cases a : t false = some 0 <;> by_cases b : t true = some 0 <;> simp [a, b, Value.add]
  have positive (t : Bool → Option ℝ) (hn : ∀ a v, t a = some v → 0 ≤ v) : integrate d t = integrate e t := by
    rw [together, apart]
    cases ha : t false with
    | none => rfl
    | some a =>
      cases hb : t true with
      | none => simp [Value.add]
      | some b =>
        simp [Value.add, add_eq_zero_iff_of_nonneg (hn false a ha) (hn true b hb)]
  refine ⟨d, e, ?_, positive, fun b => some (if b then (-1 : ℝ) else 1), ?_⟩
  · ext x
    change (integrate d _ = none) ↔ (integrate e _ = none)
    rw [positive]
    intro a v h
    split at h <;> simp_all
  · rw [together, apart]
    norm_num [Value.add] <;> simp

end QSym.Distribution.Atomic
