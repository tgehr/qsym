import QSym.DistributionCoordinateGrid
import QSym.DistributionNonvanishing

/-! Pointwise sign certificates for coordinate derivatives that have a domain
condition. Each sign statement is conditional on the source value being
defined. The separate slope certificate supplies totality. -/
noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid

/-- Positive or nonnegative wherever the scalar has a value. -/
def Lower (strict : Bool) (f : Scalar) : Prop :=
  ∀ x v, f x = some v → if strict then 0 < v else 0 ≤ v

namespace Lower

theorem constant (strict : Bool) (v : Option ℝ) (q : ℚ)
    (sign : if strict then 0 < q else 0 ≤ q) (h : v = some (q : ℝ)) :
    Lower strict (fun _ => v) := by
  subst v
  intro _ y hy
  cases hy
  cases strict <;> simp_all

/-- The constant coefficient is strict only at the outermost step. Each
pair contributes a nonnegative even power and a zero odd coefficient. -/
def evenLower (strict : Bool) : List ℚ → Bool
  | [] => !strict
  | [c] => decide (if strict then 0 < c else 0 ≤ c)
  | c :: b :: p => decide (if strict then 0 < c else 0 ≤ c) && decide (b = 0) && evenLower false p

private theorem evenLower_sound (strict : Bool) : ∀ (p : List ℚ) (x : ℝ), evenLower strict p = true →
    if strict then 0 < StepSource.polyEval p x else 0 ≤ StepSource.polyEval p x
  | [], _, h => by cases strict <;> simp_all [evenLower, StepSource.polyEval]
  | [c], _, h => by cases strict <;> simp_all [evenLower, StepSource.polyEval]
  | c :: b :: p, x, h => by
    simp only [evenLower, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, rfl⟩, hp⟩ := h
    have htail : 0 ≤ StepSource.polyEval p x := evenLower_sound false p x hp
    have hn := mul_nonneg (mul_self_nonneg x) htail
    cases strict <;> simp only [Bool.false_eq_true, ↓reduceIte, StepSource.polyEval, Rat.cast_zero, zero_add] at hc ⊢
    · have h : 0 ≤ (c : ℝ) := by exact_mod_cast hc
      linarith only [h, hn, mul_assoc x x (StepSource.polyEval p x)]
    · have h : 0 < (c : ℝ) := by exact_mod_cast hc
      linarith only [h, hn, mul_assoc x x (StepSource.polyEval p x)]

/-- A rational translation exhibits the polynomial as a sum of nonnegative
even powers. Choosing the vertex gives a complete test for an upward quadratic. -/
theorem centered (strict : Bool) (s : ℚ) {f p} (source : StepSource.PolynomialOn (fun _ => True) f p)
    (check : evenLower strict (StepSource.polyTranslate s p) = true) : Lower strict f := by
  intro x v hv
  rw [source.equation x trivial] at hv
  cases hv
  have h := evenLower_sound strict _ (x - s) check
  simpa only [StepSource.polyEval_translate, sub_add_cancel] using h

theorem evenPow (f : Scalar) (k : ℕ) (even : k % 2 = 0) :
    Lower false (fun x => (f x).map (fun y => y^k)) := by
  intro x v h
  cases e : f x with
  | none => simp [e] at h
  | some y =>
    simp [e] at h
    subst v
    exact (Nat.even_iff.mpr even).pow_nonneg y

theorem exp (f : Scalar) : Lower true (fun x => Functions.expR.apply (f x)) := by
  intro x v h
  cases e : f x <;> simp [e, Functions.expR, Function1.apply] at h
  subst v
  exact Real.exp_pos _

theorem cosh (f : Scalar) : Lower true (fun x => Functions.coshR.apply (f x)) := by
  intro x v h
  cases e : f x <;> simp [e, Functions.coshR, Function1.apply] at h
  subst v
  exact Real.cosh_pos _

theorem pow {f strict} (k : ℕ) (hf : Lower strict f) :
    Lower strict (fun x => (f x).map (fun y => y^k)) := by
  intro x v h
  cases e : f x <;> simp [e] at h
  subst v
  have hy := hf x _ e
  cases strict <;> simp_all

theorem sqrt {f} (hf : Lower true f) : Lower true (fun x => Functions.sqrtR.apply (f x)) := by
  intro x v h
  cases e : f x with
  | none => simp [e, Function1.apply] at h
  | some y =>
    have hy : 0 < y := hf x _ e
    simp [e, Functions.sqrtR, Function1.apply, hy.le] at h
    subst v
    exact Real.sqrt_pos.2 hy

theorem inv {f} (hf : Lower true f) : Lower true (fun x => Value.inv (f x)) := by
  intro x v h
  cases e : f x with
  | none => simp [e, Value.inv] at h
  | some y =>
    have hy : 0 < y := hf x _ e
    simp [e, Value.inv, hy.ne'] at h
    subst v
    exact inv_pos.2 hy

theorem add {a b f g} (hf : Lower a f) (hg : Lower b g) :
    Lower (a || b) (fun x => Value.add (f x) (g x)) := by
  intro x v h
  cases ef : f x <;> cases eg : g x <;> simp [Value.add, ef, eg] at h
  subst v
  have hu := hf x _ ef
  have hv := hg x _ eg
  cases a <;> cases b <;> simp_all <;> linarith

theorem mul {a b f g} (hf : Lower a f) (hg : Lower b g) :
    Lower (a && b) (fun x => Value.mul (f x) (g x)) := by
  intro x v h
  cases ef : f x <;> cases eg : g x <;> simp [Value.mul, ef, eg] at h
  subst v
  have hu := hf x _ ef
  have hv := hg x _ eg
  cases a <;> cases b <;> simp_all
  positivity

end Lower

/-- A defined value of the coordinate is nonzero. The slope certificate supplies totality. -/
def Nonzero (f : Scalar) : Prop := ∀ x, StepSource.Nonvanishing (f x)

namespace Nonzero
theorem positive {f} (h : Lower true f) : Nonzero f :=
  fun x v hv => (show 0 < v from h x v hv).ne'

theorem literal (v : Option ℝ) (q : ℚ) (h : v = some (q : ℝ)) (hn : q ≠ 0) :
    Nonzero (fun _ => v) :=
  fun _ => StepSource.Nonvanishing.literal q h (decide_eq_true hn)

theorem mul {f g} (h : Nonzero f) (k : Nonzero g) : Nonzero (fun x => Value.mul (f x) (g x)) :=
  fun x => (h x).mul (k x)

theorem inv (f : Scalar) : Nonzero (fun x => Value.inv (f x)) := fun x => StepSource.Nonvanishing.inv (f x)

theorem pow {f} (n : ℕ) (h : Nonzero f) : Nonzero (fun x => (f x).map (fun y => y^n)) := by
  intro x v hv
  cases e : f x <;> simp [e] at hv
  subst v
  exact pow_ne_zero _ (h x _ e)

theorem centeredNegative (s : ℚ) {f p} (source : StepSource.PolynomialOn (fun _ => True) f p)
    (check : Lower.evenLower true (StepSource.polyTranslate s (StepSource.polyScale (-1) p)) = true) :
    Nonzero f := by
  let g (x : ℝ) := (f x).map Neg.neg
  have pg : StepSource.PolynomialOn (fun _ => True) g (StepSource.polyScale (-1) p) :=
    ⟨fun x _ => by simp [g, source.equation x trivial, StepSource.polyEval_scale]⟩
  have positive := Lower.centered true s pg check
  intro x v hv
  have hp : 0 < -v := positive x _ (by simp [g, hv])
  exact (neg_pos.mp hp).ne
end Nonzero

namespace Slope

theorem log {f d} (h : Slope f d) (pos : Lower true f) :
    Slope (fun x => Functions.logR.apply (f x)) (fun x => Value.mul (Value.inv (f x)) (d x)) := by
  obtain ⟨g, dg, cg, hg, eqf, eqd⟩ := h
  have hp (x) : 0 < g x := pos x _ (eqf x)
  exact ⟨_, _, cg.log (fun x => (hp x).ne'), fun x => (Real.hasDerivAt_log (hp x).ne').comp x (hg x),
    fun x => by simp [eqf, Function1.apply, Functions.logR, hp],
    fun x => by simp [eqf, eqd, Value.inv, Value.mul, (hp x).ne']⟩

theorem sqrt {f d} (h : Slope f d) (pos : Lower true f) :
    Slope (fun x => Functions.sqrtR.apply (f x))
      (fun x => Value.mul (Value.inv (Value.mul (some ((2 : ℤ) : ℝ)) (Functions.sqrtR.apply (f x)))) (d x)) := by
  obtain ⟨g, dg, cg, hg, eqf, eqd⟩ := h
  have hp (x) : 0 < g x := pos x _ (eqf x)
  exact ⟨_, _, cg.sqrt (fun x => (hp x).ne'), fun x => (Real.hasDerivAt_sqrt (hp x).ne').comp x (hg x),
    fun x => by simp [eqf, Function1.apply, Functions.sqrtR, (hp x).le],
    fun x => by simp [eqf, eqd, Function1.apply, Functions.sqrtR, (hp x).le, Value.inv, Value.mul,
      (Real.sqrt_pos.2 (hp x)).ne', one_div]⟩

theorem inv_nonzero {f d} (h : Slope f d) (nonzero : Nonzero f) :
    Slope (fun x => Value.inv (f x))
      (fun x => Value.mul (Value.mul (some ((-1 : ℤ) : ℝ)) (Value.inv ((f x).map (fun y => y^2)))) (d x)) := by
  obtain ⟨g, dg, cg, hg, eqf, eqd⟩ := h
  have hn (x) : g x ≠ 0 := nonzero x _ (eqf x)
  exact ⟨_, _, cg.inv hn, fun x => (hg x).inv (hn x),
    fun x => by simp [eqf, Value.inv, hn],
    fun x => by simp [eqf, eqd, Value.mul, Value.inv, hn, div_eq_mul_inv, mul_comm]⟩

theorem inv {f d} (h : Slope f d) (pos : Lower true f) :
    Slope (fun x => Value.inv (f x))
      (fun x => Value.mul (Value.mul (some ((-1 : ℤ) : ℝ)) (Value.inv ((f x).map (fun y => y^2)))) (d x)) :=
  h.inv_nonzero (Nonzero.positive pos)

end Slope
end QSym.Distribution.GraphFibre.Coordinates.Grid
