import QSym.DistributionCoordinateGrid

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

theorem inv {f d} (h : Slope f d) (pos : Lower true f) :
    Slope (fun x => Value.inv (f x))
      (fun x => Value.mul (Value.mul (some ((-1 : ℤ) : ℝ)) (Value.inv ((f x).map (fun y => y^2)))) (d x)) := by
  obtain ⟨g, dg, cg, hg, eqf, eqd⟩ := h
  have hn (x) : g x ≠ 0 := (show 0 < g x from pos x _ (eqf x)).ne'
  exact ⟨_, _, cg.inv hn, fun x => (hg x).inv (hn x),
    fun x => by simp [eqf, Value.inv, hn],
    fun x => by simp [eqf, eqd, Value.mul, Value.inv, hn, div_eq_mul_inv, mul_comm]⟩

end Slope
end QSym.Distribution.GraphFibre.Coordinates.Grid
