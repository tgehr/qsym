import QSym.DistributionInverseBranch

noncomputable section
namespace QSym.Distribution.GraphFibre

/-- Connect three frontend expressions to a real inverse branch. The inverse
Jacobian is partial at critical values. Both target expressions are strict
in a missing query. -/
structure BranchExpression (forward inverse jac : Option ℝ → Option ℝ) where
  f : ℝ → ℝ
  root : ℝ → ℝ
  slope : ℝ → ℝ
  branch : GlobalInverseBranch f root slope
  forward_eq : ∀ x, forward (some x) = some (f x)
  inverse_eq : ∀ y, inverse y = y.map root
  jac_eq : ∀ y, jac y = y.bind (fun t => Value.inv (some |slope (root t)|))

namespace BranchExpression
variable {F I J G R W : Option ℝ → Option ℝ}

def comp (a : BranchExpression F I J) (b : BranchExpression G R W) :
    BranchExpression (fun x => G (F x)) (fun y => I (R y))
      (fun y => Value.mul (W y) (J (R y))) where
  f x := b.f (a.f x)
  root y := a.root (b.root y)
  slope x := b.slope (a.f x) * a.slope x
  branch := a.branch.comp b.branch
  forward_eq x := by rw [a.forward_eq, b.forward_eq]
  inverse_eq y := by rw [a.inverse_eq, b.inverse_eq]; cases y <;> rfl
  jac_eq y := by
    rw [b.jac_eq, a.jac_eq, b.inverse_eq]
    cases y with
    | none => rfl
    | some y =>
      simp only [Option.map_some, Option.some_bind, a.branch.inverse (b.root y), abs_mul]
      by_cases hb : b.slope (b.root y) = 0 <;> by_cases ha : a.slope (a.root (b.root y)) = 0 <;>
        simp [Value.mul, Value.inv, hb, ha, mul_inv_rev, mul_comm]

variable (c : BranchExpression F I J)
include c

private theorem measurable_map : Measurable c.f :=
  (continuous_iff_continuousAt.mpr (fun x => (c.branch.derivative x).continuousAt)).measurable

private theorem atoms_eq (y : Option ℝ) :
    atomsValue (some fun x => F (some x)) y =
      (J y).bind (fun w => (I y).map (fun x => [(x,w)])) := by
  rw [funext c.forward_eq, c.jac_eq, c.inverse_eq]
  cases y with
  | none => simp [atomsValue]
  | some y =>
    rw [atomsValue_total c.f c.measurable_map, ← fibreOn_univ, c.branch.fibreOn_eq]
    by_cases h : c.slope (c.root y) = 0 <;> simp [Value.inv, h]

theorem fibre_rule (y : Option ℝ) :
    value (some fun x => F (some x)) y = scaleValue (J y) (diracValue (I y)) := by
  rw [value, c.atoms_eq]
  cases J y <;> cases I y <;> rfl

theorem mass_rule (y : Option ℝ) :
    marginal (some fun x => F (some x)) y = J y := by
  rw [marginal, c.atoms_eq, c.jac_eq, c.inverse_eq]
  cases y with
  | none => rfl
  | some y =>
    simp only [Option.some_bind, Option.map_some]
    cases Value.inv (some |c.slope (c.root y)|) <;> simp [observe, Value.mul, Value.add]

theorem masked_rule (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    (maskedKernel p (some fun x => F (some x))).bind (fun fn => y.bind fn) =
      scaleValue (Value.mask (p.bind fun pred => (I y).bind pred) (J y)) (diracValue (I y)) := by
  cases p with
  | none => rfl
  | some p =>
    rw [funext c.forward_eq, maskedKernel_total p c.f c.measurable_map, c.inverse_eq, c.jac_eq]
    cases y with
    | none => rfl
    | some y =>
      simp only [Option.some_bind, Option.map_some, c.branch.maskedAtoms_eq]
      change _ = scaleValue (Value.mask (p (c.root y)) (Value.inv (some |c.slope (c.root y)|)))
        (diracValue (some (c.root y)))
      cases Value.mask (p (c.root y)) (Value.inv (some |c.slope (c.root y)|)) <;> rfl

theorem density_rule (p : Option (ℝ → Option Bool)) (y : Option ℝ) :
    densityAtValue (realPushforwardOnValue p (some fun x => F (some x))) y =
      Value.mask (p.bind fun pred => (I y).bind pred) (J y) := by
  cases p with
  | none => rfl
  | some p =>
    rw [funext c.forward_eq, c.inverse_eq, c.jac_eq]
    cases y with
    | none => rfl
    | some y => exact c.branch.density_eq p y

theorem chart_rule (p : ℝ → Option Bool) (hp : ∀ x, Value.Defined (p x))
    (hc : ∀ x, c.slope x = 0 → p x = some false) :
    realPushforwardOnValue (some p) (some fun x => F (some x)) =
      weightValue (some fun y => Value.mask ((I (some y)).bind p) (J (some y))) lebesgueValue := by
  rw [funext c.forward_eq, c.branch.lebesgueChart p hp hc]
  simp [c.inverse_eq, c.jac_eq, weightValue, weight, lebesgueValue, densityValue, Value.mul_one_left]

end BranchExpression
end QSym.Distribution.GraphFibre
