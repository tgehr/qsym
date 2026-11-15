import QSym.SummationElementary
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Complete natural-index cycles of complex roots of unity. The zero-length
case does not evaluate the ratio, which contains a reciprocal of the length. -/
noncomputable section
namespace QSym.SummationRoots
open SummationElementary
open scoped BigOperators
attribute [local instance] Classical.propDecidable

-- Preserve the input's multiplication tree at the certificate boundary.
def triple {K : Type} [Mul K] (order : Fin 6) (left : Bool) (a b c : Option K) : Option K :=
  let (x,y,z) := match order.val with
    | 0 => (a,b,c) | 1 => (a,c,b) | 2 => (b,a,c)
    | 3 => (b,c,a) | 4 => (c,a,b) | _ => (c,b,a)
  if left then Value.mul (Value.mul x y) z else Value.mul x (Value.mul y z)

theorem triple_eq {K : Type} [CommSemigroup K] (order : Fin 6) (left : Bool) (a b c : Option K) :
    triple order left a b c = Value.mul a (Value.mul b c) := by
  fin_cases order <;> cases left <;> cases a <;> cases b <;> cases c <;>
    simp [triple, Value.mul, mul_comm, mul_left_comm, _root_.mul_assoc]

def reciprocal (n : Option ℕ) (rational : Bool) : Option ℝ :=
  if rational then Functions.castQR.apply (Functions.invQ.apply
    (Functions.castZQ.apply (Functions.castNZ.apply n))) else Value.inv (natR n)

def ratio (n : Option ℕ) (rational exponential : Bool) (order : Fin 6) (left : Bool) : Option ℂ :=
  if exponential then Functions.expC.apply (triple order left
    (Functions.castRC.apply (reciprocal n rational))
    (some (((0 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Complex.I))
    (Functions.castRC.apply (some Functions.pi)))
  else Functions.cisR.apply (triple order left (reciprocal n rational) twoR (some Functions.pi))

theorem ratio_some (n : ℕ) (hn : n ≠ 0) (rational exponential : Bool) (order : Fin 6) (left : Bool) :
    ratio (some n) rational exponential order left = some (Complex.exp (2 * Real.pi * Complex.I / n)) := by
  have hr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  cases exponential <;> cases rational <;>
    simp [ratio, triple_eq, reciprocal, twoR, natR, Function1.apply, Functions.cisR,
      Functions.expC, Functions.castNZ, Functions.castZQ, Functions.castQR,
      Functions.castRC, Functions.invQ, Functions.pi, Value.mul, Value.inv, hr, hq, hn] <;>
    congr 1 <;> push_cast <;> ring

def isOne (n : Option ℕ) : Option Bool := Value.not (Functions.nonzeroZ.apply
  (Functions.addZ.apply (Functions.castNZ.apply n) (some (-1))))

theorem isOne_eq (n : Option ℕ) : isOne n = Binding.equalValue n (some 1) := by
  cases n with
  | none => rfl
  | some n =>
    simp [isOne, Value.not, Function1.apply, Function2.apply, Functions.nonzeroZ,
      Functions.addZ, Functions.castNZ, Binding.equalValue]
    omega

theorem range_value (n : Option ℕ) (rational exponential : Bool) (order : Fin 6) (left : Bool) :
    Summation.rangeValue (some (fun i => Functions.powCN.apply
      (ratio n rational exponential order left) (some i))) n =
      Value.mask (isOne n) oneC := by
  rw [isOne_eq]
  cases n with
  | none => rfl
  | some n =>
    by_cases hz : n = 0
    · subst n
      simp [Summation.rangeValue, Summation.finite, Binding.equalValue, Value.mask]
    rw [ratio_some n hz]
    by_cases ho : n = 1
    · subst n
      simp [Summation.rangeValue, Summation.finite, Function2.apply,
        Functions.powCN, Binding.equalValue, Value.mask, oneC]
    have hn : 1 < n := by omega
    have hs := (Complex.isPrimitiveRoot_exp n hz).geom_sum_eq_zero hn
    simpa [Summation.rangeValue, Summation.finite, Function2.apply,
      Functions.powCN, Binding.equalValue, Value.mask, ho] using congrArg some hs

end QSym.SummationRoots
