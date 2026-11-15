import QSym.DistributionDensityModel

/-! Factoring a parameter out of a certified finite density observation.
The parameter can be zero or undefined. Finiteness of the remaining density
is essential; the analogous equation for an arbitrary density is false.
-/
noncomputable section
namespace QSym

theorem Value.mul_assoc {α : Type} [Semigroup α] (a b c : Option α) :
    Value.mul (Value.mul a b) c = Value.mul a (Value.mul b c) := by
  cases a <;> cases b <;> cases c <;> simp [Value.mul, _root_.mul_assoc]

theorem Value.mul_comm {α : Type} [CommMagma α] (a b : Option α) :
    Value.mul a b = Value.mul b a := by
  cases a <;> cases b <;> simp [Value.mul, _root_.mul_comm]

theorem Value.mul_left_comm {α : Type} [CommSemigroup α] (a b c : Option α) :
    Value.mul a (Value.mul b c) = Value.mul b (Value.mul a c) := by
  rw [← Value.mul_assoc, Value.mul_comm a b, Value.mul_assoc]

namespace Distribution.DensityProgram

theorem mass_factor (p q : DensityProgram) (c : Option ℝ)
    (h : ∀ x, p.density x = Value.mul c (q.density x))
    (hq : Value.Defined q.mass) : p.mass = Value.mul c q.mass := by
  simp only [mass, Model.densityMassValue_eq] at *
  change Value.Defined (partialIntegral MeasureTheory.volume q.density) at hq
  change partialIntegral MeasureTheory.volume p.density =
    Value.mul c (partialIntegral MeasureTheory.volume q.density)
  rw [show p.density = fun x => Value.mul c (q.density x) from funext h]
  cases c with
  | none =>
    simp only [Value.mul]
    simp [partialIntegral, Value.Defined]
  | some c => exact partialIntegral_scale_defined _ c _ hq

end Distribution.DensityProgram
end QSym
