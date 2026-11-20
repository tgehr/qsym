import QSym.IntegrationLaws

/-! A real distribution with one unit atom and an identity-coordinate Lebesgue
branch. Its data are a location and a partial weight. Integration uses their
disjoint parameter space; density extraction uses the retained coordinate. -/
noncomputable section
namespace QSym.Distribution
open MeasureTheory

structure AtomPlusDensity where
  atom : ℝ
  weight : ℝ → Option ℝ

namespace AtomPlusDensity

def observe (d : AtomPlusDensity) (f : ℝ → Option ℝ) : Option ℝ :=
  partialIntegral ((Measure.dirac (PUnit.unit : PUnit.{1})).map Sum.inl +
      (volume : Measure ℝ).map Sum.inr)
    (Sum.elim (fun _ => f d.atom) (fun x => Value.mul (d.weight x) (f x)))

theorem observe_eq (d : AtomPlusDensity) (f : ℝ → Option ℝ) :
    d.observe f = Value.add (f d.atom)
      (partialIntegral volume (fun x => Value.mul (d.weight x) (f x))) := by
  rw [observe, partialIntegral_sum, partialIntegral_point]

def mass (d : AtomPlusDensity) : Option ℝ := d.observe (fun _ => some 1)

theorem mass_eq (d : AtomPlusDensity) :
    d.mass = Value.add (some 1) (partialIntegral volume d.weight) := by
  simp only [mass, observe_eq, Value.mul_one_right]

/-- The designated atomic component must give the query singleton zero mass.
The Lebesgue branch has a specified pointwise weight even on null sets. -/
def densityAt (d : AtomPlusDensity) (x : ℝ) : Option ℝ :=
  if (Measure.dirac d.atom) {x} = 0 then d.weight x else none

theorem densityAt_eq (d : AtomPlusDensity) (x : ℝ) :
    d.densityAt x = if x = d.atom then none else d.weight x := by
  by_cases h : x = d.atom
  · subst x
    simp [densityAt]
  · simp [densityAt, Measure.dirac_apply', h, Ne.symm h, Set.indicator]

end AtomPlusDensity
end QSym.Distribution
