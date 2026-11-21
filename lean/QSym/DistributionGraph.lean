import QSym.DistributionRestrictedGraph
import QSym.Distribution

noncomputable section
namespace QSym.Distribution.GraphFibre
open MeasureTheory

theorem bind_masked_dirac_test (s : Set ℝ) (f : ℝ → ℝ) (t : ℝ → Option ℝ) :
    (bindValue lebesgueValue (some (fun x =>
      scaleValue (some (sourceWeight s x)) (diracValue (some (f x)))))).bind
      (fun d => integrate d t) = pushforwardTest s f t := by
  unfold pushforwardTest
  apply congrArg (partialIntegral volume)
  funext x
  change Value.mul (some 1) (Value.mul _ (t (f x))) = Value.mul _ (t (f x))
  cases t (f x) <;> simp [Value.mul]

/-- Embed a weighted fibre in the current frontend distribution type. -/
def presentation : List (ℝ × ℝ) → D ℝ
  | [] => .zero
  | [(a,c)] => .scale c (.dirac a)
  | (a,c) :: b :: rest => .add (.scale c (.dirac a)) (presentation (b :: rest))

theorem integrate_presentation (atoms : List (ℝ × ℝ)) (test : ℝ → Option ℝ) :
    integrate (presentation atoms) test = observe atoms test := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    obtain ⟨x,c⟩ := atom
    cases rest with
    | nil => cases h : test x <;> simp [presentation, integrate, observe, Value.mul, Value.add, h]
    | cons a rest =>
      change Value.add _ (integrate (presentation (a :: rest)) test) = Value.add _ _
      rw [ih]
      rfl

def value (g : Option (ℝ → Option ℝ)) (y : Option ℝ) : Option (D ℝ) :=
  (atomsValue g y).map presentation

theorem value_total (f : ℝ → ℝ) (hf : Measurable f) (y : ℝ) :
    value (some (fun x => some (f x))) (some y) = (fibre f y).map presentation := by
  rw [value, atomsValue_total f hf]

theorem mass_eq_marginal (g : Option (ℝ → Option ℝ)) (y : Option ℝ) :
    massValue (value g y) = marginal g y := by
  unfold value marginal
  cases atomsValue g y with
  | none => rfl
  | some atoms => exact integrate_presentation atoms _

theorem square_test {y : ℝ} (hy : 0 < y) (test : ℝ → Option ℝ) :
    (fibre square y).bind (fun atoms => integrate (presentation atoms) test) =
      Value.add (Value.mul (some (jac y)) (test (-√y))) (Value.mul (some (jac y)) (test (√y))) := by
  simpa only [integrate_presentation] using square_observe hy test

end QSym.Distribution.GraphFibre
