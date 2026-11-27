import QSym.DistributionCoordinateDomain
import QSym.DistributionCoordinateGridChange

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid

/-- For fixed outer parameters, the coordinate is smooth on the entire axis
or missing on the entire axis. A single sample distinguishes the two cases. -/
def UniformSlope (f d : Scalar) : Prop := Slope f d ∨ ∀ x, f x = none

namespace UniformSlope

theorem parameter (c : Option ℝ) {z : Option ℝ}
    (hz : z = some (Numeric.denote (s := .real) (0 : ℚ))) : UniformSlope (fun _ => c) (fun _ => z) := by
  cases c with
  | none => exact Or.inr (fun _ => rfl)
  | some v => exact Or.inl (Slope.parameter (some v) ⟨v, rfl⟩ hz)

theorem unary {f d e : Scalar} (op : Option ℝ → Option ℝ) (strict : op none = none)
    (h : UniformSlope f d) (total : Slope f d → Slope (fun x => op (f x)) e) :
    UniformSlope (fun x => op (f x)) e := by
  rcases h with hf | hf
  · exact Or.inl (total hf)
  · exact Or.inr (fun x => (congrArg op (hf x)).trans strict)

private theorem binary {f d g e v : Scalar} (op : Option ℝ → Option ℝ → Option ℝ)
    (left : ∀ a, op none a = none) (right : ∀ a, op a none = none)
    (h : UniformSlope f d) (k : UniformSlope g e)
    (total : Slope f d → Slope g e → Slope (fun x => op (f x) (g x)) v) :
    UniformSlope (fun x => op (f x) (g x)) v := by
  rcases h with hf | hf
  · rcases k with hg | hg
    · exact Or.inl (total hf hg)
    · exact Or.inr (fun x => (congrArg (op (f x)) (hg x)).trans (right _))
  · exact Or.inr (fun x => (congrArg (fun a => op a (g x)) (hf x)).trans (left _))

theorem add {f d g e} (h : UniformSlope f d) (k : UniformSlope g e) :
    UniformSlope (fun x => Value.add (f x) (g x)) (fun x => Value.add (d x) (e x)) :=
  binary Value.add (fun _ => rfl) (fun a => by cases a <;> rfl) h k Slope.add

theorem mul {f d g e} (h : UniformSlope f d) (k : UniformSlope g e) :
    UniformSlope (fun x => Value.mul (f x) (g x))
      (fun x => Value.add (Value.mul (d x) (g x)) (Value.mul (f x) (e x))) :=
  binary Value.mul (fun _ => rfl) (fun a => by cases a <;> rfl) h k Slope.mul

theorem pow {f d} (n : ℕ) (h : UniformSlope f d) :
    UniformSlope (fun x => (f x).map (fun y => y ^ n))
      (fun x => Value.mul (Value.mul (some ((n : ℤ) : ℝ)) ((f x).map (fun y => y ^ (n-1)))) (d x)) :=
  unary (fun v => v.map (· ^ n)) rfl h (Slope.pow n)

private theorem selection {α : Type} {f d : Scalar} (s : ℝ) (h : UniformSlope f d)
    (chart : Scalar → Option α) (regular : Option α) (law : Slope f d → chart f = regular) :
    chart f = Binding.conditionalValue (Binding.definedValue (f s)) regular (chart (fun _ => none)) := by
  rcases h with hf | hm
  · have reg := law hf
    obtain ⟨g, _, _, _, eqf, _⟩ := hf
    rw [eqf s]
    exact reg
  · rw [hm s]
    exact congrArg chart (funext hm)

theorem length {f d} (s : ℝ) (h : UniformSlope f d) :
    value (Tensor.consValue (some f) Tensor.nilValue) =
      Binding.conditionalValue (Binding.definedValue (f s))
        (weightValue (some fun x => Value.abs (d x)) lebesgueValue)
        (value (Tensor.consValue (some fun _ : ℝ => (none : Option ℝ)) Tensor.nilValue)) :=
  selection s h (fun g => value (Tensor.consValue (some g) Tensor.nilValue)) _ Slope.length

theorem restricted {f d} (s : ℝ) (p : ℝ → Option Bool) (h : UniformSlope f d) :
    Coordinates.restricted (some p) (Tensor.consValue (some f) Tensor.nilValue) =
      Binding.conditionalValue (Binding.definedValue (f s))
        (weightValue (some fun x => Value.mask ((f x).bind p) (Value.abs (d x))) lebesgueValue)
        (Coordinates.restricted (some p) (Tensor.consValue (some fun _ : ℝ => (none : Option ℝ)) Tensor.nilValue)) :=
  selection s h (fun g => Coordinates.restricted (some p) (Tensor.consValue (some g) Tensor.nilValue)) _ (Slope.restricted p)

end UniformSlope
end QSym.Distribution.GraphFibre.Coordinates.Grid
