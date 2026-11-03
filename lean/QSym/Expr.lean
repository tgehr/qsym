import QSym.Value

namespace QSym
inductive Ty where
  | real | complex | bool | density | measure
  deriving DecidableEq

abbrev Ty.denote : Ty → Type
  | .real => ℝ
  | .complex => ℂ
  | .bool => Bool
  | .density => Density
  | .measure => MeasureTheory.Measure ℝ

structure Env where
  real : Nat → ℝ
  complex : Nat → ℂ
  bool : Nat → Bool

inductive Expr : Ty → Type where
  | real (n : Int) : Expr .real
  | complex (re im : Int) : Expr .complex
  | bool (b : Bool) : Expr .bool
  | varR (i : Nat) : Expr .real
  | varC (i : Nat) : Expr .complex
  | varB (i : Nat) : Expr .bool
  | addR : Expr .real → Expr .real → Expr .real
  | addC : Expr .complex → Expr .complex → Expr .complex
  | mulR : Expr .real → Expr .real → Expr .real
  | mulC : Expr .complex → Expr .complex → Expr .complex
  | invR : Expr .real → Expr .real
  | invC : Expr .complex → Expr .complex
  | nonzeroR : Expr .real → Expr .bool
  | nonzeroC : Expr .complex → Expr .bool
  | maskR : Expr .bool → Expr .real → Expr .real
  | maskC : Expr .bool → Expr .complex → Expr .complex
  | conj : Expr .complex → Expr .complex
  | lebesgue : Expr .density
  | puncture : Expr .density → Expr .density
  | densityAt : Expr .density → Expr .real → Expr .real
  | forget : Expr .density → Expr .measure

namespace Expr
noncomputable def eval (ρ : Env) : {s : Ty} → Expr s → Option s.denote
  | _, .real n => some (n : ℝ)
  | _, .complex r i => some ((r : ℂ) + (i : ℂ) * Complex.I)
  | _, .bool b => some b
  | _, .varR i => some (ρ.real i)
  | _, .varC i => some (ρ.complex i)
  | _, .varB i => some (ρ.bool i)
  | _, .addR a b => Value.add (eval ρ a) (eval ρ b)
  | _, .addC a b => Value.add (eval ρ a) (eval ρ b)
  | _, .mulR a b => Value.mul (eval ρ a) (eval ρ b)
  | _, .mulC a b => Value.mul (eval ρ a) (eval ρ b)
  | _, .invR a => Value.inv (eval ρ a)
  | _, .invC a => Value.inv (eval ρ a)
  | _, .nonzeroR a => Value.nonzero (eval ρ a)
  | _, .nonzeroC a => Value.nonzero (eval ρ a)
  | _, .maskR p a => Value.mask (eval ρ p) (eval ρ a)
  | _, .maskC p a => Value.mask (eval ρ p) (eval ρ a)
  | _, .conj a => Value.conj (eval ρ a)
  | _, .lebesgue => some Density.lebesgue
  | _, .puncture a => (eval ρ a).map Density.puncture
  | _, .densityAt d x => Value.densityAt (eval ρ d) (eval ρ x)
  | _, .forget d => (eval ρ d).map Density.forget

def Defined {s : Ty} (ρ : Env) (e : Expr s) : Prop := Value.Defined (eval ρ e)

theorem density_total_measurable (ρ : Env) :
    (d : Expr .density) → ∃ f, eval ρ d = some f ∧ Measurable f
  | .lebesgue => ⟨Density.lebesgue, rfl, measurable_const⟩
  | .puncture d => by
      obtain ⟨f, h, hf⟩ := density_total_measurable ρ d
      exact ⟨Density.puncture f, by simp [eval, h], Density.measurable_puncture f hf⟩

theorem forget_puncture (ρ : Env) (d : Expr .density) :
    eval ρ (.forget (.puncture d)) = eval ρ (.forget d) := by
  simp only [eval, Option.map_map, Function.comp_def, Density.forget_puncture]

-- Partial-value equality preserves both values and definedness.
theorem defined_congr {s : Ty} {ρ : Env} {a b : Expr s}
    (h : eval ρ a = eval ρ b) : Defined ρ a ↔ Defined ρ b := by
  unfold Defined
  rw [h]
end Expr
end QSym
