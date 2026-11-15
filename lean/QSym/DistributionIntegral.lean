import QSym.Binding
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.CasesM

namespace QSym.Distribution
open MeasureTheory Set

theorem ae_away (points : List ℝ) :
    ∀ᵐ x : ℝ ∂volume, ∀ p ∈ points, x ≠ p := by
  induction points with
  | nil => simp
  | cons p ps ih =>
    filter_upwards [ih, show ∀ᵐ x : ℝ ∂volume, x ≠ p by
      rw [ae_iff]; simp] with x hx hp
    simpa using And.intro hp hx

theorem partialIntegral_congr_away (f g : ℝ → Option ℝ) (points : List ℝ)
    (hf : ∀ x, Value.Defined (f x)) (hg : ∀ x, Value.Defined (g x))
    (he : ∀ x, (∀ p ∈ points, x ≠ p) → f x = g x) :
    partialIntegral volume f = partialIntegral volume g := by
  have he' : (fun x => (f x).getD 0) =ᵐ[volume] (fun x => (g x).getD 0) := by
    filter_upwards [ae_away points] with x hx
    rw [he x hx]
  have hi := integrable_congr he'
  by_cases h : Integrable (fun x => (g x).getD 0) volume
  · rw [partialIntegral_valid volume f hf (hi.mpr h), partialIntegral_valid volume g hg h,
      integral_congr_ae he']
  · rw [partialIntegral_invalid volume g h,
      partialIntegral_invalid volume f (fun h' => h (hi.mp h'))]

theorem partialIntegral_interval (f : ℝ → Option ℝ) (a b c : ℝ) (points : List ℝ)
    (hab : a ≤ b) (hf : ∀ x, Value.Defined (f x))
    (he : ∀ x, (∀ p ∈ points, x ≠ p) →
      f x = some (if a ≤ x ∧ x ≤ b then c else 0)) :
    partialIntegral volume f = some (c * (b - a)) := by
  let g : ℝ → ℝ := (Icc a b).indicator (fun _ => c)
  have hi : Integrable g volume := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const.mpr (Or.inr (by simp [Real.volume_Icc]))
  have he' : (fun x => (f x).getD 0) =ᵐ[volume] g := by
    filter_upwards [ae_away points] with x hx
    simp [he x hx, g, Set.indicator, Set.mem_Icc]
  rw [partialIntegral_valid volume f hf ((integrable_congr he').mpr hi)]
  rw [integral_congr_ae he']
  simp [g, integral_indicator_const, Real.volume_real_Icc_of_le hab, mul_comm]

@[simp] theorem mask_some {α : Type} [Zero α] (b : Bool) (x : α) :
    Value.mask (some b) (some x) = some (cond b x 0) := by cases b <;> rfl
@[simp] theorem and_some (p q : Bool) :
    Value.and (some p) (some q) = some (p && q) := by cases p <;> rfl
@[simp] theorem or_some (p q : Bool) :
    Value.or (some p) (some q) = some (p || q) := by cases p <;> rfl

end QSym.Distribution

/-! Native integration chooses a candidate and exclusions. This elaborator
constructs proofs of totality, almost-everywhere equality, and the interval
integral. It does not trust the native choice of bounds or exceptional points.
The exported term and all its dependencies are checked by Lean's kernel. -/
syntax "qsym_integral% " "[" ident,* "]" term:max term:max term:max term:max term:max : term
macro_rules
  | `(qsym_integral% [$ids:ident,*] $f $a $b $c $points) => do
      let lemmas ← ids.getElems.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let ids := lemmas.map fun item => (⟨item.raw⟩ : Lean.TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])
      `(by
      classical
      refine Eq.trans (QSym.Distribution.partialIntegral_interval $f $a $b $c $points ?_ ?_ ?_) ?_
      · norm_num
      · intro x
        try dsimp only [$ids,*]
        try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
        simp [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ, QSym.Functions.castQR,
          QSym.Value.Defined, QSym.Value.mul, QSym.Value.add,
          QSym.Value.nonzero, QSym.Value.le, QSym.Value.lt, QSym.Value.not,
          QSym.Distribution.mask_some, QSym.Distribution.and_some, QSym.Distribution.or_some]
      · intro x hx
        try dsimp only [$ids,*]
        try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
        try simp only [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ, QSym.Functions.castQR,
          QSym.Value.mul, QSym.Value.add, QSym.Value.nonzero, QSym.Value.le,
          QSym.Value.lt, QSym.Value.not, QSym.Distribution.mask_some,
          QSym.Distribution.and_some, QSym.Distribution.or_some,
          Option.bind_some, Option.map_some, Bool.cond_decide]
        try simp_all [Bool.cond_eq_ite]
        all_goals (try split_ifs) <;> norm_num at * <;>
          (try simp_all [Bool.cond_eq_ite]) <;>
          (try simp_all only [imp_iff_not_or, not_and_or, not_or, ne_iff_lt_or_gt, not_le, not_lt, not_not]) <;>
          (try casesm* _ ∧ _, _ ∨ _) <;> (first | rfl | contradiction | nlinarith)
      · dsimp only [$ids,*]
        norm_num [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval])

syntax "qsym_integral_ae% " "[" ident,* "]" term:max term:max term:max : term
macro_rules
  | `(qsym_integral_ae% [$ids:ident,*] $f $g $points) => do
      let lemmas ← ids.getElems.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let ids := lemmas.map fun item => (⟨item.raw⟩ : Lean.TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])
      `(by
      classical
      apply QSym.Distribution.partialIntegral_congr_away $f $g $points
      · intro x
        try dsimp only [$ids,*]
        try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
        simp [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ, QSym.Functions.castQR,
          QSym.Value.Defined, QSym.Value.mul, QSym.Value.add, QSym.Value.nonzero,
          QSym.Value.le, QSym.Value.lt, QSym.Value.not,
          QSym.Distribution.mask_some, QSym.Distribution.and_some, QSym.Distribution.or_some]
      · intro x
        try dsimp only [$ids,*]
        try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
        simp [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ, QSym.Functions.castQR,
          QSym.Value.Defined, QSym.Value.mul, QSym.Value.add, QSym.Value.nonzero,
          QSym.Value.le, QSym.Value.lt, QSym.Value.not,
          QSym.Distribution.mask_some, QSym.Distribution.and_some, QSym.Distribution.or_some]
      · intro x hx
        try dsimp only [$ids,*]
        try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
        try simp only [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ, QSym.Functions.castQR,
          QSym.Value.mul, QSym.Value.add, QSym.Value.nonzero, QSym.Value.le,
          QSym.Value.lt, QSym.Value.not, QSym.Distribution.mask_some,
          QSym.Distribution.and_some, QSym.Distribution.or_some,
          Option.bind_some, Option.map_some, Bool.cond_decide]
        try simp_all [Bool.cond_eq_ite]
        all_goals (try split_ifs) <;> norm_num at * <;>
          (try simp_all [Bool.cond_eq_ite]) <;>
          (try simp_all only [imp_iff_not_or, not_and_or, not_or, ne_iff_lt_or_gt, not_le, not_lt, not_not]) <;>
          (try casesm* _ ∧ _, _ ∨ _) <;> (first | rfl | contradiction | nlinarith))
