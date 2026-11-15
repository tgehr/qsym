import QSym.Binding
import QSym.DistributionDensityModel
import QSym.Refinement
import Mathlib.Tactic.CasesM

namespace QSym.Distribution
open MeasureTheory Set

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
syntax "qsym_interval_certificate% " "[" ident,* "]" term:max term:max term:max term:max term:max : term
macro_rules
  | `(qsym_interval_certificate% [$ids:ident,*] $f $a $b $c $points) => do
      let lemmas ← ids.getElems.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let ids := lemmas.map fun item => (⟨item.raw⟩ : Lean.TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])
      `(by
      classical
      refine (⟨?_, ?_, ?_⟩ : QSym.Distribution.IntervalCertificate $f $a $b $c $points)
      · norm_num
      · intro x
        try dsimp only [QSym.Distribution.DensityProgram.density, $ids,*]
        try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
        simp [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ, QSym.Functions.castQR,
          QSym.Value.Defined, QSym.Value.mul, QSym.Value.add,
          QSym.Value.nonzero, QSym.Value.le, QSym.Value.lt, QSym.Value.not,
          QSym.Distribution.mask_some, QSym.Distribution.and_some, QSym.Distribution.or_some]
      · intro x hx
        try dsimp only [QSym.Distribution.DensityProgram.density, $ids,*]
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

syntax "qsym_null_edit_certificate% " "[" ident,* "]" term:max term:max term:max : term
macro_rules
  | `(qsym_null_edit_certificate% [$ids:ident,*] $f $g $points) => do
      let lemmas ← ids.getElems.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let ids := lemmas.map fun item => (⟨item.raw⟩ : Lean.TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])
      `(by
      classical
      refine (⟨?_, ?_, ?_⟩ : QSym.Distribution.NullEditCertificate $f $g $points)
      · intro x
        try dsimp only [QSym.Distribution.DensityProgram.density, $ids,*]
        try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
        simp [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ, QSym.Functions.castQR,
          QSym.Value.Defined, QSym.Value.mul, QSym.Value.add, QSym.Value.nonzero,
          QSym.Value.le, QSym.Value.lt, QSym.Value.not,
          QSym.Distribution.mask_some, QSym.Distribution.and_some, QSym.Distribution.or_some]
      · intro x
        try dsimp only [QSym.Distribution.DensityProgram.density, $ids,*]
        try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
        simp [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ, QSym.Functions.castQR,
          QSym.Value.Defined, QSym.Value.mul, QSym.Value.add, QSym.Value.nonzero,
          QSym.Value.le, QSym.Value.lt, QSym.Value.not,
          QSym.Distribution.mask_some, QSym.Distribution.and_some, QSym.Distribution.or_some]
      · intro x hx
        try dsimp only [QSym.Distribution.DensityProgram.density, $ids,*]
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


syntax "qsym_integral_finish " "[" ident,* "]" : tactic
macro_rules
  | `(tactic| qsym_integral_finish [$ids:ident,*]) => do
      let lemmas ← ids.getElems.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let ids := lemmas.map fun item => (⟨item.raw⟩ : Lean.TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])
      `(tactic| (
        try dsimp only [$ids,*]
        norm_num [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]))

-- Compatibility with previously extracted certificates.
syntax "qsym_integral% " "[" ident,* "]" term:max term:max term:max term:max term:max : term
macro_rules
  | `(qsym_integral% [$ids:ident,*] $f $a $b $c $points) => `(by
      have h : QSym.Distribution.IntervalCertificate $f $a $b $c $points :=
        qsym_interval_certificate% [$ids,*] $f $a $b $c $points
      refine Eq.trans h.integrate ?_
      qsym_integral_finish [$ids,*])

syntax "qsym_integral_ae% " "[" ident,* "]" term:max term:max term:max : term
macro_rules
  | `(qsym_integral_ae% [$ids:ident,*] $f $g $points) => `(by
      have h : QSym.Distribution.NullEditCertificate $f $g $points :=
        qsym_null_edit_certificate% [$ids,*] $f $g $points
      exact QSym.Distribution.partialIntegral_congr_away $f $g $points
        h.source_total h.target_total h.away)

/-! Frontend extraction now constructs a density program and a certificate,
then applies the model law through the ordinary rule prover. Native bounds
and exception lists are proposals; no source assertion is trusted. -/
syntax "qsym_density_integral% " "[" ident,* "]" term:max term:max term:max term:max term:max : term
macro_rules
  | `(qsym_density_integral% [$ids:ident,*] $p $a $b $c $points) => `(by
      have h : QSym.Distribution.IntervalCertificate
          (QSym.Distribution.DensityProgram.density $p) $a $b $c $points :=
        qsym_interval_certificate% [$ids,*] (QSym.Distribution.DensityProgram.density $p) $a $b $c $points
      refine Eq.trans (QSym.Distribution.DensityProgram.mass_bridge $p) ?_
      refine Eq.trans (show QSym.Distribution.DensityProgram.mass $p = some ($c * ($b - $a)) from by
        qsym_rule) ?_
      qsym_integral_finish [$ids,*])

syntax "qsym_density_integral_ae% " "[" ident,* "]" term:max term:max term:max : term
macro_rules
  | `(qsym_density_integral_ae% [$ids:ident,*] $p $q $points) => `(by
      have h : QSym.Distribution.NullEditCertificate
          (QSym.Distribution.DensityProgram.density $p) (QSym.Distribution.DensityProgram.density $q) $points :=
        qsym_null_edit_certificate% [$ids,*]
          (QSym.Distribution.DensityProgram.density $p) (QSym.Distribution.DensityProgram.density $q) $points
      refine Eq.trans (QSym.Distribution.DensityProgram.mass_bridge $p) ?_
      refine Eq.trans ?_ (QSym.Distribution.DensityProgram.mass_bridge $q).symm
      qsym_rule)
