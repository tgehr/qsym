import QSym.Binding
import QSym.DistributionDensityModel
import QSym.Refinement
import Mathlib.Tactic.CasesM

namespace QSym.Distribution
open MeasureTheory Set

@[simp] theorem mask_some {α : Type} [Zero α] (b : Bool) (x : α) :
    Value.mask (some b) (some x) = some (cond b x 0) := by cases b <;> rfl
@[simp] theorem mask_none {α : Type} [Zero α] (x : Option α) :
    Value.mask none x = none := rfl
theorem mask_option {α : Type} [Zero α] (b : Bool) (x : Option α) :
    Value.mask (some b) x = cond b x (some 0) := by cases b <;> rfl
@[simp] theorem and_some (p q : Bool) :
    Value.and (some p) (some q) = some (p && q) := by cases p <;> rfl
@[simp] theorem or_some (p q : Bool) :
    Value.or (some p) (some q) = some (p || q) := by cases p <;> rfl

end QSym.Distribution

/-! Compatibility elaborators for older certificates and handwritten library
proofs. New frontend exports use explicit applications of the precompiled
`Distribution.StepSource` lemmas instead of invoking these tactics. The legacy
elaborators remain available so previously exported certificates still check. -/
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

syntax "qsym_null_support_certificate% " "[" ident,* "]" term:max term:max term:max "[" term,* "]" : term
macro_rules
  | `(qsym_null_support_certificate% [$ids:ident,*] $f $probes $points [$parameters,*]) => do
      let lemmas ← ids.getElems.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let defs := lemmas.map fun item => (⟨item.raw⟩ : Lean.TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])
      let splits ← parameters.getElems.mapM fun p => `(tactic| all_goals cases hp : $p)
      let reduce ← `(tactic|
        simp only [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ,
          QSym.Functions.castQR, QSym.Value.Defined, QSym.Value.mul, QSym.Value.add, QSym.Value.le,
          QSym.Value.lt, QSym.Value.nonzero, QSym.Value.not, QSym.Distribution.mask_option,
          QSym.Distribution.mask_some, QSym.Distribution.mask_none, QSym.Distribution.and_some, QSym.Distribution.or_some,
          Option.bind_eq_bind, Option.some_bind, Option.none_bind, Option.map_eq_map,
          Option.map_some', Option.map_none', Option.pure_def,
          Function.comp_apply, Bool.cond_eq_ite, Bool.decide_iff] at *)
      let finish ← `(tactic| (
        $reduce:tactic
        all_goals norm_num only at *
        all_goals (try $reduce:tactic)
        all_goals (try split_ifs) <;> norm_num at * <;>
          (try simp_all [QSym.Value.Defined, QSym.Value.mul, Bool.cond_eq_ite]) <;>
          (try simp_all only [imp_iff_not_or, not_and_or, not_or, ne_iff_lt_or_gt, not_le, not_lt, not_not]) <;>
          (try casesm* _ ∧ _, _ ∨ _) <;>
          (first | rfl | contradiction | nlinarith | (by_contra h; push_neg at h; nlinarith))))
      `(by
      classical
      show QSym.Distribution.NullSupportCertificate $f $probes $points
      try dsimp only [QSym.Distribution.DensityProgram.density, $defs,*]
      try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
      $[$splits:tactic]*
      all_goals (try dsimp only [$defs,*, QSym.Binding.Expr.eval, QSym.Binding.Env.cons,
        QSym.Expr.eval, QSym.Binding.Ty.denote, QSym.Ty.denote] at *)
      all_goals (try casesm* Bool, QSym.Binding.Ty.denote (.scalar .bool))
      all_goals (try simp only [*])
      all_goals (
        refine ⟨?_, ?_⟩
        · intro hd x
          simp only [List.forall_mem_cons, List.forall_mem_nil] at hd
          norm_num [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ,
            QSym.Functions.castQR, QSym.Value.Defined, QSym.Value.mul, QSym.Value.add,
            QSym.Value.le, QSym.Value.lt, QSym.Value.nonzero, QSym.Value.not,
            QSym.Distribution.mask_option, QSym.Distribution.mask_none,
            QSym.Distribution.and_some, QSym.Distribution.or_some, Bool.cond_eq_ite] at hd
          all_goals (first | solve | obtain ⟨v, hv⟩ := hd; cases hv | $finish:tactic)
        · intro hd x hx
          simp only [List.forall_mem_cons, List.forall_mem_nil] at hd
          norm_num [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ,
            QSym.Functions.castQR, QSym.Value.Defined, QSym.Value.mul, QSym.Value.add,
            QSym.Value.le, QSym.Value.lt, QSym.Value.nonzero, QSym.Value.not,
            QSym.Distribution.mask_option, QSym.Distribution.mask_none,
            QSym.Distribution.and_some, QSym.Distribution.or_some, Bool.cond_eq_ite] at hd
          all_goals (first | solve | obtain ⟨v, hv⟩ := hd; cases hv | $finish:tactic)))

syntax "qsym_density_null_support% " "[" ident,* "]" term:max term:max term:max "[" term,* "]" : term
macro_rules
  | `(qsym_density_null_support% [$ids:ident,*] $p $probes $points [$parameters,*]) => do
      let lemmas ← ids.getElems.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let defs := lemmas.map fun item => (⟨item.raw⟩ : Lean.TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])
      `(by
      have h : QSym.Distribution.NullSupportCertificate
          (QSym.Distribution.DensityProgram.density $p) $probes $points :=
        qsym_null_support_certificate% [$ids,*] (QSym.Distribution.DensityProgram.density $p)
          $probes $points [$parameters,*]
      refine Eq.trans (QSym.Distribution.DensityProgram.mass_bridge $p) ?_
      refine Eq.trans (show QSym.Distribution.DensityProgram.mass $p =
          QSym.Distribution.zeroOnProbes (QSym.Distribution.DensityProgram.density $p) $probes from by qsym_rule) ?_
      try dsimp only [$defs,*]
      all_goals (try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval])
      all_goals simp only [QSym.Distribution.zeroOnProbes, QSym.Distribution.DensityProgram.density,
        QSym.Value.mul_bind_const, Option.bind_some]
      all_goals (
        qsym_integral_finish [$ids,*]
        all_goals norm_num [QSym.Distribution.DensityProgram.density,
          QSym.Value.mul_bind_const, QSym.Value.mask, QSym.Value.mul]))

/-! Unlike strict factoring, this path proves the observation's domain as
well as its value. Splits are on a bounded list of source parameter values;
native bounds, parameters, and the witness are all checked by the kernel. -/
syntax "qsym_parametric_certificate% " "[" ident,* "]" term:max term:max term:max term:max term:max term:max "[" term,* "]" : term
macro_rules
  | `(qsym_parametric_certificate% [$ids:ident,*] $f $c $a $b $w $points [$parameters,*]) => do
      let lemmas ← ids.getElems.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let defs := lemmas.map fun item => (⟨item.raw⟩ : Lean.TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])
      let splits ← parameters.getElems.mapM fun p => `(tactic| all_goals cases hp : $p)
      `(by
      classical
      show QSym.Distribution.ParametricIntervalCertificate $f $c $a $b $w $points
      try dsimp only [QSym.Distribution.DensityProgram.density, $defs,*]
      try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
      $[$splits:tactic]*
      all_goals (try dsimp only [$defs,*, QSym.Binding.Expr.eval, QSym.Binding.Env.cons,
        QSym.Expr.eval, QSym.Binding.Ty.denote, QSym.Ty.denote] at *)
      all_goals (try casesm* Bool, QSym.Binding.Ty.denote (.scalar .bool))
      all_goals (try simp only [*])
      all_goals (
        refine ⟨by norm_num, ?_, ?_, ?_⟩
        · intro hc x
          simp_all [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ,
            QSym.Functions.castQR, QSym.Value.Defined, QSym.Value.mul,
            QSym.Value.le, QSym.Value.lt, QSym.Value.nonzero, QSym.Value.not,
            QSym.Distribution.mask_some, QSym.Distribution.mask_none, QSym.Value.mask_true,
            QSym.Value.mask_false, QSym.Distribution.and_some, QSym.Distribution.or_some]
        · intro r hc x hx
          simp_all [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ,
            QSym.Functions.castQR, QSym.Value.mul, QSym.Value.le, QSym.Value.lt,
            QSym.Value.nonzero, QSym.Value.not, QSym.Distribution.mask_some,
            QSym.Distribution.mask_none, QSym.Value.mask_true, QSym.Value.mask_false,
            QSym.Distribution.and_some, QSym.Distribution.or_some, Bool.cond_eq_ite]
          all_goals (try split_ifs) <;> norm_num at * <;>
            (try simp_all [Bool.cond_eq_ite]) <;>
            (try simp_all only [imp_iff_not_or, not_and_or, not_or, ne_iff_lt_or_gt, not_le, not_lt, not_not]) <;>
            (try casesm* _ ∧ _, _ ∨ _) <;> (first | rfl | contradiction | nlinarith)
        · norm_num [QSym.Function1.apply, QSym.Functions.castNZ, QSym.Functions.castZQ,
            QSym.Functions.castQR, QSym.Value.mul, QSym.Value.le, QSym.Value.lt,
            QSym.Value.nonzero, QSym.Value.not, QSym.Value.mask, QSym.Value.and, QSym.Value.or] at *))

syntax "qsym_density_parametric% " "[" ident,* "]" term:max term:max term:max term:max term:max term:max "[" term,* "]" : term
macro_rules
  | `(qsym_density_parametric% [$ids:ident,*] $p $c $a $b $w $points [$parameters,*]) => `(by
      have h : QSym.Distribution.ParametricIntervalCertificate
          (QSym.Distribution.DensityProgram.density $p) $c $a $b $w $points :=
        qsym_parametric_certificate% [$ids,*] (QSym.Distribution.DensityProgram.density $p)
          $c $a $b $w $points [$parameters,*]
      refine Eq.trans (QSym.Distribution.DensityProgram.mass_bridge $p) ?_
      refine Eq.trans (show QSym.Distribution.DensityProgram.mass $p =
          QSym.Value.mul $c (some ($b - $a)) from by qsym_rule) ?_
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

syntax "qsym_density_factor% " "[" ident,* "]" term:max term:max term:max term:max term:max term:max term:max : term
macro_rules
  | `(qsym_density_factor% [$ids:ident,*] $p $q $factor $a $b $c $points) => do
      let lemmas ← ids.getElems.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let defs := lemmas.map fun item => (⟨item.raw⟩ : Lean.TSyntax [`Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma])
      `(by
      have h : QSym.Distribution.IntervalCertificate
          (QSym.Distribution.DensityProgram.density $q) $a $b $c $points :=
        qsym_interval_certificate% [$ids,*] (QSym.Distribution.DensityProgram.density $q) $a $b $c $points
      have hq : QSym.Distribution.DensityProgram.mass $q = some ($c * ($b - $a)) := by qsym_rule
      have hd : QSym.Value.Defined (QSym.Distribution.DensityProgram.mass $q) := ⟨_, hq⟩
      have hf : ∀ x, QSym.Distribution.DensityProgram.density $p x =
          QSym.Value.mul $factor (QSym.Distribution.DensityProgram.density $q x) := by
        intro x
        try dsimp only [QSym.Distribution.DensityProgram.density, $defs,*]
        try dsimp only [QSym.Binding.Expr.eval, QSym.Binding.Env.cons, QSym.Expr.eval]
        simp only [QSym.Value.mul_one_left, QSym.Value.mul_one_right,
          QSym.Value.mul_assoc, QSym.Value.mul_comm, QSym.Value.mul_left_comm]
      refine Eq.trans (QSym.Distribution.DensityProgram.mass_bridge $p) ?_
      refine Eq.trans (show QSym.Distribution.DensityProgram.mass $p =
        QSym.Value.mul $factor (QSym.Distribution.DensityProgram.mass $q) from by qsym_rule) ?_
      rw [hq]
      qsym_integral_finish [$ids,*])
