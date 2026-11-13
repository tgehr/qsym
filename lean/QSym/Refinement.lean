import QSym.RefinementBase
import QSym.AffineAlgebra
import QSym.RuleBranches
import QSym.Partitions
import QSym.Trigonometry
import QSym.PowerPredicates
import QSym.ScalarTypes
import QSym.CubeRootSigns
import QSym.SignThresholds
import QSym.SignDifferences
import QSym.DecreasingSigns
import QSym.LogBaseSigns
import QSym.DecreasingThresholds
import QSym.IntegerEquations
import QSym.PowerSigns
import QSym.DiscreteDomains
import QSym.ScalarOrder
import QSym.SignCompositions

namespace QSym

open Lean Meta Elab Tactic in
elab "qsym_split_and" : tactic => liftMetaTactic fun goal => goal.withContext do
  for decl in ← getLCtx do
    if decl.type.isAppOfArity ``And 2 || decl.type.isAppOfArity ``Exists 2 then
      return (← goal.cases decl.fvarId).toList.map (·.mvarId)
  throwError "no conjunction"

open Lean Meta Elab Tactic in
elab "qsym_split_bool" : tactic => liftMetaTactic fun goal => goal.withContext do
  for decl in ← getLCtx do
    if (← whnf decl.type).isConstOf ``Bool then
      return (← goal.cases decl.fvarId).toList.map (·.mvarId)
  throwError "no Boolean"

-- Search is untrusted: every successful tactic emits a kernel-checked proof.
open Lean Meta Elab Tactic in
elab "qsym_order_goal" : tactic => do
  let t ← getMainTarget
  unless t.isAppOfArity ``Value.Refines 3 && (← whnf t.getAppArgs[0]!).isConstOf ``Bool do
    throwError "not a Boolean refinement"

macro "qsym_order_core" mode:ident : tactic => do
  let early := mode.getId.eraseMacroScopes==`early
  let enter ← if early then `(tactic| intro v hv) else `(tactic| skip)
  let domains ← if early then `(tactic| all_goals try split_ifs at *) else `(tactic| skip)
  let powers ← if early then `(tactic| (
  all_goals repeat' qsym_split_and
  all_goals try simp_all only [← sub_eq_add_neg, sub_eq_zero, ← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  all_goals try simp (disch := (first | assumption | (simp only [Functions.powerR]; assumption))) only [
    Real.rpow_right_inj, Real.rpow_lt_rpow_iff, Real.rpow_le_rpow_iff, Real.rpow_left_inj,
    Order.power_not_negative, Order.power_not_nonpositive,
    Order.power_negative_lt, Order.power_negative_le, Order.power_noninteger_lt, Order.power_noninteger_le,
    Order.power_noninteger_negative_lt, Order.power_noninteger_negative_le, Order.power_noninteger_eq,
    Elementary.cpow_contract_eq, Elementary.cpow_negative_contract_eq, Complex.cpow_eq_zero_iff,
    PowerPredicates.noninteger_eq_one,
    Order.nonnegative_inverse_lt, Order.nonnegative_inverse_le, Order.nonpositive_inverse_lt, Order.nonpositive_inverse_le] at *
  all_goals try assumption
  )) else `(tactic| (
  all_goals try simp_all only [← sub_eq_add_neg, sub_eq_zero, ← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  ))
  `(tactic| (
  qsym_order_goal
  classical
  $enter:tactic
  simp only [Value.Refines, Value.Defined, Function1.apply, Function2.apply,
    Functions.expR, Functions.logR, Functions.sqrtR, Functions.powerR, Functions.powerC, Functions.isIntR,
    Functions.minR, Functions.maxR, Functions.absC, Functions.reC, Functions.imC,
    Functions.expC, Functions.logC, Functions.sqrtC, Functions.pi, Functions.sinR, Functions.cosR,
    Value.inv, Value.conj, Value.add, Value.mul, Value.nonzero, Value.not, Value.lt, Value.le, Value.abs,
    Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind] at *
  try simp only [Option.some.injEq, forall_eq, forall_eq', Bool.true_eq, decide_eq_true_eq] at *
  $domains:tactic
  repeat' first
    | simp_all (config := {failIfUnchanged := true}) [Value.and_some, Value.or_some, Value.mask, Real.sin_le_one, Real.neg_one_le_sin, Real.cos_le_one, Real.neg_one_le_cos, -Real.log_eq_zero]
    | qsym_split_bool
    | split_ifs at *
  $powers:tactic
  all_goals try simp_all [Identities.min_eq_max, Identities.clog_inj, Identities.clog_zero,
    Identities.csqrt_inj, Identities.cexp_inj, Identities.conj_eq,
    min_lt_iff, min_le_iff, lt_min_iff, le_min_iff, max_lt_iff, max_le_iff, lt_max_iff, le_max_iff,
    Order.nonnegative_add_eq_zero, Order.nonpositive_add_eq_zero,
    Order.odd_power_lt, Order.odd_power_le, Order.odd_power_eq,
    Order.odd_negative, Order.odd_nonpositive, Order.odd_positive, Order.odd_nonnegative,
    Order.even_lt_nonpositive, Order.even_le_negative, Order.negative_lt_even, Order.nonpositive_le_even,
    Order.odd_mul_negative, Order.odd_mul_nonpositive, Order.odd_mul_positive, Order.odd_mul_nonnegative,
    Order.even_mul_negative, Order.even_mul_nonpositive, Order.even_mul_positive, Order.even_mul_nonnegative,
    Order.even_power_lt, Order.even_power_le, Order.even_power_eq,
    Order.nonnegative_power_lt, Order.nonnegative_power_le,
    Real.exp_lt_exp, Real.exp_le_exp, Real.exp_eq_exp, Real.exp_eq_one_iff, Real.exp_ne_zero,
    Real.exp_lt_one_iff, Real.exp_le_one_iff, Real.one_lt_exp_iff, Real.one_le_exp_iff,
    Real.log_lt_log_iff, Real.log_le_log_iff, Real.log_injOn_pos.eq_iff, Order.log_eq_exp,
    Real.log_neg_iff, Order.log_nonpositive, Order.log_positive, Real.log_nonneg_iff,
    Real.sqrt_lt_sqrt_iff, Real.sqrt_le_sqrt_iff, Real.sqrt_inj, Real.sqrt_eq_zero,
    Real.rpow_lt_rpow_left_iff, Real.rpow_le_rpow_left_iff,
    Real.rpow_lt_rpow_left_iff_of_base_lt_one, Real.rpow_le_rpow_left_iff_of_base_lt_one,
    abs_lt, abs_le, Order.lt_abs_cases, Order.le_abs_cases, Order.abs_eq_cases, not_and_or, -Real.log_eq_zero]
  all_goals try simp_all only [← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide,
    eq_neg_iff_add_eq_zero, imp_iff_not_or, not_le, not_lt]
  all_goals first
    | solve | apply Order.quadratic_lt_pos <;> assumption
    | solve | symm; apply Order.quadratic_lt_pos <;> assumption
    | solve | apply Order.quadratic_le_pos <;> assumption
    | solve | symm; apply Order.quadratic_le_pos <;> assumption
    | solve | apply Order.quadratic_lt_neg <;> assumption
    | solve | symm; apply Order.quadratic_lt_neg <;> assumption
    | solve | apply Order.quadratic_le_neg <;> assumption
    | solve | symm; apply Order.quadratic_le_neg <;> assumption
    | solve | simp only [Order.sqrt_lt_bound (by assumption), Order.le_sqrt_bound (by assumption),
        Real.sqrt_le_iff, Order.lt_sqrt_bound, ← not_lt]; tauto
    | solve | simp_all only [Order.sqrt_lt_bound, Real.sqrt_le_iff, Order.lt_sqrt_bound, Order.le_sqrt_bound, ← not_lt]; tauto
    | solve | simp_all [mul_neg_iff, mul_nonpos_iff, mul_pos_iff, mul_nonneg_iff]; tauto
    | solve | constructor <;> intro h <;> nlinarith
    | solve | nlinarith
    | solve | positivity
    | solve | tauto
))

open Lean Meta Elab Tactic in
elab "qsym_order" : tactic => do
  evalTactic (← `(tactic| qsym_order_goal))
  let source := (← getMainTarget).getAppArgs[1]!
  let early := (source.find? fun e => e.isConstOf ``Functions.powerR ||
    e.isConstOf ``Functions.powerC || e.isConstOf ``Value.inv).isSome
  if early then evalTactic (← `(tactic| qsym_order_core early))
  else evalTactic (← `(tactic| qsym_order_core plain))

open Lean Meta Elab Tactic in
elab "qsym_function_order_goal" : tactic => do
  evalTactic (← `(tactic| qsym_order_goal))
  let source := (← getMainTarget).getAppArgs[1]!
  let names := [``Functions.erfR, ``Functions.erfcR, ``Functions.sinhR, ``Functions.asinhR,
    ``Functions.tanhR, ``Functions.atanR, ``Functions.asinR, ``Functions.acosR,
    ``Functions.cbrtR, ``Functions.acoshR, ``Functions.atanhR]
  unless (source.find? fun e => names.any e.isConstOf).isSome do
    throwError "not a supported unary function comparison"

macro "qsym_function_monotonicity" : tactic => `(tactic| (
  first
    | exact FunctionOrder.erf
    | exact FunctionOrder.erfc
    | exact FunctionOrder.sinh
    | exact FunctionOrder.asinh
    | exact FunctionOrder.tanh
    | exact FunctionOrder.atan
    | exact FunctionOrder.asin
    | exact FunctionOrder.acos
    | exact FunctionOrder.cbrt
    | exact FunctionOrder.acosh
    | exact FunctionOrder.atanh
))

macro "qsym_function_order" : tactic => `(tactic| (
  qsym_function_order_goal
  try simp only [Int.cast_neg, Int.cast_one] at *
  first
    | (apply Value.refines_increasing_lt; qsym_function_monotonicity)
    | (apply Value.refines_increasing_le; qsym_function_monotonicity)
    | (apply Value.refines_increasing_ne; qsym_function_monotonicity)
    | (apply Value.refines_decreasing_lt; qsym_function_monotonicity)
    | (apply Value.refines_decreasing_le; qsym_function_monotonicity)
    | (apply Value.refines_decreasing_ne; qsym_function_monotonicity)
))

open Lean Meta Elab Tactic in
elab "qsym_inverse_symmetry_goal" : tactic => do
  let names := #[``Real.arcsin, ``Real.arccos, ``Real.arctan, ``Real.arsinh]
  let target ← getMainTarget
  unless (target.find? fun e => names.any (fun n => e.isConstOf n)).isSome do
    throwError "not an inverse symmetry goal"

open Lean Meta Elab Tactic in
elab "qsym_trig_goal" : tactic => do
  let functions := #[``Real.sin, ``Real.cos, ``Real.tan, ``Real.sinh, ``Real.cosh, ``Real.tanh,
    ``Complex.sin, ``Complex.cos, ``Complex.tan, ``Complex.sinh, ``Complex.cosh, ``Complex.tanh, ``Complex.exp]
  let target ← getMainTarget
  unless (target.find? fun e => functions.any (fun n => e.isConstOf n)).isSome do
    throwError "not a trigonometric goal"

open Lean Meta Elab Tactic in
elab "qsym_log_hyperbolic_goal" : tactic => do
  let target ← getMainTarget
  let hyperbolic := #[``Real.sinh, ``Real.cosh, ``Real.tanh, ``Complex.sinh, ``Complex.cosh, ``Complex.tanh,
    ``Functions.sinhR, ``Functions.coshR, ``Functions.tanhR, ``Functions.sinhC, ``Functions.coshC, ``Functions.tanhC]
  let logarithms := #[``Real.log, ``Complex.log, ``Functions.logR, ``Functions.logC]
  unless (target.find? fun e => logarithms.any (fun n => e.isConstOf n)).isSome &&
      (target.find? fun e => hyperbolic.any (fun n => e.isConstOf n)).isSome do
    throwError "not a logarithmic hyperbolic goal"

open Lean Meta Elab Tactic in
elab "qsym_log_base_goal" : tactic => do
  let target ← getMainTarget
  unless (target.find? fun e => e.isConstOf ``Functions.log2R || e.isConstOf ``Functions.log10R).isSome do
    throwError "not a base logarithm goal"

open Lean Meta Elab Tactic in
elab "qsym_new_trig_goal" : tactic => withMainContext do
  let functions := #[``Real.sin, ``Real.cos, ``Real.tan, ``Real.sinh, ``Real.cosh, ``Real.tanh,
    ``Complex.sin, ``Complex.cos, ``Complex.tan, ``Complex.sinh, ``Complex.cosh, ``Complex.tanh, ``Complex.exp]
  let target ← getMainTarget
  let powers := #[``Real.rpow, ``Complex.cpow, ``Functions.powerR, ``Functions.powerC, ``Functions.sqrtC]
  let containsPower := fun t : Lean.Expr => (t.find? fun e => powers.any (fun n => e.isConstOf n)).isSome
  if containsPower target then throwError "general-power goal"
  for decl in (← getLCtx) do
    if containsPower decl.type then throwError "general-power hypothesis"
  let containsFunction := fun t : Lean.Expr => (t.find? fun e => functions.any (fun n => e.isConstOf n)).isSome
  let mut found := containsFunction target
  for decl in (← getLCtx) do
    found := found || containsFunction decl.type
  unless found do
    throwError "not a trigonometric goal"

open Lean Meta Elab Tactic in
elab "qsym_integer_power_goal" : tactic => withMainContext do
  let containsPower := fun t : Lean.Expr => (t.find? fun e =>
    e.isAppOfArity ``HPow.hPow 6 && e.getAppArgs[1]!.isConstOf ``Int).isSome
  let mut found := containsPower (← getMainTarget)
  for decl in (← getLCtx) do
    found := found || containsPower decl.type
  unless found do
    throwError "not an integer-power goal"

open Lean Meta Elab Tactic in
elab "qsym_inverse_goal" : tactic => do
  let functions := #[``Functions.asinhR, ``Functions.acoshR, ``Functions.atanhR, ``Functions.asinC, ``Functions.acosC,
    ``Functions.atanC, ``Functions.asinhC, ``Functions.acoshC, ``Functions.atanhC]
  let target ← getMainTarget
  let tangentComposition := (target.find? fun e => e.isConstOf ``Functions.tanR).isSome &&
    (target.find? fun e => e.isConstOf ``Functions.asinR || e.isConstOf ``Functions.acosR).isSome
  unless tangentComposition || (target.find? fun e => functions.any (fun n => e.isConstOf n)).isSome do
    throwError "not an inverse-function goal"

macro "qsym_inverse" : tactic => `(tactic| (qsym_inverse_goal; first
  | exact Value.refines_inverse Functions.coshR Functions.acoshR _ (fun x h _ => Inverse.real_cosh_acosh x h)
  | exact Value.refines_inverse Functions.tanhR Functions.atanhR _ (fun x h _ => Inverse.real_tanh_atanh x h.1 h.2)
  | exact Value.refines_inverse Functions.atanhR Functions.tanhR _ (fun x _ h => Inverse.real_atanh_tanh x h)
  | exact Value.refines_inverse Functions.sinC Functions.asinC _ (fun z _ _ => Inverse.complex_sin_asin z)
  | exact Value.refines_inverse Functions.cosC Functions.acosC _ (fun z _ _ => Inverse.complex_cos_acos z)
  | exact Value.refines_inverse Functions.tanC Functions.atanC _ (fun z h _ => Inverse.complex_tan_atan z h.1 h.2)
  | exact Value.refines_inverse Functions.sinhC Functions.asinhC _ (fun z _ _ => Inverse.complex_sinh_asinh z)
  | exact Value.refines_inverse Functions.coshC Functions.acoshC _ (fun z _ _ => Inverse.complex_cosh_acosh z)
  | exact Value.refines_inverse Functions.tanhC Functions.atanhC _ (fun z h _ => Inverse.complex_tanh_atanh z h.1 h.2)
  | exact Value.refines_real_acosh_cosh _
  | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, add_zero]; first
    | exact Value.refines_real_exp_asinh _
    | exact Value.refines_real_exp_acosh _
    | exact Value.refines_complex_exp_asinh _
    | exact Value.refines_complex_exp_acosh _
    | exact Value.refines_real_cosh_atanh _
    | exact Value.refines_real_sinh_atanh _
    | exact Value.refines_real_tan_asin _
    | exact Value.refines_real_tan_acos _
    | exact Value.refines_complex_tan_asin _
    | exact Value.refines_complex_tan_acos _
    | exact Value.refines_real_tanh_asinh _
    | exact Value.refines_real_tanh_acosh _
    | exact Value.refines_complex_tanh_asinh _
    | exact Value.refines_complex_tanh_acosh _
    | exact Value.refines_real_sinh_acosh _
    | exact Value.refines_complex_cos_asin _
    | exact Value.refines_complex_sin_acos _
    | exact Value.refines_complex_cosh_asinh _
    | exact Value.refines_complex_sinh_acosh _)))

open Lean Meta Elab Tactic in
elab "qsym_unit_power_goal" : tactic => do
  let t ← getMainTarget
  unless t.isAppOfArity ``Value.Refines 3 &&
      (t.getAppArgs[2]!.find? fun e => e.isConstOf ``Functions.isIntR).isSome &&
      (t.getAppArgs[1]!.find? fun e => e.isConstOf ``Functions.powerR || e.isConstOf ``Functions.powerC).isSome do
    throwError "not a unit-power predicate"

macro "qsym_unit_power" : tactic => `(tactic| (
  qsym_unit_power_goal
  classical
  intro v hv
  simp [Value.Refines, Function1.apply, Function2.apply, Functions.isIntR, Functions.reC, Functions.imC,
    Value.not, Value.nonzero, Value.add, Value.mul, Value.inv] at *
  all_goals split_ifs at *
  all_goals simp_all [PowerPredicates.real_value, PowerPredicates.complex_value,
    Value.add, Value.not, Value.nonzero, Value.mul, Value.inv, Value.and_some, Value.or_some,
    Function1.apply, Functions.isIntR, ← sub_eq_add_neg, sub_eq_zero,
    add_eq_zero_iff_eq_neg, ← div_eq_mul_inv, Bool.or_assoc]
  all_goals try simp_all [PowerPredicates.real_neg_one_eq_one, PowerPredicates.complex_minus_one_eq_one]
  all_goals simp_all [PowerPredicates.real_eq_one, PowerPredicates.real_eq_neg_one,
    PowerPredicates.complex_real_eq_one, Bool.or_assoc]
))

open Lean Meta Elab Tactic in
elab "qsym_real_power_bridge_goal" : tactic => do
  let t ← getMainTarget
  unless t.isAppOfArity ``Value.Refines 3 &&
      (t.getAppArgs[2]!.find? fun e => e.isConstOf ``Functions.powerR).isSome &&
      (t.getAppArgs[1]!.find? fun e => e.isConstOf ``Functions.powerC).isSome do
    throwError "not a real-to-complex power bridge"

macro "qsym_real_power_bridge" : tactic => `(tactic| (
  qsym_real_power_bridge_goal
  classical
  intro v hv
  simp [Value.Refines, Function1.apply, Function2.apply, Functions.castRC, Functions.reC, Functions.imC,
    Value.not, Value.nonzero, Value.le] at *
  all_goals split_ifs at *
  all_goals simp_all [PowerPredicates.real_value, PowerPredicates.complex_value,
    PowerPredicates.nonnegative_domain, PowerPredicates.complex_nonnegative_power,
    Function1.apply, Functions.castRC]
))

open Lean Meta Elab Tactic in
elab "qsym_exact_scalar_goal" : tactic => do
  unless ((← getMainTarget).find? fun e => e.isConstOf ``Functions.denQ).isSome do
    throwError "not an exact scalar predicate"

macro "qsym_exact_scalar" : tactic => `(tactic| (
  qsym_exact_scalar_goal
  classical
  intro v hv
  simp [Value.Refines, Function1.apply, Function2.apply,
    Functions.isIntR, Functions.denQ, Functions.castNZ, Functions.castZQ, Functions.castQR,
    Functions.castRC, Functions.imC, Functions.addZ, Functions.mulZ, Functions.nonzeroZ,
    Functions.addQ, Functions.mulQ, Functions.invQ, Functions.nonzeroQ,
    Functions.powZN, Functions.powQN, Functions.powRN, Functions.powCN,
    Functions.powQZ, Functions.powRZ, Functions.powCZ,
    Value.not, Value.nonzero, Value.add, Value.mul, Value.inv] at *
  all_goals try split_ifs at *
  all_goals simp_all [Value.add, Value.not, Value.nonzero, Value.mul, Value.inv,
    Value.and_some, Value.or_some, Function1.apply, Functions.castNZ, Functions.nonzeroN,
    ← sub_eq_add_neg, sub_eq_zero, add_eq_zero_iff_eq_neg, ← div_eq_mul_inv, Bool.or_assoc,
    ScalarTypes.rational_integer, ScalarTypes.rational_integer_cast, ScalarTypes.complex_nat_unit, ScalarTypes.complex_int_unit,
    pow_eq_one_iff_cases, pow_eq_neg_one_iff, zpow_eq_one_iff_cases₀, zpow_eq_neg_one_iff₀,
    ScalarTypes.even_int, ScalarTypes.odd_int, ScalarTypes.even_nat, ScalarTypes.odd_nat]
  all_goals try (subst v; simp [Bool.not_and, Bool.not_or, Bool.or_assoc])
))

-- Rational normalization is useful for exact bounds and inverses, but must
-- not spend the heartbeat budget of unrelated real/complex power proofs.
open Lean Meta Elab Tactic in
elab "qsym_rational_goal" : tactic => withMainContext do
  for decl in (← getLCtx) do
    if (← whnf decl.type).isConstOf ``Rat then return
  throwError "no rational scalar"

macro "qsym_scalar" : tactic => `(tactic| (
  first
  | solve | qsym_partition
  | solve | qsym_branch
  | solve | (apply Value.refines_integer_literal_affine_nonzero; assumption)
  | solve | (apply Value.refines_natural_literal_affine_nonzero; assumption)
  | solve | qsym_extrema
  | exact Value.refines_sign_sinh _
  | exact Value.refines_sign_tanh _
  | exact Value.refines_sign_asinh _
  | exact Value.refines_sign_atan _
  | exact Value.refines_sign_asin _
  | exact Value.refines_sign_atanh _
  | exact Value.refines_sign_product _ _
  | exact Value.refines_abs_cbrt _
  | exact Value.refines_sign_cbrt _
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_log _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_exp_difference _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_exp_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_log_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_sinh_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_tanh_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_asinh_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_atan_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_asin_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_atanh_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_cbrt_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_acosh_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_acos_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_erfc_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_log2 _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_log2_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_log10 _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_log10_pair_difference _ _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_acos_half_pi _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_half_pi_acos _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_erfc_minus_one _)
  | solve | (simp only [Int.cast_neg, Int.cast_one]; exact Value.refines_sign_one_minus_erfc _)
  | solve | (simp only [Int.cast_neg, Int.cast_one, Int.cast_zero] at *; apply Value.refines_sign_power_pair_above_one <;> assumption)
  | solve | (simp only [Int.cast_neg, Int.cast_one, Int.cast_zero] at *; apply Value.refines_sign_power_pair_below_one <;> assumption)
  | exact Value.refines_sign_abs _
  | solve | qsym_exact_scalar
  | solve | qsym_real_power_bridge
  | solve | qsym_unit_power
  | solve | qsym_inverse
  | exact Value.refines_quotient_add_nonzero _ _ _
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one] at *; apply Value.refines_log_rational <;> assumption)
  | solve | qsym_function_order
  | solve | qsym_order
  | solve | apply Value.refines_cbrt_power
  | solve | apply Value.refines_cbrt_cube
  | solve | (simp only [Int.cast_neg, Int.cast_one]; apply Value.refines_cbrt_neg)
  | solve | apply Value.refines_cbrt_inverse
  | solve | apply Value.refines_cbrt_power_multiple
  | solve | apply Value.refines_cbrt_power_one
  | solve | apply Value.refines_cbrt_power_two
  | solve | apply Value.refines_cbrt_factor_left
  | solve | apply Value.refines_cbrt_factor_right
  | solve | (qsym_log_base_goal; first
    | (simp only [Int.cast_zero, Int.cast_one, Int.cast_natCast] at *; apply Value.refines_log2_product <;> assumption)
    | (simp only [Int.cast_zero, Int.cast_one, Int.cast_natCast] at *; apply Value.refines_log2_power <;> assumption)
    | (simp only [Int.cast_zero, Int.cast_one, Int.cast_natCast] at *; apply Value.refines_log10_product <;> assumption)
    | (simp only [Int.cast_zero, Int.cast_one, Int.cast_natCast] at *; apply Value.refines_log10_power <;> assumption))
  | solve | apply Value.refines_cbrt_product
  | solve | apply Value.refines_sqrt_even_power
  | solve | (simp only [Int.cast_zero] at *; apply Value.refines_sqrt_even_factor; assumption)
  | exact Value.refines_inv_inv _
  | solve | (simp only [Int.cast_zero] at *; apply Value.refines_log_product <;> assumption)
  | solve | apply Value.refines_power_exact <;> assumption
  | solve | (simp only [Int.cast_natCast, Int.cast_zero, Int.cast_neg, Int.cast_one, Int.cast_ofNat] at *; apply Value.refines_power_scale <;> assumption)
  | solve | apply Value.refines_phase_period <;> assumption
  | solve | apply Value.refines_tan_cos
  | solve | apply Value.refines_complex_tan_cos
  | solve | (qsym_log_hyperbolic_goal; first
    | (simp only [Int.cast_one, Int.cast_neg]; apply Value.refines_real_sinh_log)
    | (simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, add_zero]; apply Value.refines_complex_tanh_log))
  | solve | apply Value.refines_complex_tanh_cosh
  | solve | (simp only [Int.cast_one]; apply Value.refines_sin_atan)
  | solve | (simp only [Int.cast_one]; apply Value.refines_cos_atan)
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one] at *; apply Value.refines_power_negative <;> assumption)
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one] at *; apply Value.refines_lt_factor <;> assumption)
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one] at *; apply Value.refines_le_factor <;> assumption)
  | (
    classical
    intro v hv
    try simp only [Value.Refines, Value.Defined] at *
    try simp only [Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.addN, Functions.subN,
      Functions.mulN, Functions.ltN, Functions.leN, Functions.nonzeroN, Functions.addZ,
      Functions.mulZ, Functions.ltZ, Functions.leZ, Functions.nonzeroZ, Functions.addQ,
      Functions.mulQ, Functions.ltQ, Functions.leQ, Functions.nonzeroQ, Functions.invQ,
      Functions.eqB, Functions.powNN, Functions.powZN, Functions.powQN, Functions.powRN, Functions.powCN,
      Functions.powQZ, Functions.powRZ, Functions.powCZ, Functions.cbrtR, Functions.exp2R, Functions.log2R, Functions.log10R,
      Functions.floorR, Functions.ceilR, Functions.roundR, Functions.isIntR, Functions.hypotR, Functions.argC,
      Functions.expiC, Functions.polarC, Functions.atan2R, Functions.asinhR, Functions.acoshR, Functions.atanhR,
      Functions.asinC, Functions.acosC, Functions.atanC, Functions.asinhC, Functions.acoshC, Functions.atanhC,
      Functions.erfR, Functions.erfcR, Functions.gammaR, Functions.gammaC, Functions.lgammaR, Elementary.half_domain, Functions.powerR, Functions.powerC, Functions.sqrtR, Functions.sqrtC,
      Functions.expR, Functions.expC, Functions.sinR, Functions.sinC, Functions.cosR,
      Functions.cosC, Functions.sinhR, Functions.sinhC, Functions.coshR, Functions.coshC,
      Functions.tanhR, Functions.tanhC, Functions.logR, Functions.logC, Functions.tanR,
      Functions.tanC, Functions.minR, Functions.maxR, Functions.signR, Functions.asinR,
      Functions.acosR, Functions.atanR, Functions.absC, Functions.pi, Functions.e, Functions.makeC, Functions.reC, Functions.imC, Functions.cisR,
      Value.add, Value.mul, Value.inv, Value.nonzero, Value.mask, Value.conj,
      Value.not, Value.and, Value.or, Value.lt, Value.le, Value.abs,
      Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind] at *
    try simp only [Option.some.injEq, forall_eq, forall_eq', Bool.true_eq, decide_eq_true_eq] at *
    repeat' first
      | simp_all (config := {failIfUnchanged := true}) [Real.exp_pos, Real.sqrt_nonneg, Real.sqrt_pos, Real.pi_pos, Elementary.half_ne_int, Elementary.inv_two_ne_int, Elementary.sqrt_not_neg]
      | qsym_split_and
      | qsym_split_bool
      | split at *
    all_goals try (simp_all only [← sub_eq_add_neg, sub_eq_zero])
    all_goals subst_vars
    all_goals try (qsym_rational_goal; solve | simp_all [← sub_eq_add_neg, sub_eq_zero, inv_inj,
      ScalarOrder.nonnegative_inverse_lt, ScalarOrder.nonnegative_inverse_le,
      ScalarOrder.nonpositive_inverse_lt, ScalarOrder.nonpositive_inverse_le,
      Rat.floor_cast, Rat.ceil_cast, Int.lt_ceil, Int.le_floor])
    all_goals try (qsym_new_trig_goal; solve | (
      push_cast at *
      simp_all [Real.sin_int_mul_pi, Trigonometry.real_integer_cos,
        Real.sin_sub_int_mul_pi, Real.cos_sub_int_mul_pi,
        Trigonometry.complex_sin_sub, Trigonometry.complex_cos_sub,
        Complex.sin_sub_int_mul_two_pi, Complex.cos_sub_int_mul_two_pi,
        Trigonometry.tan_period, Trigonometry.tan_period_domain,
        Trigonometry.sinh_period, Trigonometry.cosh_period, Trigonometry.exp_period,
        Trigonometry.sinh_sub_imaginary, Trigonometry.cosh_sub_imaginary,
        Trigonometry.exp_sub_imaginary, Trigonometry.tanh_period_imaginary,
        Trigonometry.cosh_quarter_sub, Trigonometry.sinh_quarter_sub, Trigonometry.exp_quarter_sub,
        Complex.cos_sub_pi_div_two, Complex.sin_sub_pi_div_two,
        Trigonometry.integer_phase, Trigonometry.phase_sub,
        Trigonometry.parity_cancel_mul, Trigonometry.parity_square, zpow_ne_zero,
        Complex.ofReal_zpow, ← mul_assoc]))
    all_goals try (qsym_integer_power_goal; solve | simp_all [Trigonometry.parity_even, Trigonometry.parity_odd,
      Trigonometry.parity_neg, Trigonometry.parity_square, Trigonometry.parity_inverse])
    all_goals try (qsym_integer_power_goal; solve | simp_all [zpow_mul, zpow_ne_zero, mul_assoc])
    all_goals try (qsym_new_trig_goal; solve | (simp_all [Real.sin_sub, Complex.sin_sub, Real.cos_add, Complex.cos_add,
      Real.sinh_add, Complex.sinh_add, Real.sinh_sub, Complex.sinh_sub,
      Real.cosh_add, Complex.cosh_add, Real.cosh_sub, Complex.cosh_sub,
      Real.sinh_two_mul, Complex.sinh_two_mul, Real.cosh_two_mul, Complex.cosh_two_mul,
      Real.cos_sq', Complex.cos_sq',
      Real.cosh_sq, Complex.cosh_sq,
      Real.cosh_pos, Real.one_le_cosh, abs_of_pos (Real.cosh_pos _),
      Trigonometry.tanh_lt_one, Trigonometry.neg_one_lt_tanh,
      Trigonometry.cosh_not_nonpositive, Trigonometry.tanh_not_ge_one, Trigonometry.tanh_not_le_neg_one, Elementary.cosh_ne_zero] <;> ring))
    all_goals try (qsym_new_trig_goal; solve | (simp_all [Real.cosh_eq, Complex.cosh, Real.sinh_eq, Complex.sinh] <;> ring))
    all_goals try (qsym_trig_goal; solve | simp_all [Elementary.sin_quarter_turn, Elementary.cos_quarter_turn,
      Elementary.phase_quarter_turn, Elementary.phase_cartesian, Elementary.tan_period, Elementary.tan_period_domain,
      Real.tan_eq_sin_div_cos, Complex.tan_eq_sin_div_cos, Real.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh,
      Real.cosh_add_sinh, Real.cosh_sub_sinh, Complex.cosh_add_sinh, Complex.cosh_sub_sinh,
      Complex.sin_add_pi, Complex.cos_add_pi, Complex.tan_add_pi,
      Complex.sin_add_pi_div_two, Complex.cos_add_pi_div_two,
      Real.sin_add, Real.cos_sub, Complex.sin_add, Complex.cos_sub,
      Real.sin_arctan, Real.cos_arctan, Real.cosh_arsinh,
      ← Complex.tan_conj, ← Complex.tanh_conj, ← Complex.cos_conj, ← Complex.cosh_conj,
      Real.cos_abs, Real.cosh_abs, Real.abs_sinh,
      Real.sin_pi_div_three, Real.cos_pi_div_six, Elementary.cosh_ne_zero,
      Real.cos_two_mul', Complex.cos_two_mul', div_eq_mul_inv])
    all_goals try (qsym_log_hyperbolic_goal; solve | simp_all [Real.sinh_log, Real.cosh_log, Complex.sinh, Complex.cosh, Complex.exp_neg, Complex.exp_log, Real.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh] <;> field_simp <;> ring)
    all_goals try (qsym_trig_goal; solve | simp_all [Elementary.sin_re, Elementary.sin_im, Elementary.cos_re, Elementary.cos_im,
      Elementary.sinh_re, Elementary.sinh_im, Elementary.cosh_re, Elementary.cosh_im])
    all_goals try (have h := Elementary.log_product_domain (by assumption) (by assumption); rcases h with ⟨_, _⟩)
    all_goals try (have h := Elementary.log_product_domain_right (by assumption) (by assumption); rcases h with ⟨_, _⟩)
    all_goals try (have h := Elementary.log_odd_domain _ (by assumption))
    all_goals try (simp_all [Int.floor_neg, Int.ceil_neg, Int.floor_add_intCast, Int.ceil_add_intCast,
      Int.floor_lt, Int.floor_le_iff, Int.lt_floor_iff, Int.le_floor,
      Int.ceil_lt_iff, Int.ceil_le, Int.lt_ceil, Int.le_ceil_iff,
      Elementary.floor_ne, Elementary.ceil_ne, Int.floor_le, Int.le_ceil,
      Elementary.not_lt_floor, Elementary.not_ceil_lt, Elementary.not_add_one_le_ceil,
      Elementary.log_odd_power, Elementary.log_positive_real, Elementary.log_scale,
      Elementary.log_scale_right, Complex.log_inv])
    all_goals try (simp_all [Identities.abs_even_power, Identities.log_even_power,
      Identities.log_even_domain, Identities.exp_log_scale, Identities.cexp_log_scale,
      Identities.exp_log_scale_right, Identities.cexp_log_scale_right, Real.exp_add, Complex.exp_add, Real.sqrt_mul,
      Real.mul_rpow, min_add_max, Identities.min_mul_max,
      Real.sin_le_one, Real.neg_one_le_sin, Real.cos_le_one, Real.neg_one_le_cos,
      Real.sin_two_mul, Complex.sin_two_mul, Real.tanh_neg, Complex.tanh_neg,
      Complex.cosh_sq_sub_sinh_sq, Complex.mul_conj', Complex.ofReal_pow,
      Identities.square_re, Identities.square_im, Complex.conj_ofReal])
    all_goals try (solve | simp only [← mul_eq_zero]; apply Identities.power_product_domain <;> assumption)
    all_goals try (simp_all [Elementary.sqrt_scale, Elementary.sqrt_real_nonnegative, Elementary.sqrt_real_negative])
    all_goals try (simp_all [Elementary.log_mul_pos, Elementary.root_power, Real.sqrt_sq_eq_abs,
      Real.rpow_add, Elementary.rpow_mul_pos, Elementary.rpow_half, ← Real.sqrt_eq_rpow,
      Real.sin_sub_int_mul_two_pi, Real.cos_sub_int_mul_two_pi, Elementary.sin_period, Elementary.cos_period,
      Elementary.sin_three_half_pi, Elementary.cos_three_half_pi, Elementary.exp_phase,
      Elementary.phase_period, Complex.exp_pi_div_two_mul_I,
      Complex.ofReal_add, add_mul, Complex.exp_add])
    all_goals try (qsym_inverse_symmetry_goal; solve | simp_all [Real.arcsin_neg, Real.arctan_neg, Real.arsinh_neg, Real.arccos_neg, Real.arccos_eq_pi_div_two_sub_arcsin] <;> ring)
    all_goals try (simp_all [pow_add, pow_mul, mul_pow, inv_pow, Real.rpow_natCast, Complex.cpow_natCast,
      Real.exp_log, Complex.exp_log, Real.log_exp, Real.sqrt_sq_eq_abs,
      Real.exp_add, Complex.exp_add, Real.exp_sub, Complex.exp_sub, Real.exp_neg, Complex.exp_neg,
      Real.exp_nat_mul, Complex.exp_nat_mul, Real.exp_one_rpow,
      Real.log_mul, Real.log_pow, Real.log_inv, Real.log_abs, Real.log_sqrt,
      Real.sin_sq_add_cos_sq, Complex.sin_sq_add_cos_sq,
      Real.cosh_sq_sub_sinh_sq, Real.tan_arctan, Real.sin_arcsin, Real.cos_arccos,
      Real.arcsin_sin, Real.arccos_cos, min_eq_left, min_eq_right, max_eq_left, max_eq_right,
      Complex.exp_conj, Complex.mul_re, Complex.mul_im, Complex.re_add_im, norm_mul])
    all_goals try (simp_all [Elementary.log_cpow_contract, Elementary.arg_cpow_contract,
      Elementary.log_sqrt, Elementary.arg_sqrt, Elementary.norm_cpow_real, Elementary.norm_sqrt,
      Elementary.arg_exp, Complex.log_exp, Complex.log_re, Complex.log_im, Complex.norm_exp,
      norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_pos_iff,
      Complex.cpow_ne_zero_iff, Complex.cpow_ofNat_inv_pow,
      Real.sinh_arsinh, Real.arsinh_sinh, Real.cos_arcsin, Real.sin_arccos,
      Complex.sin_conj, Complex.cos_conj, Complex.sinh_conj, Complex.cosh_conj])
    all_goals try (simp_all [Elementary.sin_imaginary, Elementary.cos_imaginary, Elementary.tan_imaginary,
      Elementary.sinh_imaginary, Elementary.cosh_imaginary, Elementary.tanh_imaginary])
    all_goals try (simp_all only [← Complex.ofReal_cos, Complex.ofReal_eq_zero])
    all_goals try (solve | simp_all only [Elementary.exp_real, ← Complex.ofReal_exp])
    all_goals try (simp_all [Elementary.real_exp_zpow, Elementary.sqrt_exp, Real.pi_pos,
      Elementary.exp_cpow, Elementary.real_exp_cpow, Elementary.sqrt_cexp,
      Elementary.phase_pow, Elementary.phase_zpow, Elementary.phase_inverse, Elementary.phase_conjugate,
      ← Real.exp_mul, ← Complex.exp_int_mul, Complex.ofReal_exp, Complex.ofReal_inv, Complex.ofReal_zpow,
      Complex.exp_re, Complex.exp_im])
    all_goals try (simp_all [abs_mul, abs_inv, abs_pow])
    all_goals try (simp_all [Int.floor_eq_iff, Int.ceil_eq_iff, Real.rpow_neg, Complex.cpow_neg,
      zpow_natCast, zpow_neg, Real.norm_eq_abs, Complex.norm_def, Complex.normSq_apply,
      Real.arcsin_zero, Real.arcsin_one, Real.arccos_zero, Real.arccos_one, Real.arccos_neg_one,
      Real.arctan_zero, Real.arctan_one, Real.arsinh_zero, Real.Gamma_one, Complex.Gamma_one,
      Real.log_exp, Complex.zero_cpow, Complex.one_cpow])
    all_goals try norm_num at *
    all_goals try field_simp
    all_goals try ring_nf at *
    all_goals try (qsym_trig_goal; simp_all [Elementary.sin_quarter_turn_normal, Elementary.cos_quarter_turn_normal,
      Elementary.phase_quarter_turn_normal, Elementary.tan_period_normal, Elementary.tan_period_domain_normal,
      Complex.tan_conj, Complex.tanh_conj])
    all_goals try simp_all [Complex.I_sq, Elementary.phase_half_pi, Elementary.phase_period_normal]
    all_goals try norm_num [Complex.I_pow_eq_pow_mod] at *
    all_goals try ring
    all_goals try (simp only [abs_eq_max_neg, min_def, max_def] at *; split_ifs at * <;> nlinarith)
    all_goals try ring
    all_goals try (simp only [← decide_not, decide_eq_decide] at *)
    all_goals try (simp_all [← div_eq_mul_inv, lt_div_iff₀, le_div_iff₀,
      div_lt_iff₀, div_le_iff₀, lt_div_iff_of_neg, le_div_iff_of_neg,
      div_lt_iff_of_neg, div_le_iff_of_neg, mul_comm])
    all_goals try (qsym_trig_goal; simp_all [Complex.sin_add_pi_div_two, Complex.cos_add_pi_div_two])
    all_goals try (simp only [pow_mul] at *; nlinarith)
    all_goals try (simp_all [neg_eq_iff_add_eq_zero, add_comm])
    all_goals try (solve | (apply Eq.symm; apply Real.arcsin_sin <;> linarith))
    all_goals try (simp_all [Elementary.sqrt_not_neg])
    all_goals try (solve | have h := Real.sqrt_pos.mpr (by assumption); linarith [h])
    all_goals try (apply Elementary.nonnegative_of_pos_or_zero; assumption)
    all_goals try (solve | (convert Elementary.phase_half_pi.symm using 2 <;> push_cast <;> ring))
    all_goals try (solve | apply Elementary.floor_exact <;> assumption)
    all_goals try (solve | apply Elementary.ceil_exact <;> assumption)
    all_goals try (solve | exact (Complex.sq_cpow_two_inv (by assumption)).symm)
    all_goals try (solve | apply Elementary.sqrt_imaginary; assumption)
    all_goals try (solve | apply Elementary.cartesian_ne_zero; assumption)
    all_goals try (solve | apply Elementary.gamma_real_next; assumption)
    all_goals try (solve | apply Elementary.gamma_complex_next; assumption)
    all_goals try (solve | exact (Elementary.complex_nat_succ_ne_neg _ _) (by assumption))
    all_goals try (solve | apply Elementary.indexed_negative <;> assumption)
    all_goals try (solve | apply Elementary.complex_negative <;> assumption)
    all_goals try (solve | apply lt_of_le_of_ne <;> assumption)
    all_goals try (simp [Real.log_rpow (by norm_num : (0 : ℝ)<2), Real.log_rpow (by norm_num : (0 : ℝ)<10)])
    all_goals try (solve | apply Eq.symm; apply Complex.arg_eq_zero_iff.mpr; constructor <;> first | assumption | linarith)
    all_goals try (solve | apply Eq.symm; apply Complex.arg_eq_pi_iff.mpr; constructor <;> assumption)
    all_goals try (solve | have h := Complex.arg_eq_pi_div_two_iff.mpr ⟨by assumption, by assumption⟩; linarith [h])
    all_goals try (solve | have h := Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨by assumption, by assumption⟩; linarith [h])
    all_goals try (solve | exact (Elementary.rpow_half _).symm)
    all_goals try (solve | apply Elementary.norm_power_domain; assumption)
    all_goals try (solve | apply Elementary.nonnegative_cases; assumption)
    all_goals try positivity
    all_goals try nlinarith
    all_goals try omega
    all_goals try (qsym_trig_goal; simp_all [Elementary.cos_quarter_turn_normal,
      Elementary.tan_period_normal, Elementary.tan_period_domain_normal])
    all_goals try (solve | have h := eq_neg_of_add_eq_zero_left (by assumption); subst_vars; ring)
    all_goals try (solve | exact Or.resolve_left (by assumption) (not_lt.mpr (by assumption)))
    all_goals try (solve | exact Or.resolve_left (by assumption) (not_le.mpr (by assumption)))
    all_goals try (solve | simp only [Elementary.abs_tanh, Elementary.abs_asinh, Elementary.abs_atan])
    all_goals try (constructor <;> intro h <;> nlinarith)
    all_goals try (qsym_new_trig_goal; solve | (simp_all [
      Trigonometry.real_sin_half_normal, Trigonometry.real_cos_half_normal,
      Trigonometry.complex_sin_half_normal, Trigonometry.complex_cos_half_normal,
      Trigonometry.complex_sin_period_normal, Trigonometry.complex_cos_period_normal,
      Trigonometry.tan_period_normal,
      Trigonometry.sinh_period_normal, Trigonometry.cosh_period_normal, Trigonometry.exp_period_normal,
      Trigonometry.sinh_half_normal, Trigonometry.cosh_half_normal, Trigonometry.exp_half_normal,
      Trigonometry.tanh_period_normal,
      Trigonometry.sinh_quarter_normal, Trigonometry.cosh_quarter_normal, Trigonometry.exp_quarter_normal,
      Trigonometry.exp_integer_half_normal, Trigonometry.exp_integer_period_normal, Trigonometry.exp_quarter_value, Trigonometry.complex_sin_quarter_normal, Trigonometry.complex_cos_quarter_normal, Trigonometry.integer_cos_normal, Trigonometry.integer_phase_normal,
      Trigonometry.sinh_quarter_add_normal, Trigonometry.cosh_quarter_add_normal,
      Trigonometry.parity_cancel_mul, Trigonometry.parity_square, zpow_ne_zero]
      <;> ring_nf <;> simp [Trigonometry.parity_square, Complex.I_sq]))
  )
))

macro "qsym_defined" : tactic => `(tactic| (
  classical
  try simp only [Value.add, Value.mul, Value.inv, Value.nonzero, Value.mask, Value.conj,
    Value.not, Value.and, Value.or, Value.lt, Value.le, Value.abs,
    Option.map, Option.bind]
  repeat' first
    | simp_all (config := {failIfUnchanged := true})
    | split at *
  all_goals try (simp only [← not_lt]; tauto)
))

macro "qsym_rule" : tactic => `(tactic| (
  first
  | solve
    | apply Value.refines_of_eq
      first
      | apply Value.spectral_interpolation
      | exact (Value.spectral_interpolation _ _ _ _ _).symm
      | apply Value.spectral_interpolationQ
      | exact (Value.spectral_interpolationQ _ _ _ _ _).symm
      | apply Value.affine_add
      | apply Value.affine_left
      | apply Value.affine_right
      | exact (Value.affine_add _ _ _ _ _).symm
      | exact (Value.affine_left _ _ _ _).symm
      | exact (Value.affine_right _ _ _ _).symm
  | solve | qsym_discrete
  | solve
    | apply Value.refines_of_eq
      simp only [Expr.eval, Int.cast_zero, Int.cast_one, zero_mul, add_zero,
        Value.add_zero_right, Value.add_zero_left, Value.mul_one_right, Value.mul_one_left,
        Value.mask_true, Value.mask_false, Value.conj_conj,
        Option.map_map, Function.comp_def, Density.forget_puncture]
  | try simp only [Expr.eval]
    qsym_scalar
))

end QSym
