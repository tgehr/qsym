import QSym.Binding
import QSym.AxiomCheck

namespace QSym.FunctionalTests
open Binding

abbrev R : Binding.Ty := .scalar .real
noncomputable def reciprocal : Binding.Expr [] (.arrow R R) :=
  .lam (.unary Value.inv (.var .here))
noncomputable def zero : Binding.Expr [] R := .scalar (.real 0)
noncomputable def one : Binding.Expr [] R := .scalar (.real 1)
noncomputable def badPredicate : Binding.Expr [] (.set R) :=
  .set (.scalar (.ltR (.invR (.real 0)) (.real 1)))

theorem function_value (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.defined reciprocal).eval ξ ρ = some true := rfl

theorem zero_outside (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.mem (.domain reciprocal) zero).eval ξ ρ = some false := by
  simp [reciprocal, zero, Binding.Expr.eval, QSym.Expr.eval, inputDomain, memberValue,
    Binding.Env.cons, Value.inv]

theorem one_inside (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.mem (.domain reciprocal) one).eval ξ ρ = some true := by
  simp [reciprocal, one, Binding.Expr.eval, QSym.Expr.eval, inputDomain, memberValue,
    Binding.Env.cons, Value.inv]

theorem invalid_predicate (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.mem badPredicate one).eval ξ ρ = some false := by
  simp [badPredicate, one, Binding.Expr.eval, QSym.Expr.eval, memberValue, Value.inv, Value.lt]

theorem false_restriction (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.guard (.scalar (.bool false)) one).eval ξ ρ = none := rfl

theorem membership_defined (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.defined (.mem badPredicate one)).eval ξ ρ = some true := by
  change some ((Binding.Expr.mem badPredicate one).eval ξ ρ).isSome = some true
  rw [invalid_predicate]
  rfl

#qsym_check_axioms Binding.Reduction.domainLam
#qsym_check_axioms Binding.Reduction.memberSet
#qsym_check_axioms Binding.Reduction.seqGuard
#qsym_check_axioms Binding.Reduction.definedLam
#qsym_check_axioms Binding.Reduction.definedSet
#qsym_check_axioms Binding.Reduction.definedDomain
#qsym_check_axioms Binding.Reduction.definedDefined
#qsym_check_axioms Binding.Reduction.definedHolds
#qsym_check_axioms Binding.Reduction.guardTrue
#qsym_check_axioms Binding.Reduction.definedGuardFalse
#qsym_check_axioms Binding.Reduction.scalarDomain
#qsym_check_axioms Binding.Reduction.scalarHolds
#qsym_check_axioms Binding.Reduction.scalarSimplify
#qsym_check_axioms Binding.preserveDomain
#qsym_check_axioms function_value
#qsym_check_axioms zero_outside
#qsym_check_axioms one_inside
#qsym_check_axioms invalid_predicate
#qsym_check_axioms false_restriction
#qsym_check_axioms membership_defined
end QSym.FunctionalTests
