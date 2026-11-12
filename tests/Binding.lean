import QSym.Binding
import QSym.AxiomCheck

namespace QSym.BindingTests
open Binding

abbrev N : Binding.Ty := .scalar .natural
abbrev R : Binding.Ty := .scalar .real

noncomputable def plus : Binding.Expr [] (.arrow N (.arrow N N)) :=
  .lam (.lam (.binary Functions.addN.apply (.var (.there .here)) (.var .here)))

theorem curried (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.app (.app plus (.scalar (.nat 1))) (.scalar (.nat 2))).eval ξ ρ = some 3 := by
  simp [plus, Binding.Expr.eval, QSym.Expr.eval, Binding.Env.cons, Functions.addN, Function2.apply]

theorem shadow (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.app (.app (.lam (.lam (.var .here)) : Binding.Expr [] (.arrow N (.arrow N N)))
      (.scalar (.nat 1))) (.scalar (.nat 2))).eval ξ ρ = some 2 := rfl

theorem capture (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.app (.app (.lam (.lam (.var (.there .here))) : Binding.Expr [] (.arrow N (.arrow N N)))
      (.scalar (.nat 1))) (.scalar (.nat 2))).eval ξ ρ = some 1 := rfl

noncomputable def bottom : Binding.Expr [] R := .scalar (.invR (.real 0))
noncomputable def constant : Binding.Expr [] (.arrow R R) := .lam (.scalar (.real 0))

theorem strict_unused (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.app constant bottom).eval ξ ρ = none := by
  simp [constant, bottom, Binding.Expr.eval, QSym.Expr.eval, Value.inv]

theorem lambda_defined (ξ : QSym.Env) (ρ : Binding.Env []) :
    Value.Defined ((Binding.Expr.lam (.scalar (.invR (.real 0))) : Binding.Expr [] (.arrow R R)).eval ξ ρ) :=
  Binding.Expr.defined_lam _ ξ ρ

theorem masked_argument (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.app constant (.scalar (.maskR (.bool false) (.invR (.real 0))))).eval ξ ρ = some 0 := by
  simp [constant, Binding.Expr.eval, QSym.Expr.eval, Value.mask]

theorem masked_body (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.app
      (.lam (.binary Value.mask (.scalar (.bool false)) (.var .here)) : Binding.Expr [] (.arrow R R))
      bottom).eval ξ ρ = none := by
  simp [bottom, Binding.Expr.eval, QSym.Expr.eval, Value.inv]

theorem body_domain (ξ : QSym.Env) (ρ : Binding.Env []) :
    (Binding.Expr.app (.lam (.scalar (.invR (.real 0))) : Binding.Expr [] (.arrow R R))
      (.scalar (.real 1))).eval ξ ρ = none := by
  simp [Binding.Expr.eval, QSym.Expr.eval, Value.inv]

#qsym_check_axioms Binding.Expr.eval_rename
#qsym_check_axioms Binding.Expr.eval_subst
#qsym_check_axioms Binding.Expr.eval_beta
#qsym_check_axioms Binding.Reduction.sound
#qsym_check_axioms Binding.Reduction.defined
#qsym_check_axioms Binding.Expr.defined_app
#qsym_check_axioms curried
#qsym_check_axioms shadow
#qsym_check_axioms capture
#qsym_check_axioms strict_unused
#qsym_check_axioms lambda_defined
#qsym_check_axioms masked_argument
#qsym_check_axioms masked_body
#qsym_check_axioms body_domain
end QSym.BindingTests
