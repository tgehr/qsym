import QSym.Binding

/-! The body of a function with its variable opened.

A function evaluates its body at arguments that exist only, while the
environment of a term lets every variable be missing. So a step that needs
the variable of a function to exist cannot be a reduction of the body, but
it can be one of the body with the variable taken for a scalar variable: a
term in the context around the function, where a scalar variable always has
a value. Evaluated with that scalar variable set to an argument, the term is
the body at that argument. -/
namespace QSym.Binding

/-- A reduction of the opened body is a reduction of the function, where the
two bodies are the two opened terms with the scalar variable set to the
argument, at every argument. -/
theorem Reduction.lamOpened {Γ : List Ty} {a c : Ty} {x y : Expr (a :: Γ) c} {X Y : Expr Γ c}
    (env : QSym.Env → a.denote → QSym.Env) (h : Reduction X Y)
    (hx : ∀ ξ (ρ : Env Γ) v, x.eval ξ (ρ.cons (some v)) = X.eval (env ξ v) ρ)
    (hy : ∀ ξ (ρ : Env Γ) v, Y.eval (env ξ v) ρ = y.eval ξ (ρ.cons (some v))) :
    Reduction (.lam x) (.lam y) :=
  .lamPointwise (fun ξ ρ v => (hx ξ ρ v).trans ((h.sound (env ξ v) ρ).trans (hy ξ ρ v)))

end QSym.Binding
