import QSym

open QSym
attribute [local semireducible] Rat.add Rat.mul Rat.sub Rat.inv

-- Failure and unsupported syntax must not be mistaken for equal values.
example : Numeric.check (.invR (.real 0)) (.invR (.real 0)) = false := rfl
example : Numeric.check (.invC (.complex 0 0)) (.complex 0 0) = false := rfl
example : Numeric.check (.varR 0) (.varR 0) = false := rfl
example : Numeric.check (.varR 0) (.varR 1) = false := rfl
example : Numeric.check (.invR (.real 0)) (.varR 0) = false := rfl
example : Numeric.check (.invR (.real 0)) (.real 0) = false := rfl
example : Numeric.check (.addR (.real 1) (.real 1)) (.real 3) = false := rfl

example (ρ : Env) : Value.Refines (Expr.eval ρ (.invR (.real (-3))))
    (Expr.eval ρ (.ratR (-1/3))) := Numeric.sound ρ _ _ rfl
example (ρ : Env) : Value.Refines (Expr.eval ρ (.invC (.complex 2 (-1))))
    (Expr.eval ρ (.ratC (2/5) (1/5))) := Numeric.sound ρ _ _ rfl
example (ρ : Env) : Value.Refines (Expr.eval ρ (.mulC (.ratC (1/2) (-1/3)) (.ratC (2/3) (1/2))))
    (Expr.eval ρ (.ratC (1/2) (1/36))) := Numeric.sound ρ _ _ rfl
example (ρ : Env) : Value.Refines (Expr.eval ρ (.nonzeroC (.complex 0 0)))
    (Expr.eval ρ (.bool false)) := Numeric.sound ρ _ _ rfl
example (ρ : Env) : Value.Refines (Expr.eval ρ (.nonzeroC (.ratC 0 (1/7))))
    (Expr.eval ρ (.bool true)) := Numeric.sound ρ _ _ rfl
example (ρ : Env) : Value.Refines (Expr.eval ρ (.ltR (.ratR (-1/3)) (.ratR (-1/4))))
    (Expr.eval ρ (.bool true)) := Numeric.sound ρ _ _ rfl
example (ρ : Env) : Value.Refines (Expr.eval ρ (.leR (.ratR (1/3)) (.ratR (1/3))))
    (Expr.eval ρ (.bool true)) := Numeric.sound ρ _ _ rfl
