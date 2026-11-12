import QSym.Expr

namespace QSym.Binding

inductive Ty where
  | scalar : QSym.Ty → Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq

abbrev Ty.denote : Ty → Type
  | .scalar s => s.denote
  | .arrow a b => a.denote → Option b.denote

inductive Var : List Ty → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

abbrev Env (Γ : List Ty) := {a : Ty} → Var Γ a → Option a.denote

def Env.cons (x : Option a.denote) (ρ : Env Γ) : Env (a :: Γ)
  | _, .here => x
  | _, .there v => ρ v

inductive Expr : List Ty → Ty → Type where
  | var : Var Γ a → Expr Γ a
  | scalar : QSym.Expr s → Expr Γ (.scalar s)
  | unary : (Option a.denote → Option b.denote) → Expr Γ a → Expr Γ b
  | binary : (Option a.denote → Option b.denote → Option c.denote) →
      Expr Γ a → Expr Γ b → Expr Γ c
  | lam : Expr (a :: Γ) b → Expr Γ (.arrow a b)
  | app : Expr Γ (.arrow a b) → Expr Γ a → Expr Γ b
  | seq : Expr Γ a → Expr Γ b → Expr Γ b

noncomputable def Expr.eval (ξ : QSym.Env) (ρ : Env Γ) : Expr Γ a → Option a.denote
  | .var v => ρ v
  | .scalar term => term.eval ξ
  | .unary f x => f (x.eval ξ ρ)
  | .binary f x y => f (x.eval ξ ρ) (y.eval ξ ρ)
  | .lam b => some (fun x => b.eval ξ (ρ.cons (some x)))
  | .app f x => (f.eval ξ ρ).bind (fun g => (x.eval ξ ρ).bind g)
  | .seq x y => (x.eval ξ ρ).bind (fun _ => y.eval ξ ρ)

abbrev Renaming (Γ Δ : List Ty) := {a : Ty} → Var Γ a → Var Δ a

def Renaming.lift (r : Renaming Γ Δ) : Renaming (a :: Γ) (a :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def Expr.rename (r : Renaming Γ Δ) : Expr Γ a → Expr Δ a
  | .var v => .var (r v)
  | .scalar term => .scalar term
  | .unary f x => .unary f (x.rename r)
  | .binary f x y => .binary f (x.rename r) (y.rename r)
  | .lam b => .lam (b.rename r.lift)
  | .app f x => .app (f.rename r) (x.rename r)
  | .seq x y => .seq (x.rename r) (y.rename r)

theorem Expr.eval_rename (e : Expr Γ a) (r : Renaming Γ Δ) (ξ : QSym.Env) (ρ : Env Δ) :
    (e.rename r).eval ξ ρ = e.eval ξ (fun v => ρ (r v)) := by
  induction e generalizing Δ with
  | var v => rfl
  | scalar term => rfl
  | unary f x ih => simp only [rename, eval, ih]
  | binary f x y ihx ihy => simp only [rename, eval, ihx, ihy]
  | app f x ihf ihx => simp only [rename, eval, ihf, ihx]
  | seq x y ihx ihy => simp only [rename, eval, ihx, ihy]
  | lam b ih =>
    simp only [rename, eval]
    congr 1
    funext x
    rw [ih]
    congr 1
    funext s v
    cases v <;> rfl

abbrev Substitution (Γ Δ : List Ty) := {a : Ty} → Var Γ a → Expr Δ a

def Substitution.lift (σ : Substitution Γ Δ) : Substitution (a :: Γ) (a :: Δ)
  | _, .here => .var .here
  | _, .there v => (σ v).rename Var.there

def Expr.subst (σ : Substitution Γ Δ) : Expr Γ a → Expr Δ a
  | .var v => σ v
  | .scalar term => .scalar term
  | .unary f x => .unary f (x.subst σ)
  | .binary f x y => .binary f (x.subst σ) (y.subst σ)
  | .lam b => .lam (b.subst σ.lift)
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .seq x y => .seq (x.subst σ) (y.subst σ)

theorem Expr.eval_subst (e : Expr Γ a) (σ : Substitution Γ Δ) (ξ : QSym.Env) (ρ : Env Δ) :
    (e.subst σ).eval ξ ρ = e.eval ξ (fun v => (σ v).eval ξ ρ) := by
  induction e generalizing Δ with
  | var v => rfl
  | scalar term => rfl
  | unary f x ih => simp only [subst, eval, ih]
  | binary f x y ihx ihy => simp only [subst, eval, ihx, ihy]
  | app f x ihf ihx => simp only [subst, eval, ihf, ihx]
  | seq x y ihx ihy => simp only [subst, eval, ihx, ihy]
  | lam b ih =>
    simp only [subst, eval]
    congr 1
    funext x
    rw [ih]
    congr 1
    funext s v
    cases v with
    | here => rfl
    | there v => exact eval_rename (σ v) Var.there ξ (ρ.cons (some x))

def Substitution.single (x : Expr Γ a) : Substitution (a :: Γ) Γ
  | _, .here => x
  | _, .there v => .var v

def Expr.beta (b : Expr (a :: Γ) c) (x : Expr Γ a) : Expr Γ c :=
  .seq x (b.subst (Substitution.single x))

theorem Expr.eval_beta (b : Expr (a :: Γ) c) (x : Expr Γ a) (ξ : QSym.Env) (ρ : Env Γ) :
    (Expr.app (.lam b) x).eval ξ ρ = (b.beta x).eval ξ ρ := by
  change (x.eval ξ ρ).bind (fun v => b.eval ξ (ρ.cons (some v))) =
    (x.eval ξ ρ).bind (fun _ => (b.subst (Substitution.single x)).eval ξ ρ)
  rw [eval_subst]
  cases h : x.eval ξ ρ with
  | none => rfl
  | some v =>
    change b.eval ξ (ρ.cons (some v)) = b.eval ξ (fun w => (Substitution.single x w).eval ξ ρ)
    apply congrArg (fun (env : Env (a :: Γ)) => b.eval ξ env)
    funext s w
    cases w <;> simp [Env.cons, Substitution.single, eval, h]

inductive Reduction : {Γ : List Ty} → {a : Ty} → Expr Γ a → Expr Γ a → Prop where
  | refl (e : Expr Γ a) : Reduction e e
  | trans {x y z : Expr Γ a} : Reduction x y → Reduction y z → Reduction x z
  | beta (b : Expr (a :: Γ) c) (x : Expr Γ a) : Reduction (.app (.lam b) x) (b.beta x)
  | unary {a b : Ty} {x y : Expr Γ a} (f : Option a.denote → Option b.denote) : Reduction x y →
      Reduction (.unary f x) (.unary f y)
  | binary {a b c : Ty} {x x' : Expr Γ a} {y y' : Expr Γ b}
      (f : Option a.denote → Option b.denote → Option c.denote) :
      Reduction x x' → Reduction y y' → Reduction (.binary f x y) (.binary f x' y')
  | lam {b b' : Expr (a :: Γ) c} : Reduction b b' → Reduction (.lam b) (.lam b')
  | app {f f' : Expr Γ (.arrow a b)} {x x' : Expr Γ a} :
      Reduction f f' → Reduction x x' → Reduction (.app f x) (.app f' x')
  | seq {x x' : Expr Γ a} {y y' : Expr Γ b} :
      Reduction x x' → Reduction y y' → Reduction (.seq x y) (.seq x' y')
  | seqScalar (term : QSym.Expr s) (y : Expr Γ a)
      (h : ∀ ξ, Value.Defined (term.eval ξ)) : Reduction (.seq (.scalar term) y) y
  | seqLam (b : Expr (a :: Γ) c) (y : Expr Γ d) : Reduction (.seq (.lam b) y) y
  | seqSelf (x : Expr Γ a) : Reduction (.seq x x) x

theorem Reduction.sound {x y : Expr Γ a} (h : Reduction x y) (ξ : QSym.Env) (ρ : Env Γ) :
    x.eval ξ ρ = y.eval ξ ρ := by
  induction h with
  | refl => rfl
  | trans _ _ ih₁ ih₂ => exact (ih₁ ρ).trans (ih₂ ρ)
  | beta b x => exact Expr.eval_beta b x ξ ρ
  | unary f _ ih => exact congrArg f (ih ρ)
  | binary f _ _ ihx ihy => exact congrArg₂ f (ihx ρ) (ihy ρ)
  | lam _ ih => exact congrArg some (funext (fun x => ih (ρ.cons (some x))))
  | app _ _ ihf ihx => simp only [Expr.eval, ihf ρ, ihx ρ]
  | seq _ _ ihx ihy => simp only [Expr.eval, ihx ρ, ihy ρ]
  | seqScalar term y h =>
    obtain ⟨v, hv⟩ := h ξ
    simp only [Expr.eval, hv]
    rfl
  | seqLam => rfl
  | seqSelf x => cases h : x.eval ξ ρ <;> simp [Expr.eval, h]

theorem Reduction.defined {x y : Expr Γ a} (h : Reduction x y) (ξ : QSym.Env) (ρ : Env Γ) :
    Value.Defined (x.eval ξ ρ) ↔ Value.Defined (y.eval ξ ρ) :=
  (h.sound ξ ρ) ▸ Iff.rfl

theorem Expr.defined_lam (b : Expr (a :: Γ) c) (ξ : QSym.Env) (ρ : Env Γ) :
    Value.Defined ((Expr.lam b).eval ξ ρ) := ⟨_, rfl⟩

theorem Expr.defined_app (f : Expr Γ (.arrow a b)) (x : Expr Γ a) (ξ : QSym.Env) (ρ : Env Γ) :
    Value.Defined ((Expr.app f x).eval ξ ρ) ↔
      ∃ g v, f.eval ξ ρ = some g ∧ x.eval ξ ρ = some v ∧ Value.Defined (g v) := by
  cases hf : f.eval ξ ρ <;> cases hx : x.eval ξ ρ <;>
    simp [eval, hf, hx, Value.Defined]

end QSym.Binding
