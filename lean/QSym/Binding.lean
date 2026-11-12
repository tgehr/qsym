import QSym.Expr
import QSym.Domain

namespace QSym.Binding

inductive Ty where
  | scalar : QSym.Ty → Ty
  | arrow : Ty → Ty → Ty
  | set : Ty → Ty
  deriving DecidableEq

abbrev Ty.denote : Ty → Type
  | .scalar s => s.denote
  | .arrow a b => a.denote → Option b.denote
  | .set a => Set a.denote

abbrev Globals := (a : Ty) → Nat → a.denote

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
  | constant : Option a.denote → Expr Γ a
  | unary : (Option a.denote → Option b.denote) → Expr Γ a → Expr Γ b
  | binary : (Option a.denote → Option b.denote → Option c.denote) →
      Expr Γ a → Expr Γ b → Expr Γ c
  | lam : Expr (a :: Γ) b → Expr Γ (.arrow a b)
  | set : Expr (a :: Γ) (.scalar .bool) → Expr Γ (.set a)
  | app : Expr Γ (.arrow a b) → Expr Γ a → Expr Γ b
  | seq : Expr Γ a → Expr Γ b → Expr Γ b

noncomputable def Expr.eval (ξ : QSym.Env) (ρ : Env Γ) : Expr Γ a → Option a.denote
  | .var v => ρ v
  | .scalar term => term.eval ξ
  | .constant v => v
  | .unary f x => f (x.eval ξ ρ)
  | .binary f x y => f (x.eval ξ ρ) (y.eval ξ ρ)
  | .lam b => some (fun x => b.eval ξ (ρ.cons (some x)))
  | .set p => some {x | p.eval ξ (ρ.cons (some x)) = some true}
  | .app f x => (f.eval ξ ρ).bind (fun g => (x.eval ξ ρ).bind g)
  | .seq x y => (x.eval ξ ρ).bind (fun _ => y.eval ξ ρ)

def definedValue {α : Type} (x : Option α) : Option Bool := some x.isSome

def holdsValue (p : Option Bool) : Option Bool := some (p == some true)

noncomputable def inputDomain {α β : Type} (f : Option (α → Option β)) : Option (Set α) :=
  some {x | (f.bind (fun g => g x)).isSome}

noncomputable def memberValue {α : Type} (s : Option (Set α)) (x : Option α) : Option Bool := by
  classical
  exact s.bind (fun p => x.map (fun v => decide (v ∈ p)))

noncomputable def subsetValue {α : Type} (s t : Option (Set α)) : Option Bool := by
  classical
  exact s.bind (fun a => t.map (fun b => decide (a ⊆ b)))

def guardValue {α : Type} (p : Option Bool) (x : Option α) : Option α :=
  if p == some true then x else none

abbrev Expr.defined (x : Expr Γ a) : Expr Γ (.scalar .bool) := .unary definedValue x
abbrev Expr.holds (p : Expr Γ (.scalar .bool)) : Expr Γ (.scalar .bool) := .unary holdsValue p
noncomputable abbrev Expr.domain (f : Expr Γ (.arrow a b)) : Expr Γ (.set a) := .unary inputDomain f
noncomputable abbrev Expr.mem (s : Expr Γ (.set a)) (x : Expr Γ a) : Expr Γ (.scalar .bool) :=
  .binary memberValue s x
noncomputable abbrev Expr.subset (s t : Expr Γ (.set a)) : Expr Γ (.scalar .bool) :=
  .binary subsetValue s t
abbrev Expr.guard (p : Expr Γ (.scalar .bool)) (x : Expr Γ a) : Expr Γ a :=
  .binary guardValue p x

abbrev Renaming (Γ Δ : List Ty) := {a : Ty} → Var Γ a → Var Δ a

def Renaming.lift (r : Renaming Γ Δ) : Renaming (a :: Γ) (a :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def Expr.rename (r : Renaming Γ Δ) : Expr Γ a → Expr Δ a
  | .var v => .var (r v)
  | .scalar term => .scalar term
  | .constant v => .constant v
  | .unary f x => .unary f (x.rename r)
  | .binary f x y => .binary f (x.rename r) (y.rename r)
  | .lam b => .lam (b.rename r.lift)
  | .set p => .set (p.rename r.lift)
  | .app f x => .app (f.rename r) (x.rename r)
  | .seq x y => .seq (x.rename r) (y.rename r)

theorem Expr.eval_rename (e : Expr Γ a) (r : Renaming Γ Δ) (ξ : QSym.Env) (ρ : Env Δ) :
    (e.rename r).eval ξ ρ = e.eval ξ (fun v => ρ (r v)) := by
  induction e generalizing Δ with
  | var v => rfl
  | scalar term => rfl
  | constant v => rfl
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

  | set b ih =>
    simp only [rename, eval]
    congr 1
    funext x
    dsimp only [setOf]
    rw [ih]
    congr 2
    funext s v
    cases v <;> rfl

abbrev Substitution (Γ Δ : List Ty) := {a : Ty} → Var Γ a → Expr Δ a

def Substitution.lift (σ : Substitution Γ Δ) : Substitution (a :: Γ) (a :: Δ)
  | _, .here => .var .here
  | _, .there v => (σ v).rename Var.there

def Expr.subst (σ : Substitution Γ Δ) : Expr Γ a → Expr Δ a
  | .var v => σ v
  | .scalar term => .scalar term
  | .constant v => .constant v
  | .unary f x => .unary f (x.subst σ)
  | .binary f x y => .binary f (x.subst σ) (y.subst σ)
  | .lam b => .lam (b.subst σ.lift)
  | .set p => .set (p.subst σ.lift)
  | .app f x => .app (f.subst σ) (x.subst σ)
  | .seq x y => .seq (x.subst σ) (y.subst σ)

theorem Expr.eval_subst (e : Expr Γ a) (σ : Substitution Γ Δ) (ξ : QSym.Env) (ρ : Env Δ) :
    (e.subst σ).eval ξ ρ = e.eval ξ (fun v => (σ v).eval ξ ρ) := by
  induction e generalizing Δ with
  | var v => rfl
  | scalar term => rfl
  | constant v => rfl
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

  | set b ih =>
    simp only [subst, eval]
    congr 1
    funext x
    dsimp only [setOf]
    rw [ih]
    congr 2
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
  | ofEq {x y : Expr Γ a} : (∀ ξ ρ, x.eval ξ ρ = y.eval ξ ρ) → Reduction x y
  | trans {x y z : Expr Γ a} : Reduction x y → Reduction y z → Reduction x z
  | beta (b : Expr (a :: Γ) c) (x : Expr Γ a) : Reduction (.app (.lam b) x) (b.beta x)
  | unary {a b : Ty} {x y : Expr Γ a} (f : Option a.denote → Option b.denote) : Reduction x y →
      Reduction (.unary f x) (.unary f y)
  | binary {a b c : Ty} {x x' : Expr Γ a} {y y' : Expr Γ b}
      (f : Option a.denote → Option b.denote → Option c.denote) :
      Reduction x x' → Reduction y y' → Reduction (.binary f x y) (.binary f x' y')
  | lam {b b' : Expr (a :: Γ) c} : Reduction b b' → Reduction (.lam b) (.lam b')
  | set {p p' : Expr (a :: Γ) (.scalar .bool)} : Reduction p p' → Reduction (.set p) (.set p')
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
  | ofEq h => exact h ξ ρ
  | trans _ _ ih₁ ih₂ => exact (ih₁ ρ).trans (ih₂ ρ)
  | beta b x => exact Expr.eval_beta b x ξ ρ
  | unary f _ ih => exact congrArg f (ih ρ)
  | binary f _ _ ihx ihy => exact congrArg₂ f (ihx ρ) (ihy ρ)
  | lam _ ih => exact congrArg some (funext (fun x => ih (ρ.cons (some x))))
  | set _ ih =>
    simp only [Expr.eval]
    congr 1
    funext x
    dsimp only [setOf]
    rw [ih]
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

theorem Reduction.domainLam (b : Expr (a :: Γ) c) :
    Reduction (.domain (.lam b)) (.set (.defined b)) := .ofEq (by
  intro ξ ρ
  simp only [Expr.eval, inputDomain, definedValue, Option.bind_some]
  congr 1
  ext x
  simp)

theorem Reduction.memberSet (p : Expr (a :: Γ) (.scalar .bool)) (x : Expr Γ a) :
    Reduction (.mem (.set p) x) (.seq x (.holds (p.subst (Substitution.single x)))) := .ofEq (by
  classical
  intro ξ ρ
  simp only [Expr.eval, memberValue, Option.bind_some, Expr.eval_subst]
  cases hx : x.eval ξ ρ with
  | none => rfl
  | some v =>
    have he : (fun {s} (w : Var (a :: Γ) s) => (Substitution.single x w).eval ξ ρ) =
        (fun {s} w => (ρ.cons (some v)) w) := by
      funext s w
      cases w <;> simp [Substitution.single, Expr.eval, Env.cons, hx]
    rw [he]
    simp only [holdsValue, Option.map_some, Option.bind_some, Option.some.injEq]
    simp only [Option.bind, Option.map]
    cases hp : p.eval ξ (ρ.cons (some v)) with
    | none => simp [hp]
    | some b => cases b <;> simp [hp])

theorem Reduction.seqGuard (x : Expr Γ a) (y : Expr Γ b) :
    Reduction (.seq x y) (.guard (.defined x) y) := .ofEq (by
  intro ξ ρ
  cases h : x.eval ξ ρ <;> simp [Expr.eval, definedValue, guardValue, h])

theorem Reduction.definedLam (b : Expr (a :: Γ) c) :
    Reduction (.defined (.lam b)) (.scalar (.bool true)) := .ofEq (fun _ _ => rfl)

theorem Reduction.definedSet (p : Expr (a :: Γ) (.scalar .bool)) :
    Reduction (.defined (.set p)) (.scalar (.bool true)) := .ofEq (fun _ _ => rfl)

theorem Reduction.definedDomain (f : Expr Γ (.arrow a b)) :
    Reduction (.defined (.domain f)) (.scalar (.bool true)) := .ofEq (fun _ _ => rfl)

theorem Reduction.definedDefined (x : Expr Γ a) :
    Reduction (.defined (.defined x)) (.scalar (.bool true)) := .ofEq (fun _ _ => rfl)

theorem Reduction.definedHolds (x : Expr Γ (.scalar .bool)) :
    Reduction (.defined (.holds x)) (.scalar (.bool true)) := .ofEq (fun _ _ => rfl)

theorem Reduction.guardTrue (x : Expr Γ a) :
    Reduction (.guard (.scalar (.bool true)) x) x := .ofEq (fun _ _ => rfl)

theorem Reduction.definedGuardFalse (x : Expr Γ a) :
    Reduction (.defined (.guard (.scalar (.bool false)) x)) (.scalar (.bool false)) :=
  .ofEq (fun _ _ => rfl)

theorem Reduction.scalarDomain (x : QSym.Expr s) (d : QSym.Expr .bool)
    (h : ∀ ξ, Domain.Correct (x.eval ξ) (d.eval ξ)) :
    Reduction (Γ := Γ) (.defined (.scalar x)) (.scalar d) := .ofEq (fun ξ _ => (h ξ).symm)

theorem Reduction.scalarHolds (x d : QSym.Expr .bool)
    (h : ∀ ξ, Domain.Correct (x.eval ξ) (d.eval ξ)) :
    Reduction (Γ := Γ) (.holds (.scalar x)) (.scalar (.and d x)) := .ofEq (by
  intro ξ ρ
  change holdsValue (x.eval ξ) = Value.and (d.eval ξ) (x.eval ξ)
  rw [h ξ]
  cases hx : x.eval ξ with
  | none => rfl
  | some v => cases v <;> rfl)

theorem holdsDomain (x d : Option Bool) (h : Domain.Correct x d) :
    holdsValue x = Value.and d x := by
  rw [h]
  cases x with
  | none => rfl
  | some v => cases v <;> rfl

theorem preserveDomain {α : Type} (x y : Option α) (d : Option Bool)
    (hd : Domain.Correct x d) (h : Value.Refines x y) : x = guardValue d y := by
  rw [hd]
  cases hx : x with
  | none => rfl
  | some v => simpa [hx, guardValue] using h.eq_of_defined ⟨v, hx⟩

theorem Reduction.scalarSimplify (x : QSym.Expr s) (d : QSym.Expr .bool) (y : QSym.Expr s)
    (hd : ∀ ξ, Domain.Correct (x.eval ξ) (d.eval ξ))
    (h : ∀ ξ, Value.Refines (x.eval ξ) (y.eval ξ)) :
    Reduction (Γ := Γ) (.scalar x) (.guard (.scalar d) (.scalar y)) :=
  .ofEq (fun ξ _ => preserveDomain _ _ _ (hd ξ) (h ξ))

theorem Reduction.subsetRefl (s : Expr Γ (.set a)) :
    Reduction (.subset s s) (.seq s (.scalar (.bool true))) := .ofEq (by
  intro ξ ρ
  cases hs : s.eval ξ ρ <;> simp [Expr.eval, QSym.Expr.eval, subsetValue, hs])

theorem Reduction.subsetEmpty (s : Expr Γ (.set a)) :
    Reduction (.subset (.set (.scalar (.bool false))) s) (.seq s (.scalar (.bool true))) := .ofEq (by
  intro ξ ρ
  cases hs : s.eval ξ ρ <;> simp [Expr.eval, QSym.Expr.eval, subsetValue, hs, Set.subset_def])

theorem Reduction.subsetUniv (s : Expr Γ (.set a)) :
    Reduction (.subset s (.set (.scalar (.bool true)))) (.seq s (.scalar (.bool true))) := .ofEq (by
  intro ξ ρ
  cases hs : s.eval ξ ρ <;> simp [Expr.eval, QSym.Expr.eval, subsetValue, hs, Set.subset_def])

theorem Reduction.subsetUnivEmpty {a : Ty} (w : a.denote) :
    Reduction (Γ := Γ) (.subset (a := a) (.set (.scalar (.bool true))) (.set (.scalar (.bool false))))
      (.scalar (.bool false)) := .ofEq (by
  intro ξ ρ
  letI : Nonempty a.denote := ⟨w⟩
  simp [Expr.eval, QSym.Expr.eval, subsetValue, Set.subset_def])

theorem Reduction.definedMember (s : Expr Γ (.set a)) (x : Expr Γ a) :
    Reduction (.defined (.mem s x)) (.binary Value.and (.defined s) (.defined x)) := .ofEq (by
  intro ξ ρ
  cases hs : s.eval ξ ρ <;> cases hx : x.eval ξ ρ <;>
    simp [Expr.eval, memberValue, definedValue, Value.and, hs, hx])

theorem Reduction.definedSubset (s t : Expr Γ (.set a)) :
    Reduction (.defined (.subset s t)) (.binary Value.and (.defined s) (.defined t)) := .ofEq (by
  intro ξ ρ
  cases hs : s.eval ξ ρ <;> cases ht : t.eval ξ ρ <;>
    simp [Expr.eval, subsetValue, definedValue, Value.and, hs, ht])

theorem Reduction.definedGuard (p : Expr Γ (.scalar .bool)) (x : Expr Γ a) :
    Reduction (.defined (.guard p x)) (.binary Value.and (.holds p) (.defined x)) := .ofEq (by
  intro ξ ρ
  cases hp : p.eval ξ ρ with
  | none => simp [Expr.eval, guardValue, holdsValue, definedValue, Value.and, hp]
  | some b => cases b <;> simp [Expr.eval, guardValue, holdsValue, definedValue, Value.and, hp])

theorem Reduction.definedApp (f : Expr Γ (.arrow a b)) (x : Expr Γ a) :
    Reduction (.defined (.app f x)) (.holds (.mem (.domain f) x)) := .ofEq (by
  intro ξ ρ
  cases hf : f.eval ξ ρ with
  | none => cases hx : x.eval ξ ρ <;>
      simp [Expr.eval, holdsValue, inputDomain, memberValue, definedValue, hf, hx]
  | some g => cases hx : x.eval ξ ρ with
    | none => simp [Expr.eval, holdsValue, inputDomain, memberValue, definedValue, hf, hx]
    | some v => cases hv : g v <;>
        simp [Expr.eval, holdsValue, inputDomain, memberValue, definedValue, hf, hx, hv])

theorem Reduction.domainGuardFalse (f : Expr Γ (.arrow a b)) :
    Reduction (.domain (.guard (.scalar (.bool false)) f)) (.set (.scalar (.bool false))) := .ofEq (by
  intro ξ ρ
  simp [Expr.eval, QSym.Expr.eval, guardValue, inputDomain])

theorem Reduction.definedNot (p : Expr Γ (.scalar .bool)) :
    Reduction (.defined (.unary (b := .scalar .bool) Value.not p)) (.defined p) := .ofEq (by
  intro ξ ρ
  cases hp : p.eval ξ ρ <;> simp [Expr.eval, Value.not, definedValue, hp])

theorem Reduction.lamPointwise {x y : Expr (a :: Γ) b}
    (h : ∀ (ξ : QSym.Env) (ρ : Env Γ) v, x.eval ξ (ρ.cons (some v)) = y.eval ξ (ρ.cons (some v))) :
    Reduction (.lam x) (.lam y) := .ofEq (by
  intro ξ ρ
  exact congrArg some (funext (h ξ ρ)))

theorem Reduction.setPointwise {x y : Expr (a :: Γ) (.scalar .bool)}
    (h : ∀ (ξ : QSym.Env) (ρ : Env Γ) v, x.eval ξ (ρ.cons (some v)) = y.eval ξ (ρ.cons (some v))) :
    Reduction (.set x) (.set y) := .ofEq (by
  intro ξ ρ
  simp only [Expr.eval]
  congr 1
  ext v
  change x.eval ξ (ρ.cons (some v)) = some true ↔ y.eval ξ (ρ.cons (some v)) = some true
  rw [h ξ ρ v])

theorem Reduction.guardAnd (p q : Expr Γ (.scalar .bool)) (x : Expr Γ a) :
    Reduction (.guard p (.guard q x)) (.guard (.binary Value.and p q) x) := .ofEq (by
  intro ξ ρ
  cases hp : p.eval ξ ρ with
  | none => simp [Expr.eval, guardValue, Value.and, hp]
  | some v => cases v <;> simp [Expr.eval, guardValue, Value.and, hp])

theorem Reduction.holdsGuard (p q : Expr Γ (.scalar .bool)) :
    Reduction (.holds (.guard p q)) (.binary Value.and (.holds p) (.holds q)) := .ofEq (by
  intro ξ ρ
  cases hp : p.eval ξ ρ with
  | none => simp [Expr.eval, guardValue, holdsValue, Value.and, hp]
  | some v => cases v <;> simp [Expr.eval, guardValue, holdsValue, Value.and, hp])

theorem Reduction.setHolds (p : Expr (a :: Γ) (.scalar .bool)) :
    Reduction (.set p) (.set (.holds p)) := .ofEq (by
  intro ξ ρ
  apply congrArg some
  ext v
  change p.eval ξ (ρ.cons (some v)) = some true ↔ holdsValue (p.eval ξ (ρ.cons (some v))) = some true
  simp [holdsValue])

end QSym.Binding
