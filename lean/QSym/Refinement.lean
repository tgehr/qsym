import QSym.Expr

namespace QSym.Value

def Refines {α : Type} (x y : Option α) : Prop := ∀ v, x = some v → y = some v

theorem refines_refl {α : Type} (x : Option α) : Refines x x := fun _ h => h
theorem refines_of_eq {α : Type} {x y : Option α} (h : x = y) : Refines x y := by
  subst y; exact refines_refl x
theorem Refines.trans {α : Type} {x y z : Option α}
    (h : Refines x y) (k : Refines y z) : Refines x z := fun v hv => k v (h v hv)
theorem Refines.antisymm {α : Type} {x y : Option α}
    (h : Refines x y) (k : Refines y x) : x = y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some v => have impossible := k v rfl; cases impossible
  | some v => exact (h v rfl).symm
theorem Refines.defined {α : Type} {x y : Option α}
    (h : Refines x y) (hx : Defined x) : Defined y := by
  obtain ⟨v, hv⟩ := hx
  exact ⟨v, h v hv⟩
theorem Refines.eq_of_defined {α : Type} {x y : Option α}
    (h : Refines x y) (hx : Defined x) : x = y := by
  obtain ⟨v, hv⟩ := hx
  exact hv.trans (h v hv).symm

theorem refines_bind {α β : Type} {x y : Option α} {f g : α → Option β}
    (h : Refines x y) (k : ∀ v, Refines (f v) (g v)) :
    Refines (x.bind f) (y.bind g) := by
  cases x with
  | none => intro v hv; cases hv
  | some a => rw [h a rfl]; exact k a

theorem refines_map {α β : Type} (f : α → β) {x y : Option α}
    (h : Refines x y) : Refines (x.map f) (y.map f) := by
  cases x with
  | none => intro v hv; cases hv
  | some a => rw [h a rfl]; exact refines_refl _

theorem refines_add {α : Type} [Add α] {a b x y : Option α}
    (h : Refines a x) (k : Refines b y) : Refines (add a b) (add x y) := by
  cases a with
  | none => intro v hv; cases hv
  | some a =>
    cases b with
    | none => intro v hv; cases hv
    | some b => rw [h a rfl, k b rfl]; exact refines_refl _

theorem refines_mul {α : Type} [Mul α] {a b x y : Option α}
    (h : Refines a x) (k : Refines b y) : Refines (mul a b) (mul x y) := by
  cases a with
  | none => intro v hv; cases hv
  | some a =>
    cases b with
    | none => intro v hv; cases hv
    | some b => rw [h a rfl, k b rfl]; exact refines_refl _

theorem refines_inv {α : Type} [Zero α] [Inv α] {a b : Option α}
    (h : Refines a b) : Refines (inv a) (inv b) :=
  refines_bind h (fun _ => refines_refl _)

theorem refines_inv_inv {α : Type} [DivisionRing α] (x : Option α) :
    Refines (inv (inv x)) x := by
  cases x with
  | none => simp [Refines, inv]
  | some x => by_cases h : x = 0 <;> simp [Refines, inv, h]

theorem refines_nonzero {α : Type} [Zero α] {a b : Option α}
    (h : Refines a b) : Refines (nonzero a) (nonzero b) :=
  refines_map _ h

theorem refines_conj {a b : Option ℂ} (h : Refines a b) : Refines (conj a) (conj b) :=
  refines_map _ h

theorem refines_not {p q : Option Bool} (h : Refines p q) : Refines (not p) (not q) :=
  refines_map _ h
theorem refines_and {p q x y : Option Bool} (h : Refines p x) (k : Refines q y) :
    Refines (and p q) (and x y) := by
  cases p with
  | none => intro v hv; cases hv
  | some p => rw [h p rfl]; cases p <;> first | exact refines_refl _ | exact k
theorem refines_or {p q x y : Option Bool} (h : Refines p x) (k : Refines q y) :
    Refines (or p q) (or x y) := by
  cases p with
  | none => intro v hv; cases hv
  | some p => rw [h p rfl]; cases p <;> first | exact refines_refl _ | exact k
theorem refines_lt {a b x y : Option ℝ} (h : Refines a x) (k : Refines b y) :
    Refines (lt a b) (lt x y) := refines_bind h (fun _ => refines_bind k (fun _ => refines_refl _))
theorem refines_le {a b x y : Option ℝ} (h : Refines a x) (k : Refines b y) :
    Refines (le a b) (le x y) := refines_bind h (fun _ => refines_bind k (fun _ => refines_refl _))

theorem refines_mask {α : Type} [Zero α] {p q : Option Bool} {a b : Option α}
    (h : Refines p q) (k : Refines a b) : Refines (mask p a) (mask q b) := by
  cases p with
  | none => intro v hv; cases hv
  | some p =>
    rw [h p rfl]
    cases p with
    | false => exact refines_refl _
    | true => exact k

theorem refines_densityAt {a b : Option Density} {x y : Option ℝ}
    (h : Refines a b) (k : Refines x y) : Refines (densityAt a x) (densityAt b y) :=
  refines_bind h (fun _ => refines_bind k (fun _ => refines_refl _))

end QSym.Value

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
    if decl.type.isConstOf ``Bool then
      return (← goal.cases decl.fvarId).toList.map (·.mvarId)
  throwError "no Boolean"

-- Search is untrusted: every successful tactic emits a kernel-checked proof.
macro "qsym_scalar" : tactic => `(tactic| (
  first
  | exact Value.refines_inv_inv _
  | (
    classical
    intro v hv
    try simp only [Value.Refines, Value.Defined] at *
    try simp only [Value.add, Value.mul, Value.inv, Value.nonzero, Value.mask, Value.conj,
      Value.not, Value.and, Value.or, Value.lt, Value.le, Value.abs,
      Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind] at *
    try simp only [Option.some.injEq, forall_eq, forall_eq', Bool.true_eq, decide_eq_true_eq] at *
    repeat' first
      | simp_all (config := {failIfUnchanged := true})
      | qsym_split_and
      | qsym_split_bool
      | split at *
    all_goals subst_vars
    all_goals try (simp_all [pow_add, pow_mul, mul_pow, inv_pow])
    all_goals try (simp_all [abs_mul, abs_inv, abs_pow])
    all_goals try norm_num at *
    all_goals try field_simp
    all_goals try ring_nf at *
    all_goals try simp_all [Complex.I_sq]
    all_goals try norm_num [Complex.I_pow_eq_pow_mod] at *
    all_goals try ring
    all_goals try (simp only [abs_eq_max_neg, max_def] at *; split_ifs at * <;> nlinarith)
    all_goals try ring
    all_goals try (simp only [← decide_not, decide_eq_decide] at *)
    all_goals try (simp_all [← div_eq_mul_inv, lt_div_iff₀, le_div_iff₀,
      div_lt_iff₀, div_le_iff₀, lt_div_iff_of_neg, le_div_iff_of_neg,
      div_lt_iff_of_neg, div_le_iff_of_neg, mul_comm])
    all_goals try (simp only [pow_mul] at *; nlinarith)
    all_goals try positivity
    all_goals try nlinarith
    all_goals try (constructor <;> intro h <;> nlinarith)
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
      simp only [Expr.eval, Int.cast_zero, Int.cast_one, zero_mul, add_zero,
        Value.add_zero_right, Value.add_zero_left, Value.mul_one_right, Value.mul_one_left,
        Value.mask_true, Value.mask_false, Value.conj_conj,
        Option.map_map, Function.comp_def, Density.forget_puncture]
  | try simp only [Expr.eval]
    qsym_scalar
))

end QSym
