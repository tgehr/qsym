import QSym.Generated

namespace QSym.Value

theorem refines_mask_under {α : Type} [Zero α] (p : Option Bool) (x y : Option α)
    (h : p = some true → Refines x y) : Refines (mask p x) (mask p y) := by
  cases p with
  | none => exact refines_refl _
  | some b => cases b with
    | false => exact refines_refl _
    | true => exact h rfl

theorem refines_and_under (p x y : Option Bool)
    (h : p = some true → Refines x y) : Refines (and p x) (and p y) := by
  cases p with
  | none => exact refines_refl _
  | some b => cases b with
    | false => exact refines_refl _
    | true => exact h rfl

theorem refines_or_under (p x y : Option Bool)
    (h : p = some false → Refines x y) : Refines (or p x) (or p y) := by
  cases p with
  | none => exact refines_refl _
  | some b => cases b with
    | false => exact h rfl
    | true => exact refines_refl _

theorem and_true_left {p q : Option Bool} (h : and p q = some true) : p = some true := by
  cases p with
  | none => simp [and] at h
  | some b => cases b <;> simp_all [and]
theorem and_true_right {p q : Option Bool} (h : and p q = some true) : q = some true := by
  cases p with
  | none => simp [and] at h
  | some b => cases b <;> simp_all [and]
theorem or_false_left {p q : Option Bool} (h : or p q = some false) : p = some false := by
  cases p with
  | none => simp [or] at h
  | some b => cases b <;> simp_all [or]
theorem or_false_right {p q : Option Bool} (h : or p q = some false) : q = some false := by
  cases p with
  | none => simp [or] at h
  | some b => cases b <;> simp_all [or]
theorem of_not {p : Option Bool} {b : Bool} (h : not p = some b) : p = some (!b) := by
  cases p with
  | none => simp [not] at h
  | some p => cases p <;> cases b <;> simp_all [not]
theorem not_eq {p : Option Bool} {b : Bool} (h : p = some b) : not p = some (!b) := by
  rw [h]; rfl

theorem defined_inv_arg {α : Type} [Zero α] [Inv α] (x : Option α)
    (h : Defined (inv x)) : Defined x := by
  obtain ⟨v, hv, _⟩ := (defined_inv x).mp h
  exact ⟨v, hv⟩
theorem defined_mask_guard {α : Type} [Zero α] (p : Option Bool) (x : Option α)
    (h : Defined (mask p x)) : Defined p := by
  rcases (defined_mask p x).mp h with h | ⟨h, _⟩
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩
theorem defined_and_guard (p q : Option Bool) (h : Defined (and p q)) : Defined p := by
  rcases (defined_and p q).mp h with h | ⟨h, _⟩
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩
theorem defined_or_guard (p q : Option Bool) (h : Defined (or p q)) : Defined p := by
  rcases (defined_or p q).mp h with h | ⟨h, _⟩
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩
end QSym.Value

namespace QSym.Replay

structure AC (α : Type) where
  op : α → α → α
  unit : α
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  comm : ∀ x y, op x y = op y x
  right_id : ∀ x, op x unit = x

inductive Tree where
  | leaf (index : Nat)
  | unit
  | node (left right : Tree)
  deriving DecidableEq

def Tree.leaves : Tree → List Nat
  | .leaf i => [i]
  | .unit => []
  | .node l r => l.leaves ++ r.leaves

def AC.eval {α : Type} (a : AC α) (ρ : Nat → α) : Tree → α
  | .leaf i => ρ i
  | .unit => a.unit
  | .node l r => a.op (a.eval ρ l) (a.eval ρ r)

def AC.fold {α : Type} (a : AC α) (ρ : Nat → α) : List Nat → α
  | [] => a.unit
  | i :: is => a.op (ρ i) (a.fold ρ is)

theorem AC.left_id {α : Type} (a : AC α) (x : α) : a.op a.unit x = x := by
  rw [a.comm, a.right_id]

theorem AC.fold_append {α : Type} (a : AC α) (ρ : Nat → α) (xs ys : List Nat) :
    a.fold ρ (xs ++ ys) = a.op (a.fold ρ xs) (a.fold ρ ys) := by
  induction xs with
  | nil => simp [fold, a.left_id]
  | cons x xs ih => simp [fold, ih, a.assoc]

theorem AC.eval_fold {α : Type} (a : AC α) (ρ : Nat → α) (t : Tree) :
    a.eval ρ t = a.fold ρ t.leaves := by
  induction t with
  | leaf i => simp [eval, Tree.leaves, fold, a.right_id]
  | unit => rfl
  | node l r hl hr => simp [eval, Tree.leaves, hl, hr, a.fold_append]

theorem AC.fold_perm {α : Type} (a : AC α) (ρ : Nat → α) {xs ys : List Nat}
    (h : xs.Perm ys) : a.fold ρ xs = a.fold ρ ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [fold, ih]
  | swap x y xs =>
    simp only [fold]
    rw [← a.assoc, ← a.assoc, a.comm (ρ x) (ρ y)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem AC.sound {α : Type} (a : AC α) (ρ : Nat → α) (x y : Tree)
    (h : x.leaves.Perm y.leaves) : a.eval ρ x = a.eval ρ y := by
  rw [a.eval_fold, a.eval_fold]
  exact a.fold_perm ρ h

noncomputable def addR : AC (Option ℝ) :=
  ⟨Value.add, some 0, Generated.r_real_add_assoc, Generated.r_real_add_comm,
    by simpa using Generated.r_real_add_unit⟩
noncomputable def mulR : AC (Option ℝ) :=
  ⟨Value.mul, some 1, Generated.r_real_mul_assoc, Generated.r_real_mul_comm,
    by simpa using Generated.r_real_mul_unit⟩
noncomputable def addC : AC (Option ℂ) :=
  ⟨Value.add, some 0, Generated.r_complex_add_assoc, Generated.r_complex_add_comm,
    by simpa using Generated.r_complex_add_unit⟩
noncomputable def mulC : AC (Option ℂ) :=
  ⟨Value.mul, some 1, Generated.r_complex_mul_assoc, Generated.r_complex_mul_comm,
    by simpa using Generated.r_complex_mul_unit⟩

end QSym.Replay
