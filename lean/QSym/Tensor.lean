import QSym.Binding

namespace QSym.Tensor

theorem apply_some {α β : Type} (f : Function1 α β) (x : α) (h : f.domain x) :
    f.apply (some x) = some (f.value x) := by simp [Function1.apply, h]

def pairValue {α β : Type} (x : Option α) (y : Option β) : Option (α × β) :=
  x.bind (fun a => y.map (fun b => (a,b)))

def nilValue {α : Type} : Option (Fin 0 → α) := some Fin.elim0

def consValue {α : Type} {n : ℕ} (x : Option α) (xs : Option (Fin n → α)) : Option (Fin (n+1) → α) :=
  x.bind (fun a => xs.map (fun as => Fin.cases a as))

theorem guard_pair_left {α β : Type} (p : Option Bool) (x : Option α) (y : Option β) :
    pairValue (Binding.guardValue p x) y = Binding.guardValue p (pairValue x y) := by
  cases p with
  | none => rfl
  | some p => cases p <;> rfl

theorem guard_pair_right {α β : Type} (p : Option Bool) (x : Option α) (y : Option β) :
    pairValue x (Binding.guardValue p y) = Binding.guardValue p (pairValue x y) := by
  cases p with
  | none => cases x <;> rfl
  | some p => cases p <;> cases x <;> rfl

theorem guard_cons_left {α : Type} {n : ℕ} (p : Option Bool) (x : Option α) (xs : Option (Fin n → α)) :
    consValue (Binding.guardValue p x) xs = Binding.guardValue p (consValue x xs) := by
  cases p with
  | none => rfl
  | some p => cases p <;> rfl

theorem guard_cons_right {α : Type} {n : ℕ} (p : Option Bool) (x : Option α) (xs : Option (Fin n → α)) :
    consValue x (Binding.guardValue p xs) = Binding.guardValue p (consValue x xs) := by
  cases p with
  | none => cases x <;> rfl
  | some p => cases p <;> cases x <;> rfl

def headValue {α : Type} {n : ℕ} (xs : Option (Fin (n+1) → α)) : Option α :=
  xs.map (fun x => x 0)

def tailValue {α : Type} {n : ℕ} (xs : Option (Fin (n+1) → α)) : Option (Fin n → α) :=
  xs.map (fun x i => x i.succ)

def getValue {α : Type} {n : ℕ} (xs : Option (Fin n → α)) (i : Option ℕ) : Option α :=
  xs.bind (fun x => i.bind (fun j => if h : j < n then some (x ⟨j,h⟩) else none))

theorem guard_get_left {α : Type} {n : ℕ} (p : Option Bool) (xs : Option (Fin n → α)) (i : Option ℕ) :
    getValue (Binding.guardValue p xs) i = Binding.guardValue p (getValue xs i) := by
  cases p with
  | none => rfl
  | some p => cases p <;> rfl

theorem guard_get_right {α : Type} {n : ℕ} (p : Option Bool) (xs : Option (Fin n → α)) (i : Option ℕ) :
    getValue xs (Binding.guardValue p i) = Binding.guardValue p (getValue xs i) := by
  cases p with
  | none => cases xs <;> rfl
  | some p => cases p <;> cases xs <;> rfl

theorem guard_map {α β : Type} (f : α → β) (p : Option Bool) (x : Option α) :
    (Binding.guardValue p x).map f = Binding.guardValue p (x.map f) := by
  cases p with
  | none => rfl
  | some p => cases p <;> rfl

theorem get_cons_zero {α : Type} {n : ℕ} (x : Option α) (xs : Option (Fin n → α)) :
    getValue (consValue x xs) (some 0) = xs.bind (fun _ => x) := by
  cases x <;> cases xs <;> simp [getValue, consValue]

theorem get_cons_succ {α : Type} {n : ℕ} (x : Option α) (xs : Option (Fin n → α)) (i : ℕ) :
    getValue (consValue x xs) (some (i+1)) = x.bind (fun _ => getValue xs (some i)) := by
  cases x <;> cases xs <;> simp [getValue, consValue, Nat.succ_lt_succ_iff]

theorem get_none_left {α : Type} {n : ℕ} (i : Option ℕ) : @getValue α n none i = none := rfl

theorem get_none_right {α : Type} {n : ℕ} (x : Option (Fin n → α)) : getValue x none = none := by
  cases x <;> rfl

theorem getScalarUndefined (f : Binding.Expr Γ (.vector a n)) (x : QSym.Expr .natural)
    (h : ∀ ξ, Domain.Correct (x.eval ξ) (some false)) :
    Binding.Reduction (.binary getValue f (.scalar x)) (.constant none) := .ofEq (by
  intro ξ ρ
  cases hx : x.eval ξ with
  | none =>
    change getValue (f.eval ξ ρ) (x.eval ξ) = none
    rw [hx, get_none_right]
  | some v => have hn := h ξ; simp [Domain.Correct, hx] at hn)

def tabulateValue {α : Type} : (n : ℕ) → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => nilValue
  | n+1, f => consValue (f 0) (tabulateValue n (fun i => f i.succ))

def zipValue {α β γ : Type} (op : Option α → Option β → Option γ) :
    (n : ℕ) → Option (Fin n → α) → Option (Fin n → β) → Option (Fin n → γ)
  | 0, x, y => x.bind (fun _ => y.bind (fun _ => nilValue))
  | n+1, x, y => consValue (op (headValue x) (headValue y)) (zipValue op n (tailValue x) (tailValue y))

def dotValue {α : Type} (add mul : Option α → Option α → Option α)
    (dual : Option α → Option α) (zero : α) :
    (n : ℕ) → Option (Fin n → α) → Option (Fin n → α) → Option α
  | 0, x, y => x.bind (fun _ => y.map (fun _ => zero))
  | n+1, x, y => add (mul (dual (headValue x)) (headValue y))
      (dotValue add mul dual zero n (tailValue x) (tailValue y))

def columnValue {α : Type} {m n : ℕ} (a : Option (Fin m → Fin n → α)) (j : Fin n) : Option (Fin m → α) :=
  a.map (fun a i => a i j)

def matvecValue {α : Type} (add mul : Option α → Option α → Option α) (zero : α)
    (m n : ℕ) (a : Option (Fin m → Fin n → α)) (x : Option (Fin n → α)) : Option (Fin m → α) :=
  a.bind (fun a => x.bind (fun x =>
    tabulateValue m (fun i => dotValue add mul id zero n (some (a i)) (some x))))

def matmulValue {α : Type} (add mul : Option α → Option α → Option α) (zero : α)
    (m k n : ℕ) (a : Option (Fin m → Fin k → α)) (b : Option (Fin k → Fin n → α)) :
    Option (Fin m → Fin n → α) :=
  a.bind (fun a => b.bind (fun b => tabulateValue m (fun i => tabulateValue n (fun j =>
    dotValue add mul id zero k (some (a i)) (columnValue (some b) j)))))

def matrixPowerValue {α : Type} (add mul : Option α → Option α → Option α) (zero one : α)
    (n : ℕ) (a : Option (Fin n → Fin n → α)) (exponent : Option ℕ) : Option (Fin n → Fin n → α) :=
  a.bind (fun a => exponent.bind (fun k =>
    (fun b => matmulValue add mul zero n n n (some a) b)^[k]
      (tabulateValue n (fun i => tabulateValue n (fun j => some (if i = j then one else zero))))))

theorem matrixPowerValue_succ {α : Type} (add mul : Option α → Option α → Option α) (zero one : α)
    (n : ℕ) (a : Option (Fin n → Fin n → α)) (k : ℕ) :
    matrixPowerValue add mul zero one n a (some (k+1)) =
      matmulValue add mul zero n n n a (matrixPowerValue add mul zero one n a (some k)) := by
  cases a with
  | none => rfl
  | some a =>
    change (fun b => matmulValue add mul zero n n n (some a) b)^[k+1] _ = _
    exact Function.iterate_succ_apply' _ _ _

theorem defined_pair {α β : Type} (x : Option α) (y : Option β) :
    Binding.definedValue (pairValue x y) = Value.and (Binding.definedValue x) (Binding.definedValue y) := by
  cases x <;> cases y <;> rfl

theorem defined_cons {α : Type} {n : ℕ} (x : Option α) (xs : Option (Fin n → α)) :
    Binding.definedValue (consValue x xs) = Value.and (Binding.definedValue x) (Binding.definedValue xs) := by
  cases x <;> cases xs <;> rfl

theorem tabulateValue_some {α : Type} (n : ℕ) (f : Fin n → α) :
    tabulateValue n (fun i => some (f i)) = some f := by
  induction n with
  | zero =>
    apply congrArg some
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [tabulateValue, ih, consValue, Option.some_bind, Option.map_some]
    apply congrArg some
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem dotValue_some {α : Type} [AddCommMonoid α] [Mul α]
    (add mul : Option α → Option α → Option α) (dual : Option α → Option α) (conj : α → α)
    (ha : ∀ x y, add (some x) (some y) = some (x+y))
    (hm : ∀ x y, mul (some x) (some y) = some (x*y))
    (hd : ∀ x, dual (some x) = some (conj x))
    (n : ℕ) (x y : Fin n → α) :
    dotValue add mul dual 0 n (some x) (some y) = some (∑ i, conj (x i) * y i) := by
  induction n with
  | zero => simp [dotValue]
  | succ n ih =>
    simp only [dotValue, headValue, tailValue, Option.map, hd, hm, ih, ha]
    rw [Fin.sum_univ_succ]

theorem matvecValue_some {α : Type} [AddCommMonoid α] [Mul α]
    (add mul : Option α → Option α → Option α)
    (ha : ∀ x y, add (some x) (some y) = some (x+y))
    (hm : ∀ x y, mul (some x) (some y) = some (x*y))
    (m n : ℕ) (a : Fin m → Fin n → α) (x : Fin n → α) :
    matvecValue add mul 0 m n (some a) (some x) = some (fun i => ∑ j, a i j * x j) := by
  simp only [matvecValue, Option.some_bind, dotValue_some add mul id id ha hm (fun _ => rfl), id_eq]
  exact tabulateValue_some _ _

end QSym.Tensor
