import QSym.Tensor

namespace QSym.TensorDomains

structure Unary {α β : Type} (f : Option α → Option β) : Prop where
  none : f none=none
  total : ∀ x, Value.Defined (f (some x))

structure Binary {α β γ : Type} (f : Option α → Option β → Option γ) : Prop where
  left : ∀ y, f none y=none
  right : ∀ x, f x none=none
  total : ∀ x y, Value.Defined (f (some x) (some y))

theorem Binary.defined {α β γ : Type} {f : Option α → Option β → Option γ}
    (h : Binary f) (x : Option α) (y : Option β) :
    Binding.definedValue (f x y)=Value.and (Binding.definedValue x) (Binding.definedValue y) := by
  cases x with
  | none => rw [h.left]; rfl
  | some x =>
    cases y with
    | none => rw [h.right]; rfl
    | some y => obtain ⟨z, hz⟩ := h.total x y; rw [hz]; rfl

theorem add {α : Type} [Add α] : Binary (@Value.add α _) :=
  ⟨fun _ => rfl, fun x => by cases x <;> rfl, fun x y => ⟨x+y,rfl⟩⟩

theorem mul {α : Type} [Mul α] : Binary (@Value.mul α _) :=
  ⟨fun _ => rfl, fun x => by cases x <;> rfl, fun x y => ⟨x*y,rfl⟩⟩

theorem builtin2 {α β γ : Type} (f : Function2 α β γ) (h : ∀ x y, f.domain x y) :
    Binary f.apply := by
  constructor
  · intro y; rfl
  · intro x; cases x <;> rfl
  · intro x y; exact f.total h _ _ ⟨x,rfl⟩ ⟨y,rfl⟩

theorem identity {α : Type} : Unary (@id (Option α)) := ⟨rfl,fun x => ⟨x,rfl⟩⟩

theorem conjugate : Unary Value.conj := ⟨rfl,fun x => ⟨star x,rfl⟩⟩

theorem tabulate {α : Type} (n : ℕ) (f : Fin n → Option α)
    (h : ∀ i, Value.Defined (f i)) : Value.Defined (Tensor.tabulateValue n f) := by
  induction n with
  | zero => exact ⟨Fin.elim0,rfl⟩
  | succ n ih =>
    obtain ⟨x,hx⟩ := h 0
    obtain ⟨xs,hxs⟩ := ih (fun i => f i.succ) (fun i => h i.succ)
    rw [Tensor.tabulateValue, hx, hxs]
    exact ⟨Fin.cases x xs,rfl⟩

theorem zip {α β γ : Type} (op : Option α → Option β → Option γ) (h : Binary op) (n : ℕ) :
    Binary (Tensor.zipValue op n) := by
  induction n with
  | zero =>
    constructor
    · intro y; rfl
    · intro x; cases x <;> rfl
    · intro x y; exact ⟨Fin.elim0,rfl⟩
  | succ n ih =>
    constructor
    · intro y; simp [Tensor.zipValue, Tensor.headValue, Tensor.tailValue, h.left, Tensor.consValue]
    · intro x; simp [Tensor.zipValue, Tensor.headValue, Tensor.tailValue, h.right, Tensor.consValue]
    · intro x y
      obtain ⟨z,hz⟩ := h.total (x 0) (y 0)
      obtain ⟨zs,hzs⟩ := ih.total (fun i => x i.succ) (fun i => y i.succ)
      change Value.Defined (Tensor.consValue (op (some (x 0)) (some (y 0)))
        (Tensor.zipValue op n (some (fun i => x i.succ)) (some (fun i => y i.succ))))
      rw [hz,hzs]
      exact ⟨Fin.cases z zs,rfl⟩

theorem dot {α : Type} (add mul : Option α → Option α → Option α) (dual : Option α → Option α)
    (ha : Binary add) (hm : Binary mul) (hd : Unary dual) (zero : α) (n : ℕ) :
    Binary (Tensor.dotValue add mul dual zero n) := by
  induction n with
  | zero =>
    constructor
    · intro y; rfl
    · intro x; cases x <;> rfl
    · intro x y; exact ⟨zero,rfl⟩
  | succ n ih =>
    constructor
    · intro y; simp [Tensor.dotValue, Tensor.headValue, hd.none, hm.left, ha.left]
    · intro x; simp [Tensor.dotValue, Tensor.headValue, hm.right, ha.left]
    · intro x y
      obtain ⟨a,he⟩ := hd.total (x 0)
      obtain ⟨b,hb⟩ := hm.total a (y 0)
      obtain ⟨c,hc⟩ := ih.total (fun i => x i.succ) (fun i => y i.succ)
      change Value.Defined (add (mul (dual (some (x 0))) (some (y 0)))
        (Tensor.dotValue add mul dual zero n (some (fun i => x i.succ)) (some (fun i => y i.succ))))
      rw [he,hb,hc]
      exact ha.total b c

theorem matvec {α : Type} (add mul : Option α → Option α → Option α)
    (ha : Binary add) (hm : Binary mul) (zero : α) (m n : ℕ) :
    Binary (Tensor.matvecValue add mul zero m n) := by
  constructor
  · intro x; rfl
  · intro a; cases a <;> rfl
  · intro a x
    exact tabulate m _ (fun i => (dot add mul id ha hm identity zero n).total (a i) x)

theorem matmul {α : Type} (add mul : Option α → Option α → Option α)
    (ha : Binary add) (hm : Binary mul) (zero : α) (m k n : ℕ) :
    Binary (Tensor.matmulValue add mul zero m k n) := by
  constructor
  · intro b; rfl
  · intro a; cases a <;> rfl
  · intro a b
    exact tabulate m _ (fun i => tabulate n _ (fun j =>
      (dot add mul id ha hm identity zero k).total (a i) (fun r => b r j)))

theorem power {α : Type} (add mul : Option α → Option α → Option α)
    (ha : Binary add) (hm : Binary mul) (zero one : α) (n : ℕ) :
    Binary (Tensor.matrixPowerValue add mul zero one n) := by
  constructor
  · intro k; rfl
  · intro a; cases a <;> rfl
  · intro a k
    induction k with
    | zero => exact tabulate n _ (fun i => tabulate n _ (fun j => ⟨if i=j then one else zero,rfl⟩))
    | succ k ih =>
      obtain ⟨b,hb⟩ := ih
      rw [Tensor.matrixPowerValue_succ, hb]
      exact (matmul add mul ha hm zero n n n).total a b

theorem get {α : Type} (n i : ℕ) (h : i<n) (x : Option (Fin n → α)) :
    Binding.definedValue (Tensor.getValue x (some i))=Binding.definedValue x := by
  cases x <;> simp [Tensor.getValue, Binding.definedValue, h]

end QSym.TensorDomains
