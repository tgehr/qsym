import QSym.AffineRecurrence
import QSym.Domain

namespace QSym.LinearRecurrence

inductive Expr (R : Type) (d : ℕ) where
  | constant (value : R)
  | previous (index : Fin d)
  | add (left right : Expr R d)
  | left (value : R) (body : Expr R d)
  | right (body : Expr R d) (value : R)

variable {R : Type} [CommSemiring R] {k : ℕ}

def Expr.coefficient {d : ℕ} : Expr R d → Fin d → R
  | .constant _ => fun _ => 0
  | .previous j => fun i => if i=j then 1 else 0
  | .add x y => fun i => x.coefficient i + y.coefficient i
  | .left c x => fun i => c * x.coefficient i
  | .right x c => fun i => x.coefficient i * c

def Expr.offset {d : ℕ} : Expr R d → R
  | .constant c => c
  | .previous _ => 0
  | .add x y => x.offset + y.offset
  | .left c x => c * x.offset
  | .right x c => x.offset * c

def Expr.eval {d : ℕ} (add mul : Option R → Option R → Option R)
    (x : Fin d → Option R) : Expr R d → Option R
  | .constant c => some c
  | .previous i => x i
  | .add a b => add (a.eval add mul x) (b.eval add mul x)
  | .left c a => mul (some c) (a.eval add mul x)
  | .right a c => mul (a.eval add mul x) (some c)

theorem Expr.eval_some {d : ℕ} (e : Expr R d) (x : Fin d → R) :
    e.eval Value.add Value.mul (fun i => some (x i)) =
      some ((∑ i, e.coefficient i * x i) + e.offset) := by
  induction e <;> simp_all [eval, coefficient, offset, Value.add, Value.mul,
    add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, mul_comm, mul_left_comm] <;> ring

def append {A : Type} {d : ℕ} (v : Fin d → A) (a : A) (i : Fin (d+1)) : A :=
  if h : i.val<d then v ⟨i.val,h⟩ else a

@[simp] theorem append_castSucc {A : Type} {d : ℕ} (v : Fin d → A) (a : A) (i : Fin d) :
    append v a i.castSucc = v i := by simp [append, i.isLt]

@[simp] theorem append_last {A : Type} {d : ℕ} (v : Fin d → A) (a : A) :
    append v a (Fin.last d) = a := by simp [append]

def matrix (e : Expr R (k+1)) : Matrix (Fin (k+2)) (Fin (k+2)) R :=
  append (append (fun i j => if j=i.succ.castSucc then 1 else 0)
    (append e.coefficient e.offset)) (fun j => if j=Fin.last (k+1) then 1 else 0)

def initial (v : Fin (k+1) → R) : Fin (k+2) → R := append v 1

theorem row_shift (e : Expr R (k+1)) (v : Fin (k+2) → R) (i : Fin k) :
    (matrix e).mulVec v i.castSucc.castSucc = v i.succ.castSucc := by
  simp [matrix, Matrix.mulVec, dotProduct]

theorem row_last (e : Expr R (k+1)) (v : Fin (k+2) → R) :
    (matrix e).mulVec v (Fin.last k).castSucc =
      (∑ i, e.coefficient i * v i.castSucc) + e.offset * v (Fin.last (k+1)) := by
  simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

theorem row_one (e : Expr R (k+1)) (v : Fin (k+2) → R) :
    (matrix e).mulVec v (Fin.last (k+1)) = v (Fin.last (k+1)) := by
  simp [matrix, Matrix.mulVec, dotProduct]

def state (e : Expr R (k+1)) (v : Fin (k+1) → R) (n : ℕ) :=
  (matrix e ^ n).mulVec (initial v)

theorem state_step (e : Expr R (k+1)) (v : Fin (k+1) → R) (n : ℕ) :
    state e v (n+1) = (matrix e).mulVec (state e v n) := by
  rw [state, pow_succ', ← Matrix.mulVec_mulVec]; rfl

theorem state_one (e : Expr R (k+1)) (v : Fin (k+1) → R) (n : ℕ) :
    state e v n (Fin.last (k+1)) = 1 := by
  induction n with
  | zero => simp [state, initial]
  | succ n ih => rw [state_step, row_one, ih]

theorem state_shift (e : Expr R (k+1)) (v : Fin (k+1) → R) (n : ℕ) (i : Fin k) :
    state e v (n+1) i.castSucc.castSucc = state e v n i.succ.castSucc := by
  rw [state_step, row_shift]

theorem state_index (e : Expr R (k+1)) (v : Fin (k+1) → R) (i : Fin (k+1)) :
    ∀ n, state e v n i.castSucc = state e v (n+i.val) 0 := by
  induction i using Fin.induction with
  | zero => intro n; simp
  | succ i ih =>
    intro n
    rw [← state_shift, ih]
    congr 1
    simp only [Fin.val_succ, Fin.coe_castSucc]
    omega

def sequence (e : Expr R (k+1)) (v : Fin (k+1) → R) (n : ℕ) := state e v n 0

theorem sequence_initial (e : Expr R (k+1)) (v : Fin (k+1) → R) (i : Fin (k+1)) :
    sequence e v i.val = v i := by
  have h := state_index e v i 0
  simpa [sequence, state, initial] using h.symm

theorem recurrence (e : Expr R (k+1)) (v : Fin (k+1) → R) (n : ℕ) :
    sequence e v (n+(k+1)) = (∑ i, e.coefficient i * sequence e v (n+i.val)) + e.offset := by
  have h := state_index e v (Fin.last k) (n+1)
  have hn : n+1+(Fin.last k).val=n+(k+1) := by simp; omega
  rw [hn, state_step, row_last, state_one, mul_one] at h
  rw [sequence, ← h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [state_index]
  rfl

theorem solve (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (ha : add = Value.add) (hm : mul = Value.mul) (e : Expr R (k+1)) (v : Fin (k+1) → R)
    (hbase : ∀ g (i : Fin (k+1)), p.eval g i.val = some (v i))
    (hstep : ∀ g n, p.eval g (n+(k+1)) = e.eval add mul (fun i => g (n+i.val))) :
    FixedPoint.value p.functional = fun n => some (sequence e v n) := by
  subst add; subst mul
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [← p.unfold]
    by_cases hn : n < k+1
    · exact (hbase _ ⟨n, hn⟩).trans (congrArg some (sequence_initial e v ⟨n, hn⟩).symm)
    · obtain ⟨m, rfl⟩ : ∃ m, n=m+(k+1) := ⟨n-(k+1), by omega⟩
      rw [hstep]
      have h (i : Fin (k+1)) : FixedPoint.value p.functional (m+i.val) = some (sequence e v (m+i.val)) :=
        ih _ (by have := i.isLt; omega)
      simp only [h, Expr.eval_some, recurrence]

theorem solve_matrix (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (ha : add = Value.add) (hm : mul = Value.mul) (e : Expr R (k+1)) (v : Fin (k+1) → R)
    (hbase : ∀ g (i : Fin (k+1)), p.eval g i.val = some (v i))
    (hstep : ∀ g n, p.eval g (n+(k+1)) = e.eval add mul (fun i => g (n+i.val)))
    (z o : R) (hz : z = 0) (ho : o = 1)
    (m : Option (Matrix (Fin (k+2)) (Fin (k+2)) R)) (a : Option (Fin (k+2) → R))
    (hmat : m = some (matrix e)) (hv : a = some (initial v)) :
    FixedPoint.value p.functional = fun n => Tensor.getValue (Tensor.matvecValue add mul z (k+2) (k+2)
      (Tensor.matrixPowerValue add mul z o (k+2) m (some n)) a) (some 0) := by
  subst z; subst o; subst add; subst mul; rw [hmat, hv, solve p _ _ rfl rfl e v hbase hstep]
  funext n
  rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

theorem known {A : Type} {x y : Option A} (hd : Domain.Correct x (some true))
    (h : Value.Refines x y) : x = y := h.eq_of_defined (hd.iff.mpr rfl)

theorem select (add : Option R → Option R → Option R) (ha : add=Value.add)
    {p : Option Bool} (b : Bool) (x y : Option R) (hp : p=some b) :
    add (Value.mask p x) (Value.mask (Value.not p) y) = if b then x else y := by
  subst add; subst p
  cases b <;> cases x <;> cases y <;> simp [Value.add, Value.mask, Value.not]

theorem select_rev (add : Option R → Option R → Option R) (ha : add=Value.add)
    {p : Option Bool} (b : Bool) (x y : Option R) (hp : p=some b) :
    add (Value.mask (Value.not p) y) (Value.mask p x) = if b then x else y := by
  subst add; subst p
  cases b <;> cases x <;> cases y <;> simp [Value.add, Value.mask, Value.not]

theorem lag (n d l : ℕ) (hl : l ≤ d) :
    Functions.subN.apply (some (n+d)) (some l) = some (n+(d-l)) := by
  have h : l ≤ n+d := by omega
  simp only [Function2.apply, Functions.subN, Option.some_bind, h, ↓reduceIte]
  congr 1; omega

end QSym.LinearRecurrence
