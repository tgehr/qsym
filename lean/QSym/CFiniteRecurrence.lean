import QSym.CFinite

namespace QSym.CFiniteRecurrence
open CFinite
variable {R : Type} [CommSemiring R]

inductive Expr (R : Type) where
  | force (s : Sequence R)
  | previous
  | add (a b : Expr R)
  | left (c : R) (a : Expr R)
  | right (a : Expr R) (c : R)

def Expr.coefficient : Expr R → R
  | .force _ => 0
  | .previous => 1
  | .add a b => a.coefficient + b.coefficient
  | .left c a => c*a.coefficient
  | .right a c => a.coefficient*c

def Expr.forcing : Expr R → Sequence R
  | .force s => s
  | .previous => .zero
  | .add a b => a.forcing.plus b.forcing
  | .left c a => a.forcing.left c
  | .right a c => a.forcing.right c

def Expr.eval (add mul : Option R → Option R → Option R) (previous : Option R) (n : ℕ) : Expr R → Option R
  | .force s => some (s.value n)
  | .previous => previous
  | .add a b => add (a.eval add mul previous n) (b.eval add mul previous n)
  | .left c a => mul (some c) (a.eval add mul previous n)
  | .right a c => mul (a.eval add mul previous n) (some c)

theorem Expr.eval_some (e : Expr R) (x : R) (n : ℕ) :
    e.eval Value.add Value.mul (some x) n = some (e.coefficient*x+e.forcing.value n) := by
  induction e <;> simp_all [eval, coefficient, forcing, Sequence.add_value,
    Sequence.plus_value, Sequence.left_value, Sequence.right_value, Value.add, Value.mul] <;> ring

def matrix (e : Expr R) : Matrix (Fin (e.forcing.size+1)) (Fin (e.forcing.size+1)) R :=
  Fin.cons (Fin.cons e.coefficient (fun j => dot e.forcing.output (fun i => e.forcing.matrix i j)))
    (fun i => Fin.cons 0 (e.forcing.matrix i))
def initial (e : Expr R) (a : R) : Fin (e.forcing.size+1) → R := Fin.cons a e.forcing.initial

def state (e : Expr R) (a : R) (n : ℕ) := (matrix e ^ n).mulVec (initial e a)

theorem state_zero (e : Expr R) (a : R) : state e a 0 = initial e a := by simp [state]
theorem state_succ (e : Expr R) (a : R) (n : ℕ) : state e a (n+1) = (matrix e).mulVec (state e a n) := by
  rw [state, pow_succ', ← Matrix.mulVec_mulVec]; rfl

theorem auxiliary (e : Expr R) (a : R) (n : ℕ) :
    (fun i => state e a n i.succ) = e.forcing.state n := by
  induction n with
  | zero => simp [state_zero, initial, Sequence.state_zero]
  | succ n ih =>
    rw [state_succ, Sequence.state_succ]
    funext i
    simp only [matrix, Matrix.mulVec, dotProduct, Fin.cons_succ, Fin.sum_univ_succ,
      Fin.cons_zero, zero_mul, zero_add]
    exact congrArg (fun v => ∑ j, e.forcing.matrix i j * v j) ih

theorem dot_matrix {d : ℕ} (o x : Fin d → R) (m : Matrix (Fin d) (Fin d) R) :
    dot (fun j => dot o (fun i => m i j)) x = dot o (m.mulVec x) := by
  simp only [dot_eq, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  exact mul_assoc _ _ _

theorem head_succ (e : Expr R) (a : R) (n : ℕ) :
    state e a (n+1) 0 = e.coefficient*state e a n 0+e.forcing.value (n+1) := by
  rw [state_succ]
  simp only [matrix, Matrix.mulVec, dotProduct, Fin.cons_zero, Fin.sum_univ_succ, Fin.cons_succ]
  rw [← dot_eq]
  change e.coefficient*state e a n 0 + dot (fun j => dot e.forcing.output (fun i => e.forcing.matrix i j)) (fun j => state e a n j.succ) = _
  rw [auxiliary, dot_matrix, ← Sequence.state_succ]
  rfl

def result (add mul : Option R → Option R → Option R) (e : Expr R) (a : R) (n : ℕ) :=
  Tensor.getValue (Tensor.matvecValue add mul 0 (e.forcing.size+1) (e.forcing.size+1)
    (Tensor.matrixPowerValue add mul 0 1 (e.forcing.size+1) (some (matrix e)) (some n))
    (some (initial e a))) (some 0)

theorem result_eq (e : Expr R) (a : R) (n : ℕ) :
    result Value.add Value.mul e a n = some (state e a n 0) := by
  rw [result, AffineRecurrence.power_some,
    Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
  simp [Tensor.getValue, state, Matrix.mulVec, dotProduct]

noncomputable def step (add mul : Option R → Option R → Option R) (e : Expr R) (a : R)
    (g : ℕ → Option R) (n : ℕ) :=
  let p := Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))
  add (Value.mask p (some a)) (Value.mask (Value.not p)
    (e.eval add mul ((Functions.subN.apply (some n) (some 1)).bind g) n))

theorem step_zero (e : Expr R) (a : R) (g : ℕ → Option R) :
    step Value.add Value.mul e a g 0 = some a := by
  simp [step, Function1.apply, Functions.nonzeroZ, Functions.castNZ, Value.not, Value.mask, Value.add]
theorem step_succ (e : Expr R) (a : R) (g : ℕ → Option R) (n : ℕ) :
    step Value.add Value.mul e a g (n+1) = e.eval Value.add Value.mul (g n) (n+1) := by
  have hn : (↑n+1 : ℤ) ≠ 0 := by omega
  have ht : Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some (n+1)))) = some false := by
    simp [Function1.apply, Functions.nonzeroZ, Functions.castNZ, Value.not, hn]
  have hp : Functions.subN.apply (some (n+1)) (some 1) = some n := by simp [Function2.apply, Functions.subN]
  unfold step
  rw [ht, hp]
  simp only [Option.some_bind, Value.not, Value.mask, Bool.not_false]
  cases e.eval Value.add Value.mul (g n) (n+1) <;> simp [Value.add]

theorem solve (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (ha : add=Value.add) (hm : mul=Value.mul) (e : Expr R) (a : R)
    (hp : ∀ g n, p.eval g n = step add mul e a g n) :
    FixedPoint.value p.functional = result add mul e a := by
  subst add; subst mul; funext n
  induction n with
  | zero => rw [← p.unfold, hp, step_zero, result_eq, state_zero]; rfl
  | succ n ih => rw [← p.unfold, hp, step_succ, ih, result_eq, Expr.eval_some, result_eq, head_succ]

theorem solve_matrix (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (ha : add=Value.add) (hm : mul=Value.mul) (e : Expr R) (a : R)
    (hp : ∀ g n, p.eval g n = step add mul e a g n)
    (z o : R) (hz : z=0) (ho : o=1)
    (m : Option (Matrix (Fin (e.forcing.size+1)) (Fin (e.forcing.size+1)) R))
    (v : Option (Fin (e.forcing.size+1) → R))
    (hmat : m=some (matrix e)) (hv : v=some (initial e a)) :
    FixedPoint.value p.functional = fun n => Tensor.getValue
      (Tensor.matvecValue add mul z (e.forcing.size+1) (e.forcing.size+1)
        (Tensor.matrixPowerValue add mul z o (e.forcing.size+1) m (some n)) v) (some 0) := by
  subst z; subst o; rw [hmat, hv]
  exact solve p add mul ha hm e a hp

#qsym_check_axioms solve_matrix

namespace Prefix

-- Advance auxiliary state explicitly with dot, so certificate rows reduce
-- without evaluating matrix powers or enumerating a Finset.
def advance (s : Sequence R) : ℕ → Fin s.size → R
  | 0 => s.initial
  | n+1 => fun i => dot (s.matrix i) (advance s n)

theorem advance_eq (s : Sequence R) (n : ℕ) : advance s n = s.state n := by
  induction n with
  | zero => exact s.state_zero.symm
  | succ n ih => rw [advance, ih, Sequence.state_succ]; funext i; exact dot_eq _ _

def tail (e : Expr R) (a : R) (start : ℕ) : Sequence R :=
  ⟨e.forcing.size+1, matrix e, Fin.cons a (advance e.forcing start),
    Fin.cons 1 (fun _ => 0)⟩

def prepend (a : R) (s : Sequence R) : Sequence R :=
  ⟨s.size+1, Fin.cons (Fin.cons 0 s.output) (fun i => Fin.cons 0 (s.matrix i)),
    Fin.cons a s.initial, Fin.cons 1 (fun _ => 0)⟩

def prependMany : (k : ℕ) → (Fin k → R) → Sequence R → Sequence R
  | 0, _, s => s
  | k+1, v, s => prepend (v 0) (prependMany k (fun i => v i.succ) s)

def sequence {k : ℕ} (e : Expr R) (v : Fin (k+1) → R) : Sequence R :=
  prependMany k (fun i => v i.castSucc) (tail e (v (Fin.last k)) k)

theorem head_value {d : ℕ} (m : Matrix (Fin (d+1)) (Fin (d+1)) R) (v : Fin (d+1) → R) (n : ℕ) :
    (Sequence.mk (d+1) m v (Fin.cons 1 (fun _ => 0))).value n = (m^n).mulVec v 0 := by
  simp [Sequence.value, Sequence.state, dot_eq, Fin.sum_univ_succ]

theorem prepend_auxiliary (a : R) (s : Sequence R) (n : ℕ) :
    (fun i => (prepend a s).state n i.succ) = s.state n := by
  induction n with
  | zero => simp [Sequence.state_zero, prepend]
  | succ n ih =>
    rw [Sequence.state_succ, Sequence.state_succ]
    funext i
    simp only [prepend, Matrix.mulVec, dotProduct, Fin.cons_succ, Fin.sum_univ_succ,
      Fin.cons_zero, zero_mul, zero_add]
    exact congrArg (fun v => ∑ j, s.matrix i j * v j) ih

theorem prepend_zero (a : R) (s : Sequence R) : (prepend a s).value 0 = a := by
  simp [prepend, head_value]

theorem prepend_succ (a : R) (s : Sequence R) (n : ℕ) :
    (prepend a s).value (n+1) = s.value n := by
  change (Sequence.mk _ _ _ _).value _ = _
  rw [head_value]
  change (prepend a s).state (n+1) ⟨0, Nat.zero_lt_succ _⟩ = _
  rw [Sequence.state_succ]
  simp only [prepend, Matrix.mulVec, dotProduct, Fin.mk_zero, Fin.cons_zero, Fin.sum_univ_succ,
    Fin.cons_succ, zero_mul, zero_add]
  rw [← dot_eq]
  change dot s.output (fun i => (prepend a s).state n i.succ) = _
  rw [prepend_auxiliary]; rfl

theorem prefix_initial (k : ℕ) (v : Fin k → R) (s : Sequence R) (i : Fin k) :
    (prependMany k v s).value i.val = v i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact prepend_zero _ _
    · exact (prepend_succ _ _ j.val).trans (ih _ j)

theorem prefix_tail (k : ℕ) (v : Fin k → R) (s : Sequence R) (n : ℕ) :
    (prependMany k v s).value (n+k) = s.value n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Nat.add_succ, prependMany, prepend_succ]
    exact ih _

theorem tail_auxiliary (e : Expr R) (a : R) (start n : ℕ) :
    (fun i => (tail e a start).state n i.succ) = e.forcing.state (n+start) := by
  induction n with
  | zero => simp [Sequence.state_zero, tail, advance_eq]
  | succ n ih =>
    rw [show n+1+start=(n+start)+1 by omega, Sequence.state_succ, Sequence.state_succ]
    funext i
    simp only [tail, matrix, Matrix.mulVec, dotProduct, Fin.cons_succ, Fin.sum_univ_succ,
      Fin.cons_zero, zero_mul, zero_add]
    exact congrArg (fun v => ∑ j, e.forcing.matrix i j * v j) ih

theorem tail_zero (e : Expr R) (a : R) (start : ℕ) : (tail e a start).value 0 = a := by
  simp [tail, head_value]

theorem tail_succ (e : Expr R) (a : R) (start n : ℕ) :
    (tail e a start).value (n+1) = e.coefficient*(tail e a start).value n + e.forcing.value (n+start+1) := by
  simp only [tail, head_value]
  change (tail e a start).state (n+1) ⟨0, Nat.zero_lt_succ _⟩ = e.coefficient*(tail e a start).state n ⟨0, Nat.zero_lt_succ _⟩ + _
  rw [Sequence.state_succ]
  simp only [tail, matrix, Matrix.mulVec, dotProduct, Fin.cons_zero, Fin.sum_univ_succ, Fin.cons_succ]
  rw [← dot_eq]
  change e.coefficient*(tail e a start).state n ⟨0, Nat.zero_lt_succ _⟩ + dot (fun j => dot e.forcing.output (fun i => e.forcing.matrix i j)) (fun j => (tail e a start).state n j.succ) = _
  rw [tail_auxiliary, dot_matrix, ← Sequence.state_succ]; rfl

theorem sequence_initial {k : ℕ} (e : Expr R) (v : Fin (k+1) → R) (i : Fin (k+1)) :
    (sequence e v).value i.val = v i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Nat.zero_add, Fin.val_last, sequence] using (prefix_tail k (fun i => v i.castSucc) (tail e (v (Fin.last k)) k) 0).trans (tail_zero e (v (Fin.last k)) k)
  · exact prefix_initial k _ _ j

theorem sequence_succ {k : ℕ} (e : Expr R) (v : Fin (k+1) → R) (n : ℕ) :
    (sequence e v).value (n+(k+1)) = e.coefficient*(sequence e v).value (n+k) + e.forcing.value (n+(k+1)) := by
  rw [show n+(k+1)=(n+1)+k by omega]
  simp only [sequence, prefix_tail, tail_succ]
  congr 2; omega

theorem sequence_size {k : ℕ} (e : Expr R) (v : Fin (k+1) → R) : 0 < (sequence e v).size := by
  cases k with
  | zero => exact Nat.zero_lt_succ _
  | succ k => exact Nat.zero_lt_succ _

theorem sequence_head {k : ℕ} (e : Expr R) (v : Fin (k+1) → R) (n : ℕ) :
    (sequence e v).value n = (sequence e v).state n ⟨0, sequence_size e v⟩ := by
  cases k <;> exact head_value _ _ n

theorem solve {k : ℕ} (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (ha : add=Value.add) (hm : mul=Value.mul) (e : Expr R) (v : Fin (k+1) → R)
    (hb : ∀ g (i : Fin (k+1)), p.eval g i.val = some (v i))
    (hs : ∀ g n, p.eval g (n+(k+1)) = e.eval add mul (g (n+k)) (n+(k+1))) :
    FixedPoint.value p.functional = fun n => some ((sequence e v).value n) := by
  subst add; subst mul; funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [← p.unfold]
    by_cases hn : n < k+1
    · exact (hb _ ⟨n,hn⟩).trans (congrArg some (sequence_initial e v ⟨n,hn⟩).symm)
    · obtain ⟨m,rfl⟩ : ∃ m, n=m+(k+1) := ⟨n-(k+1), by omega⟩
      rw [hs, ih (m+k) (by omega), Expr.eval_some, sequence_succ]

theorem solve_matrix {k : ℕ} (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (ha : add=Value.add) (hm : mul=Value.mul) (e : Expr R) (v : Fin (k+1) → R)
    (hb : ∀ g (i : Fin (k+1)), p.eval g i.val = some (v i))
    (hs : ∀ g n, p.eval g (n+(k+1)) = e.eval add mul (g (n+k)) (n+(k+1)))
    (z o : R) (hz : z=0) (ho : o=1)
    (m : Option (Matrix (Fin (sequence e v).size) (Fin (sequence e v).size) R))
    (a : Option (Fin (sequence e v).size → R))
    (hmat : m=some (sequence e v).matrix) (hv : a=some (sequence e v).initial) :
    FixedPoint.value p.functional = fun n => Tensor.getValue
      (Tensor.matvecValue add mul z (sequence e v).size (sequence e v).size
        (Tensor.matrixPowerValue add mul z o (sequence e v).size m (some n)) a) (some 0) := by
  subst z; subst o; subst add; subst mul
  rw [hmat, hv, solve p _ _ rfl rfl e v hb hs]
  funext n
  rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
  simp only [Tensor.getValue, sequence_size, ↓reduceDIte, sequence_head, Sequence.state, Option.some_bind, Matrix.mulVec, dotProduct]

#qsym_check_axioms solve_matrix
end Prefix

end QSym.CFiniteRecurrence
