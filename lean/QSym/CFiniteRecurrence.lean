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

end QSym.CFiniteRecurrence
