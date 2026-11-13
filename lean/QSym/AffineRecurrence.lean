import QSym.Tensor
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace QSym.AffineRecurrence
attribute [local instance] Classical.propDecidable

inductive Expr (R : Type) where
  | constant (value : R)
  | previous
  | add (left right : Expr R)
  | left (value : R) (body : Expr R)
  | right (body : Expr R) (value : R)

variable {R : Type} [CommSemiring R]

def Expr.coefficient : Expr R → R
  | .constant _ => 0
  | .previous => 1
  | .add x y => x.coefficient + y.coefficient
  | .left c x => c * x.coefficient
  | .right x c => x.coefficient * c

def Expr.offset : Expr R → R
  | .constant c => c
  | .previous => 0
  | .add x y => x.offset + y.offset
  | .left c x => c * x.offset
  | .right x c => x.offset * c

def Expr.eval (add mul : Option R → Option R → Option R) (x : Option R) : Expr R → Option R
  | .constant c => some c
  | .previous => x
  | .add a b => add (a.eval add mul x) (b.eval add mul x)
  | .left c a => mul (some c) (a.eval add mul x)
  | .right a c => mul (a.eval add mul x) (some c)

theorem Expr.eval_some (e : Expr R) (x : R) :
    e.eval Value.add Value.mul (some x) = some (e.coefficient * x + e.offset) := by
  induction e <;> simp_all [eval, coefficient, offset, Value.add, Value.mul] <;> ring

def matrix (e : Expr R) : Matrix (Fin 2) (Fin 2) R :=
  ![![e.coefficient,e.offset],![0,1]]

theorem matmul_some (m n k : ℕ) (a : Matrix (Fin m) (Fin k) R) (b : Matrix (Fin k) (Fin n) R) :
    Tensor.matmulValue Value.add Value.mul 0 m k n (some a) (some b) = some (a * b) := by
  simp only [Tensor.matmulValue, Option.some_bind, Tensor.columnValue, Option.map]
  simp_rw [Tensor.dotValue_some Value.add Value.mul id id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl), id_eq]
  simp_rw [Tensor.tabulateValue_some]
  rfl

theorem power_some (d : ℕ) (a : Matrix (Fin d) (Fin d) R) (n : ℕ) :
    Tensor.matrixPowerValue Value.add Value.mul 0 1 d (some a) (some n) = some (a^n) := by
  induction n with
  | zero =>
    simp only [Tensor.matrixPowerValue, Option.some_bind, Function.iterate_zero_apply,
      Tensor.tabulateValue_some, pow_zero]
    rfl
  | succ n ih => rw [Tensor.matrixPowerValue_succ, ih, matmul_some, pow_succ']

def result (add mul : Option R → Option R → Option R) (a : R) (e : Expr R) (n : ℕ) : Option R :=
  Tensor.getValue (Tensor.matvecValue add mul 0 2 2
    (Tensor.matrixPowerValue add mul 0 1 2 (some (matrix e)) (some n)) (some ![a,1])) (some 0)

theorem result_eq (a : R) (e : Expr R) (n : ℕ) :
    result Value.add Value.mul a e n = some ((matrix e ^ n).mulVec ![a,1] 0) := by
  rw [result, power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

theorem last_one (a : R) (e : Expr R) (n : ℕ) : (matrix e ^ n).mulVec ![a,1] 1 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simpa [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using ih

theorem result_zero (a : R) (e : Expr R) : result Value.add Value.mul a e 0 = some a := by
  simp [result_eq]

theorem result_succ (a : R) (e : Expr R) (n : ℕ) :
    result Value.add Value.mul a e (n+1) = e.eval Value.add Value.mul (result Value.add Value.mul a e n) := by
  rw [result_eq, result_eq, Expr.eval_some, pow_succ', ← Matrix.mulVec_mulVec]
  have h (v : Fin 2 → R) : (matrix e).mulVec v 0 = e.coefficient * v 0 + e.offset * v 1 := by
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h, last_one, mul_one]

noncomputable def step (add mul : Option R → Option R → Option R) (a : R) (e : Expr R)
    (g : ℕ → Option R) (n : ℕ) : Option R :=
  let p := Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))
  add (Value.mask p (some a)) (Value.mask (Value.not p)
    (e.eval add mul ((Functions.subN.apply (some n) (some 1)).bind g)))

theorem step_zero (a : R) (e : Expr R) (g : ℕ → Option R) :
    step Value.add Value.mul a e g 0 = some a := by
  simp [step, Function1.apply, Functions.nonzeroZ, Functions.castNZ, Value.not, Value.mask, Value.add]

theorem step_succ (a : R) (e : Expr R) (g : ℕ → Option R) (n : ℕ) :
    step Value.add Value.mul a e g (n+1) = e.eval Value.add Value.mul (g n) := by
  have ht : Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some (n+1)))) = some false := by
    have hn : (↑n + 1 : ℤ) ≠ 0 := by omega
    simp [Function1.apply, Functions.nonzeroZ, Functions.castNZ, Value.not, hn]
  have hp : Functions.subN.apply (some (n+1)) (some 1) = some n := by
    simp [Function2.apply, Functions.subN]
  unfold step
  rw [ht, hp]
  simp only [Option.some_bind, Value.not, Value.mask, Bool.not_false]
  cases e.eval Value.add Value.mul (g n) <;> simp [Value.add]

theorem solve (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (ha : add = Value.add) (hm : mul = Value.mul) (a : R) (e : Expr R)
    (hp : ∀ g n, p.eval g n = step add mul a e g n) :
    FixedPoint.value p.functional = result add mul a e := by
  subst add; subst mul
  funext n
  induction n with
  | zero => rw [← p.unfold, hp, step_zero, result_zero]
  | succ n ih => rw [← p.unfold, hp, step_succ, ih, result_succ]

theorem apply2_some {A B C : Type} (f : Function2 A B C) (a : A) (b : B) (h : f.domain a b) :
    f.apply (some a) (some b) = some (f.value a b) := by simp [Function2.apply, h]

theorem zeroR : some (((0 : ℤ) : ℝ)) = some (0 : ℝ) := by simp
theorem oneR : some (((1 : ℤ) : ℝ)) = some (1 : ℝ) := by simp

theorem zeroC : some (((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) = some (0 : ℂ) := by simp
theorem oneC : some (((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I) = some (1 : ℂ) := by simp

theorem solve_matrix (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (ha : add = Value.add) (hm : mul = Value.mul) (a : R) (e : Expr R)
    (hp : ∀ g n, p.eval g n = step add mul a e g n)
    (z o : R) (hz : z = 0) (ho : o = 1)
    (m : Option (Matrix (Fin 2) (Fin 2) R)) (v : Option (Fin 2 → R))
    (hmat : m = some (matrix e)) (hv : v = some ![a,1]) :
    FixedPoint.value p.functional = fun n => Tensor.getValue (Tensor.matvecValue add mul z 2 2
      (Tensor.matrixPowerValue add mul z o 2 m (some n)) v) (some 0) := by
  subst z; subst o; rw [hmat, hv]
  exact solve p add mul ha hm a e hp

theorem addN : Functions.addN.apply = @Value.add ℕ _ := by funext x y; cases x <;> cases y <;> simp [Function2.apply, Functions.addN, Value.add]
theorem mulN : Functions.mulN.apply = @Value.mul ℕ _ := by funext x y; cases x <;> cases y <;> simp [Function2.apply, Functions.mulN, Value.mul]
theorem addZ : Functions.addZ.apply = @Value.add ℤ _ := by funext x y; cases x <;> cases y <;> simp [Function2.apply, Functions.addZ, Value.add]
theorem mulZ : Functions.mulZ.apply = @Value.mul ℤ _ := by funext x y; cases x <;> cases y <;> simp [Function2.apply, Functions.mulZ, Value.mul]
theorem addQ : Functions.addQ.apply = @Value.add ℚ _ := by funext x y; cases x <;> cases y <;> simp [Function2.apply, Functions.addQ, Value.add]
theorem mulQ : Functions.mulQ.apply = @Value.mul ℚ _ := by funext x y; cases x <;> cases y <;> simp [Function2.apply, Functions.mulQ, Value.mul]

end QSym.AffineRecurrence
