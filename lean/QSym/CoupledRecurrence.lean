import QSym.LinearRecurrence

namespace QSym.CoupledRecurrence
open LinearRecurrence
variable {R : Type} [CommSemiring R] {d : ℕ}

def matrix (e : Fin d → LinearRecurrence.Expr R d) : Matrix (Fin (d+1)) (Fin (d+1)) R :=
  append (fun i => append (e i).coefficient (e i).offset)
    (fun j => if j=Fin.last d then 1 else 0)

def state (e : Fin d → LinearRecurrence.Expr R d) (v : Fin d → R) (n : ℕ) :=
  (matrix e ^ n).mulVec (append v 1)

theorem state_step (e : Fin d → LinearRecurrence.Expr R d) (v : Fin d → R) (n : ℕ) :
    state e v (n+1) = (matrix e).mulVec (state e v n) := by
  rw [state, pow_succ', ← Matrix.mulVec_mulVec]; rfl

theorem row_one (e : Fin d → LinearRecurrence.Expr R d) (v : Fin (d+1) → R) :
    (matrix e).mulVec v (Fin.last d) = v (Fin.last d) := by
  simp [matrix, Matrix.mulVec, dotProduct]

theorem state_one (e : Fin d → LinearRecurrence.Expr R d) (v : Fin d → R) (n : ℕ) :
    state e v n (Fin.last d) = 1 := by
  induction n with
  | zero => simp [state]
  | succ n ih => rw [state_step, row_one, ih]

theorem row (e : Fin d → LinearRecurrence.Expr R d) (v : Fin (d+1) → R) (i : Fin d) :
    (matrix e).mulVec v i.castSucc =
      (∑ j, (e i).coefficient j * v j.castSucc) + (e i).offset * v (Fin.last d) := by
  simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

def evaluate (add mul : Option R → Option R → Option R)
    (e : Fin d → LinearRecurrence.Expr R d) (x : Option (Fin d → R)) : Option (Fin d → R) :=
  Tensor.tabulateValue d (fun i => (e i).eval add mul (fun j => Tensor.getValue x (some j.val)))

noncomputable def step (add mul : Option R → Option R → Option R)
    (v : Fin d → R) (e : Fin d → LinearRecurrence.Expr R d) (g : ℕ → Option (Fin d → R)) (n : ℕ) :=
  Binding.conditionalValue (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n))))
    (some v) (evaluate add mul e ((Functions.subN.apply (some n) (some 1)).bind g))

theorem step_zero (v : Fin d → R) (e : Fin d → LinearRecurrence.Expr R d) (g : ℕ → Option (Fin d → R)) :
    step Value.add Value.mul v e g 0 = some v := by
  simp [step, Binding.conditionalValue, Function1.apply, Functions.nonzeroZ, Functions.castNZ, Value.not]

theorem step_succ (v : Fin d → R) (e : Fin d → LinearRecurrence.Expr R d) (g : ℕ → Option (Fin d → R)) (n : ℕ) :
    step Value.add Value.mul v e g (n+1) = evaluate Value.add Value.mul e (g n) := by
  have hn : (↑n + 1 : ℤ) ≠ 0 := by omega
  simp [step, Binding.conditionalValue, Function1.apply, Function2.apply,
    Functions.nonzeroZ, Functions.castNZ, Functions.subN, Value.not, hn]

theorem evaluate_state (e : Fin d → LinearRecurrence.Expr R d) (v : Fin d → R) (n : ℕ) :
    evaluate Value.add Value.mul e (some (fun i => state e v n i.castSucc)) =
      some (fun i => state e v (n+1) i.castSucc) := by
  have hg (i : Fin d) : Tensor.getValue (some (fun i => state e v n i.castSucc)) (some i.val) =
      some (state e v n i.castSucc) := by simp [Tensor.getValue, i.isLt]
  simp only [evaluate, hg, LinearRecurrence.Expr.eval_some]
  rw [Tensor.tabulateValue_some]
  congr 1
  funext i
  rw [state_step, row, state_one, mul_one]

theorem solve (p : Recursion.Program ℕ (Fin d → R) (Fin d → R))
    (add mul : Option R → Option R → Option R) (ha : add=Value.add) (hm : mul=Value.mul)
    (v : Fin d → R) (e : Fin d → LinearRecurrence.Expr R d)
    (hp : ∀ g n, p.eval g n = step add mul v e g n) :
    FixedPoint.value p.functional = fun n => some (fun i => state e v n i.castSucc) := by
  subst add; subst mul
  funext n
  induction n with
  | zero => rw [← p.unfold, hp, step_zero]; simp [state]
  | succ n ih => rw [← p.unfold, hp, step_succ, ih, evaluate_state]

theorem solve_matrix (p : Recursion.Program ℕ (Fin d → R) (Fin d → R))
    (add mul : Option R → Option R → Option R) (ha : add=Value.add) (hm : mul=Value.mul)
    (v : Fin d → R) (e : Fin d → LinearRecurrence.Expr R d)
    (hp : ∀ g n, p.eval g n = step add mul v e g n)
    (z o : R) (hz : z=0) (ho : o=1)
    (m : Option (Matrix (Fin (d+1)) (Fin (d+1)) R)) (a : Option (Fin (d+1) → R))
    (hmat : m=some (matrix e)) (hv : a=some (append v 1)) :
    FixedPoint.value p.functional = fun n => Tensor.tabulateValue d (fun i =>
      Tensor.getValue (Tensor.matvecValue add mul z (d+1) (d+1)
        (Tensor.matrixPowerValue add mul z o (d+1) m (some n)) a) (some i.val)) := by
  subst z; subst o; subst add; subst mul
  rw [hmat, hv, solve p _ _ rfl rfl v e hp]
  funext n
  rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
  have hg (i : Fin d) : Tensor.getValue (some ((matrix e ^ n).mulVec (append v 1))) (some i.val) =
      some (state e v n i.castSucc) := by
    simp only [Tensor.getValue, Option.some_bind, dif_pos (Nat.lt_succ_of_lt i.isLt)]
    rfl
  change some (fun i => state e v n i.castSucc) = Tensor.tabulateValue d (fun i =>
    Tensor.getValue (some ((matrix e ^ n).mulVec (append v 1))) (some i.val))
  simp only [hg, Tensor.tabulateValue_some]

end QSym.CoupledRecurrence
