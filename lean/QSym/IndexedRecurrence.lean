import QSym.LinearRecurrence

namespace QSym.IndexedRecurrence
variable {R : Type} [CommSemiring R]

-- The two expression variables are f(n-1) and the current index n.
def matrix (e : LinearRecurrence.Expr R 2) : Matrix (Fin 3) (Fin 3) R :=
  ![![e.coefficient 0, e.coefficient 1, e.coefficient 1 + e.offset], ![0,1,1], ![0,0,1]]

def state (a : R) (e : LinearRecurrence.Expr R 2) (n : ℕ) : Fin 3 → R :=
  (matrix e ^ n).mulVec ![a,0,1]

def natCast (n : Option ℕ) : Option R := n.map Nat.cast

theorem state_step (a : R) (e : LinearRecurrence.Expr R 2) (n : ℕ) :
    state a e (n+1) = (matrix e).mulVec (state a e n) := by
  rw [state, pow_succ', ← Matrix.mulVec_mulVec]; rfl

theorem state_one (a : R) (e : LinearRecurrence.Expr R 2) (n : ℕ) :
    state a e n 2 = 1 := by
  induction n with
  | zero => simp [state]
  | succ n ih => simpa [state_step, matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using ih

theorem state_index (a : R) (e : LinearRecurrence.Expr R 2) (n : ℕ) :
    state a e n 1 = (n : R) := by
  induction n with
  | zero => simp [state]
  | succ n ih => simp [state_step, matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, state_one, ih]

theorem eval_some (e : LinearRecurrence.Expr R 2) (x y : R) :
    e.eval Value.add Value.mul ![some x,some y] =
      some (e.coefficient 0*x + e.coefficient 1*y + e.offset) := by
  have h : ![some x,some y] = fun i => some (![x,y] i) := by
    funext i; fin_cases i <;> rfl
  rw [h, LinearRecurrence.Expr.eval_some]
  simp [Fin.sum_univ_two]

def result (add mul : Option R → Option R → Option R) (a : R)
    (e : LinearRecurrence.Expr R 2) (n : ℕ) : Option R :=
  Tensor.getValue (Tensor.matvecValue add mul 0 3 3
    (Tensor.matrixPowerValue add mul 0 1 3 (some (matrix e)) (some n)) (some ![a,0,1])) (some 0)

theorem result_eq (a : R) (e : LinearRecurrence.Expr R 2) (n : ℕ) :
    result Value.add Value.mul a e n = some (state a e n 0) := by
  rw [result, AffineRecurrence.power_some,
    Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

theorem result_zero (a : R) (e : LinearRecurrence.Expr R 2) :
    result Value.add Value.mul a e 0 = some a := by simp [result_eq, state]

theorem result_succ (a : R) (e : LinearRecurrence.Expr R 2) (n : ℕ) :
    result Value.add Value.mul a e (n+1) =
      e.eval Value.add Value.mul ![result Value.add Value.mul a e n, natCast (some (n+1))] := by
  rw [result_eq, result_eq]
  change some (state a e (n+1) 0) = e.eval Value.add Value.mul ![some (state a e n 0),some ((n+1 : ℕ) : R)]
  rw [eval_some, state_step]
  congr 1
  simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, state_one, state_index]
  ring

noncomputable def step (add mul : Option R → Option R → Option R) (cast : Option ℕ → Option R)
    (a : R) (e : LinearRecurrence.Expr R 2) (g : ℕ → Option R) (n : ℕ) :=
  let p := Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))
  add (Value.mask p (some a)) (Value.mask (Value.not p)
    (e.eval add mul ![(Functions.subN.apply (some n) (some 1)).bind g, cast (some n)]))

theorem step_zero (a : R) (e : LinearRecurrence.Expr R 2) (g : ℕ → Option R) :
    step Value.add Value.mul natCast a e g 0 = some a := by
  simp [step, Function1.apply, Functions.nonzeroZ, Functions.castNZ, Value.not, Value.mask, Value.add]

theorem step_succ (a : R) (e : LinearRecurrence.Expr R 2) (g : ℕ → Option R) (n : ℕ) :
    step Value.add Value.mul natCast a e g (n+1) =
      e.eval Value.add Value.mul ![g n,natCast (some (n+1))] := by
  have ht : Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some (n+1)))) = some false := by
    have hn : (↑n + 1 : ℤ) ≠ 0 := by omega
    simp [Function1.apply, Functions.nonzeroZ, Functions.castNZ, Value.not, hn]
  have hp : Functions.subN.apply (some (n+1)) (some 1) = some n := by
    simp [Function2.apply, Functions.subN]
  unfold step
  rw [ht, hp]
  simp only [Option.some_bind, Value.not, Value.mask, Bool.not_false]
  cases e.eval Value.add Value.mul ![g n,natCast (some (n+1))] <;> simp [Value.add]

theorem solve (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (cast : Option ℕ → Option R) (ha : add=Value.add) (hm : mul=Value.mul) (hc : cast=natCast)
    (a : R) (e : LinearRecurrence.Expr R 2) (hp : ∀ g n, p.eval g n = step add mul cast a e g n) :
    FixedPoint.value p.functional = result add mul a e := by
  subst add; subst mul; subst cast
  funext n
  induction n with
  | zero => rw [← p.unfold, hp, step_zero, result_zero]
  | succ n ih => rw [← p.unfold, hp, step_succ, ih, result_succ]

theorem solve_matrix (p : Recursion.Program ℕ R R) (add mul : Option R → Option R → Option R)
    (cast : Option ℕ → Option R) (ha : add=Value.add) (hm : mul=Value.mul) (hc : cast=natCast)
    (a : R) (e : LinearRecurrence.Expr R 2) (hp : ∀ g n, p.eval g n = step add mul cast a e g n)
    (z o : R) (hz : z=0) (ho : o=1)
    (m : Option (Matrix (Fin 3) (Fin 3) R)) (v : Option (Fin 3 → R))
    (hmat : m=some (matrix e)) (hv : v=some ![a,0,1]) :
    FixedPoint.value p.functional = fun n => Tensor.getValue (Tensor.matvecValue add mul z 3 3
      (Tensor.matrixPowerValue add mul z o 3 m (some n)) v) (some 0) := by
  subst z; subst o; rw [hmat, hv]
  exact solve p add mul cast ha hm hc a e hp

theorem castN : (fun n : Option ℕ => n) = @natCast ℕ _ := by
  funext n; cases n <;> rfl

theorem castZ : Functions.castNZ.apply = @natCast ℤ _ := by
  funext n; cases n <;> simp [natCast, Function1.apply, Functions.castNZ]

end QSym.IndexedRecurrence
