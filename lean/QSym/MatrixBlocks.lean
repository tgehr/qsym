import QSym.AffineRecurrence

namespace QSym.MatrixBlocks

variable {R : Type} [CommSemiring R] {m n : ℕ}

def vector (x : Fin m → R) (y : Fin n → R) : Fin (m+n) → R := Fin.addCases x y

def matrix (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (m+n)) (Fin (m+n)) R :=
  Fin.addCases (fun i => Fin.addCases (a i) (fun _ => 0))
    (fun i => Fin.addCases (fun _ => 0) (b i))

theorem mulVec (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R)
    (x : Fin m → R) (y : Fin n → R) :
    (matrix a b).mulVec (vector x y) = vector (a.mulVec x) (b.mulVec y) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [matrix, vector, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

theorem power_mulVec (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R)
    (x : Fin m → R) (y : Fin n → R) (k : ℕ) :
    (matrix a b ^ k).mulVec (vector x y) = vector ((a^k).mulVec x) ((b^k).mulVec y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, mulVec]
    simp only [pow_succ', ← Matrix.mulVec_mulVec]

def action (add mul : Option R → Option R → Option R) (z o : R) (d : ℕ)
    (a : Option (Matrix (Fin d) (Fin d) R)) (x : Option (Fin d → R)) (k : Option ℕ) :=
  Tensor.matvecValue add mul z d d (Tensor.matrixPowerValue add mul z o d a k) x

theorem tabulate_none (d : ℕ) (h : 0 < d) :
    Tensor.tabulateValue d (fun _ => (none : Option R))=none := by
  cases d with
  | zero => omega
  | succ d => rfl

theorem split_value (hm : 0 < m) (hn : 0 < n)
    (add mul : Option R → Option R → Option R) (ha : add=Value.add) (hu : mul=Value.mul)
    (z o : R) (hz : z=0) (ho : o=1)
    (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R)
    (x : Fin m → R) (y : Fin n → R)
    (c : Option (Matrix (Fin (m+n)) (Fin (m+n)) R)) (v : Option (Fin (m+n) → R))
    (ca : Option (Matrix (Fin m) (Fin m) R)) (cb : Option (Matrix (Fin n) (Fin n) R))
    (vx : Option (Fin m → R)) (vy : Option (Fin n → R))
    (hc : c=some (matrix a b)) (hv : v=some (vector x y))
    (hca : ca=some a) (hcb : cb=some b) (hvx : vx=some x) (hvy : vy=some y) (k : Option ℕ) :
    action add mul z o (m+n) c v k =
      Tensor.tabulateValue (m+n) (Fin.addCases
        (fun i => Tensor.getValue (action add mul z o m ca vx k) (some i.val))
        (fun i => Tensor.getValue (action add mul z o n cb vy k) (some i.val))) := by
  subst add; subst mul; subst z; subst o
  rw [hc,hv,hca,hcb,hvx,hvy]
  cases k with
  | none =>
    change none=Tensor.tabulateValue (m+n)
      (Fin.addCases (fun (_ : Fin m) => (none : Option R)) (fun (_ : Fin n) => none))
    have h : (Fin.addCases (fun (_ : Fin m) => (none : Option R))
        (fun (_ : Fin n) => none)) = (fun (_ : Fin (m+n)) => none) := by
      funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
    rw [h,tabulate_none (m+n) (by omega)]
  | some k =>
    simp only [action]
    rw [AffineRecurrence.power_some, AffineRecurrence.power_some, AffineRecurrence.power_some]
    simp only [Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    simp only [Tensor.getValue, Option.some_bind, Fin.isLt, ↓reduceDIte]
    change some ((matrix a b ^ k).mulVec (vector x y)) =
      Tensor.tabulateValue (m+n) (Fin.addCases
        (fun i => some (((a^k).mulVec x) i)) (fun i => some (((b^k).mulVec y) i)))
    rw [show (Fin.addCases
      (fun i : Fin m => some (((a^k).mulVec x) ⟨i.val,i.isLt⟩))
      (fun i : Fin n => some (((b^k).mulVec y) ⟨i.val,i.isLt⟩))) =
      (fun i => some (vector ((a^k).mulVec x) ((b^k).mulVec y) i)) from by
        funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [vector]]
    rw [Tensor.tabulateValue_some]
    exact congrArg some (power_mulVec a b x y k)

end QSym.MatrixBlocks
