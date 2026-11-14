import QSym.IndexedRecurrence
import QSym.AxiomCheck

set_option maxHeartbeats 800000

namespace QSym.CFinite
variable {R S : Type} [CommSemiring R] [CommSemiring S]

-- A concrete finite state realization. No root finding or division is required.
structure Sequence (R : Type) where
  size : ℕ
  matrix : Matrix (Fin size) (Fin size) R
  initial : Fin size → R
  output : Fin size → R

def dot : {d : ℕ} → (Fin d → R) → (Fin d → R) → R
  | 0, _, _ => 0
  | _+1, x, y => x 0 * y 0 + dot (fun i => x i.succ) (fun i => y i.succ)

theorem dot_eq {d : ℕ} (x y : Fin d → R) : dot x y = ∑ i, x i*y i := by
  induction d with
  | zero => simp [dot]
  | succ d ih => rw [dot, Fin.sum_univ_succ, ih]

def Sequence.state (s : Sequence R) (n : ℕ) := (s.matrix ^ n).mulVec s.initial
def Sequence.value (s : Sequence R) (n : ℕ) := dot s.output (s.state n)

theorem Sequence.state_zero (s : Sequence R) : s.state 0 = s.initial := by simp [state]
theorem Sequence.state_succ (s : Sequence R) (n : ℕ) : s.state (n+1) = s.matrix.mulVec (s.state n) := by
  rw [state, pow_succ', ← Matrix.mulVec_mulVec]; rfl

def Sequence.zero : Sequence R := ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
def Sequence.constant (c : R) : Sequence R := ⟨1, ![![1]], ![c], ![1]⟩
def Sequence.index : Sequence R := ⟨2, ![![1,1],![0,1]], ![0,1], ![1,0]⟩
def Sequence.geometric (a : R) : Sequence R := ⟨1, ![![a]], ![1], ![1]⟩

def Sequence.add (s t : Sequence R) : Sequence R :=
  ⟨s.size+t.size,
    Fin.addCases (fun i => Fin.addCases (s.matrix i) (fun _ => 0))
      (fun i => Fin.addCases (fun _ => 0) (t.matrix i)),
    Fin.addCases s.initial t.initial, Fin.addCases s.output t.output⟩

def Sequence.mul (s t : Sequence R) : Sequence R :=
  ⟨s.size*t.size, fun i j => s.matrix i.divNat j.divNat * t.matrix i.modNat j.modNat,
    fun i => s.initial i.divNat * t.initial i.modNat,
    fun i => s.output i.divNat * t.output i.modNat⟩

def Sequence.left (c : R) (s : Sequence R) : Sequence R :=
  {s with output := fun i => c*s.output i}
def Sequence.right (s : Sequence R) (c : R) : Sequence R :=
  {s with output := fun i => s.output i*c}
def Sequence.map (s : Sequence R) (f : R →+* S) : Sequence S :=
  ⟨s.size, fun i j => f (s.matrix i j), fun i => f (s.initial i), fun i => f (s.output i)⟩

@[simp] theorem Sequence.zero_value (n : ℕ) : (zero : Sequence R).value n = 0 := rfl
@[simp] theorem Sequence.constant_value (c : R) (n : ℕ) : (constant c).value n = c := by
  have h : (constant c).state n = ![c] := by
    induction n with
    | zero => simp [state_zero, constant]
    | succ n ih => rw [state_succ, ih]; funext i; fin_cases i; simp [constant, Matrix.mulVec, dotProduct]
  rw [value, h]; simp [constant, dot]

@[simp] theorem Sequence.index_value (n : ℕ) : (index : Sequence R).value n = (n : R) := by
  have h : (index : Sequence R).state n = ![(n:R),1] := by
    induction n with
    | zero => simp [state_zero, index]
    | succ n ih =>
      rw [state_succ, ih]; funext i; fin_cases i <;>
        simp [index, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [value, h]; simp [index, dot]

@[simp] theorem Sequence.geometric_value (a : R) (n : ℕ) : (geometric a).value n = a^n := by
  have h : (geometric a).state n = ![a^n] := by
    induction n with
    | zero => simp [state_zero, geometric]
    | succ n ih => rw [state_succ, ih]; funext i; fin_cases i; simp [geometric, Matrix.mulVec, dotProduct, pow_succ']
  rw [value, h]; simp [geometric, dot]

theorem sum_product {m n : ℕ} (f : Fin (m*n) → R) :
    (∑ i, f i) = ∑ i : Fin m, ∑ j : Fin n, f (finProdFinEquiv (i,j)) := by
  exact (Equiv.sum_comp finProdFinEquiv f).symm.trans (Fintype.sum_prod_type _)

theorem Sequence.add_state (s t : Sequence R) (n : ℕ) :
    (s.add t).state n = Fin.addCases (s.state n) (t.state n) := by
  induction n with
  | zero => simp [state_zero, add]
  | succ n ih =>
    rw [state_succ, ih, state_succ, state_succ]
    funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [add, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

theorem Sequence.add_value (s t : Sequence R) (n : ℕ) :
    (s.add t).value n = s.value n + t.value n := by
  rw [value, add_state]
  simp [value, dot_eq, add, Fin.sum_univ_add]

@[simp] theorem product_div {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i,j)).divNat = i := by
  exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i,j))
@[simp] theorem product_mod {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i,j)).modNat = j := by
  exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i,j))

-- The empty state represents zero. Eliminate it before composing a solver
-- matrix, avoiding dependent-index transports through zero-sized blocks.
def Sequence.plus (s t : Sequence R) : Sequence R :=
  if s.size=0 then t else if t.size=0 then s else s.add t

theorem Sequence.empty_value (s : Sequence R) (h : s.size=0) (n : ℕ) : s.value n=0 := by
  rcases s with ⟨d,m,v,o⟩
  change d=0 at h
  subst d
  rfl

theorem Sequence.plus_value (s t : Sequence R) (n : ℕ) :
    (s.plus t).value n=s.value n+t.value n := by
  unfold plus
  split_ifs with hs ht
  · rw [s.empty_value hs]; simp
  · rw [t.empty_value ht]; simp
  · exact s.add_value t n

theorem Sequence.mul_state (s t : Sequence R) (n : ℕ) :
    (s.mul t).state n = fun i => s.state n i.divNat * t.state n i.modNat := by
  induction n with
  | zero => simp [state_zero, mul]
  | succ n ih =>
    rw [state_succ, ih, state_succ, state_succ]
    funext i
    simp only [mul, Matrix.mulVec, dotProduct]
    rw [sum_product]
    simp only [product_div, product_mod]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, mul_mul_mul_comm]

theorem Sequence.mul_value (s t : Sequence R) (n : ℕ) :
    (s.mul t).value n = s.value n * t.value n := by
  rw [value, mul_state]
  simp only [value, dot_eq, mul]
  rw [sum_product]
  simp only [product_div, product_mod]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, mul_mul_mul_comm]

theorem Sequence.left_value (c : R) (s : Sequence R) (n : ℕ) :
    (s.left c).value n = c*s.value n := by simp [left, value, state, dot_eq, Finset.mul_sum, mul_assoc]
theorem Sequence.right_value (s : Sequence R) (c : R) (n : ℕ) :
    (s.right c).value n = s.value n*c := by
  simp only [right, value, state, dot_eq]
  rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

theorem Sequence.map_state (s : Sequence R) (f : R →+* S) (n : ℕ) :
    (s.map f).state n = fun i => f (s.state n i) := by
  induction n with
  | zero => simp [state_zero, map]
  | succ n ih => rw [state_succ, ih, state_succ]; funext i; simp [map, Matrix.mulVec, dotProduct, map_sum, map_mul]
theorem Sequence.map_value (s : Sequence R) (f : R →+* S) (n : ℕ) :
    (s.map f).value n = f (s.value n) := by
  rw [value, map_state]; simp [value, dot_eq, map, map_sum, map_mul]

def Sequence.power (s : Sequence R) : ℕ → Sequence R
  | 0 => .constant 1
  | n+1 => s.mul (s.power n)
theorem Sequence.power_value (s : Sequence R) (k n : ℕ) : (s.power k).value n = s.value n ^ k := by
  induction k with
  | zero => simp [power]
  | succ k ih => rw [power, mul_value, ih, pow_succ']

theorem constant_eq (c : R) (n : ℕ) {v : Option R} (h : v=some c) :
    v=some ((Sequence.constant c).value n) := by simpa using h

theorem index_eq (n : ℕ) {v : Option R} (h : v=some (n:R)) :
    v=some ((Sequence.index : Sequence R).value n) := by simpa using h

theorem geometric_eq (op : Option R → Option ℕ → Option R)
    (hop : ∀ a n, op (some a) (some n) = some (a^n))
    (a : R) (n : ℕ) {v : Option R} (h : v=some a) :
    op v (some n)=some ((Sequence.geometric a).value n) := by rw [h, hop, Sequence.geometric_value]

theorem add_eq (op : Option R → Option R → Option R)
    (hop : ∀ a b, op (some a) (some b) = some (a+b))
    (s t : Sequence R) (n : ℕ) {a b : Option R}
    (ha : a=some (s.value n)) (hb : b=some (t.value n)) :
    op a b=some ((s.add t).value n) := by rw [ha, hb, hop, Sequence.add_value]

theorem mul_eq (op : Option R → Option R → Option R)
    (hop : ∀ a b, op (some a) (some b) = some (a*b))
    (s t : Sequence R) (n : ℕ) {a b : Option R}
    (ha : a=some (s.value n)) (hb : b=some (t.value n)) :
    op a b=some ((s.mul t).value n) := by rw [ha, hb, hop, Sequence.mul_value]

theorem power_eq (op : Option R → Option R) (k : ℕ)
    (hop : ∀ a, op (some a) = some (a^k))
    (s : Sequence R) (n : ℕ) {a : Option R} (ha : a=some (s.value n)) :
    op a=some ((s.power k).value n) := by rw [ha, hop, Sequence.power_value]

theorem map_eq (f : R →+* S) (op : Option R → Option S)
    (hop : ∀ a, op (some a)=some (f a))
    (s : Sequence R) (n : ℕ) {a : Option R} (ha : a=some (s.value n)) :
    op a=some ((s.map f).value n) := by rw [ha, hop, Sequence.map_value]

def Sequence.coordinate {d : ℕ} (m : Matrix (Fin d) (Fin d) R) (v : Fin d → R) (i : Fin d) : Sequence R :=
  ⟨d, m, v, fun j => if j=i then 1 else 0⟩
theorem Sequence.coordinate_value {d : ℕ} (m : Matrix (Fin d) (Fin d) R) (v : Fin d → R) (i : Fin d) (n : ℕ) :
    (coordinate m v i).value n = (m^n).mulVec v i := by
  simp [coordinate, value, state, dot_eq]

theorem coordinate_eq (add mul : Option R → Option R → Option R)
    (ha : add=Value.add) (hm : mul=Value.mul) (z o : R) (hz : z=0) (ho : o=1)
    (d : ℕ) (m : Option (Matrix (Fin d) (Fin d) R)) (v : Option (Fin d → R))
    (M : Matrix (Fin d) (Fin d) R) (V : Fin d → R) (i : Fin d)
    (hmat : m=some M) (hv : v=some V) (n : ℕ) :
    Tensor.getValue (Tensor.matvecValue add mul z d d
      (Tensor.matrixPowerValue add mul z o d m (some n)) v) (some i.val) =
      some ((Sequence.coordinate M V i).value n) := by
  subst add; subst mul; subst z; subst o; rw [hmat, hv, AffineRecurrence.power_some,
    Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
  simp [Tensor.getValue, i.isLt, Sequence.coordinate_value, Matrix.mulVec, dotProduct]

#qsym_check_axioms Sequence.add_value
#qsym_check_axioms Sequence.mul_value
#qsym_check_axioms Sequence.map_value
#qsym_check_axioms Sequence.power_value
#qsym_check_axioms coordinate_eq

end QSym.CFinite
