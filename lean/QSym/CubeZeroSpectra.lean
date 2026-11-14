import QSym.Spectral

namespace QSym.CubeZeroSpectra

variable {R : Type} [CommSemiring R]

def formula (x y z : R) (n : ℕ) : R :=
  ((if n=0 then x else 0)+(if n=1 then y else 0))+(if n=2 then z else 0)

theorem power {d : ℕ} (a : Matrix (Fin d) (Fin d) R) (v : Fin d → R)
    (h : a^3=0) (n : ℕ) :
    (a^n).mulVec v = fun i => formula (v i) (a.mulVec v i) (a.mulVec (a.mulVec v) i) n := by
  cases n with
  | zero => simp [formula]
  | succ n =>
    cases n with
    | zero => simp [formula]
    | succ n =>
      cases n with
      | zero => simp [formula, pow_two, Matrix.mulVec_mulVec]
      | succ n =>
        rw [show n+1+1+1=n+3 by omega, pow_add, h]
        ext i
        simp [formula]

def step (add mul : Option R → Option R → Option R)
    (a : Fin 3 → Fin 3 → Option R) (v : Fin 3 → Option R) (i : Fin 3) : Option R :=
  add (add (mul (a i 0) (v 0)) (mul (a i 1) (v 1))) (mul (a i 2) (v 2))

theorem step_some (a : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) (i : Fin 3) :
    step Value.add Value.mul (fun i j => some (a i j)) (fun i => some (v i)) i =
      some (a.mulVec v i) := by
  simp [step, Value.add, Value.mul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

def square (add mul : Option R → Option R → Option R)
    (a : Fin 3 → Fin 3 → Option R) (i j : Fin 3) : Option R :=
  step add mul a (fun k => a k j) i

theorem square_some (a : Matrix (Fin 3) (Fin 3) R) :
    square Value.add Value.mul (fun i j => some (a i j)) = fun i j => some ((a*a) i j) := by
  ext i j
  simp [square, step_some, Matrix.mul_apply, Matrix.mulVec, dotProduct]

noncomputable def index (n : Option ℕ) (k : ℕ) : Option Bool :=
  Value.and (Functions.leN.apply (some k) n) (Functions.leN.apply n (some k))

theorem index_some (n k : ℕ) : index (some n) k=some (decide (n=k)) := by
  by_cases h : n=k
  · subst n; simp [index, Function2.apply, Functions.leN, Value.and]
  · rcases lt_or_gt_of_ne h with h | h
    · simp [index, Function2.apply, Functions.leN, Value.and, h.ne, Nat.not_le.mpr h]
    · simp [index, Function2.apply, Functions.leN, Value.and, h.ne', Nat.le_of_lt h, Nat.not_le.mpr h]

noncomputable def value (add mul : Option R → Option R → Option R)
    (a : Fin 3 → Fin 3 → Option R) (v : Fin 3 → Option R) (n : Option ℕ) (i : Fin 3) : Option R :=
  add (add (Value.mask (index n 0) (v i)) (Value.mask (index n 1) (step add mul a v i)))
    (Value.mask (index n 2) (step add mul (square add mul a) v i))

theorem mask_some (p : Prop) [Decidable p] (x : R) :
    Value.mask (some (decide p)) (some x) = some (if p then x else 0) := by
  by_cases h : p <;> simp [h, Value.mask]

theorem value_some (a : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) (n : ℕ) (i : Fin 3) :
    value Value.add Value.mul (fun i j => some (a i j)) (fun i => some (v i)) (some n) i =
      some (formula (v i) (a.mulVec v i) (a.mulVec (a.mulVec v) i) n) := by
  simp only [value, square_some, index_some, step_some, mask_some, Value.add]
  simp only [formula, Matrix.mulVec_mulVec]


theorem checked_cube (a : Matrix (Fin 3) (Fin 3) R)
    (h : ∀ i j, step Value.add Value.mul (fun i j => some (a i j))
      (fun k => step Value.add Value.mul (fun i j => some (a i j)) (fun l => some (a l j)) k) i = some 0) :
    a^3=0 := by
  ext i j
  have hi := h i j
  simp only [step_some, Option.some.injEq] at hi
  simpa [pow_succ', Matrix.mul_apply, Matrix.mulVec, dotProduct] using hi

theorem three_value (add mul : Option R → Option R → Option R)
    (hadd : add=Value.add) (hmul : mul=Value.mul)
    (zero one : R) (hzero : zero=0) (hone : one=1)
    (a : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R)
    (ar : Fin 3 → Fin 3 → Option R) (vr : Fin 3 → Option R)
    (ha : ∀ i j, ar i j=some (a i j)) (hv : ∀ i, vr i=some (v i))
    (hcube : ∀ i j, step add mul ar (fun k => step add mul ar (fun l => ar l j) k) i=some 0)
    (m : Option (Matrix (Fin 3) (Fin 3) R)) (w : Option (Fin 3 → R))
    (hmat : m=some a) (hvec : w=some v) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 3 3 (Tensor.matrixPowerValue add mul zero one 3 m n) w =
      Tensor.consValue (value add mul ar vr n 0)
        (Tensor.consValue (value add mul ar vr n 1)
          (Tensor.consValue (value add mul ar vr n 2) Tensor.nilValue)) := by
  subst add; subst mul; subst zero; subst one
  have har : ar=fun i j => some (a i j) := funext (fun i => funext (ha i))
  have hvr : vr=fun i => some (v i) := funext hv
  rw [har] at hcube
  rw [hmat, hvec, har, hvr]
  cases n with
  | none => rfl
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some ((a^n).mulVec v) = _
    rw [power a v (checked_cube a hcube)]
    simp only [value_some, Tensor.consValue, Tensor.nilValue, Option.some_bind, Option.map_some]
    congr 1
    ext i
    fin_cases i <;> rfl

noncomputable def compactValue (add : Option R → Option R → Option R)
    (v first second : Fin 3 → Option R) (n : Option ℕ) (i : Fin 3) : Option R :=
  add (add (Value.mask (index n 0) (v i)) (Value.mask (index n 1) (first i)))
    (Value.mask (index n 2) (second i))

theorem three_compact_value (add mul : Option R → Option R → Option R)
    (hadd : add=Value.add) (hmul : mul=Value.mul)
    (zero one : R) (hzero : zero=0) (hone : one=1)
    (a : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R)
    (ar : Fin 3 → Fin 3 → Option R) (vr : Fin 3 → Option R)
    (ha : ∀ i j, ar i j=some (a i j)) (hv : ∀ i, vr i=some (v i))
    (hcube : ∀ i j, step add mul ar (fun k => step add mul ar (fun l => ar l j) k) i=some 0)
    (first second : Fin 3 → Option R)
    (hfirst : ∀ i, step add mul ar vr i=first i)
    (hsecond : ∀ i, step add mul (square add mul ar) vr i=second i)
    (m : Option (Matrix (Fin 3) (Fin 3) R)) (w : Option (Fin 3 → R))
    (hmat : m=some a) (hvec : w=some v) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 3 3 (Tensor.matrixPowerValue add mul zero one 3 m n) w =
      Tensor.consValue (compactValue add vr first second n 0)
        (Tensor.consValue (compactValue add vr first second n 1)
          (Tensor.consValue (compactValue add vr first second n 2) Tensor.nilValue)) := by
  rw [three_value add mul hadd hmul zero one hzero hone a v ar vr ha hv hcube m w hmat hvec n]
  simp only [value, compactValue, hfirst, hsecond]

end QSym.CubeZeroSpectra
