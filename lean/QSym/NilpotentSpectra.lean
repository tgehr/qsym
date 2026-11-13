import QSym.Spectral

namespace QSym.NilpotentSpectra

variable {K : Type} [Field K]

def formula (x y : K) (n : ℕ) : K :=
  (if n=0 then x else 0)+(if n=1 then y else 0)

theorem square_zero (a b c d : K) (ht : a+d=0) (hd : a*d-b*c=0) :
    Spectral.matrix a b c d ^ 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Spectral.matrix, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination a*ht-hd
  · linear_combination b*ht
  · linear_combination c*ht
  · linear_combination d*ht-hd

theorem two (a b c d x y : K) (ht : a+d=0) (hd : a*d-b*c=0) (n : ℕ) :
    ((Spectral.matrix a b c d)^n).mulVec ![x,y] =
      ![formula x (a*x+b*y) n,formula y (c*x+d*y) n] := by
  cases n with
  | zero => simp [formula]
  | succ n =>
    cases n with
    | zero =>
      ext i
      fin_cases i <;> simp [formula, Spectral.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    | succ n =>
      rw [show n+1+1=n+2 by omega, pow_add, square_zero a b c d ht hd]
      ext i
      fin_cases i <;> simp [formula]

noncomputable def value (add : Option K → Option K → Option K)
    (x y : Option K) (n : Option ℕ) : Option K :=
  add (Value.mask (Value.not (Functions.nonzeroN.apply n)) x)
    (Value.mask (Value.and (Functions.leN.apply (some 1) n)
      (Functions.leN.apply n (some 1))) y)

theorem value_some (x y : K) (n : ℕ) :
    value Value.add (some x) (some y) (some n)=some (formula x y n) := by
  simp only [value, Function1.apply, Function2.apply, Functions.nonzeroN, Functions.leN]
  by_cases h0 : n=0
  · subst n; simp [Value.not, Value.and, Value.mask, Value.add, formula]
  · by_cases h1 : n=1
    · subst n; simp [Value.not, Value.and, Value.mask, Value.add, formula]
    · have hn : 1<n := by omega
      simp [Value.not, Value.and, Value.mask, Value.add, formula, h0, h1, Nat.not_le.mpr hn, Nat.le_of_lt hn]

theorem two_value (add mul : Option K → Option K → Option K)
    (pow : Option K → Option ℕ → Option K)
    (hadd : add=Value.add) (hmul : mul=Value.mul)
    (hpow : pow=Spectral.power)
    (zero one : K) (hzero : zero=0) (hone : one=1)
    (a b c d r x y : K) (ar br cr dr rr xr yr neg : Option K)
    (ha : ar=some a) (hb : br=some b) (hc : cr=some c) (hd : dr=some d)
    (hr : rr=some r) (hx : xr=some x) (hy : yr=some y) (hn : neg=some (-1))
    (ht : add ar dr=add rr rr) (hdet : add (mul ar dr) (mul neg (mul br cr))=mul rr rr)
    (hroot : r=0)
    (m : Option (Matrix (Fin 2) (Fin 2) K)) (v : Option (Fin 2 → K))
    (hmat : m=some ![![a,b],![c,d]]) (hv : v=some ![x,y]) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 2 2 (Tensor.matrixPowerValue add mul zero one 2 m n) v =
      Tensor.consValue (value add xr (add (mul ar xr) (mul br yr)) n)
        (Tensor.consValue (value add yr (add (mul cr xr) (mul dr yr)) n) Tensor.nilValue) := by
  subst zero; subst one; subst add; subst mul; subst pow; rw [hroot] at hr
  rw [ha, hb, hc, hd, hr, hx, hy, hn, hmat, hv] at *
  have ht' : a+d=0 := by simpa [Value.add] using ht
  have hd' : a*d-b*c=0 := by simpa [Value.add, Value.mul, sub_eq_add_neg] using hdet
  cases n with
  | none => rfl
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some (((Spectral.matrix a b c d)^n).mulVec ![x,y]) = _
    rw [two a b c d x y ht' hd']
    simp only [Value.mul, Value.add, Option.some_bind, Option.map_some, value_some]
    rfl

theorem block_value (add mul : Option K → Option K → Option K)
    (pow : Option K → Option ℕ → Option K)
    (hadd : add=Value.add) (hmul : mul=Value.mul)
    (hpow : pow=Spectral.power)
    (zero one : K) (hzero : zero=0) (hone : one=1)
    (a b c d r x y z w : K) (ar br cr dr rr xr yr zr wr neg : Option K)
    (ha : ar=some a) (hb : br=some b) (hc : cr=some c) (hd : dr=some d)
    (hr : rr=some r) (hx : xr=some x) (hy : yr=some y)
    (hz : zr=some z) (hw : wr=some w) (hn : neg=some (-1))
    (ht : add ar dr=add rr rr) (hdet : add (mul ar dr) (mul neg (mul br cr))=mul rr rr)
    (hroot : r=0)
    (m : Option (Matrix (Fin 3) (Fin 3) K)) (v : Option (Fin 3 → K))
    (hmat : m=some (Spectral.block a b c d z)) (hv : v=some ![x,y,w]) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 3 3 (Tensor.matrixPowerValue add mul zero one 3 m n) v =
      Tensor.consValue (value add xr (add (mul ar xr) (mul br yr)) n)
        (Tensor.consValue (value add yr (add (mul cr xr) (mul dr yr)) n)
          (Tensor.consValue (mul (pow zr n) wr) Tensor.nilValue)) := by
  subst zero; subst one; subst add; subst mul; subst pow; rw [hroot] at hr
  rw [ha, hb, hc, hd, hr, hx, hy, hz, hw, hn, hmat, hv] at *
  have ht' : a+d=0 := by simpa [Value.add] using ht
  have hd' : a*d-b*c=0 := by simpa [Value.add, Value.mul, sub_eq_add_neg] using hdet
  cases n with
  | none => rfl
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some ((Spectral.block a b c d z ^ n).mulVec ![x,y,w]) = _
    rw [Spectral.block_power, two a b c d x y ht' hd']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Value.mul, Value.add, Option.some_bind,
      Option.map_some, value_some]
    rfl

end QSym.NilpotentSpectra
