import QSym.Spectral

namespace QSym.RepeatedSpectra

variable {K : Type} [Field K]

def formula (x y r : K) (n : ℕ) : K := (x+(n : K)*(y/r-x))*r^n

theorem generalized_power {d : ℕ} (a : Matrix (Fin d) (Fin d) K)
    (v u : Fin d → K) (r : K) (hr : r≠0)
    (hv : a.mulVec v=r • v+u) (hu : a.mulVec u=r • u) (n : ℕ) :
    (a^n).mulVec v=r^n • (v+((n : K)/r) • u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
      Matrix.mulVec_add, Matrix.mulVec_smul, hv, hu]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
    ring

theorem two (a b c d r x y : K) (hr : r≠0) (ht : a+d=r+r) (hd : a*d-b*c=r*r) (n : ℕ) :
    ((Spectral.matrix a b c d)^n).mulVec ![x,y] =
      ![formula x (a*x+b*y) r n,formula y (c*x+d*y) r n] := by
  have hv : (Spectral.matrix a b c d).mulVec ![x,y] =
      r • ![x,y]+Spectral.part a b c d r x y := by
    ext i
    fin_cases i <;> simp [Spectral.matrix, Spectral.part, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] <;> ring
  rw [generalized_power _ _ _ r hr hv (Spectral.part_eigen a b c d r r x y ht hd) n]
  ext i
  fin_cases i <;> simp [formula, Spectral.part, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, div_eq_mul_inv] <;> field_simp [hr] <;> ring

def value (add mul : Option K → Option K → Option K) (inv : Option K → Option K)
    (pow : Option K → Option ℕ → Option K) (cast : Option ℕ → Option K)
    (neg x y r : Option K) (n : Option ℕ) : Option K :=
  mul (add x (mul (cast n) (add (mul y (inv r)) (mul neg x)))) (pow r n)

def natCast (n : Option ℕ) : Option K := n.map Nat.cast

theorem value_some (x y r : K) (hr : r≠0) (n : ℕ) :
    value Value.add Value.mul Value.inv Spectral.power natCast
      (some (-1)) (some x) (some y) (some r) (some n)=some (formula x y r n) := by
  simp [value, natCast, Spectral.power, Value.add, Value.mul, Value.inv, hr,
    formula, sub_eq_add_neg, div_eq_mul_inv]

theorem nonzero (r : K) (h : Domain.Correct (Value.inv (some r)) (some true)) : r≠0 := by
  intro e; subst r
  simp [Domain.Correct, Value.inv] at h

theorem two_value (add mul : Option K → Option K → Option K) (inv : Option K → Option K)
    (pow : Option K → Option ℕ → Option K) (cast : Option ℕ → Option K)
    (hadd : add=Value.add) (hmul : mul=Value.mul) (hinv : inv=Value.inv)
    (hpow : pow=Spectral.power) (hcast : cast=natCast)
    (zero one : K) (hzero : zero=0) (hone : one=1)
    (a b c d r x y : K) (ar br cr dr rr xr yr neg : Option K)
    (ha : ar=some a) (hb : br=some b) (hc : cr=some c) (hd : dr=some d)
    (hr : rr=some r) (hx : xr=some x) (hy : yr=some y) (hn : neg=some (-1))
    (ht : add ar dr=add rr rr) (hdet : add (mul ar dr) (mul neg (mul br cr))=mul rr rr)
    (hsep : Domain.Correct (inv rr) (some true))
    (m : Option (Matrix (Fin 2) (Fin 2) K)) (v : Option (Fin 2 → K))
    (hmat : m=some ![![a,b],![c,d]]) (hv : v=some ![x,y]) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 2 2 (Tensor.matrixPowerValue add mul zero one 2 m n) v =
      Tensor.consValue (value add mul inv pow cast neg xr (add (mul ar xr) (mul br yr)) rr n)
        (Tensor.consValue (value add mul inv pow cast neg yr (add (mul cr xr) (mul dr yr)) rr n) Tensor.nilValue) := by
  subst zero; subst one; subst add; subst mul; subst inv; subst pow; subst cast
  rw [ha, hb, hc, hd, hr, hx, hy, hn, hmat, hv] at *
  have ht' : a+d=r+r := Option.some.inj ht
  have hd' : a*d-b*c=r*r := by simpa [Value.add, Value.mul, sub_eq_add_neg] using hdet
  have hr' : r≠0 := nonzero r hsep
  cases n with
  | none => simp [Tensor.matrixPowerValue, Tensor.matvecValue, Tensor.consValue, value, natCast,
      Spectral.power, Value.add, Value.mul, Value.inv, hr']
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some (((Spectral.matrix a b c d)^n).mulVec ![x,y]) = _
    rw [two a b c d r x y hr' ht' hd']
    simp only [Value.mul, Value.add, Option.some_bind, Option.map_some, value_some _ _ _ hr']
    rfl

theorem block_value (add mul : Option K → Option K → Option K) (inv : Option K → Option K)
    (pow : Option K → Option ℕ → Option K) (cast : Option ℕ → Option K)
    (hadd : add=Value.add) (hmul : mul=Value.mul) (hinv : inv=Value.inv)
    (hpow : pow=Spectral.power) (hcast : cast=natCast)
    (zero one : K) (hzero : zero=0) (hone : one=1)
    (a b c d r x y z w : K) (ar br cr dr rr xr yr zr wr neg : Option K)
    (ha : ar=some a) (hb : br=some b) (hc : cr=some c) (hd : dr=some d)
    (hr : rr=some r) (hx : xr=some x) (hy : yr=some y)
    (hz : zr=some z) (hw : wr=some w) (hn : neg=some (-1))
    (ht : add ar dr=add rr rr) (hdet : add (mul ar dr) (mul neg (mul br cr))=mul rr rr)
    (hsep : Domain.Correct (inv rr) (some true))
    (m : Option (Matrix (Fin 3) (Fin 3) K)) (v : Option (Fin 3 → K))
    (hmat : m=some (Spectral.block a b c d z)) (hv : v=some ![x,y,w]) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 3 3 (Tensor.matrixPowerValue add mul zero one 3 m n) v =
      Tensor.consValue (value add mul inv pow cast neg xr (add (mul ar xr) (mul br yr)) rr n)
        (Tensor.consValue (value add mul inv pow cast neg yr (add (mul cr xr) (mul dr yr)) rr n)
          (Tensor.consValue (mul (pow zr n) wr) Tensor.nilValue)) := by
  subst zero; subst one; subst add; subst mul; subst inv; subst pow; subst cast
  rw [ha, hb, hc, hd, hr, hx, hy, hz, hw, hn, hmat, hv] at *
  have ht' : a+d=r+r := Option.some.inj ht
  have hd' : a*d-b*c=r*r := by simpa [Value.add, Value.mul, sub_eq_add_neg] using hdet
  have hr' : r≠0 := nonzero r hsep
  cases n with
  | none => simp [Tensor.matrixPowerValue, Tensor.matvecValue, Tensor.consValue, value, natCast,
      Spectral.power, Value.add, Value.mul, Value.inv, hr']
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some ((Spectral.block a b c d z ^ n).mulVec ![x,y,w]) = _
    rw [Spectral.block_power, two a b c d r x y hr' ht' hd']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Value.mul, Value.add, Option.some_bind,
      Option.map_some, value_some _ _ _ hr']
    rfl

theorem castQ : (fun n => Functions.castZQ.apply (Functions.castNZ.apply n))= @natCast ℚ _ := by
  funext n; cases n <;> simp [natCast, Function1.apply, Functions.castZQ, Functions.castNZ]

theorem castR : (fun n => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n)))= @natCast ℝ _ := by
  funext n; cases n <;> simp [natCast, Function1.apply, Functions.castQR, Functions.castZQ, Functions.castNZ]

theorem castC : (fun n => Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))))= @natCast ℂ _ := by
  funext n; cases n <;> simp [natCast, Function1.apply, Functions.castRC, Functions.castQR, Functions.castZQ, Functions.castNZ]

end QSym.RepeatedSpectra
