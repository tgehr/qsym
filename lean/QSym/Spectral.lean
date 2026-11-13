import QSym.LinearRecurrence

namespace QSym.Spectral

variable {R : Type} [CommSemiring R] {d : ℕ}

theorem eigen_power (a : Matrix (Fin d) (Fin d) R) (v : Fin d → R) (r : R)
    (h : a.mulVec v = r • v) (n : ℕ) : (a^n).mulVec v = r^n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul]
    simp [pow_succ]

theorem diagonal (a v : Fin d → R) (n : ℕ) :
    (Matrix.diagonal a ^ n).mulVec v = fun i => a i ^ n * v i := by
  rw [Matrix.diagonal_pow]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]

def power (x : Option R) (n : Option ℕ) : Option R := x.bind (fun x => n.map (fun n => x^n))

theorem some_of_domain {A : Type} (fallback : A) (x : Option A)
    (h : Domain.Correct x (some true)) : x=some (x.getD fallback) := by
  cases x <;> simp_all [Domain.Correct]

theorem diagonal_value (add mul : Option R → Option R → Option R) (pow : Option R → Option ℕ → Option R)
    (ha : add=Value.add) (hm : mul=Value.mul) (hp : pow=power)
    (zero one : R) (hz : zero=0) (ho : one=1)
    (a v : Fin (d+1) → R) (ar vr : Fin (d+1) → Option R)
    (hda : ∀ i, ar i=some (a i)) (hdv : ∀ i, vr i=some (v i))
    (m : Option (Matrix (Fin (d+1)) (Fin (d+1)) R)) (w : Option (Fin (d+1) → R))
    (hmat : m=some (Matrix.diagonal a)) (hv : w=some v) (n : Option ℕ) :
    Tensor.matvecValue add mul zero (d+1) (d+1) (Tensor.matrixPowerValue add mul zero one (d+1) m n) w =
      Tensor.tabulateValue (d+1) (fun i => mul (pow (ar i) n) (vr i)) := by
  subst zero; subst one; subst add; subst mul; subst pow; rw [hmat, hv]
  simp_rw [hda, hdv]
  cases n with
  | none => rfl
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some ((Matrix.diagonal a ^ n).mulVec v) = _
    rw [diagonal]
    simpa [power, Value.mul] using (Tensor.tabulateValue_some (d+1) (fun i => a i^n*v i)).symm

section Field
variable {K : Type} [Field K]

def matrix (a b c d : K) : Matrix (Fin 2) (Fin 2) K := ![![a,b],![c,d]]

def formula (x y r s : K) (n : ℕ) : K :=
  (y-s*x)/(r-s)*r^n + (r*x-y)/(r-s)*s^n

def part (a b c d s x y : K) : Fin 2 → K := ![(a-s)*x+b*y,c*x+(d-s)*y]

theorem part_eigen (a b c d r s x y : K) (ht : a+d=r+s) (hd : a*d-b*c=r*s) :
    (matrix a b c d).mulVec (part a b c d s x y) =
      r • part a b c d s x y := by
  ext i
  fin_cases i <;> simp [part, matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · linear_combination (a*x+b*y)*ht-x*hd
  · linear_combination (c*x+d*y)*ht-y*hd

theorem two (a b c d r s x y : K) (hr : r≠s) (ht : a+d=r+s) (hd : a*d-b*c=r*s) (n : ℕ) :
    ((matrix a b c d)^n).mulVec ![x,y] =
      ![formula x (a*x+b*y) r s n,formula y (c*x+d*y) r s n] := by
  have hv : (![x,y] : Fin 2 → K) = (r-s)⁻¹ • (part a b c d s x y - part a b c d r x y) := by
    ext i
    fin_cases i <;> simp [part, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] <;>
      field_simp [sub_ne_zero.mpr hr] <;> ring
  rw [hv, Matrix.mulVec_smul, Matrix.mulVec_sub,
    eigen_power (matrix a b c d) _ r (part_eigen a b c d r s x y ht hd) n,
    eigen_power (matrix a b c d) _ s (part_eigen a b c d s r x y (ht.trans (add_comm _ _)) (hd.trans (mul_comm _ _))) n]
  ext i
  fin_cases i <;> simp [formula, part, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, div_eq_mul_inv] <;> ring

def block (a b c d z : K) : Matrix (Fin 3) (Fin 3) K := ![![a,b,0],![c,d,0],![0,0,z]]

theorem block_power (a b c d z x y w : K) (n : ℕ) :
    (block a b c d z ^ n).mulVec ![x,y,w] =
      ![((matrix a b c d)^n).mulVec ![x,y] 0,
        ((matrix a b c d)^n).mulVec ![x,y] 1,z^n*w] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    simp only [pow_succ', ← Matrix.mulVec_mulVec]
    ext i
    fin_cases i <;> simp [block, matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, pow_succ'] <;> ring

def value (add mul : Option K → Option K → Option K) (inv : Option K → Option K)
    (pow : Option K → Option ℕ → Option K) (neg x y r s : Option K) (n : Option ℕ) : Option K :=
  add (mul (mul (add y (mul neg (mul s x))) (inv (add r (mul neg s)))) (pow r n))
    (mul (mul (add (mul r x) (mul neg y)) (inv (add r (mul neg s)))) (pow s n))


theorem value_some (x y r s : K) (hr : r≠s) (n : ℕ) :
    value Value.add Value.mul Value.inv power (some (-1)) (some x) (some y) (some r) (some s) (some n) =
      some (formula x y r s n) := by
  simp [value, power, Value.add, Value.mul, Value.inv, formula, sub_eq_add_neg, div_eq_mul_inv,
    show r+-s≠0 by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hr]

theorem checked_eq (add mul : Option K → Option K → Option K)
    (ha : add=Value.add) (hm : mul=Value.mul) (neg x y : Option K) (hn : neg=some (-1))
    (h : add x (mul neg y)=some 0) : x=y := by
  subst add; subst mul; subst neg
  cases x <;> cases y <;> simp [Value.add, Value.mul] at h ⊢
  simpa [← sub_eq_add_neg, sub_eq_zero] using h

theorem separated (r s : K) (h : Domain.Correct (Value.inv (some (r+(-1)*s))) (some true)) : r≠s := by
  intro e; subst s
  simp [Domain.Correct, Value.inv] at h

theorem two_value (add mul : Option K → Option K → Option K) (inv : Option K → Option K)
    (pow : Option K → Option ℕ → Option K)
    (hadd : add=Value.add) (hmul : mul=Value.mul) (hinv : inv=Value.inv) (hpow : pow=power)
    (zero one : K) (hzero : zero=0) (hone : one=1)
    (a b c d r s x y : K) (ar br cr dr rr sr xr yr neg : Option K)
    (ha : ar=some a) (hb : br=some b) (hc : cr=some c) (hd : dr=some d)
    (hr : rr=some r) (hs : sr=some s) (hx : xr=some x) (hy : yr=some y) (hn : neg=some (-1))
    (ht : add ar dr=add rr sr) (hdet : add (mul ar dr) (mul neg (mul br cr))=mul rr sr)
    (hsep : Domain.Correct (inv (add rr (mul neg sr))) (some true))
    (m : Option (Matrix (Fin 2) (Fin 2) K)) (v : Option (Fin 2 → K))
    (hmat : m=some ![![a,b],![c,d]]) (hv : v=some ![x,y]) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 2 2 (Tensor.matrixPowerValue add mul zero one 2 m n) v =
      Tensor.consValue (value add mul inv pow neg xr (add (mul ar xr) (mul br yr)) rr sr n)
        (Tensor.consValue (value add mul inv pow neg yr (add (mul cr xr) (mul dr yr)) rr sr n) Tensor.nilValue) := by
  subst zero; subst one; subst add; subst mul; subst inv; subst pow
  rw [ha, hb, hc, hd, hr, hs, hx, hy, hn, hmat, hv] at *
  have ht' : a+d=r+s := Option.some.inj ht
  have hd' : a*d-b*c=r*s := by simpa [Value.add, Value.mul, sub_eq_add_neg] using hdet
  have hrs : r≠s := separated r s hsep
  cases n with
  | none =>
    simp [Tensor.matrixPowerValue, Tensor.matvecValue, Tensor.consValue, value, power, Value.add, Value.mul, Value.inv, show r+-s≠0 by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hrs]
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some (((matrix a b c d)^n).mulVec ![x,y]) = _
    rw [two a b c d r s x y hrs ht' hd']
    simp only [Value.mul, Value.add, Option.some_bind, Option.map_some, value_some _ _ _ _ hrs]
    rfl

theorem block_value (add mul : Option K → Option K → Option K) (inv : Option K → Option K)
    (pow : Option K → Option ℕ → Option K)
    (hadd : add=Value.add) (hmul : mul=Value.mul) (hinv : inv=Value.inv) (hpow : pow=power)
    (zero one : K) (hzero : zero=0) (hone : one=1)
    (a b c d r s x y z w : K) (ar br cr dr rr sr xr yr zr wr neg : Option K)
    (ha : ar=some a) (hb : br=some b) (hc : cr=some c) (hd : dr=some d)
    (hr : rr=some r) (hs : sr=some s) (hx : xr=some x) (hy : yr=some y)
    (hz : zr=some z) (hw : wr=some w) (hn : neg=some (-1))
    (ht : add ar dr=add rr sr) (hdet : add (mul ar dr) (mul neg (mul br cr))=mul rr sr)
    (hsep : Domain.Correct (inv (add rr (mul neg sr))) (some true))
    (m : Option (Matrix (Fin 3) (Fin 3) K)) (v : Option (Fin 3 → K))
    (hmat : m=some (block a b c d z)) (hv : v=some ![x,y,w]) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 3 3 (Tensor.matrixPowerValue add mul zero one 3 m n) v =
      Tensor.consValue (value add mul inv pow neg xr (add (mul ar xr) (mul br yr)) rr sr n)
        (Tensor.consValue (value add mul inv pow neg yr (add (mul cr xr) (mul dr yr)) rr sr n)
          (Tensor.consValue (mul (pow zr n) wr) Tensor.nilValue)) := by
  subst zero; subst one; subst add; subst mul; subst inv; subst pow
  rw [ha, hb, hc, hd, hr, hs, hx, hy, hz, hw, hn, hmat, hv] at *
  have ht' : a+d=r+s := Option.some.inj ht
  have hd' : a*d-b*c=r*s := by simpa [Value.add, Value.mul, sub_eq_add_neg] using hdet
  have hrs : r≠s := separated r s hsep
  cases n with
  | none =>
    simp [Tensor.matrixPowerValue, Tensor.matvecValue, Tensor.consValue, value, power, Value.add, Value.mul, Value.inv,
      show r+-s≠0 by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hrs]
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some ((block a b c d z ^ n).mulVec ![x,y,w]) = _
    rw [block_power, two a b c d r s x y hrs ht' hd']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Value.mul, Value.add, Option.some_bind, Option.map_some,
      value_some _ _ _ _ hrs]
    rfl

end Field

theorem minusR : some (((-1 : ℤ) : ℝ)) = some (-1 : ℝ) := by simp
theorem minusC : some (((-1 : ℤ) : ℂ)+((0 : ℤ) : ℂ)*Complex.I) = some (-1 : ℂ) := by simp

theorem invQ : Functions.invQ.apply = @Value.inv ℚ _ _ := by
  funext x; cases x <;> simp [Function1.apply, Functions.invQ, Value.inv]

theorem powN : Functions.powNN.apply = @power ℕ _ := by
  funext x n; cases x <;> cases n <;> simp [Function2.apply, Functions.powNN, power]
theorem powZ : Functions.powZN.apply = @power ℤ _ := by
  funext x n; cases x <;> cases n <;> simp [Function2.apply, Functions.powZN, power]

theorem powQ : Functions.powQN.apply = @power ℚ _ := by
  funext x n; cases x <;> cases n <;> simp [Function2.apply, Functions.powQN, power]
theorem powR : Functions.powRN.apply = @power ℝ _ := by
  funext x n; cases x <;> cases n <;> simp [Function2.apply, Functions.powRN, power]
theorem powC : Functions.powCN.apply = @power ℂ _ := by
  funext x n; cases x <;> cases n <;> simp [Function2.apply, Functions.powCN, power]

end QSym.Spectral
