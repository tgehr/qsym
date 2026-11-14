import QSym.ZeroRootSpectra
import QSym.RepeatedSpectra

namespace QSym.JordanSpectra
variable {K : Type} [Field K]

theorem decomposition (a : Matrix (Fin 3) (Fin 3) K) (v : Fin 3 → K)
    (r s : K) (c : Fin 3 → Fin 3 → K) (hs : s≠0)
    (hv : ∀ i, c 0 i+c 1 i=v i)
    (h0 : a.mulVec (c 0)=r • c 0)
    (h1 : a.mulVec (c 1)=s • c 1+c 2)
    (h2 : a.mulVec (c 2)=s • c 2) (n : ℕ) :
    (a^n).mulVec v = fun i => r^n*c 0 i+s^n*(c 1 i+(n : K)*(s⁻¹*c 2 i)) := by
  rw [show v=c 0+c 1 from funext (fun i => (hv i).symm), Matrix.mulVec_add,
    Spectral.eigen_power a (c 0) r h0,
    RepeatedSpectra.generalized_power a (c 1) (c 2) s hs h1 h2]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_assoc]

def value (add mul : Option K → Option K → Option K) (inv : Option K → Option K)
    (pow : Option K → Option ℕ → Option K) (cast : Option ℕ → Option K)
    (r : Fin 3 → Option K) (c : Fin 3 → Fin 3 → Option K) (n : Option ℕ) (i : Fin 3) :=
  add (mul (pow (r 0) n) (c 0 i))
    (mul (pow (r 1) n) (add (c 1 i) (mul (cast n) (mul (inv (r 1)) (c 2 i)))))

theorem three_value (add mul : Option K → Option K → Option K) (inv : Option K → Option K)
    (pow : Option K → Option ℕ → Option K) (cast : Option ℕ → Option K)
    (hadd : add=Value.add) (hmul : mul=Value.mul) (hinv : inv=Value.inv)
    (hpow : pow=Spectral.power) (hcast : cast=RepeatedSpectra.natCast)
    (zero one : K) (hzero : zero=0) (hone : one=1)
    (a : Matrix (Fin 3) (Fin 3) K) (v r : Fin 3 → K) (c : Fin 3 → Fin 3 → K)
    (ar : Fin 3 → Fin 3 → Option K) (vr rr : Fin 3 → Option K)
    (cr : Fin 3 → Fin 3 → Option K)
    (ha : ∀ i j, ar i j=some (a i j)) (hv : ∀ i, vr i=some (v i))
    (hr : ∀ i, rr i=some (r i)) (hc : ∀ i j, cr i j=some (c i j))
    (hs : ∀ i, add (cr 0 i) (cr 1 i)=vr i)
    (he : ∀ j i, CubeZeroSpectra.step add mul ar (cr j) i=
      if j=1 then add (mul (rr 1) (cr j i)) (cr 2 i)
      else mul (rr (if j=0 then 0 else 1)) (cr j i))
    (hsep : Domain.Correct (inv (rr 1)) (some true))
    (m : Option (Matrix (Fin 3) (Fin 3) K)) (w : Option (Fin 3 → K))
    (hmat : m=some a) (hvec : w=some v) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 3 3 (Tensor.matrixPowerValue add mul zero one 3 m n) w =
      Tensor.consValue (value add mul inv pow cast rr cr n 0)
        (Tensor.consValue (value add mul inv pow cast rr cr n 1)
          (Tensor.consValue (value add mul inv pow cast rr cr n 2) Tensor.nilValue)) := by
  subst add; subst mul; subst inv; subst pow; subst cast; subst zero; subst one
  have har : ar=fun i j => some (a i j) := funext (fun i => funext (ha i))
  have hvr : vr=fun i => some (v i) := funext hv
  have hrr : rr=fun i => some (r i) := funext hr
  have hcr : cr=fun i j => some (c i j) := funext (fun i => funext (hc i))
  rw [har, hcr, hrr] at he
  rw [hcr, hvr] at hs
  rw [hrr] at hsep
  have hr' : r 1≠0 := RepeatedSpectra.nonzero (r 1) hsep
  have hs' : ∀ i, c 0 i+c 1 i=v i := fun i => Option.some.inj (hs i)
  have h0 : a.mulVec (c 0)=r 0 • c 0 := by
    ext i
    exact Option.some.inj ((CubeZeroSpectra.step_some a (c 0) i).symm.trans (he 0 i))
  have h1 : a.mulVec (c 1)=r 1 • c 1+c 2 := by
    ext i
    exact Option.some.inj ((CubeZeroSpectra.step_some a (c 1) i).symm.trans (he 1 i))
  have h2 : a.mulVec (c 2)=r 1 • c 2 := by
    ext i
    exact Option.some.inj ((CubeZeroSpectra.step_some a (c 2) i).symm.trans (he 2 i))
  rw [hmat, hvec, hrr, hcr]
  cases n with
  | none => rfl
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some ((a^n).mulVec v) = _
    rw [decomposition a v (r 0) (r 1) c hr' hs' h0 h1 h2]
    simp only [value, Spectral.power, RepeatedSpectra.natCast, Value.inv, if_neg hr',
      Value.add, Value.mul, Tensor.consValue, Tensor.nilValue, Option.some_bind, Option.map_some]
    congr 1
    ext i
    fin_cases i <;> rfl

end QSym.JordanSpectra
