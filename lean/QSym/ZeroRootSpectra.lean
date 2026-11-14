import QSym.CubeZeroSpectra

namespace QSym.ZeroRootSpectra

variable {R : Type} [CommSemiring R]

theorem decomposition (a : Matrix (Fin 3) (Fin 3) R) (v r : Fin 3 → R)
    (c : Fin 3 → Fin 3 → R)
    (hs : ∀ i, (c 0 i + c 1 i) + c 2 i = v i)
    (he : ∀ j, a.mulVec (c j) = r j • c j) (n : ℕ) :
    (a^n).mulVec v = fun i => (r 0^n*c 0 i+r 1^n*c 1 i)+r 2^n*c 2 i := by
  have hv : v = (c 0+c 1)+c 2 := funext (fun i => (hs i).symm)
  rw [hv, Matrix.mulVec_add, Matrix.mulVec_add,
    Spectral.eigen_power a (c 0) (r 0) (he 0),
    Spectral.eigen_power a (c 1) (r 1) (he 1),
    Spectral.eigen_power a (c 2) (r 2) (he 2)]
  rfl

def value (add mul : Option R → Option R → Option R)
    (pow : Option R → Option ℕ → Option R)
    (r : Fin 3 → Option R) (c : Fin 3 → Fin 3 → Option R) (n : Option ℕ) (i : Fin 3) :=
  add (add (mul (pow (r 0) n) (c 0 i)) (mul (pow (r 1) n) (c 1 i)))
    (mul (pow (r 2) n) (c 2 i))

theorem three_value (add mul : Option R → Option R → Option R)
    (pow : Option R → Option ℕ → Option R)
    (hadd : add=Value.add) (hmul : mul=Value.mul) (hpow : pow=Spectral.power)
    (zero one : R) (hzero : zero=0) (hone : one=1)
    (a : Matrix (Fin 3) (Fin 3) R) (v r : Fin 3 → R) (c : Fin 3 → Fin 3 → R)
    (ar : Fin 3 → Fin 3 → Option R) (vr rr : Fin 3 → Option R)
    (cr : Fin 3 → Fin 3 → Option R)
    (ha : ∀ i j, ar i j=some (a i j)) (hv : ∀ i, vr i=some (v i))
    (hr : ∀ i, rr i=some (r i)) (hc : ∀ i j, cr i j=some (c i j))
    (hs : ∀ i, add (add (cr 0 i) (cr 1 i)) (cr 2 i)=vr i)
    (he : ∀ j i, CubeZeroSpectra.step add mul ar (cr j) i=mul (rr j) (cr j i))
    (m : Option (Matrix (Fin 3) (Fin 3) R)) (w : Option (Fin 3 → R))
    (hmat : m=some a) (hvec : w=some v) (n : Option ℕ) :
    Tensor.matvecValue add mul zero 3 3 (Tensor.matrixPowerValue add mul zero one 3 m n) w =
      Tensor.consValue (value add mul pow rr cr n 0)
        (Tensor.consValue (value add mul pow rr cr n 1)
          (Tensor.consValue (value add mul pow rr cr n 2) Tensor.nilValue)) := by
  subst add; subst mul; subst pow; subst zero; subst one
  have har : ar=fun i j => some (a i j) := funext (fun i => funext (ha i))
  have hvr : vr=fun i => some (v i) := funext hv
  have hrr : rr=fun i => some (r i) := funext hr
  have hcr : cr=fun i j => some (c i j) := funext (fun i => funext (hc i))
  rw [har, hcr, hrr] at he
  rw [hcr, hvr] at hs
  have hs' : ∀ i, (c 0 i+c 1 i)+c 2 i=v i := fun i => Option.some.inj (hs i)
  have he' : ∀ j, a.mulVec (c j)=r j • c j := by
    intro j; ext i
    exact Option.some.inj ((CubeZeroSpectra.step_some a (c j) i).symm.trans (he j i))
  rw [hmat, hvec, hrr, hcr]
  cases n with
  | none => rfl
  | some n =>
    rw [AffineRecurrence.power_some, Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
    change some ((a^n).mulVec v) = _
    rw [decomposition a v r c hs' he']
    simp only [value, Spectral.power, Value.add, Value.mul, Tensor.consValue, Tensor.nilValue,
      Option.some_bind, Option.map_some]
    congr 1
    ext i
    fin_cases i <;> rfl

end QSym.ZeroRootSpectra
