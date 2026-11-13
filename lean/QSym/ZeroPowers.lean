import QSym.RefinementBase

namespace QSym.ZeroPowers

private theorem natural {α : Type} [MonoidWithZero α] (n : Option ℕ) :
    (Function2.mk (fun (x : α) (n : ℕ) => x^n) (fun _ _ => True)).apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply n))) (some 1) := by
  classical
  cases n with
  | none => rfl
  | some n =>
    by_cases h : n=0 <;>
      simp [Function1.apply, Function2.apply, Functions.castNZ, Functions.nonzeroZ,
        Value.mask, Value.not, h, zero_pow]

theorem powNN (n : Option ℕ) :
    Functions.powNN.apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply n))) (some 1) :=
  natural n

theorem powZN (n : Option ℕ) :
    Functions.powZN.apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply n))) (some 1) :=
  natural n

theorem powQN (n : Option ℕ) :
    Functions.powQN.apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply n))) (some 1) :=
  natural n

theorem powRN (n : Option ℕ) :
    Functions.powRN.apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply n))) (some 1) :=
  natural n

theorem powCN (n : Option ℕ) :
    Functions.powCN.apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply n))) (some 1) :=
  natural n

private theorem integer {α : Type} [GroupWithZero α] (n : Option ℤ)
    (h : Value.Refines (Functions.leZ.apply (some 0) n) (some true)) :
    (Function2.mk (fun (x : α) (n : ℤ) => x^n) (fun x n => x≠0 ∨ 0≤n)).apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply n)) (some 1) := by
  classical
  cases n with
  | none => rfl
  | some n =>
    have hn : 0≤n := by simpa [Value.Refines, Function2.apply, Functions.leZ] using h
    by_cases hz : n=0 <;>
      simp [Function1.apply, Function2.apply, Functions.nonzeroZ,
        Value.mask, Value.not, hn, hz, zero_zpow]

theorem powQZ (n : Option ℤ)
    (h : Value.Refines (Functions.leZ.apply (some 0) n) (some true)) :
    Functions.powQZ.apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply n)) (some 1) :=
  integer n h

theorem powRZ (n : Option ℤ)
    (h : Value.Refines (Functions.leZ.apply (some 0) n) (some true)) :
    Functions.powRZ.apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply n)) (some 1) :=
  integer n h

theorem powCZ (n : Option ℤ)
    (h : Value.Refines (Functions.leZ.apply (some 0) n) (some true)) :
    Functions.powCZ.apply (some 0) n =
      Value.mask (Value.not (Functions.nonzeroZ.apply n)) (some 1) :=
  integer n h

private theorem integer_positive {α : Type} [GroupWithZero α] (n : Option ℤ)
    (h : Value.Refines (Functions.ltZ.apply (some 0) n) (some true)) :
    Value.Refines
      ((Function2.mk (fun (x : α) (n : ℤ) => x^n) (fun x n => x≠0 ∨ 0≤n)).apply (some 0) n)
      (some 0) := by
  classical
  cases n with
  | none => intro v hv; cases hv
  | some n =>
    have hn : 0<n := by simpa [Value.Refines, Function2.apply, Functions.ltZ] using h
    simp [Value.Refines, Function2.apply, hn.le, ne_of_gt hn, zero_zpow]

theorem powQZ_positive (n : Option ℤ)
    (h : Value.Refines (Functions.ltZ.apply (some 0) n) (some true)) :
    Value.Refines (Functions.powQZ.apply (some 0) n) (some 0) := integer_positive n h

theorem powRZ_positive (n : Option ℤ)
    (h : Value.Refines (Functions.ltZ.apply (some 0) n) (some true)) :
    Value.Refines (Functions.powRZ.apply (some 0) n) (some 0) := integer_positive n h

theorem powCZ_positive (n : Option ℤ)
    (h : Value.Refines (Functions.ltZ.apply (some 0) n) (some true)) :
    Value.Refines (Functions.powCZ.apply (some 0) n) (some 0) := integer_positive n h

theorem powerR (x : Option ℝ)
    (h : Value.Refines (Value.le (some 0) x) (some true)) :
    Functions.powerR.apply (some 0) x =
      Value.mask (Value.not (Value.nonzero x)) (some 1) := by
  classical
  cases x with
  | none => rfl
  | some x =>
    have hx : 0≤x := by simpa [Value.Refines, Value.le] using h
    by_cases hz : x=0 <;>
      simp [Function2.apply, Functions.powerR, Value.mask, Value.not, Value.nonzero,
        hx, hz, Real.zero_rpow]

theorem powerC (z : Option ℂ)
    (hi : Value.Refines (Value.not (Value.nonzero (Functions.imC.apply z))) (some true))
    (hr : Value.Refines (Value.le (some 0) (Functions.reC.apply z)) (some true)) :
    Functions.powerC.apply (some 0) z =
      Value.mask (Value.not (Value.nonzero z)) (some 1) := by
  classical
  cases z with
  | none => rfl
  | some z =>
    have him : z.im=0 := by
      simpa [Value.Refines, Value.not, Value.nonzero, Function1.apply, Functions.imC] using hi
    have hre : 0≤z.re := by
      simpa [Value.Refines, Value.le, Function1.apply, Functions.reC] using hr
    by_cases hz : z=0
    · simp [hz, Function2.apply, Functions.powerC, Value.mask, Value.not, Value.nonzero]
    · have hp : 0<z.re := lt_of_le_of_ne hre (by
        intro he
        exact hz (Complex.ext he.symm him))
      simp [Function2.apply, Functions.powerC, Value.mask, Value.not, Value.nonzero,
        hz, him, hp, Complex.zero_cpow]

end QSym.ZeroPowers
