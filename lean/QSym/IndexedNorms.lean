import QSym.Functions

namespace QSym.Value

theorem abs_powRN (x : Option ℝ) (n : Option ℕ) :
    abs (Functions.powRN.apply x n)=Functions.powRN.apply (abs x) n := by
  classical
  cases x <;> cases n <;>
    simp [abs, Function2.apply, Functions.powRN, abs_pow]

theorem abs_powRZ (x : Option ℝ) (k : Option ℤ) :
    abs (Functions.powRZ.apply x k)=Functions.powRZ.apply (abs x) k := by
  classical
  cases x <;> cases k <;>
    simp [abs, Function2.apply, Functions.powRZ, ← Real.norm_eq_abs, norm_zpow]

theorem norm_powCN (z : Option ℂ) (n : Option ℕ) :
    Functions.absC.apply (Functions.powCN.apply z n)=
      Functions.powRN.apply (Functions.absC.apply z) n := by
  classical
  cases z <;> cases n <;>
    simp [Function1.apply, Function2.apply, Functions.absC, Functions.powCN,
      Functions.powRN, norm_pow]

theorem norm_powCZ (z : Option ℂ) (k : Option ℤ) :
    Functions.absC.apply (Functions.powCZ.apply z k)=
      Functions.powRZ.apply (Functions.absC.apply z) k := by
  classical
  cases z <;> cases k <;>
    simp [Function1.apply, Function2.apply, Functions.absC, Functions.powCZ,
      Functions.powRZ, norm_zpow]
  split <;> simp_all [norm_zpow]

theorem conj_powCN (z : Option ℂ) (n : Option ℕ) :
    conj (Functions.powCN.apply z n)=Functions.powCN.apply (conj z) n := by
  classical
  cases z <;> cases n <;>
    simp [conj, Function2.apply, Functions.powCN, star_pow]

theorem conj_powCZ (z : Option ℂ) (k : Option ℤ) :
    conj (Functions.powCZ.apply z k)=Functions.powCZ.apply (conj z) k := by
  classical
  cases z <;> cases k <;>
    simp [conj, Function2.apply, Functions.powCZ, star_zpow₀]

end QSym.Value
