import QSym.SummationBounds

noncomputable section
namespace QSym.SummationAffine
open SummationBounds

def threshold (a b : Option ℕ) (n neg : Option ℝ) : Option ℝ :=
  Value.mul (Value.add n (Value.mul neg (realN b))) (Value.inv (realN a))

theorem affineN (a b i : Option ℕ) (n : Option ℝ) (m : ℕ) (hm : 0 < m)
    (ha : a = some m) (neg : Option ℝ) (hn : neg = some (-1)) (inclusive reverse : Bool) :
    (if inclusive then Value.le else Value.lt)
      (if reverse then n else realN (Functions.addN.apply (Functions.mulN.apply a i) b))
      (if reverse then realN (Functions.addN.apply (Functions.mulN.apply a i) b) else n) =
    (if inclusive then Value.le else Value.lt)
      (if reverse then threshold a b n neg else realN i)
      (if reverse then realN i else threshold a b n neg) := by
  subst a; subst neg
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := ne_of_gt hmR
  cases b <;> cases i <;> cases n <;> cases inclusive <;> cases reverse <;>
    simp [threshold,realN,realZ,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,
      Functions.castQR,Functions.addN,Functions.mulN,Value.le,Value.lt,Value.add,Value.mul,Value.inv,hm0]
  all_goals rw [← div_eq_mul_inv]
  all_goals first | rw [le_div_iff₀ hmR] | rw [div_le_iff₀ hmR] | rw [lt_div_iff₀ hmR] | rw [div_lt_iff₀ hmR]
  all_goals constructor <;> intro h <;> nlinarith

theorem natural_lt (a b : Option ℕ) : Functions.ltN.apply a b = Value.lt (realN a) (realN b) := by
  cases a <;> cases b <;> simp [realN,realZ,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltN,Value.lt]

theorem natural_le (a b : Option ℕ) : Functions.leN.apply a b = Value.le (realN a) (realN b) := by
  cases a <;> cases b <;> simp [realN,realZ,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leN,Value.le]

end QSym.SummationAffine
