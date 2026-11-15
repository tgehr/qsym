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

def thresholdZ (a b : Option ℤ) (n neg : Option ℝ) : Option ℝ :=
  Value.mul (Value.add n (Value.mul neg (realZ b))) (Value.inv (realZ a))

theorem affineZ (a b i : Option ℤ) (n : Option ℝ) (m : ℕ) (hm : 0 < m)
    (ha : a = some (m : ℤ)) (neg : Option ℝ) (hn : neg = some (-1)) (inclusive reverse : Bool) :
    (if inclusive then Value.le else Value.lt)
      (if reverse then n else realZ (Functions.addZ.apply (Functions.mulZ.apply a i) b))
      (if reverse then realZ (Functions.addZ.apply (Functions.mulZ.apply a i) b) else n) =
    (if inclusive then Value.le else Value.lt)
      (if reverse then thresholdZ a b n neg else realZ i)
      (if reverse then realZ i else thresholdZ a b n neg) := by
  subst a; subst neg
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := ne_of_gt hmR
  cases b <;> cases i <;> cases n <;> cases inclusive <;> cases reverse <;>
    simp [thresholdZ,realZ,Function1.apply,Function2.apply,Functions.castZQ,
      Functions.castQR,Functions.addZ,Functions.mulZ,Value.le,Value.lt,Value.add,Value.mul,Value.inv,hm0]
  all_goals rw [← div_eq_mul_inv]
  all_goals first | rw [le_div_iff₀ hmR] | rw [div_le_iff₀ hmR] | rw [lt_div_iff₀ hmR] | rw [div_lt_iff₀ hmR]
  all_goals constructor <;> intro h <;> nlinarith

theorem shiftZ (b i : Option ℤ) (n neg : Option ℝ) (hn : neg = some (-1)) (inclusive reverse : Bool) :
    (if inclusive then Value.le else Value.lt)
      (if reverse then n else realZ (Functions.addZ.apply i b))
      (if reverse then realZ (Functions.addZ.apply i b) else n) =
    (if inclusive then Value.le else Value.lt)
      (if reverse then Value.add n (Value.mul neg (realZ b)) else realZ i)
      (if reverse then realZ i else Value.add n (Value.mul neg (realZ b))) := by
  subst neg
  cases b <;> cases i <;> cases n <;> cases inclusive <;> cases reverse <;>
    simp [realZ,Function1.apply,Function2.apply,Functions.castZQ,Functions.castQR,
      Functions.addZ,Value.le,Value.lt,Value.add,Value.mul]

theorem scaleZ (a i : Option ℤ) (n : Option ℝ) (m : ℕ) (hm : 0 < m)
    (ha : a = some (m : ℤ)) (inclusive reverse : Bool) :
    (if inclusive then Value.le else Value.lt)
      (if reverse then n else realZ (Functions.mulZ.apply a i))
      (if reverse then realZ (Functions.mulZ.apply a i) else n) =
    (if inclusive then Value.le else Value.lt)
      (if reverse then Value.mul n (Value.inv (realZ a)) else realZ i)
      (if reverse then realZ i else Value.mul n (Value.inv (realZ a))) := by
  have h := affineZ a (some 0) i n m hm ha (some (-1)) rfl inclusive reverse
  have hi : Functions.addZ.apply (Functions.mulZ.apply a i) (some 0) = Functions.mulZ.apply a i := by
    cases Functions.mulZ.apply a i <;> simp [Function2.apply,Functions.addZ]
  rw [hi] at h
  cases n <;> simpa [thresholdZ,realZ,Function1.apply,Functions.castZQ,Functions.castQR,Value.mul,Value.add] using h

theorem real_eq_offset (i c neg : Option ℝ) (hn : neg = some (-1)) :
    Value.not (Value.nonzero (Value.add i c)) =
      Value.and (Value.le (Value.mul neg c) i) (Value.le i (Value.mul neg c)) := by
  subst neg
  cases i <;> cases c <;> simp [Value.not,Value.nonzero,Value.add,Value.mul,Value.le,Value.and]
  rename_i i c
  by_cases h : i+c=0
  · have he : i = -c := by linarith
    simp [he]
  · by_cases hle : i ≤ -c
    · have hlt : i < -c := lt_of_le_of_ne hle (by intro he; apply h; linarith)
      simp [h,hle,not_le_of_gt hlt]
    · have hge : -c ≤ i := le_of_lt (lt_of_not_ge hle)
      simp [h,hle,hge]

theorem real_ne_mask {α : Type} [AddCommMonoid α]
    (add : Option α → Option α → Option α) (ha : add = Value.add)
    (i c neg : Option ℝ) (hn : neg = some (-1)) (x : Option α) :
    Value.mask (Value.nonzero (Value.add i c)) x = add
      (Value.mask (Value.lt i (Value.mul neg c)) x)
      (Value.mask (Value.lt (Value.mul neg c) i) x) := by
  rw [ha,hn]
  cases i with
  | none => rfl
  | some i =>
    cases c with
    | none => rfl
    | some c =>
      have hz : i+c=0 ↔ i = -c := by constructor <;> intro h <;> linarith
      rcases lt_trichotomy i (-c) with h | h | h <;> cases x <;>
        simp [Value.mask,Value.nonzero,Value.add,Value.mul,Value.lt,hz,h,
          ne_of_lt,ne_of_gt,not_lt_of_ge,le_of_lt]

theorem integer_lt (a b : Option ℤ) : Functions.ltZ.apply a b = Value.lt (realZ a) (realZ b) := by
  cases a <;> cases b <;> simp [realZ,Function1.apply,Function2.apply,Functions.castZQ,Functions.castQR,Functions.ltZ,Value.lt]

theorem integer_le (a b : Option ℤ) : Functions.leZ.apply a b = Value.le (realZ a) (realZ b) := by
  cases a <;> cases b <;> simp [realZ,Function1.apply,Function2.apply,Functions.castZQ,Functions.castQR,Functions.leZ,Value.le]

theorem rational_selector (i c : Option ℚ) :
    Functions.nonzeroQ.apply (Functions.addQ.apply i c) =
      Value.nonzero (Value.add (Functions.castQR.apply i) (Functions.castQR.apply c)) := by
  cases i <;> cases c <;> simp [Function1.apply,Function2.apply,Functions.nonzeroQ,
    Functions.addQ,Functions.castQR,Value.nonzero,Value.add,← Rat.cast_add]

end QSym.SummationAffine
