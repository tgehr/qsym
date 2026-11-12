import QSym.RefinementBase

namespace QSym.Value

theorem refines_sign_increasing (f : Function1 ℝ ℝ)
    (hf : FunctionOrder.Increasing f) (h0 : f.domain 0) (hz : f.value 0=0)
    (x : Option ℝ) : Refines (Functions.signR.apply (f.apply x)) (Functions.signR.apply x) := by
  cases x with
  | none => simp [Refines, Function1.apply]
  | some x =>
    by_cases hx : f.domain x
    · have hn : f.value x < 0 ↔ x < 0 := by
        simpa only [hz] using hf.lt_iff_lt hx h0
      have hp : 0 < f.value x ↔ 0 < x := by
        simpa only [hz] using hf.lt_iff_lt h0 hx
      simp [Refines, Function1.apply, hx, Functions.signR, hn, hp]
    · simp [Refines, Function1.apply, hx]

theorem refines_sign_sinh (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.sinhR.apply x)) (Functions.signR.apply x) :=
  refines_sign_increasing Functions.sinhR FunctionOrder.sinh
    (by norm_num [Functions.sinhR]) (by simp [Functions.sinhR]) x

theorem refines_sign_tanh (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.tanhR.apply x)) (Functions.signR.apply x) :=
  refines_sign_increasing Functions.tanhR FunctionOrder.tanh
    (by norm_num [Functions.tanhR]) (by simp [Functions.tanhR]) x

theorem refines_sign_asinh (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.asinhR.apply x)) (Functions.signR.apply x) :=
  refines_sign_increasing Functions.asinhR FunctionOrder.asinh
    (by norm_num [Functions.asinhR]) (by simp [Functions.asinhR]) x

theorem refines_sign_atan (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.atanR.apply x)) (Functions.signR.apply x) :=
  refines_sign_increasing Functions.atanR FunctionOrder.atan
    (by norm_num [Functions.atanR]) (by simp [Functions.atanR]) x

theorem refines_sign_asin (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.asinR.apply x)) (Functions.signR.apply x) :=
  refines_sign_increasing Functions.asinR FunctionOrder.asin
    (by norm_num [Functions.asinR]) (by simp [Functions.asinR]) x

theorem refines_sign_atanh (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.atanhR.apply x)) (Functions.signR.apply x) :=
  refines_sign_increasing Functions.atanhR FunctionOrder.atanh
    (by norm_num [Functions.atanhR]) (by simp [Functions.atanhR]) x

end QSym.Value
