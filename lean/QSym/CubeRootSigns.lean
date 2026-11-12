import QSym.RefinementBase

namespace QSym.Value

theorem refines_abs_cbrt (x : Option ℝ) :
    Refines (abs (Functions.cbrtR.apply x)) (Functions.cbrtR.apply (abs x)) := by
  have h (x : ℝ) : |Functions.cbrtR.value x|=Functions.cbrtR.value |x| := by
    apply (show Odd 3 from ⟨1, rfl⟩).pow_inj.mp
    rw [← abs_pow, FunctionOrder.cbrt_cube, FunctionOrder.cbrt_cube]
  cases x with
  | none => simp [Refines, Function1.apply, abs]
  | some x =>
    apply refines_of_eq
    simpa [Function1.apply, abs, Functions.cbrtR] using congrArg some (h x)

theorem refines_sign_cbrt (x : Option ℝ) :
    Refines (Functions.signR.apply (Functions.cbrtR.apply x)) (Functions.signR.apply x) := by
  have hz : Functions.cbrtR.value 0=0 := by simp [Functions.cbrtR]
  cases x with
  | none => simp [Refines, Function1.apply]
  | some x =>
    have hn : Functions.cbrtR.value x<0 ↔ x<0 := by
      simpa only [hz] using FunctionOrder.cbrt.lt_iff_lt (a:=x) (b:=0) (show Functions.cbrtR.domain x from trivial) (show Functions.cbrtR.domain 0 from trivial)
    have hp : 0<Functions.cbrtR.value x ↔ 0<x := by
      simpa only [hz] using FunctionOrder.cbrt.lt_iff_lt (a:=0) (b:=x) (show Functions.cbrtR.domain 0 from trivial) (show Functions.cbrtR.domain x from trivial)
    have hc : Functions.cbrtR.apply (some x)=some (Functions.cbrtR.value x) := by simp [Function1.apply, Functions.cbrtR]
    rw [hc]
    simp [Refines, Function1.apply, Functions.signR, hn, hp]

end QSym.Value
