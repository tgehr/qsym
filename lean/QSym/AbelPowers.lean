import QSym.RefinementBase

namespace QSym.Value

theorem powerR_add_pos (x y z : Option ℝ)
    (h : Refines (lt (some (((0 : Int) : ℝ))) x) (some true)) :
    Functions.powerR.apply x (add y z) =
      mul (Functions.powerR.apply x y) (Functions.powerR.apply x z) := by
  classical
  cases x with
  | none => cases y <;> cases z <;> rfl
  | some x =>
    have hx : 0 < x := by simpa [Refines, lt] using h
    cases y <;> cases z <;>
      simp [Functions.powerR, Function2.apply, add, mul, hx, Real.rpow_add]

end QSym.Value
