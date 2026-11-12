import QSym.RefinementBase

namespace QSym.Value

theorem refines_sign_power_pair_above_one (b x y : Option ℝ)
    (hb : Refines (lt (some 1) b) (some true)) :
    Refines (Functions.signR.apply (add (Functions.powerR.apply b x)
      (mul (some (-1)) (Functions.powerR.apply b y))))
      (Functions.signR.apply (add x (mul (some (-1)) y))) := by
  cases b with
  | none => simp [Refines, Function1.apply, Function2.apply, add, mul]
  | some b =>
    cases x with
    | none => simp [Refines, Function1.apply, Function2.apply, add, mul]
    | some x =>
      cases y with
      | none => simp [Refines, Function1.apply, Function2.apply, add, mul]
      | some y =>
        have hb : 1<b := by simpa [Refines, lt] using hb
        have hp : 0<b := lt_trans zero_lt_one hb
        simp [Refines, Function1.apply, Function2.apply, Functions.powerR, Functions.signR,
          add, mul, hp, ← sub_eq_add_neg, sub_neg, sub_pos,
          Real.rpow_lt_rpow_left_iff hb]

theorem refines_sign_power_pair_below_one (b x y : Option ℝ)
    (hb0 : Refines (lt (some 0) b) (some true))
    (hb1 : Refines (lt b (some 1)) (some true)) :
    Refines (Functions.signR.apply (add (Functions.powerR.apply b x)
      (mul (some (-1)) (Functions.powerR.apply b y))))
      (Functions.signR.apply (add y (mul (some (-1)) x))) := by
  cases b with
  | none => simp [Refines, Function1.apply, Function2.apply, add, mul]
  | some b =>
    cases x with
    | none => simp [Refines, Function1.apply, Function2.apply, add, mul]
    | some x =>
      cases y with
      | none => simp [Refines, Function1.apply, Function2.apply, add, mul]
      | some y =>
        have hp : 0<b := by simpa [Refines, lt] using hb0
        have hb : b<1 := by simpa [Refines, lt] using hb1
        simp [Refines, Function1.apply, Function2.apply, Functions.powerR, Functions.signR,
          add, mul, hp, ← sub_eq_add_neg, sub_neg, sub_pos,
          Real.rpow_lt_rpow_left_iff_of_base_lt_one hp hb]

end QSym.Value
