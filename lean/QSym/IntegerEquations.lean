import QSym.RefinementBase
import QSym.ScalarTypes
namespace QSym.ScalarTypes
theorem integer_mul_eq_floor (a x b : ℤ) (ha : a ≠ 0) :
    a*x=b ↔ x=⌊(b : ℝ)/(a : ℝ)⌋ ∧ (b : ℝ)/(a : ℝ)=(⌊(b : ℝ)/(a : ℝ)⌋ : ℝ) := by
  have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have he : a*x=b ↔ (x : ℝ)=(b : ℝ)/(a : ℝ) := by
    rw [eq_div_iff har]
    constructor
    · intro h
      exact_mod_cast (show x*a=b from by simpa [mul_comm] using h)
    · intro h
      have hz : x*a=b := by exact_mod_cast h
      simpa [mul_comm] using hz
  rw [he]
  constructor
  · intro h
    have hf : ⌊(b : ℝ)/(a : ℝ)⌋=x := by rw [← h]; simp
    exact ⟨hf.symm, by simpa [hf] using h.symm⟩
  · rintro ⟨h, hi⟩
    simpa [h] using hi.symm
end QSym.ScalarTypes
namespace QSym.Value

theorem refines_integer_literal_affine_nonzero (v_a : Option (Ty.denote .integer)) (v_x : Option (Ty.denote .integer)) (v_b : Option (Ty.denote .integer))
    (hp2 : Value.Refines (Functions.nonzeroZ.apply v_a) (some true)) :
    Value.Refines (Functions.nonzeroZ.apply (Functions.addZ.apply (Functions.mulZ.apply v_a v_x) v_b)) (Value.not (Value.and (Value.not (Functions.nonzeroZ.apply (Functions.addZ.apply v_x (Functions.mulZ.apply (some ((-1) : ℤ)) (Functions.floorR.apply (Value.mul (Value.mul (some (((-1) : Int) : ℝ)) (Functions.castQR.apply (Functions.castZQ.apply v_b))) (Value.inv (Functions.castQR.apply (Functions.castZQ.apply v_a))))))))) (Value.not (Value.nonzero (Value.add (Value.mul (Value.mul (some (((-1) : Int) : ℝ)) (Functions.castQR.apply (Functions.castZQ.apply v_b))) (Value.inv (Functions.castQR.apply (Functions.castZQ.apply v_a)))) (Value.mul (some (((-1) : Int) : ℝ)) (Functions.castQR.apply (Functions.castZQ.apply (Functions.floorR.apply (Value.mul (Value.mul (some (((-1) : Int) : ℝ)) (Functions.castQR.apply (Functions.castZQ.apply v_b))) (Value.inv (Functions.castQR.apply (Functions.castZQ.apply v_a))))))))))))) := by
  cases v_a <;> cases v_x <;> cases v_b
  all_goals simp_all [Value.Refines, Function1.apply, Function2.apply,
    Functions.nonzeroZ, Functions.addZ, Functions.mulZ, Functions.castZQ, Functions.castQR,
    Functions.floorR, Value.not, Value.nonzero, Value.add, Value.mul, Value.inv, Value.and_some,
    ← sub_eq_add_neg, sub_eq_zero, ← div_eq_mul_inv]
  all_goals rename_i a x b
  all_goals have h := ScalarTypes.integer_mul_eq_floor a x (-b) hp2
  all_goals simp only [Int.cast_neg] at h
  all_goals simp only [add_eq_zero_iff_eq_neg, h, Int.fract, sub_eq_zero]
  all_goals tauto

theorem refines_natural_literal_affine_nonzero (v_a : Option (Ty.denote .natural)) (v_x : Option (Ty.denote .natural)) (v_b : Option (Ty.denote .integer))
    (hp2 : Value.Refines (Functions.nonzeroZ.apply (Functions.castNZ.apply v_a)) (some true)) :
    Value.Refines (Functions.nonzeroZ.apply (Functions.addZ.apply (Functions.castNZ.apply (Functions.mulN.apply v_a v_x)) v_b)) (Value.not (Value.and (Value.and (Value.le (some (((0) : Int) : ℝ)) (Value.mul (Value.mul (some (((-1) : Int) : ℝ)) (Functions.castQR.apply (Functions.castZQ.apply v_b))) (Value.inv (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply v_a)))))) (Value.not (Functions.nonzeroZ.apply (Functions.addZ.apply (Functions.castNZ.apply v_x) (Functions.mulZ.apply (some ((-1) : ℤ)) (Functions.floorR.apply (Value.mul (Value.mul (some (((-1) : Int) : ℝ)) (Functions.castQR.apply (Functions.castZQ.apply v_b))) (Value.inv (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply v_a))))))))))) (Value.not (Value.nonzero (Value.add (Value.mul (Value.mul (some (((-1) : Int) : ℝ)) (Functions.castQR.apply (Functions.castZQ.apply v_b))) (Value.inv (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply v_a))))) (Value.mul (some (((-1) : Int) : ℝ)) (Functions.castQR.apply (Functions.castZQ.apply (Functions.floorR.apply (Value.mul (Value.mul (some (((-1) : Int) : ℝ)) (Functions.castQR.apply (Functions.castZQ.apply v_b))) (Value.inv (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply v_a)))))))))))))) := by
  cases v_a <;> cases v_x <;> cases v_b
  all_goals simp_all [Value.Refines, Function1.apply, Function2.apply,
    Functions.nonzeroZ, Functions.nonzeroN, Functions.addZ, Functions.mulZ, Functions.mulN,
    Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.floorR,
    Value.not, Value.nonzero, Value.add, Value.mul, Value.inv, Value.and_some, Value.le,
    ← sub_eq_add_neg, sub_eq_zero, ← div_eq_mul_inv]
  rename_i a x b
  have ha : (a : ℤ) ≠ 0 := by exact_mod_cast hp2
  have h := ScalarTypes.integer_mul_eq_floor (a : ℤ) (x : ℤ) (-b) ha
  simp only [Int.cast_natCast, Int.cast_neg] at h
  simp only [Int.natCast_mul, add_eq_zero_iff_eq_neg, h, Int.fract, sub_eq_zero]
  have hi : (x : ℤ)=⌊-(b : ℝ)/(a : ℝ)⌋ ∧ -(b : ℝ)/(a : ℝ)=(⌊-(b : ℝ)/(a : ℝ)⌋ : ℝ) → 0 ≤ -(b : ℝ)/(a : ℝ) := by
    rintro ⟨hx, hq⟩
    rw [hq, ← hx]
    positivity
  tauto


end QSym.Value
