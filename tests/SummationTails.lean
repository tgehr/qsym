import QSym.SummationTails
import QSym.AxiomCheck

namespace QSym.Summation
#qsym_check_axioms reindex
#qsym_check_axioms tail_nat
#qsym_check_axioms tailN
#qsym_check_axioms tailN_strict
#qsym_check_axioms tailN_value
#qsym_check_axioms geometric_shift
#qsym_check_axioms geometric_shift_value
#qsym_check_axioms geometric_shift_guard

theorem tail_undefined_bound (f : ℕ → Option ℝ) :
    value norm (some (fun i => Value.mask (Functions.leN.apply none (some i)) (f i)))=none :=
  tailN norm norm_zero f none

theorem tail_undefined_strict_bound (f : ℕ → Option ℝ) :
    value norm (some (fun i => Value.mask (Functions.ltN.apply none (some i)) (f i)))=none :=
  tailN_strict norm norm_zero f none

theorem tail_selected_undefined :
    value norm (some (fun i : ℕ => if 3 ≤ i then (if i=3 then none else some (0 : ℝ)) else some 0))=none := by
  apply undefined_term norm _ 3
  norm_num

theorem tail_masked_undefined :
    value norm (some (fun i : ℕ => if 3 ≤ i then (if i<3 then none else some (0 : ℝ)) else some 0))=some 0 := by
  rw [tail_nat norm norm_zero]
  convert zero (α := ℝ) (ι := ℕ) norm norm_zero using 2

theorem tail_zero_origin :
    value norm (some (fun i : ℕ => if 0 ≤ i then (if i=0 then some (1 : ℝ) else some 0) else some 0))=some 1 := by
  simp only [Nat.zero_le,ite_true]
  exact delta norm norm_zero 0 (some 1)

theorem tail_strict_origin :
    value norm (some (fun i : ℕ => if 0 < i then (if i=0 then some (1 : ℝ) else some 0) else some 0))=some 0 := by
  have h : (fun i : ℕ => if 0 < i then (if i=0 then some (1 : ℝ) else some 0) else some 0) = fun _ => some 0 := by
    funext i; by_cases hi : i=0 <;> simp [hi]
  rw [h]; exact zero norm norm_zero

theorem tail_false_mask : Value.mask (some false)
    (value norm (some (fun i : ℕ => Value.mask (Functions.leN.apply none (some i)) (some (1 : ℝ)))))=some 0 := rfl

theorem tail_true_mask : Value.mask (some true)
    (value norm (some (fun i : ℕ => Value.mask (Functions.leN.apply none (some i)) (some (1 : ℝ)))))=none :=
  tail_undefined_bound _

#qsym_check_axioms tail_undefined_bound
#qsym_check_axioms tail_undefined_strict_bound
#qsym_check_axioms tail_selected_undefined
#qsym_check_axioms tail_masked_undefined
#qsym_check_axioms tail_zero_origin
#qsym_check_axioms tail_strict_origin
#qsym_check_axioms tail_false_mask
#qsym_check_axioms tail_true_mask
end QSym.Summation
