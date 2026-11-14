import QSym.Summation
import QSym.AxiomCheck

open QSym QSym.Summation

namespace SummationTests

theorem geometric_half : value norm (some (fun n : ℕ => some ((1/2 : ℝ)^n))) = some 2 := by
  rw [geometric]
  norm_num

theorem geometric_boundary : value norm (some (fun n : ℕ => some ((-1 : ℝ)^n))) = none := by
  rw [geometric]
  norm_num

theorem undefined_summand : value norm (some (fun _ : ℕ => (none : Option ℝ))) = none :=
  Summation.undefined_term _ _ 0 rfl

theorem empty_partial_range : finite (Finset.range 0) (fun _ => (none : Option ℝ)) = some 0 :=
  finite_empty _

theorem selected_partial_range : finite (Finset.range 1) (fun _ => (none : Option ℝ)) = none := by
  simp [finite]

theorem empty_integer_interval :
    value norm (some (fun i : ℤ => if 4 ≤ i ∧ i < 2 then (none : Option ℝ) else some 0)) = some 0 := by
  rw [interval_int _ norm_zero]
  norm_num [finite]

theorem integer_interval :
    value norm (some (fun i : ℤ => if -2 ≤ i ∧ i < 4 then some i else some 0)) = some 3 := by
  rw [interval_int _ norm_zero]
  change finite (Finset.range 6) (fun n => some ((n:ℤ)+(-2))) = some 3
  norm_num [finite, Finset.sum_range_succ]

/-- An ordinary sum does not suffice without absolute convergence. -/
theorem conditionally_convergent_undefined (f : ℕ → ℝ) (s : ℝ)
    (_hs : HasSum f s) (ha : ¬ Summable (fun n => ‖f n‖)) :
    value norm (some (fun n => some (f n))) = none := by
  have hn : ¬ Summable (fun n => |f n|) := by simpa only [Real.norm_eq_abs] using ha
  simp [value,hn]

/-- Divergent components cannot be split before cancellation. -/
theorem cancellation : value norm (some (fun _ : ℕ => some ((1:ℝ)+(-1)))) = some 0 := by
  simpa using (zero (ι := ℕ) (norm : ℝ → ℝ) norm_zero)

#qsym_check_axioms geometric_half
#qsym_check_axioms geometric_boundary
#qsym_check_axioms undefined_summand
#qsym_check_axioms empty_partial_range
#qsym_check_axioms selected_partial_range
#qsym_check_axioms empty_integer_interval
#qsym_check_axioms integer_interval
#qsym_check_axioms conditionally_convergent_undefined
#qsym_check_axioms cancellation
end SummationTests

#qsym_check_axioms QSym.Summation.of_hasSum
#qsym_check_axioms QSym.Summation.finite_support
#qsym_check_axioms QSym.Summation.deltaN
#qsym_check_axioms QSym.Summation.deltaZ
#qsym_check_axioms QSym.Summation.deltaZ_offset
#qsym_check_axioms QSym.Summation.range_convert
#qsym_check_axioms QSym.Summation.range_convert_le
#qsym_check_axioms QSym.Summation.boundsN
#qsym_check_axioms QSym.Summation.boundsZ
#qsym_check_axioms QSym.Summation.interval_convertN
#qsym_check_axioms QSym.Summation.interval_convertZ
#qsym_check_axioms QSym.Summation.range_nat_lift
#qsym_check_axioms QSym.Summation.range_int_lift
#qsym_check_axioms QSym.Summation.range_solution_partial
#qsym_check_axioms QSym.Summation.geometricR_literals
#qsym_check_axioms QSym.Summation.geometricQ_literals
#qsym_check_axioms QSym.Summation.geometricC_literals
#qsym_check_axioms QSym.Summation.constantN
#qsym_check_axioms QSym.Summation.constantZ
#qsym_check_axioms QSym.Summation.constantQ
#qsym_check_axioms QSym.Summation.constant_norm
#qsym_check_axioms QSym.Summation.tail_solution
#qsym_check_axioms QSym.Summation.range_geometric_value
#qsym_check_axioms QSym.Summation.solve_prefix
