import QSym

noncomputable section
namespace QSym.SummationParity
open Summation

-- A deleted term can be undefined without poisoning the remaining sum.
theorem deleted_pole :
    value norm (some (fun i : ℕ => if i=2 then some (0:ℝ)
      else (if i=2 then none else some 0))) = some 0 := by
  have h : (fun i : ℕ => if i=2 then some (0:ℝ) else (if i=2 then none else some 0)) = fun _ => some 0 := by
    funext i; by_cases hi : i=2 <;> simp [hi]
  rw [h]; exact zero norm norm_zero

theorem undeleted_pole :
    value norm (some (fun i : ℕ => if i=2 then some (0:ℝ)
      else (if i=3 then none else some 0))) = none := by
  exact undefined_term norm _ 3 (by norm_num)

theorem negative_zero_power (n : ℕ) :
    Functions.powRZ.apply (some 0) (some (-(n+1 : ℤ))) = none := by
  simp [Function2.apply,Functions.powRZ]; omega

theorem zero_origin_power :
    Functions.powRZ.apply (some 0) (Functions.castNZ.apply (some 0)) = some 1 := by
  rw [SummationPowers.naturalR]; simp [Function2.apply,Functions.powRN]

theorem finite_plus_divergent :
    Value.add (some (3:ℝ)) (value norm (some (fun _ : ℕ => some 1))) = none := by
  have h := constant_norm (K := ℝ) (ι := ℕ) (some 1) (some 0) rfl
  simp [Binding.guardValue,Value.not,Value.nonzero,Value.mask] at h
  rw [h]; rfl

#qsym_check_axioms deleted_pole
#qsym_check_axioms undeleted_pole
#qsym_check_axioms negative_zero_power
#qsym_check_axioms zero_origin_power
#qsym_check_axioms finite_plus_divergent
end QSym.SummationParity
#qsym_check_axioms QSym.SummationMasks.deltaN_nonzeroN
#qsym_check_axioms QSym.SummationMasks.deltaN_zero
#qsym_check_axioms QSym.SummationMasks.deltaZ_zero
#qsym_check_axioms QSym.SummationMasks.bounded_add
#qsym_check_axioms QSym.SummationMasks.castNZ_mask
#qsym_check_axioms QSym.SummationMasks.castZQ_mask
#qsym_check_axioms QSym.SummationMasks.castQR_mask
#qsym_check_axioms QSym.SummationMasks.castRC_mask
#qsym_check_axioms QSym.SummationMasks.castNZ_add
#qsym_check_axioms QSym.SummationMasks.castZQ_add
#qsym_check_axioms QSym.SummationMasks.castQR_add
#qsym_check_axioms QSym.SummationMasks.castRC_add
#qsym_check_axioms QSym.SummationMasks.add_none_left
#qsym_check_axioms QSym.SummationMasks.add_none_right
#qsym_check_axioms QSym.SummationMasks.exclude_zero
#qsym_check_axioms QSym.SummationPrefix.split_prefix
#qsym_check_axioms QSym.SummationPrefix.exclude
#qsym_check_axioms QSym.SummationPrefix.exclude_offset
#qsym_check_axioms QSym.SummationAffine.affineN
#qsym_check_axioms QSym.SummationAffine.natural_lt
#qsym_check_axioms QSym.SummationAffine.natural_le
#qsym_check_axioms QSym.SummationPowers.naturalQ
#qsym_check_axioms QSym.SummationPowers.naturalR
#qsym_check_axioms QSym.SummationPowers.naturalC
#qsym_check_axioms QSym.SummationPowers.negativeQ
#qsym_check_axioms QSym.SummationPowers.negativeR
#qsym_check_axioms QSym.SummationPowers.negativeC
#qsym_check_axioms QSym.SummationPowers.negativeReverseQ
#qsym_check_axioms QSym.SummationPowers.negativeReverseR
#qsym_check_axioms QSym.SummationPowers.negativeReverseC
