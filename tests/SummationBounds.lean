import QSym.SummationTails
import QSym.AxiomCheck
open QSym
#qsym_check_axioms QSym.SummationBounds.rational_lt
#qsym_check_axioms QSym.SummationBounds.rational_le
#qsym_check_axioms QSym.SummationBounds.roundN_lt
#qsym_check_axioms QSym.SummationBounds.roundN_le
#qsym_check_axioms QSym.SummationBounds.roundN_gt
#qsym_check_axioms QSym.SummationBounds.roundN_ge
#qsym_check_axioms QSym.SummationBounds.roundZ_lt
#qsym_check_axioms QSym.SummationBounds.roundZ_le
#qsym_check_axioms QSym.SummationBounds.roundZ_gt
#qsym_check_axioms QSym.SummationBounds.roundZ_ge
#qsym_check_axioms QSym.SummationAlgebra.mask_and
#qsym_check_axioms QSym.SummationAlgebra.range_add
#qsym_check_axioms QSym.SummationAlgebra.range_mask_lt
#qsym_check_axioms QSym.SummationAlgebra.range_mask_ge
#qsym_check_axioms QSym.SummationAlgebra.mask_ne_offset
#qsym_check_axioms QSym.SummationAlgebra.mask_eq_offset
#qsym_check_axioms QSym.SummationAlgebra.mask_ne_offset_op
#qsym_check_axioms QSym.SummationTails.reindex
#qsym_check_axioms QSym.SummationTails.lowerN
#qsym_check_axioms QSym.SummationTails.lowerZ
#qsym_check_axioms QSym.SummationTails.upperZ

example : SummationBounds.ceilN (some (-1/2)) = some 0 := by norm_num [SummationBounds.ceilN_some] <;> rfl
example : SummationBounds.ceilN (some (3/2)) = some 2 := by norm_num [SummationBounds.ceilN_some] <;> rfl
example : SummationBounds.upperN (some 2) = some 3 := by norm_num [SummationBounds.upperN_some] <;> rfl
