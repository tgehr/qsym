import QSym.DistributionSumFibre
import QSym.SummationRealSelector

/-! Compact certificates for the density of counting measure on the integer
and natural lattices, obtained from countable disintegration and index selection. -/
noncomputable section
namespace QSym.Distribution

private theorem count_guard (p : Option Bool) (i : Option ι) :
    Binding.guardValue (Value.not (Value.nonzero (Value.mask (Value.not p)
      (i.bind (fun _ => some ((1 : ℤ) : ℝ)))))) (some ((0 : ℤ) : ℝ)) =
    Binding.guardValue p (some ((0 : ℤ) : ℝ)) := by
  cases p with
  | none => rfl
  | some b => cases b <;> cases i <;> simp [Value.not, Value.nonzero, Value.mask, Binding.guardValue]

theorem counting_Z (x : Option ℝ) :
    densityAtValue (sumValue (some (fun i => diracValue (Summation.realIndexZ (some i))))) x =
    Binding.guardValue (awayFromAtom (Summation.realIndexZ (Functions.floorR.apply x)) x) (some ((0 : ℤ) : ℝ)) := by
  have h := FibreCertificate.extract_sum (fun i => FibreCertificate.dirac (Summation.realIndexZ (some i)) x)
  have hs := Summation.select_real_Z norm norm_zero false (fun _ => some ((1 : ℤ) : ℝ)) x
  have hz : Summation.value norm (some (fun _ : ℤ => some ((0 : ℤ) : ℝ))) = some ((0 : ℤ) : ℝ) := by
    simpa using (Summation.zero (ι := ℤ) (α := ℝ) norm norm_zero)
  rw [h, hz]
  change Binding.guardValue (Value.not (Value.nonzero (Summation.value norm (some
    (fun i : ℤ => Value.mask (Summation.realMatch x (Summation.realIndexZ (some i))) (some ((1 : ℤ) : ℝ))))))) _ = _
  simp only [Bool.false_eq_true, ↓reduceIte] at hs
  rw [hs]
  exact count_guard _ _

theorem counting_N (x : Option ℝ) :
    densityAtValue (sumNatValue (some (fun i => diracValue (Summation.realIndexN (some i))))) x =
    Binding.guardValue (awayFromAtom (Summation.realIndexN (Functions.floorN.apply x)) x) (some ((0 : ℤ) : ℝ)) := by
  have h := FibreCertificate.extract_nat_sum (fun i => FibreCertificate.dirac (Summation.realIndexN (some i)) x)
  have hs := Summation.select_real_N norm norm_zero false (fun _ => some ((1 : ℤ) : ℝ)) x
  have hz : Summation.value norm (some (fun _ : ℕ => some ((0 : ℤ) : ℝ))) = some ((0 : ℤ) : ℝ) := by
    simpa using (Summation.zero (ι := ℕ) (α := ℝ) norm norm_zero)
  rw [h, hz]
  change Binding.guardValue (Value.not (Value.nonzero (Summation.value norm (some
    (fun i : ℕ => Value.mask (Summation.realMatch x (Summation.realIndexN (some i))) (some ((1 : ℤ) : ℝ))))))) _ = _
  simp only [Bool.false_eq_true, ↓reduceIte] at hs
  rw [hs]
  exact count_guard _ _

end QSym.Distribution
