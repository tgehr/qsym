import QSym.DistributionFibreCertificate
import QSym.DistributionSum

/-! Pointwise Lebesgue disintegration of a countable sum. The signed singleton
charges must sum absolutely and cancel at the query. Only then can the regular
components be added. Missing terms also make the observation undefined. -/
noncomputable section
namespace QSym.Distribution.FibreCertificate

private theorem extract_total_sum (d : ℤ → D ℝ) (x : ℝ) :
    densityAt (.sum d) x =
      Binding.guardValue (Value.not (Value.nonzero (partialSum (fun i => some (realFibre (d i) x).charge))))
        (partialSum (fun i => (realFibre (d i) x).regular)) := by
  classical
  let a := fun i => (realFibre (d i) x).charge
  let w := partialSum (fun i => (realFibre (d i) x).regular)
  change (if (∑' i, a i) = 0 then (if Summable (fun i => |a i|) then w else none) else none) = _
  change _ = Binding.guardValue (Value.not (Value.nonzero (partialSum (fun i => some (a i))))) w
  by_cases ha : Summable (fun i => |a i|)
  · have hs := ha.of_abs
    by_cases hz : (∑' i, a i) = 0 <;>
      simp [partialSum, Real.norm_eq_abs, ha, hs, hz, Value.not, Value.nonzero, Binding.guardValue]
  · simp [partialSum, Real.norm_eq_abs, ha, Value.not, Value.nonzero, Binding.guardValue]

theorem extract_sum {d : ℤ → Option (D ℝ)} {x : Option ℝ} {c w : ℤ → Option ℝ}
    (h : ∀ i, FibreCertificate (d i) x (c i) (w i)) :
    densityAtValue (sumValue (some d)) x =
      Binding.guardValue (Value.not (Value.nonzero (Summation.value norm (some c))))
        (Summation.value norm (some w)) := by
  classical
  cases x with
  | none =>
    have c0 : c 0 = none := by have hc := h 0; cases d 0 <;> simp_all [FibreCertificate]
    rw [Summation.undefined_term norm c 0 c0]
    rfl
  | some x =>
    by_cases valid : ∀ i, (d i).isSome
    · let a := fun i => (d i).getD .invalid
      have he (i : ℤ) : d i = some (a i) := by
        have hi := valid i
        cases hp : d i <;> simp_all [a]
      have hc : c = fun i => some (realFibre (a i) x).charge := by
        funext i
        exact ((he i) ▸ h i : FibreCertificate (some (a i)) (some x) _ _).1
      have hw : w = fun i => (realFibre (a i) x).regular := by
        funext i
        exact ((he i) ▸ h i : FibreCertificate (some (a i)) (some x) _ _).2
      rw [hc, hw, ← partialSum_eq_value, ← partialSum_eq_value]
      exact extract_total_sum a x
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp valid
      have hm : d i = none := by cases he : d i <;> simp_all
      have hc : c i = none := by simpa [hm, FibreCertificate] using h i
      rw [Summation.undefined_term norm c i hc]
      let a := fun j => (d j).getD .invalid
      have hw : partialSum (fun j => (realFibre (a j) x).regular) = none := by
        rw [partialSum_eq_value]
        exact Summation.undefined_term norm _ i (by simp [a, hm, realFibre])
      change densityAt (.sum a) x = none
      rw [extract_total_sum, hw]
      cases Value.not (Value.nonzero (partialSum (fun j => some (realFibre (a j) x).charge))) with
      | none => rfl
      | some b => cases b <;> rfl

theorem extract_nat_sum {d : ℕ → Option (D ℝ)} {x : Option ℝ} {c w : ℕ → Option ℝ}
    (h : ∀ i, FibreCertificate (d i) x (c i) (w i)) :
    densityAtValue (sumNatValue (some d)) x =
      Binding.guardValue (Value.not (Value.nonzero (Summation.value norm (some c))))
        (Summation.value norm (some w)) := by
  classical
  cases x with
  | none =>
    have c0 : c 0 = none := by have hc := h 0; cases d 0 <;> simp_all [FibreCertificate]
    rw [Summation.undefined_term norm c 0 c0]
    rfl
  | some x =>
    let pad {α : Type} (f : ℕ → α) (z : α) (i : ℤ) := if 0 ≤ i then f i.toNat else z
    have hf : ∀ i, FibreCertificate (pad d zeroValue i) (some x) (pad c (some 0) i) (pad w (some 0) i) := by
      intro i
      by_cases hi : 0 ≤ i
      · simpa [pad, hi] using h i.toNat
      · simp only [pad, if_neg hi]
        simpa using zero (some x)
    have he : sumNatValue (some d) = sumValue (some (pad d zeroValue)) := by
      change some (Presentation.sum _) = some (Presentation.sum _)
      apply congrArg some
      apply congrArg Presentation.sum
      funext i
      by_cases hi : 0 ≤ i <;> simp [pad, hi, zeroValue]
    rw [he, extract_sum hf]
    have hp (v : ℕ → Option ℝ) : Summation.value norm (some (pad v (some 0))) = Summation.value norm (some v) :=
      (partialSum_eq_value _).symm.trans (partialSum_nat v)
    rw [hp c, hp w]

end QSym.Distribution.FibreCertificate
