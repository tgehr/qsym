import QSym.DistributionModelBridge

/-! Local certificates for the two scalar components of a real density query.
An undefined distribution or query makes the charge check fail. Once that
check succeeds the regular component retains its full pointwise partiality. -/
noncomputable section
namespace QSym.Distribution

def FibreCertificate (d : Option (D ℝ)) (x c w : Option ℝ) : Prop :=
  match d, x with
  | some v, some y => c = some (realFibre v y).charge ∧ w = (realFibre v y).regular
  | _, _ => c = none

namespace FibreCertificate

theorem extract {d x c w} (h : FibreCertificate d x c w) :
    densityAtValue d x = Binding.guardValue (Value.not (Value.nonzero c)) w := by
  cases d <;> cases x <;> simp only [FibreCertificate] at h
  all_goals try (rw [h]; rfl)
  obtain ⟨rfl, rfl⟩ := h
  change (realFibre _ _).density = _
  have law (s : RealDensityFibre) : s.density = (if s.charge = 0 then s.regular else none) := by qsym_rule
  rw [law]
  simp [Value.not, Value.nonzero, Binding.guardValue]

theorem dirac (a x : Option ℝ) :
    FibreCertificate (diracValue a) x
      (Value.mask (Value.not (Value.nonzero (Value.add x (Value.mul (some ((-1 : ℤ) : ℝ)) a))))
        (some ((1 : ℤ) : ℝ))) (some ((0 : ℤ) : ℝ)) := by
  cases a with
  | none => cases x <;> rfl
  | some a =>
    cases x with
    | none => rfl
    | some x =>
      by_cases h : x = a <;>
        simp [FibreCertificate, diracValue, realFibre, Value.mask, Value.not,
          Value.nonzero, Value.add, Value.mul, ← sub_eq_add_neg, sub_eq_zero, h]

theorem zero (x : Option ℝ) :
    FibreCertificate zeroValue x (x.bind (fun _ => some ((0 : ℤ) : ℝ))) (some ((0 : ℤ) : ℝ)) := by
  cases x <;> simp [FibreCertificate, zeroValue, realFibre]

theorem chart (p : DensityProgram) (x : Option ℝ) :
    FibreCertificate p.presentation x (x.bind (fun _ => some ((0 : ℤ) : ℝ)))
      (x.bind p.extractedWeight) := by
  rw [p.presentation_eq]
  cases x <;> simp [FibreCertificate, densityValue, realFibre, DensityProgram.extractedWeight_eq]

theorem add {a b x c e w v} (ha : FibreCertificate a x c w) (hb : FibreCertificate b x e v) :
    FibreCertificate (addValue a b) x (Value.add c e) (Value.add w v) := by
  cases a <;> cases b <;> cases x <;>
    simp_all [FibreCertificate, addValue, realFibre, RealDensityFibre.add, Value.add]

theorem scale (r : Option ℝ) {a x c w} (h : FibreCertificate a x c w) :
    FibreCertificate (scaleValue r a) x (Value.mul r c) (Value.mul r w) := by
  cases r <;> cases a <;> cases x <;>
    simp_all [FibreCertificate, scaleValue, realFibre, RealDensityFibre.scale, Value.mul]

theorem weightDirac (f : Option (ℝ → Option ℝ)) (a x : Option ℝ) :
    FibreCertificate (weightValue f (diracValue a)) x
      (Value.mul (f.bind (fun g => a.bind g))
        (Value.mask (Value.not (Value.nonzero (Value.add x (Value.mul (some ((-1 : ℤ) : ℝ)) a))))
          (some ((1 : ℤ) : ℝ))))
      (Value.mul (f.bind (fun g => a.bind g)) (some ((0 : ℤ) : ℝ))) := by
  have h : weightValue f (diracValue a) = scaleValue (f.bind (fun g => a.bind g)) (diracValue a) := by
    cases f with
    | none => rfl
    | some f =>
      cases a with
      | none => rfl
      | some a => cases hw : f a <;> simp [weightValue, weight, diracValue, scaleValue, hw]
  rw [h]
  exact scale _ (dirac a x)

end FibreCertificate
end QSym.Distribution
