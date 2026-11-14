import QSym.Summation

noncomputable section
namespace QSym.SummationPowers
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K]

def powerZ (q : Option K) (n : Option ℤ) : Option K :=
  q.bind fun q => n.bind fun n => if q ≠ 0 ∨ 0 ≤ n then some (q^n) else none

theorem natural (q : Option K) (n : Option ℕ) :
    powerZ q (Functions.castNZ.apply n) = Spectral.power q n := by
  cases q <;> cases n <;> simp [powerZ,Spectral.power,Function1.apply,Functions.castNZ]

theorem negative (q : Option K) (n : Option ℕ) (m : ℕ) (offset minus : Option ℤ)
    (ho : offset = some (-(m+1 : ℤ))) (hm : minus = some (-1)) :
    powerZ q (Functions.addZ.apply offset (Functions.mulZ.apply minus (Functions.castNZ.apply n))) =
      Spectral.power (Value.inv q) (Functions.addN.apply n (some (m+1))) := by
  rw [ho,hm]
  cases q with
  | none => rfl
  | some q =>
    cases n with
    | none => simp [powerZ,Spectral.power,Function1.apply,Function2.apply,Value.inv]
    | some n =>
      have hn : ¬ (0:ℤ) ≤ -(m+1 : ℤ) + -1*(n:ℤ) := by omega
      have he : -(m+1 : ℤ) + -1*(n:ℤ) = -((n+(m+1):ℕ):ℤ) := by push_cast; ring
      by_cases hq : q=0
      · simp only [powerZ,Spectral.power,Value.inv,Function1.apply,Function2.apply,Functions.castNZ,Functions.addZ,Functions.mulZ,Functions.addN,Option.bind,if_pos trivial,hq,ne_eq,not_true_eq_false,false_or,if_neg hn,ite_true,Option.map_none]
      · simp only [powerZ,Spectral.power,Value.inv,Function1.apply,Function2.apply,Functions.castNZ,Functions.addZ,Functions.mulZ,Functions.addN,Option.bind,if_pos trivial,if_neg hq,if_pos (Or.inl hq),Option.map_some]
        rw [he,zpow_neg,zpow_natCast]; simp [inv_pow]

theorem powerQZ : Functions.powQZ.apply = (powerZ : Option ℚ → Option ℤ → Option ℚ) := by
  funext q n
  cases q with
  | none => rfl
  | some q =>
    cases n with
    | none => rfl
    | some n =>
      by_cases h : q ≠ 0 ∨ 0 ≤ n <;> simp [powerZ,Function2.apply,Functions.powQZ,h]

theorem naturalQ (q : Option ℚ) (n : Option ℕ) :
    Functions.powQZ.apply q (Functions.castNZ.apply n) = Functions.powQN.apply q n := by
  rw [powerQZ,Spectral.powQ]; exact natural q n

theorem negativeQ (q : Option ℚ) (n : Option ℕ) (m : ℕ) (offset minus : Option ℤ)
    (ho : offset = some (-(m+1 : ℤ))) (hm : minus = some (-1)) :
    Functions.powQZ.apply q (Functions.addZ.apply offset (Functions.mulZ.apply minus (Functions.castNZ.apply n))) =
      Functions.powQN.apply (Functions.invQ.apply q) (Functions.addN.apply n (some (m+1))) := by
  rw [powerQZ,Spectral.powQ,Spectral.invQ]
  exact negative q n m offset minus ho hm

theorem powerRZ : Functions.powRZ.apply = (powerZ : Option ℝ → Option ℤ → Option ℝ) := by
  funext q n
  cases q with
  | none => rfl
  | some q =>
    cases n with
    | none => rfl
    | some n =>
      by_cases h : q ≠ 0 ∨ 0 ≤ n <;> simp [powerZ,Function2.apply,Functions.powRZ,h]

theorem naturalR (q : Option ℝ) (n : Option ℕ) :
    Functions.powRZ.apply q (Functions.castNZ.apply n) = Functions.powRN.apply q n := by
  rw [powerRZ,Spectral.powR]; exact natural q n

theorem negativeR (q : Option ℝ) (n : Option ℕ) (m : ℕ) (offset minus : Option ℤ)
    (ho : offset = some (-(m+1 : ℤ))) (hm : minus = some (-1)) :
    Functions.powRZ.apply q (Functions.addZ.apply offset (Functions.mulZ.apply minus (Functions.castNZ.apply n))) =
      Functions.powRN.apply (Value.inv q) (Functions.addN.apply n (some (m+1))) := by
  rw [powerRZ,Spectral.powR]
  exact negative q n m offset minus ho hm

theorem powerCZ : Functions.powCZ.apply = (powerZ : Option ℂ → Option ℤ → Option ℂ) := by
  funext q n
  cases q with
  | none => rfl
  | some q =>
    cases n with
    | none => rfl
    | some n =>
      by_cases h : q ≠ 0 ∨ 0 ≤ n <;> simp [powerZ,Function2.apply,Functions.powCZ,h]

theorem naturalC (q : Option ℂ) (n : Option ℕ) :
    Functions.powCZ.apply q (Functions.castNZ.apply n) = Functions.powCN.apply q n := by
  rw [powerCZ,Spectral.powC]; exact natural q n

theorem negativeC (q : Option ℂ) (n : Option ℕ) (m : ℕ) (offset minus : Option ℤ)
    (ho : offset = some (-(m+1 : ℤ))) (hm : minus = some (-1)) :
    Functions.powCZ.apply q (Functions.addZ.apply offset (Functions.mulZ.apply minus (Functions.castNZ.apply n))) =
      Functions.powCN.apply (Value.inv q) (Functions.addN.apply n (some (m+1))) := by
  rw [powerCZ,Spectral.powC]
  exact negative q n m offset minus ho hm

theorem negativeReverseQ (q : Option ℚ) (n : Option ℕ) (m : ℕ) (offset minus : Option ℤ)
    (ho : offset = some (-(m+1 : ℤ))) (hm : minus = some (-1)) :
    Functions.powQZ.apply q (Functions.addZ.apply (Functions.mulZ.apply minus (Functions.castNZ.apply n)) offset) =
      Functions.powQN.apply (Functions.invQ.apply q) (Functions.addN.apply n (some (m+1))) := by
  have hc (x y : Option ℤ) : Functions.addZ.apply x y = Functions.addZ.apply y x := by
    cases x <;> cases y <;> simp [Function2.apply,Functions.addZ,add_comm]
  rw [hc]; exact negativeQ q n m offset minus ho hm

theorem negativeReverseR (q : Option ℝ) (n : Option ℕ) (m : ℕ) (offset minus : Option ℤ)
    (ho : offset = some (-(m+1 : ℤ))) (hm : minus = some (-1)) :
    Functions.powRZ.apply q (Functions.addZ.apply (Functions.mulZ.apply minus (Functions.castNZ.apply n)) offset) =
      Functions.powRN.apply (Value.inv q) (Functions.addN.apply n (some (m+1))) := by
  have hc (x y : Option ℤ) : Functions.addZ.apply x y = Functions.addZ.apply y x := by
    cases x <;> cases y <;> simp [Function2.apply,Functions.addZ,add_comm]
  rw [hc]; exact negativeR q n m offset minus ho hm

theorem negativeReverseC (q : Option ℂ) (n : Option ℕ) (m : ℕ) (offset minus : Option ℤ)
    (ho : offset = some (-(m+1 : ℤ))) (hm : minus = some (-1)) :
    Functions.powCZ.apply q (Functions.addZ.apply (Functions.mulZ.apply minus (Functions.castNZ.apply n)) offset) =
      Functions.powCN.apply (Value.inv q) (Functions.addN.apply n (some (m+1))) := by
  have hc (x y : Option ℤ) : Functions.addZ.apply x y = Functions.addZ.apply y x := by
    cases x <;> cases y <;> simp [Function2.apply,Functions.addZ,add_comm]
  rw [hc]; exact negativeC q n m offset minus ho hm

end QSym.SummationPowers
