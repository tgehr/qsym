import QSym.SummationAlgebra

/-! Summation-only changes of representation. These are equalities of partial
values, including undefined coefficients and empty ranges. -/
noncomputable section
namespace QSym.SummationElementary
attribute [local instance] Classical.propDecidable

abbrev natR (n : Option ℕ) := Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply n))
abbrev natC (n : Option ℕ) := Functions.castRC.apply (natR n)

-- Match Expr's exact literal encodings at the binder boundary.
abbrev oneR : Option ℝ := some (((1 : ℤ) : ℝ))
abbrev minusR : Option ℝ := some (((-1 : ℤ) : ℝ))
abbrev twoR : Option ℝ := some (((2 : ℤ) : ℝ))
abbrev halfR : Option ℝ := some (((1 / 2 : ℚ) : ℝ))
abbrev halfC : Option ℂ := some (((1 / 2 : ℚ) : ℂ) + ((0 : ℚ) : ℂ) * Complex.I)
abbrev minusC : Option ℂ := some (((-1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I)
abbrev oneC : Option ℂ := some (((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * Complex.I)
abbrev imaginary : Option ℂ := some (((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * Complex.I)
abbrev minusHalfI : Option ℂ := some (((0 : ℚ) : ℂ) + ((-1 / 2 : ℚ) : ℂ) * Complex.I)

theorem expR_mul (x : Option ℝ) (n : Option ℕ) :
    Functions.expR.apply (Value.mul x (natR n)) =
      Functions.powRN.apply (Functions.expR.apply x) n := by
  cases x with
  | none => simp [natR, natC, Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.expR, Functions.powRN, Value.mul]
  | some x =>
    cases n with
    | none => simp [natR, natC, Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.expR, Functions.powRN, Value.mul]
    | some n =>
      simp only [Function1.apply, Function2.apply, Functions.expR, Functions.powRN, natR, natC, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Value.mul, Value.add, Complex.ofReal_mul, Complex.ofReal_natCast, Option.bind_some, if_pos trivial, Int.cast_natCast, Rat.cast_natCast, Option.some.injEq]
      simpa [mul_comm, mul_left_comm, _root_.mul_assoc] using Real.exp_nat_mul x n

theorem expR_mul_rev (x : Option ℝ) (n : Option ℕ) :
    Functions.expR.apply (Value.mul (natR n) x) =
      Functions.powRN.apply (Functions.expR.apply x) n := by
  have h : Value.mul (natR n) x = Value.mul x (natR n) := by
    cases natR n <;> cases x <;> simp [Value.mul, mul_comm]
  rw [h]; exact expR_mul x n

theorem expR_index (n : Option ℕ) :
    Functions.expR.apply (natR n) =
      Functions.powRN.apply (Functions.expR.apply oneR) n := by
  have h := expR_mul (some 1) n
  have hu : Value.mul (some 1) (natR n) = natR n := by
    cases natR n <;> simp [Value.mul]
  simpa [oneR, hu] using h

theorem expR_add (x y : Option ℝ) :
    Functions.expR.apply (Value.add x y) =
      Value.mul (Functions.expR.apply x) (Functions.expR.apply y) := by
  cases x <;> cases y <;> simp [Function1.apply, Function2.apply, Functions.expR, Functions.powRN, natR, natC, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Value.mul, Value.add, Real.exp_add, Complex.exp_add, Complex.ofReal_add, add_mul, mul_add]

theorem expC_mul (x : Option ℂ) (n : Option ℕ) :
    Functions.expC.apply (Value.mul x (natC n)) =
      Functions.powCN.apply (Functions.expC.apply x) n := by
  cases x with
  | none => simp [natR, natC, Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.expC, Functions.powCN, Value.mul]
  | some x =>
    cases n with
    | none => simp [natR, natC, Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.expC, Functions.powCN, Value.mul]
    | some n =>
      simp only [Function1.apply, Function2.apply, Functions.expC, Functions.powCN, natR, natC, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Value.mul, Value.add, Complex.ofReal_mul, Complex.ofReal_natCast, Option.bind_some, if_pos trivial, Int.cast_natCast, Rat.cast_natCast, Option.some.injEq]
      simpa [mul_comm, mul_left_comm, _root_.mul_assoc] using Complex.exp_nat_mul x n

theorem expC_mul_rev (x : Option ℂ) (n : Option ℕ) :
    Functions.expC.apply (Value.mul (natC n) x) =
      Functions.powCN.apply (Functions.expC.apply x) n := by
  have h : Value.mul (natC n) x = Value.mul x (natC n) := by
    cases natC n <;> cases x <;> simp [Value.mul, mul_comm]
  rw [h]; exact expC_mul x n

theorem expC_index (n : Option ℕ) :
    Functions.expC.apply (natC n) =
      Functions.powCN.apply (Functions.expC.apply oneC) n := by
  have h := expC_mul (some 1) n
  have hu : Value.mul (some 1) (natC n) = natC n := by
    cases natC n <;> simp [Value.mul]
  simpa [oneC, hu] using h

theorem expC_add (x y : Option ℂ) :
    Functions.expC.apply (Value.add x y) =
      Value.mul (Functions.expC.apply x) (Functions.expC.apply y) := by
  cases x <;> cases y <;> simp [Function1.apply, Function2.apply, Functions.expC, Functions.powCN, natR, natC, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Value.mul, Value.add, Real.exp_add, Complex.exp_add, Complex.ofReal_add, add_mul, mul_add]

theorem cis_mul (x : Option ℝ) (n : Option ℕ) :
    Functions.cisR.apply (Value.mul x (natR n)) =
      Functions.powCN.apply (Functions.cisR.apply x) n := by
  cases x with
  | none => simp [natR, natC, Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.cisR, Functions.powCN, Value.mul]
  | some x =>
    cases n with
    | none => simp [natR, natC, Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.cisR, Functions.powCN, Value.mul]
    | some n =>
      simp only [Function1.apply, Function2.apply, Functions.cisR, Functions.powCN, natR, natC, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Value.mul, Value.add, Complex.ofReal_mul, Complex.ofReal_natCast, Option.bind_some, if_pos trivial, Int.cast_natCast, Rat.cast_natCast, Option.some.injEq]
      simpa [mul_comm, mul_left_comm, _root_.mul_assoc] using Complex.exp_nat_mul (Complex.I * (x : ℂ)) n

theorem cis_mul_rev (x : Option ℝ) (n : Option ℕ) :
    Functions.cisR.apply (Value.mul (natR n) x) =
      Functions.powCN.apply (Functions.cisR.apply x) n := by
  have h : Value.mul (natR n) x = Value.mul x (natR n) := by
    cases natR n <;> cases x <;> simp [Value.mul, mul_comm]
  rw [h]; exact cis_mul x n

theorem cis_index (n : Option ℕ) :
    Functions.cisR.apply (natR n) =
      Functions.powCN.apply (Functions.cisR.apply oneR) n := by
  have h := cis_mul (some 1) n
  have hu : Value.mul (some 1) (natR n) = natR n := by
    cases natR n <;> simp [Value.mul]
  simpa [oneR, hu] using h

theorem cis_add (x y : Option ℝ) :
    Functions.cisR.apply (Value.add x y) =
      Value.mul (Functions.cisR.apply x) (Functions.cisR.apply y) := by
  cases x <;> cases y <;> simp [Function1.apply, Function2.apply, Functions.cisR, Functions.powCN, natR, natC, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Value.mul, Value.add, Real.exp_add, Complex.exp_add, Complex.ofReal_add, add_mul, mul_add]

theorem expi_mul (x : Option ℂ) (n : Option ℕ) :
    Functions.expiC.apply (Value.mul x (natC n)) =
      Functions.powCN.apply (Functions.expiC.apply x) n := by
  cases x with
  | none => simp [natR, natC, Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.expiC, Functions.powCN, Value.mul]
  | some x =>
    cases n with
    | none => simp [natR, natC, Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.expiC, Functions.powCN, Value.mul]
    | some n =>
      simp only [Function1.apply, Function2.apply, Functions.expiC, Functions.powCN, natR, natC, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Value.mul, Value.add, Complex.ofReal_mul, Complex.ofReal_natCast, Option.bind_some, if_pos trivial, Int.cast_natCast, Rat.cast_natCast, Option.some.injEq]
      simpa [mul_comm, mul_left_comm, _root_.mul_assoc] using Complex.exp_nat_mul (x * Complex.I) n

theorem expi_mul_rev (x : Option ℂ) (n : Option ℕ) :
    Functions.expiC.apply (Value.mul (natC n) x) =
      Functions.powCN.apply (Functions.expiC.apply x) n := by
  have h : Value.mul (natC n) x = Value.mul x (natC n) := by
    cases natC n <;> cases x <;> simp [Value.mul, mul_comm]
  rw [h]; exact expi_mul x n

theorem expi_index (n : Option ℕ) :
    Functions.expiC.apply (natC n) =
      Functions.powCN.apply (Functions.expiC.apply oneC) n := by
  have h := expi_mul (some 1) n
  have hu : Value.mul (some 1) (natC n) = natC n := by
    cases natC n <;> simp [Value.mul]
  simpa [oneC, hu] using h

theorem expi_add (x y : Option ℂ) :
    Functions.expiC.apply (Value.add x y) =
      Value.mul (Functions.expiC.apply x) (Functions.expiC.apply y) := by
  cases x <;> cases y <;> simp [Function1.apply, Function2.apply, Functions.expiC, Functions.powCN, natR, natC, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Value.mul, Value.add, Real.exp_add, Complex.exp_add, Complex.ofReal_add, add_mul, mul_add]

theorem powerR_natural (x : Option ℝ) (n : Option ℕ) :
    Functions.powerR.apply x (natR n) = Functions.powRN.apply x n := by
  cases x with
  | none => rfl
  | some x =>
    cases n with
    | none => rfl
    | some n =>
      have h : 0 < x ∨ x = 0 ∧ 0 ≤ (n : ℝ) ∨ x < 0 ∧ ∃ k : ℤ, (n : ℝ) = k := by
        rcases lt_trichotomy 0 x with hp | hz | hn
        · exact Or.inl hp
        · exact Or.inr (Or.inl ⟨hz.symm, Nat.cast_nonneg n⟩)
        · exact Or.inr (Or.inr ⟨hn, n, by simp⟩)
      simp [Function1.apply, Function2.apply, Functions.powerR, Functions.powRN,
        natR, Functions.castNZ, Functions.castZQ, Functions.castQR, h, Real.rpow_natCast]
      intro hx hn; exact ⟨lt_of_le_of_ne hx hn, n, by simp⟩

theorem powerC_natural (x : Option ℂ) (n : Option ℕ) :
    Functions.powerC.apply x (natC n) = Functions.powCN.apply x n := by
  cases x with
  | none => rfl
  | some x =>
    cases n with
    | none => rfl
    | some n =>
      have h : x ≠ 0 ∨ (n : ℂ) = 0 ∨ 0 < (n : ℂ).re ∧ (n : ℂ).im = 0 := by
        cases n with
        | zero => simp
        | succ n => exact Or.inr (Or.inr ⟨by simpa using (Nat.cast_pos.mpr (Nat.succ_pos n) : (0:ℝ) < (n+1:ℕ)), by simp⟩)
      simp [Function1.apply, Function2.apply, Functions.powerC, Functions.powCN,
        natR, natC, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC,
        h, Complex.cpow_natCast]

theorem constant {K : Type} [Semiring K] [TopologicalSpace K] [T2Space K] (c : Option K) (n : Option ℕ) :
    Summation.rangeValue (some (fun _ => c)) n =
      Value.mask (Functions.nonzeroN.apply n) (Value.mul (n.map fun k => (k : K)) c) := by
  cases n with
  | none => rfl
  | some n =>
    cases n with
    | zero => simp [Summation.rangeValue, Summation.finite, Value.mask, Function1.apply,
        Functions.nonzeroN]
    | succ n =>
      cases c with
      | none => simp [Summation.rangeValue, Value.mask, Value.mul, Function1.apply,
          Functions.nonzeroN, SummationAlgebra.finite_none_succ]
      | some c => simp [Summation.rangeValue, Summation.finite, Value.mask, Value.mul,
          Function1.apply, Functions.nonzeroN, Finset.sum_const, nsmul_eq_mul, Nat.cast_succ]

theorem constantN (c : Option ℕ) (n : Option ℕ) :
    Summation.rangeValue (some (fun _ => c)) n =
      Value.mask (Functions.nonzeroN.apply n) (Functions.mulN.apply (n) c) := by
  have h := constant c n
  cases n <;> cases c <;> simpa [RepeatedSpectra.natCast, Function1.apply, Function2.apply, Functions.mulN,
    Functions.mulZ, Functions.mulQ, Value.mul, natR, natC, Functions.castNZ,
    Functions.castZQ, Functions.castQR, Functions.castRC] using h

theorem constantZ (c : Option ℤ) (n : Option ℕ) :
    Summation.rangeValue (some (fun _ => c)) n =
      Value.mask (Functions.nonzeroN.apply n) (Functions.mulZ.apply (Functions.castNZ.apply n) c) := by
  have h := constant c n
  cases n <;> cases c <;> simpa [RepeatedSpectra.natCast, Function1.apply, Function2.apply, Functions.mulN,
    Functions.mulZ, Functions.mulQ, Value.mul, natR, natC, Functions.castNZ,
    Functions.castZQ, Functions.castQR, Functions.castRC] using h

theorem constantQ (c : Option ℚ) (n : Option ℕ) :
    Summation.rangeValue (some (fun _ => c)) n =
      Value.mask (Functions.nonzeroN.apply n) (Functions.mulQ.apply (Functions.castZQ.apply (Functions.castNZ.apply n)) c) := by
  have h := constant c n
  cases n <;> cases c <;> simpa [RepeatedSpectra.natCast, Function1.apply, Function2.apply, Functions.mulN,
    Functions.mulZ, Functions.mulQ, Value.mul, natR, natC, Functions.castNZ,
    Functions.castZQ, Functions.castQR, Functions.castRC] using h

theorem constantR (c : Option ℝ) (n : Option ℕ) :
    Summation.rangeValue (some (fun _ => c)) n =
      Value.mask (Functions.nonzeroN.apply n) (Value.mul (natR n) c) := by
  have h := constant c n
  cases n <;> cases c <;> simpa [RepeatedSpectra.natCast, Function1.apply, Function2.apply, Functions.mulN,
    Functions.mulZ, Functions.mulQ, Value.mul, natR, natC, Functions.castNZ,
    Functions.castZQ, Functions.castQR, Functions.castRC] using h

theorem constantC (c : Option ℂ) (n : Option ℕ) :
    Summation.rangeValue (some (fun _ => c)) n =
      Value.mask (Functions.nonzeroN.apply n) (Value.mul (natC n) c) := by
  have h := constant c n
  cases n <;> cases c <;> simpa [RepeatedSpectra.natCast, Function1.apply, Function2.apply, Functions.mulN,
    Functions.mulZ, Functions.mulQ, Value.mul, natR, natC, Functions.castNZ,
    Functions.castZQ, Functions.castQR, Functions.castRC] using h

theorem castNZ_mul (x y : Option ℕ) :
    Functions.castNZ.apply (Functions.mulN.apply x y) =
      Functions.mulZ.apply (Functions.castNZ.apply x) (Functions.castNZ.apply y) := by
  cases x <;> cases y <;> simp [Function1.apply, Function2.apply, Functions.castNZ,
    Functions.mulN, Functions.mulZ, Functions.mulQ, Value.mul]

theorem castZQ_mul (x y : Option ℤ) :
    Functions.castZQ.apply (Functions.mulZ.apply x y) =
      Functions.mulQ.apply (Functions.castZQ.apply x) (Functions.castZQ.apply y) := by
  cases x <;> cases y <;> simp [Function1.apply, Function2.apply, Functions.castZQ,
    Functions.mulN, Functions.mulZ, Functions.mulQ, Value.mul]

theorem castQR_mul (x y : Option ℚ) :
    Functions.castQR.apply (Functions.mulQ.apply x y) =
      Value.mul (Functions.castQR.apply x) (Functions.castQR.apply y) := by
  cases x <;> cases y <;> simp [Function1.apply, Function2.apply, Functions.castQR,
    Functions.mulN, Functions.mulZ, Functions.mulQ, Value.mul]

theorem castRC_mul (x y : Option ℝ) :
    Functions.castRC.apply (Value.mul x y) =
      Value.mul (Functions.castRC.apply x) (Functions.castRC.apply y) := by
  cases x <;> cases y <;> simp [Function1.apply, Function2.apply, Functions.castRC,
    Functions.mulN, Functions.mulZ, Functions.mulQ, Value.mul]

theorem powN_mul (x : Option ℕ) (m n : Option ℕ) :
    Functions.powNN.apply x (Functions.mulN.apply m n) =
      Functions.powNN.apply (Functions.powNN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powNN, Functions.mulN, pow_mul]

theorem powN_mul_rev (x : Option ℕ) (m n : Option ℕ) :
    Functions.powNN.apply x (Functions.mulN.apply n m) =
      Functions.powNN.apply (Functions.powNN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powNN, Functions.mulN, pow_mul, Nat.mul_comm]

theorem powZ_mul (x : Option ℤ) (m n : Option ℕ) :
    Functions.powZN.apply x (Functions.mulN.apply m n) =
      Functions.powZN.apply (Functions.powZN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powZN, Functions.mulN, pow_mul]

theorem powZ_mul_rev (x : Option ℤ) (m n : Option ℕ) :
    Functions.powZN.apply x (Functions.mulN.apply n m) =
      Functions.powZN.apply (Functions.powZN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powZN, Functions.mulN, pow_mul, Nat.mul_comm]

theorem powQ_mul (x : Option ℚ) (m n : Option ℕ) :
    Functions.powQN.apply x (Functions.mulN.apply m n) =
      Functions.powQN.apply (Functions.powQN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powQN, Functions.mulN, pow_mul]

theorem powQ_mul_rev (x : Option ℚ) (m n : Option ℕ) :
    Functions.powQN.apply x (Functions.mulN.apply n m) =
      Functions.powQN.apply (Functions.powQN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powQN, Functions.mulN, pow_mul, Nat.mul_comm]

theorem powR_mul (x : Option ℝ) (m n : Option ℕ) :
    Functions.powRN.apply x (Functions.mulN.apply m n) =
      Functions.powRN.apply (Functions.powRN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powRN, Functions.mulN, pow_mul]

theorem powR_mul_rev (x : Option ℝ) (m n : Option ℕ) :
    Functions.powRN.apply x (Functions.mulN.apply n m) =
      Functions.powRN.apply (Functions.powRN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powRN, Functions.mulN, pow_mul, Nat.mul_comm]

theorem powC_mul (x : Option ℂ) (m n : Option ℕ) :
    Functions.powCN.apply x (Functions.mulN.apply m n) =
      Functions.powCN.apply (Functions.powCN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powCN, Functions.mulN, pow_mul]

theorem powC_mul_rev (x : Option ℂ) (m n : Option ℕ) :
    Functions.powCN.apply x (Functions.mulN.apply n m) =
      Functions.powCN.apply (Functions.powCN.apply x m) n := by
  cases x <;> cases m <;> cases n <;>
    simp [Function2.apply, Functions.powCN, Functions.mulN, pow_mul, Nat.mul_comm]

theorem mul_swap {K : Type} [CommSemigroup K] (x y : Option K) :
    Value.mul x y = Value.mul y x := by
  cases x <;> cases y <;> simp [Value.mul, mul_comm]

theorem mul_assoc {K : Type} [Semigroup K] (x y z : Option K) :
    Value.mul x (Value.mul y z) = Value.mul (Value.mul x y) z := by
  cases x <;> cases y <;> cases z <;> simp [Value.mul, _root_.mul_assoc]

theorem finite_scale {K : Type} [Semiring K] [TopologicalSpace K] [T2Space K] (c : K) (f : ℕ → Option K) (n : ℕ) :
    Summation.finite (Finset.range n) (fun i => Value.mul (some c) (f i)) =
      Value.mul (some c) (Summation.finite (Finset.range n) f) := by
  induction n with
  | zero => simp [Summation.finite, Value.mul]
  | succ n ih =>
    rw [Summation.range_succ, Summation.range_succ, ih]
    cases Summation.finite (Finset.range n) f <;> cases f n <;>
      simp [Value.mul, mul_add]

theorem scale {K : Type} [CommSemiring K] [TopologicalSpace K] [T2Space K] (mul : Option K → Option K → Option K)
    (hm : mul = Value.mul) (c : Option K) (f : ℕ → Option K) (n : Option ℕ) :
    Summation.rangeValue (some (fun i => mul c (f i))) n =
      Value.mask (Functions.nonzeroN.apply n) (mul c (Summation.rangeValue (some f) n)) := by
  rw [hm]
  cases n with
  | none => rfl
  | some n =>
    cases n with
    | zero => simp [Summation.rangeValue, Summation.finite, Value.mask,
        Function1.apply, Functions.nonzeroN]
    | succ n =>
      cases c with
      | none => simp [Summation.rangeValue, Value.mul, Value.mask, Function1.apply,
          Functions.nonzeroN, SummationAlgebra.finite_none_succ]
      | some c => simpa [Summation.rangeValue, Value.mask, Function1.apply,
          Functions.nonzeroN] using finite_scale c f (n+1)

theorem scale_rev {K : Type} [CommSemiring K] [TopologicalSpace K] [T2Space K] (mul : Option K → Option K → Option K)
    (hm : mul = Value.mul) (c : Option K) (f : ℕ → Option K) (n : Option ℕ) :
    Summation.rangeValue (some (fun i => mul (f i) c)) n =
      Value.mask (Functions.nonzeroN.apply n) (mul c (Summation.rangeValue (some f) n)) := by
  have hc : ∀ i, mul (f i) c = mul c (f i) := by intro i; rw [hm]; exact mul_swap _ _
  simp_rw [hc]; exact scale mul hm c f n

theorem sin_phase (x : Option ℝ) :
    Functions.sinR.apply x = Functions.imC.apply (Functions.cisR.apply x) := by
  cases x <;> simp [Function1.apply, Functions.sinR, Functions.imC, Functions.cisR,
    Complex.exp_mul_I, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_sin, ← Complex.ofReal_cos]

theorem cos_phase (x : Option ℝ) :
    Functions.cosR.apply x = Functions.reC.apply (Functions.cisR.apply x) := by
  cases x <;> simp [Function1.apply, Functions.cosR, Functions.reC, Functions.cisR,
    Complex.exp_mul_I, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_sin, ← Complex.ofReal_cos]

theorem sinhR_exp (x : Option ℝ) :
    Functions.sinhR.apply x = Value.mul halfR
      (Value.add (Functions.expR.apply x) (Value.mul minusR (Functions.expR.apply (Value.mul minusR x)))) := by
  cases x <;> simp [minusR, halfR, halfC, minusC, imaginary, minusHalfI, Function1.apply, Functions.sinhR, Functions.expR,
    Value.mul, Value.add, Real.sinh_eq, div_eq_mul_inv, sub_eq_add_neg] <;> ring

theorem sinhC_exp (x : Option ℂ) :
    Functions.sinhC.apply x = Value.mul halfC
      (Value.add (Functions.expC.apply x) (Value.mul minusC (Functions.expC.apply (Value.mul minusC x)))) := by
  cases x <;> simp [halfR, halfC, minusC, imaginary, minusHalfI, Function1.apply, Functions.sinhC, Functions.expC,
    Value.mul, Value.add, Complex.sinh, div_eq_mul_inv, sub_eq_add_neg] <;> ring

theorem coshR_exp (x : Option ℝ) :
    Functions.coshR.apply x = Value.mul halfR
      (Value.add (Functions.expR.apply x) (Functions.expR.apply (Value.mul minusR x))) := by
  cases x <;> simp [minusR, halfR, halfC, minusC, imaginary, minusHalfI, Function1.apply, Functions.coshR, Functions.expR,
    Value.mul, Value.add, Real.cosh_eq, div_eq_mul_inv, sub_eq_add_neg] <;> ring

theorem coshC_exp (x : Option ℂ) :
    Functions.coshC.apply x = Value.mul halfC
      (Value.add (Functions.expC.apply x) (Functions.expC.apply (Value.mul minusC x))) := by
  cases x <;> simp [halfR, halfC, minusC, imaginary, minusHalfI, Function1.apply, Functions.coshC, Functions.expC,
    Value.mul, Value.add, Complex.cosh, div_eq_mul_inv, sub_eq_add_neg] <;> ring

theorem finite_map {A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    [TopologicalSpace A] [T2Space A] [TopologicalSpace B] [T2Space B]
    (g : A → B) (hz : g 0 = 0) (ha : ∀ x y, g (x+y) = g x + g y)
    (f : ℕ → Option A) (n : ℕ) :
    Summation.finite (Finset.range n) (fun i => (f i).map g) =
      (Summation.finite (Finset.range n) f).map g := by
  induction n with
  | zero => simp [Summation.finite, hz]
  | succ n ih =>
    rw [Summation.range_succ, Summation.range_succ, ih]
    cases Summation.finite (Finset.range n) f <;> cases f n <;> simp [ha]

-- A condition independent of the index is required only on nonempty ranges.
-- Put the empty-range test first: it must also bypass an undefined condition.
theorem range_guard {A : Type} [AddCommMonoid A] [TopologicalSpace A] [T2Space A]
    (p : Option Bool) (f : ℕ → Option A) (n : Option ℕ) :
    Summation.rangeValue (some (fun i => Binding.guardValue p (f i))) n =
      Binding.guardValue (Value.or (Value.not (Functions.nonzeroN.apply n)) p)
        (Summation.rangeValue (some f) n) := by
  cases n with
  | none => rfl
  | some n =>
    cases n with
    | zero => simp [Summation.rangeValue, Summation.finite, Binding.guardValue,
        Value.or, Value.not, Function1.apply, Functions.nonzeroN]
    | succ n =>
      cases p with
      | none => simp [Summation.rangeValue, Binding.guardValue, Value.or, Value.not,
          Function1.apply, Functions.nonzeroN, SummationAlgebra.finite_none_succ]
      | some b => cases b <;> simp [Summation.rangeValue, Binding.guardValue,
          Value.or, Value.not, Function1.apply, Functions.nonzeroN,
          SummationAlgebra.finite_none_succ]

theorem range_re (f : ℕ → Option ℂ) (n : Option ℕ) :
    Summation.rangeValue (some (fun i => Functions.reC.apply (f i))) n =
      Functions.reC.apply (Summation.rangeValue (some f) n) := by
  have h : ∀ z, Functions.reC.apply z = z.map Complex.re := by
    intro z; cases z <;> simp [Function1.apply, Functions.reC, Functions.imC]
  simp_rw [h]
  cases n with
  | none => rfl
  | some n => exact finite_map Complex.re rfl (fun _ _ => rfl) f n

theorem range_im (f : ℕ → Option ℂ) (n : Option ℕ) :
    Summation.rangeValue (some (fun i => Functions.imC.apply (f i))) n =
      Functions.imC.apply (Summation.rangeValue (some f) n) := by
  have h : ∀ z, Functions.imC.apply z = z.map Complex.im := by
    intro z; cases z <;> simp [Function1.apply, Functions.reC, Functions.imC]
  simp_rw [h]
  cases n with
  | none => rfl
  | some n => exact finite_map Complex.im rfl (fun _ _ => rfl) f n

theorem sinC_exp (x : Option ℂ) :
    Functions.sinC.apply x = Value.mul minusHalfI
      (Value.add (Functions.expC.apply (Value.mul imaginary x)) (Value.mul minusC (Functions.expC.apply (Value.mul minusC (Value.mul imaginary x))))) := by
  cases x <;> simp [halfR, halfC, minusC, imaginary, minusHalfI, Function1.apply, Functions.sinC, Functions.expC,
    Value.mul, Value.add, Complex.sin, div_eq_mul_inv, sub_eq_add_neg, mul_comm] <;> ring

theorem cosC_exp (x : Option ℂ) :
    Functions.cosC.apply x = Value.mul halfC
      (Value.add (Functions.expC.apply (Value.mul imaginary x)) (Functions.expC.apply (Value.mul minusC (Value.mul imaginary x)))) := by
  cases x <;> simp [halfR, halfC, minusC, imaginary, minusHalfI, Function1.apply, Functions.cosC, Functions.expC,
    Value.mul, Value.add, Complex.cos, div_eq_mul_inv, sub_eq_add_neg, mul_comm] <;> ring

theorem exp2_exp (x : Option ℝ) :
    Functions.exp2R.apply x = Functions.expR.apply
      (Value.mul (Functions.logR.apply twoR) x) := by
  cases x <;> simp [twoR, Function1.apply, Functions.exp2R, Functions.expR, Functions.logR,
    Value.mul, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]

end QSym.SummationElementary
