import QSym.Summation

noncomputable section
namespace QSym.SummationBounds

def realN (i : Option ℕ) : Option ℝ :=
  Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply i))
def realZ (i : Option ℤ) : Option ℝ :=
  Functions.castQR.apply (Functions.castZQ.apply i)
def ceilZ (b : Option ℝ) : Option ℤ := Functions.ceilR.apply b
def upperZ (b : Option ℝ) : Option ℤ := Functions.addZ.apply (Functions.floorR.apply b) (some 1)
def ceilN (b : Option ℝ) : Option ℕ := Functions.floorN.apply (realZ (ceilZ b))
def upperN (b : Option ℝ) : Option ℕ := Functions.floorN.apply (realZ (upperZ b))

private theorem floor_cast (z : ℤ) : Nat.floor (z : ℝ) = z.toNat := by
  rw [← Int.floor_toNat, Int.floor_intCast]

@[simp] theorem realN_some (i : ℕ) : realN (some i) = some (i : ℝ) := by
  simp [realN, Function1.apply, Functions.castNZ, Functions.castZQ, Functions.castQR]
@[simp] theorem realZ_some (i : ℤ) : realZ (some i) = some (i : ℝ) := by
  simp [realZ, Function1.apply, Functions.castZQ, Functions.castQR]
@[simp] theorem ceilN_some (b : ℝ) : ceilN (some b) = some (Int.ceil b).toNat := by
  have h : ceilZ (some b) = some (Int.ceil b) := by simp [ceilZ,Function1.apply,Functions.ceilR]
  rw [ceilN,h,realZ_some]
  simp only [Function1.apply,Functions.floorN,Option.bind,if_pos trivial]
  rw [floor_cast]
@[simp] theorem upperN_some (b : ℝ) : upperN (some b) = some (Int.floor b + 1).toNat := by
  have h : upperZ (some b) = some (Int.floor b + 1) := by
    simp [upperZ,Function1.apply,Function2.apply,Functions.floorR,Functions.addZ]
  rw [upperN,h,realZ_some]
  simp only [Function1.apply,Functions.floorN,Option.bind,if_pos trivial]
  rw [floor_cast]
@[simp] theorem ceilZ_some (b : ℝ) : ceilZ (some b) = some (Int.ceil b) := by
  simp [ceilZ,Function1.apply,Functions.ceilR]
@[simp] theorem upperZ_some (b : ℝ) : upperZ (some b) = some (Int.floor b + 1) := by
  simp [upperZ,Function1.apply,Function2.apply,Functions.floorR,Functions.addZ]


theorem roundN_lt (i : Option ℕ) (b : Option ℝ) :
    Value.lt (realN i) b = Functions.ltN.apply i (ceilN b) := by
  classical
  cases i with
  | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.lt,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltN,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
  | some i =>
    cases b with
    | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.lt,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltN,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
    | some b =>
      have h : i < (Int.ceil b).toNat ↔ (i : ℝ) < b := by
        have hz : i < (Int.ceil b).toNat ↔ (i : ℤ) < (Int.ceil b) := by omega
        rw [hz]
        simpa only [Int.cast_natCast, Int.lt_add_one_iff, Int.add_one_le_iff] using (Int.lt_ceil (a := b) (z := (i : ℤ)))
      rw [realN_some,ceilN_some]
      simp only [Value.lt,Function2.apply,Functions.ltN,Option.bind_eq_bind,Option.bind,pure,if_pos trivial,Option.some.injEq,decide_eq_decide]
      exact h.symm

theorem roundN_le (i : Option ℕ) (b : Option ℝ) :
    Value.le (realN i) b = Functions.ltN.apply i (upperN b) := by
  classical
  cases i with
  | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.le,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltN,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
  | some i =>
    cases b with
    | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.le,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltN,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
    | some b =>
      have h : i < (Int.floor b + 1).toNat ↔ (i : ℝ) ≤ b := by
        have hz : i < (Int.floor b + 1).toNat ↔ (i : ℤ) < (Int.floor b + 1) := by omega
        rw [hz]
        simpa only [Int.cast_natCast, Int.lt_add_one_iff, Int.add_one_le_iff] using (Int.le_floor (a := b) (z := (i : ℤ)))
      rw [realN_some,upperN_some]
      simp only [Value.le,Function2.apply,Functions.ltN,Option.bind_eq_bind,Option.bind,pure,if_pos trivial,Option.some.injEq,decide_eq_decide]
      exact h.symm

theorem roundN_gt (i : Option ℕ) (b : Option ℝ) :
    Value.lt b (realN i) = Functions.leN.apply (upperN b) i := by
  classical
  cases i with
  | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.lt,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leN,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
  | some i =>
    cases b with
    | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.lt,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leN,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
    | some b =>
      have h : (Int.floor b + 1).toNat ≤ i ↔ b < (i : ℝ) := by
        have hz : (Int.floor b + 1).toNat ≤ i ↔ (Int.floor b + 1) ≤ (i : ℤ) := by omega
        rw [hz]
        simpa only [Int.cast_natCast, Int.lt_add_one_iff, Int.add_one_le_iff] using (Int.floor_lt (a := b) (z := (i : ℤ)))
      rw [realN_some,upperN_some]
      simp only [Value.lt,Function2.apply,Functions.leN,Option.bind_eq_bind,Option.bind,pure,if_pos trivial,Option.some.injEq,decide_eq_decide]
      exact h.symm

theorem roundN_ge (i : Option ℕ) (b : Option ℝ) :
    Value.le b (realN i) = Functions.leN.apply (ceilN b) i := by
  classical
  cases i with
  | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.le,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leN,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
  | some i =>
    cases b with
    | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.le,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leN,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
    | some b =>
      have h : (Int.ceil b).toNat ≤ i ↔ b ≤ (i : ℝ) := by
        have hz : (Int.ceil b).toNat ≤ i ↔ (Int.ceil b) ≤ (i : ℤ) := by omega
        rw [hz]
        simpa only [Int.cast_natCast, Int.lt_add_one_iff, Int.add_one_le_iff] using (Int.ceil_le (a := b) (z := (i : ℤ)))
      rw [realN_some,ceilN_some]
      simp only [Value.le,Function2.apply,Functions.leN,Option.bind_eq_bind,Option.bind,pure,if_pos trivial,Option.some.injEq,decide_eq_decide]
      exact h.symm

theorem roundZ_lt (i : Option ℤ) (b : Option ℝ) :
    Value.lt (realZ i) b = Functions.ltZ.apply i (ceilZ b) := by
  classical
  cases i with
  | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.lt,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltZ,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
  | some i =>
    cases b with
    | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.lt,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltZ,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
    | some b =>
      have h : i < (Int.ceil b) ↔ (i : ℝ) < b := by
        simpa only [Int.cast_natCast, Int.lt_add_one_iff, Int.add_one_le_iff] using (Int.lt_ceil (a := b) (z := (i : ℤ)))
      rw [realZ_some,ceilZ_some]
      simp only [Value.lt,Function2.apply,Functions.ltZ,Option.bind_eq_bind,Option.bind,pure,if_pos trivial,Option.some.injEq,decide_eq_decide]
      exact h.symm

theorem roundZ_le (i : Option ℤ) (b : Option ℝ) :
    Value.le (realZ i) b = Functions.ltZ.apply i (upperZ b) := by
  classical
  cases i with
  | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.le,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltZ,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
  | some i =>
    cases b with
    | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.le,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.ltZ,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
    | some b =>
      have h : i < (Int.floor b + 1) ↔ (i : ℝ) ≤ b := by
        simpa only [Int.cast_natCast, Int.lt_add_one_iff, Int.add_one_le_iff] using (Int.le_floor (a := b) (z := (i : ℤ)))
      rw [realZ_some,upperZ_some]
      simp only [Value.le,Function2.apply,Functions.ltZ,Option.bind_eq_bind,Option.bind,pure,if_pos trivial,Option.some.injEq,decide_eq_decide]
      exact h.symm

theorem roundZ_gt (i : Option ℤ) (b : Option ℝ) :
    Value.lt b (realZ i) = Functions.leZ.apply (upperZ b) i := by
  classical
  cases i with
  | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.lt,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leZ,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
  | some i =>
    cases b with
    | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.lt,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leZ,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
    | some b =>
      have h : (Int.floor b + 1) ≤ i ↔ b < (i : ℝ) := by
        simpa only [Int.cast_natCast, Int.lt_add_one_iff, Int.add_one_le_iff] using (Int.floor_lt (a := b) (z := (i : ℤ)))
      rw [realZ_some,upperZ_some]
      simp only [Value.lt,Function2.apply,Functions.leZ,Option.bind_eq_bind,Option.bind,pure,if_pos trivial,Option.some.injEq,decide_eq_decide]
      exact h.symm

theorem roundZ_ge (i : Option ℤ) (b : Option ℝ) :
    Value.le b (realZ i) = Functions.leZ.apply (ceilZ b) i := by
  classical
  cases i with
  | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.le,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leZ,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
  | some i =>
    cases b with
    | none => simp [realN,realZ,ceilN,upperN,ceilZ,upperZ,Value.le,Function1.apply,Function2.apply,Functions.castNZ,Functions.castZQ,Functions.castQR,Functions.leZ,Functions.ceilR,Functions.floorR,Functions.floorN,Functions.addZ]
    | some b =>
      have h : (Int.ceil b) ≤ i ↔ b ≤ (i : ℝ) := by
        simpa only [Int.cast_natCast, Int.lt_add_one_iff, Int.add_one_le_iff] using (Int.ceil_le (a := b) (z := (i : ℤ)))
      rw [realZ_some,ceilZ_some]
      simp only [Value.le,Function2.apply,Functions.leZ,Option.bind_eq_bind,Option.bind,pure,if_pos trivial,Option.some.injEq,decide_eq_decide]
      exact h.symm

theorem rational_lt (a b : Option ℚ) : Functions.ltQ.apply a b =
    Value.lt (Functions.castQR.apply a) (Functions.castQR.apply b) := by
  cases a <;> cases b <;> simp [Function1.apply,Function2.apply,Functions.ltQ,Functions.castQR,Value.lt]
theorem rational_le (a b : Option ℚ) : Functions.leQ.apply a b =
    Value.le (Functions.castQR.apply a) (Functions.castQR.apply b) := by
  cases a <;> cases b <;> simp [Function1.apply,Function2.apply,Functions.leQ,Functions.castQR,Value.le]

end QSym.SummationBounds
