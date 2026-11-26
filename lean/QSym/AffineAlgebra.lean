import QSym.RefinementBase

namespace QSym.Value
variable {R : Type} [CommSemiring R]

theorem spectral_interpolation (a b p q z : Option R) :
    mul (add (mul a p) (mul b q)) z = add (mul (mul a z) p) (mul (mul b z) q) := by
  cases a <;> cases b <;> cases p <;> cases q <;> cases z <;>
    simp [add, mul] <;> ring

theorem spectral_interpolationQ (a b p q z : Option ℚ) :
    Functions.mulQ.apply (Functions.addQ.apply (Functions.mulQ.apply a p) (Functions.mulQ.apply b q)) z =
      Functions.addQ.apply (Functions.mulQ.apply (Functions.mulQ.apply a z) p)
        (Functions.mulQ.apply (Functions.mulQ.apply b z) q) := by
  cases a <;> cases b <;> cases p <;> cases q <;> cases z <;>
    simp [Function2.apply, Functions.addQ, Functions.mulQ] <;> ring

theorem affine_add (a b c d x : Option R) :
    add (add (mul a x) b) (add (mul c x) d) = add (mul (add a c) x) (add b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;>
    simp [add, mul] <;> ring

theorem affine_left (c a b x : Option R) :
    mul c (add (mul a x) b) = add (mul (mul c a) x) (mul c b) := by
  cases c <;> cases a <;> cases b <;> cases x <;>
    simp [add, mul] <;> ring

theorem affine_right (a b c x : Option R) :
    mul (add (mul a x) b) c = add (mul (mul a c) x) (mul b c) := by
  cases a <;> cases b <;> cases c <;> cases x <;>
    simp [add, mul] <;> ring

/- The discrete scalar frontends present addition and multiplication as
everywhere-defined Function2 operations. Transport the affine identities once,
before any case split on the five partial operands. -/
private noncomputable abbrev totalAdd := (⟨(·+·), fun _ _ => True⟩ : Function2 R R R).apply
private noncomputable abbrev totalMul := (⟨(·*·), fun _ _ => True⟩ : Function2 R R R).apply

private theorem totalAdd_eq : totalAdd (R := R) = add := by
  funext x y; cases x <;> cases y <;> simp [totalAdd, Function2.apply, add]

private theorem totalMul_eq : totalMul (R := R) = mul := by
  funext x y; cases x <;> cases y <;> simp [totalMul, Function2.apply, mul]

theorem affine_add_total (a b c d x : Option R) :
    totalAdd (totalAdd (totalMul a x) b) (totalAdd (totalMul c x) d) =
      totalAdd (totalMul (totalAdd a c) x) (totalAdd b d) := by
  simpa only [totalAdd_eq, totalMul_eq] using affine_add a b c d x

theorem affine_left_total (c a b x : Option R) :
    totalMul c (totalAdd (totalMul a x) b) = totalAdd (totalMul (totalMul c a) x) (totalMul c b) := by
  simpa only [totalAdd_eq, totalMul_eq] using affine_left c a b x

theorem affine_right_total (a b c x : Option R) :
    totalMul (totalAdd (totalMul a x) b) c = totalAdd (totalMul (totalMul a c) x) (totalMul b c) := by
  simpa only [totalAdd_eq, totalMul_eq] using affine_right a b c x

end QSym.Value

namespace QSym.Value

set_option maxHeartbeats 1000000 in
theorem spectral_repeated {K : Type} [Field K] (x y r n z : Option K) :
    mul (mul (add (mul x r) (mul n (add y (mul (some (-1)) (mul x r))))) (inv r)) z =
      mul (add x (mul n (add (mul y (inv r)) (mul (some (-1)) x)))) z := by
  cases r with
  | none => cases x <;> cases y <;> cases n <;> cases z <;> rfl
  | some r =>
    by_cases hr : r=0
    · subst r; cases x <;> cases y <;> cases n <;> cases z <;> simp [add, mul, inv]
    · cases x <;> cases y <;> cases n <;> cases z <;> simp [add, mul, inv, hr]
      field_simp

set_option maxHeartbeats 1000000 in
theorem spectral_repeatedQ (x y r n z : Option ℚ) :
    Functions.mulQ.apply (Functions.mulQ.apply (Functions.addQ.apply (Functions.mulQ.apply x r)
      (Functions.mulQ.apply n (Functions.addQ.apply y (Functions.mulQ.apply (some (-1)) (Functions.mulQ.apply x r))))) (Functions.invQ.apply r)) z =
      Functions.mulQ.apply (Functions.addQ.apply x (Functions.mulQ.apply n
        (Functions.addQ.apply (Functions.mulQ.apply y (Functions.invQ.apply r)) (Functions.mulQ.apply (some (-1)) x)))) z := by
  cases x <;> cases y <;> cases r <;> cases n <;> cases z <;>
    simp [Function2.apply, Function1.apply, Functions.addQ, Functions.mulQ, Functions.invQ]
  split <;> simp_all <;> field_simp

end QSym.Value
