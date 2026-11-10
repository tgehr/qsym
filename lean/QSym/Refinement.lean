import QSym.Expr
import QSym.Elementary
import QSym.Order
import QSym.FunctionOrder
import QSym.Identities

namespace QSym.Value

theorem and_some (p q : Bool) : and (some p) (some q) = some (p && q) := by cases p <;> rfl
theorem or_some (p q : Bool) : or (some p) (some q) = some (p || q) := by cases p <;> rfl

def Refines {α : Type} (x y : Option α) : Prop := ∀ v, x = some v → y = some v

theorem refines_refl {α : Type} (x : Option α) : Refines x x := fun _ h => h
theorem refines_of_eq {α : Type} {x y : Option α} (h : x = y) : Refines x y := by
  subst y; exact refines_refl x
theorem Refines.trans {α : Type} {x y z : Option α}
    (h : Refines x y) (k : Refines y z) : Refines x z := fun v hv => k v (h v hv)
theorem Refines.antisymm {α : Type} {x y : Option α}
    (h : Refines x y) (k : Refines y x) : x = y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some v => have impossible := k v rfl; cases impossible
  | some v => exact (h v rfl).symm
theorem Refines.defined {α : Type} {x y : Option α}
    (h : Refines x y) (hx : Defined x) : Defined y := by
  obtain ⟨v, hv⟩ := hx
  exact ⟨v, h v hv⟩
theorem Refines.eq_of_defined {α : Type} {x y : Option α}
    (h : Refines x y) (hx : Defined x) : x = y := by
  obtain ⟨v, hv⟩ := hx
  exact hv.trans (h v hv).symm

theorem refines_bind {α β : Type} {x y : Option α} {f g : α → Option β}
    (h : Refines x y) (k : ∀ v, Refines (f v) (g v)) :
    Refines (x.bind f) (y.bind g) := by
  cases x with
  | none => intro v hv; cases hv
  | some a => rw [h a rfl]; exact k a

theorem refines_map {α β : Type} (f : α → β) {x y : Option α}
    (h : Refines x y) : Refines (x.map f) (y.map f) := by
  cases x with
  | none => intro v hv; cases hv
  | some a => rw [h a rfl]; exact refines_refl _

theorem refines_function1 {α β} (f : Function1 α β) {x y : Option α} (h : Refines x y) :
    Refines (f.apply x) (f.apply y) := refines_bind h (fun _ => refines_refl _)
theorem refines_function2 {α β γ} (f : Function2 α β γ) {x y : Option α} {a b : Option β}
    (h : Refines x y) (k : Refines a b) : Refines (f.apply x a) (f.apply y b) :=
  refines_bind h (fun _ => refines_bind k (fun _ => refines_refl _))

theorem refines_add {α : Type} [Add α] {a b x y : Option α}
    (h : Refines a x) (k : Refines b y) : Refines (add a b) (add x y) := by
  cases a with
  | none => intro v hv; cases hv
  | some a =>
    cases b with
    | none => intro v hv; cases hv
    | some b => rw [h a rfl, k b rfl]; exact refines_refl _

theorem refines_mul {α : Type} [Mul α] {a b x y : Option α}
    (h : Refines a x) (k : Refines b y) : Refines (mul a b) (mul x y) := by
  cases a with
  | none => intro v hv; cases hv
  | some a =>
    cases b with
    | none => intro v hv; cases hv
    | some b => rw [h a rfl, k b rfl]; exact refines_refl _

theorem refines_inv {α : Type} [Zero α] [Inv α] {a b : Option α}
    (h : Refines a b) : Refines (inv a) (inv b) :=
  refines_bind h (fun _ => refines_refl _)

private theorem quotient_add_eq_zero {α : Type} [Field α] (x y z : α) (hy : y≠0) :
    x*y⁻¹+z=0 ↔ x+y*z=0 := by
  have h : (x*y⁻¹+z)*y=x+y*z := by
    calc
      (x*y⁻¹+z)*y=x*(y⁻¹*y)+y*z := by ring
      _=x+y*z := by rw [inv_mul_cancel₀ hy]; simp
  rw [← h, mul_eq_zero]
  simp [hy]

theorem refines_quotient_add_nonzero {α : Type} [Field α] (x y z : Option α) :
    Refines (nonzero (add (mul x (inv y)) z)) (nonzero (add x (mul y z))) := by
  classical
  cases x <;> cases y <;> cases z <;> simp [Refines, nonzero, add, mul, inv]
  next x y z =>
    by_cases hy : y=0
    · simp [hy, mul, add, nonzero]
    · simp [hy, mul, add, nonzero, quotient_add_eq_zero x y z hy]

theorem refines_inv_inv {α : Type} [DivisionRing α] (x : Option α) :
    Refines (inv (inv x)) x := by
  cases x with
  | none => simp [Refines, inv]
  | some x => by_cases h : x = 0 <;> simp [Refines, inv, h]

theorem refines_nonzero {α : Type} [Zero α] {a b : Option α}
    (h : Refines a b) : Refines (nonzero a) (nonzero b) :=
  refines_map _ h

theorem refines_conj {a b : Option ℂ} (h : Refines a b) : Refines (conj a) (conj b) :=
  refines_map _ h

theorem refines_not {p q : Option Bool} (h : Refines p q) : Refines (not p) (not q) :=
  refines_map _ h
theorem refines_and {p q x y : Option Bool} (h : Refines p x) (k : Refines q y) :
    Refines (and p q) (and x y) := by
  cases p with
  | none => intro v hv; cases hv
  | some p => rw [h p rfl]; cases p <;> first | exact refines_refl _ | exact k
theorem refines_or {p q x y : Option Bool} (h : Refines p x) (k : Refines q y) :
    Refines (or p q) (or x y) := by
  cases p with
  | none => intro v hv; cases hv
  | some p => rw [h p rfl]; cases p <;> first | exact refines_refl _ | exact k
theorem refines_lt {a b x y : Option ℝ} (h : Refines a x) (k : Refines b y) :
    Refines (lt a b) (lt x y) := refines_bind h (fun _ => refines_bind k (fun _ => refines_refl _))
theorem refines_le {a b x y : Option ℝ} (h : Refines a x) (k : Refines b y) :
    Refines (le a b) (le x y) := refines_bind h (fun _ => refines_bind k (fun _ => refines_refl _))

theorem refines_increasing_lt {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (h : FunctionOrder.Increasing f) : Refines (lt (f.apply x) (f.apply y)) (lt x y) := by
  classical
  cases x <;> cases y <;> simp [Refines, lt, Function1.apply]
  next a b =>
    by_cases ha : f.domain a
    · by_cases hb : f.domain b
      · simp [ha, hb, ← sub_eq_add_neg, sub_eq_zero, StrictMonoOn.lt_iff_lt h ha hb]
      · simp [ha, hb]
    · simp [ha]

theorem refines_increasing_le {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (h : FunctionOrder.Increasing f) : Refines (le (f.apply x) (f.apply y)) (le x y) := by
  classical
  cases x <;> cases y <;> simp [Refines, le, Function1.apply]
  next a b =>
    by_cases ha : f.domain a
    · by_cases hb : f.domain b
      · simp [ha, hb, ← sub_eq_add_neg, sub_eq_zero, StrictMonoOn.le_iff_le h ha hb]
      · simp [ha, hb]
    · simp [ha]

theorem refines_increasing_ne {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (h : FunctionOrder.Increasing f) : Refines (nonzero (add (f.apply x) (mul (some (-1)) (f.apply y)))) (nonzero (add x (mul (some (-1)) y))) := by
  classical
  cases x <;> cases y <;> simp [Refines, nonzero, add, mul, Function1.apply]
  next a b =>
    by_cases ha : f.domain a
    · by_cases hb : f.domain b
      · simp [ha, hb, ← sub_eq_add_neg, sub_eq_zero, StrictMonoOn.eq_iff_eq h ha hb]
      · simp [ha, hb]
    · simp [ha]

theorem refines_decreasing_lt {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (h : FunctionOrder.Decreasing f) : Refines (lt (f.apply x) (f.apply y)) (lt y x) := by
  classical
  cases x <;> cases y <;> simp [Refines, lt, Function1.apply]
  next a b =>
    by_cases ha : f.domain a
    · by_cases hb : f.domain b
      · simp [ha, hb, ← sub_eq_add_neg, sub_eq_zero, StrictAntiOn.lt_iff_lt h ha hb]
      · simp [ha, hb]
    · simp [ha]

theorem refines_decreasing_le {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (h : FunctionOrder.Decreasing f) : Refines (le (f.apply x) (f.apply y)) (le y x) := by
  classical
  cases x <;> cases y <;> simp [Refines, le, Function1.apply]
  next a b =>
    by_cases ha : f.domain a
    · by_cases hb : f.domain b
      · simp [ha, hb, ← sub_eq_add_neg, sub_eq_zero, StrictAntiOn.le_iff_le h ha hb]
      · simp [ha, hb]
    · simp [ha]

theorem refines_decreasing_ne {f : Function1 ℝ ℝ} (x y : Option ℝ)
    (h : FunctionOrder.Decreasing f) : Refines (nonzero (add (f.apply x) (mul (some (-1)) (f.apply y)))) (nonzero (add x (mul (some (-1)) y))) := by
  classical
  cases x <;> cases y <;> simp [Refines, nonzero, add, mul, Function1.apply]
  next a b =>
    by_cases ha : f.domain a
    · by_cases hb : f.domain b
      · simp [ha, hb, ← sub_eq_add_neg, sub_eq_zero, (StrictAntiOn.eq_iff_eq h ha hb).trans eq_comm]
      · simp [ha, hb]
    · simp [ha]

theorem refines_mask {α : Type} [Zero α] {p q : Option Bool} {a b : Option α}
    (h : Refines p q) (k : Refines a b) : Refines (mask p a) (mask q b) := by
  cases p with
  | none => intro v hv; cases hv
  | some p =>
    rw [h p rfl]
    cases p with
    | false => exact refines_refl _
    | true => exact k

theorem refines_densityAt {a b : Option Density} {x y : Option ℝ}
    (h : Refines a b) (k : Refines x y) : Refines (densityAt a x) (densityAt b y) :=
  refines_bind h (fun _ => refines_bind k (fun _ => refines_refl _))

theorem refines_log_product (x y : Option ℝ)
    (hx : Refines (lt (some 0) x) (some true))
    (hy : Refines (lt (some 0) y) (some true)) :
    Refines (Functions.logR.apply (mul x y)) (add (Functions.logR.apply x) (Functions.logR.apply y)) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    cases y with
    | none => intro v hv; cases hv
    | some y =>
      have hx' : 0 < x := by simpa [Refines, lt] using hx
      have hy' : 0 < y := by simpa [Refines, lt] using hy
      intro v hv
      simpa [Function1.apply, Functions.logR, mul, add, hx', hy', mul_pos hx' hy',
        Elementary.log_mul_pos hx' hy'] using hv

theorem refines_log_rational (x y z : Option ℝ)
    (h : Refines (not (nonzero (add x (mul (some (-1)) (mul y (inv z)))))) (some true))
    (hy : Refines (lt (some 0) y) (some true)) (hz : Refines (lt (some 0) z) (some true))
    (dy : Defined y) (dz : Defined z) :
    Refines (Functions.logR.apply x) (add (Functions.logR.apply y) (mul (some (-1)) (Functions.logR.apply z))) := by
  classical
  obtain ⟨y, rfl⟩ := dy
  obtain ⟨z, rfl⟩ := dz
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    have hy' : 0<y := by simpa [Refines, lt] using hy
    have hz' : 0<z := by simpa [Refines, lt] using hz
    have he : x-y*z⁻¹=0 := by simpa [Refines, not, nonzero, add, mul, inv, hz'.ne', sub_eq_add_neg] using h
    have he' := sub_eq_zero.mp he
    subst x
    intro v hv
    simpa [Function1.apply, Functions.logR, add, mul, hy', hz', mul_pos hy' (inv_pos.mpr hz'),
      Real.log_mul hy'.ne' (inv_ne_zero hz'.ne'), Real.log_inv] using hv

theorem refines_power_exact (v_x : Option (Ty.denote .real)) (v_y : Option (Ty.denote .real)) (v_z : Option (Ty.denote .real)) (v_m : Nat) (v_n : Nat)
    (hp0 : Value.Refines (Value.not (Value.nonzero (Value.add v_z (Value.mul (some (((-1) : Int) : ℝ)) (Value.mul (some ((v_m : Int) : ℝ)) (Value.inv (Value.add (some ((v_n : Int) : ℝ)) (some (((1) : Int) : ℝ))))))))) (some true))
    (hp1 : Value.Refines (Value.not (Value.nonzero (Value.add (v_y.map (fun x => x ^ (v_n + (1)))) (Value.mul (some (((-1) : Int) : ℝ)) v_x)))) (some true))
    (hp2 : Value.Refines (Value.le (some (((0) : Int) : ℝ)) v_y) (some true))
    (hp3 : Value.Defined v_y) :
    Value.Refines (Functions.powerR.apply v_x v_z) (v_y.map (fun x => x ^ v_m)) := by
  classical
  obtain ⟨y, rfl⟩ := hp3
  cases v_x with
  | none => intro v hv; cases hv
  | some x =>
    cases v_z with
    | none => intro v hv; cases hv
    | some z =>
      have hn : (v_n : ℝ)+1 ≠ 0 := by positivity
      have hz : z = (v_m : ℝ)/((v_n : ℝ)+1) := by
        simpa [Refines, not, nonzero, add, mul, inv, hn, ← sub_eq_add_neg, sub_eq_zero, div_eq_mul_inv] using hp0
      have hx : y^(v_n+1) = x := by
        simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using hp1
      have hy : 0 ≤ y := by simpa [Refines, le] using hp2
      subst x; subst z
      intro v hv
      simp only [Function2.apply, Functions.powerR, Option.bind] at hv
      split at hv
      · simpa [Elementary.root_power y v_m v_n hy] using hv
      · cases hv

theorem refines_phase_period (v_x : Option (Ty.denote .real)) (v_n : Option (Ty.denote .integer))
    (hp0 : Value.Defined v_n) :
    Value.Refines (Functions.cisR.apply v_x) (Functions.cisR.apply (Value.add v_x (Value.mul (some (((-1) : Int) : ℝ)) (Value.mul (Functions.castQR.apply (Functions.castZQ.apply v_n)) (Value.mul (some (((2) : Int) : ℝ)) (some Functions.pi)))))) := by
  classical
  obtain ⟨n, rfl⟩ := hp0
  cases v_x with
  | none => intro v hv; cases hv
  | some x =>
    apply refines_of_eq
    simpa only [Function1.apply, Functions.cisR, Functions.castQR, Functions.castZQ,
      add, mul, Option.bind, if_true, Int.cast_neg, Int.cast_one, Int.cast_ofNat, Rat.cast_intCast]
      using congrArg some (Elementary.phase_period x n).symm

theorem and_decide (p q : Prop) [Decidable p] [Decidable q] :
    and (some (decide p)) (some (decide q)) = some (decide (p ∧ q)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, and]
theorem or_decide (p q : Prop) [Decidable p] [Decidable q] :
    or (some (decide p)) (some (decide q)) = some (decide (p ∨ q)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, or]

theorem refines_lt_factor (l r x y : Option ℝ)
    (h : Refines (not (nonzero (add (add l (mul (some (-1)) r)) (mul (some (-1)) (mul x y))))) (some true))
    (hx : Defined x) (hy : Defined y) :
    Refines (lt l r) (or (and (lt x (some 0)) (lt (some 0) y)) (and (lt (some 0) x) (lt y (some 0)))) := by
  classical
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  cases l with
  | none => intro v hv; cases hv
  | some l =>
    cases r with
    | none => intro v hv; cases hv
    | some r =>
      have he : l-r = x*y := by
        simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using h
      apply refines_of_eq
      simp only [lt, Option.bind_eq_bind, Option.bind, Option.pure_def, and_decide, or_decide, Option.some.injEq, decide_eq_decide]
      rw [← sub_lt_zero, he, mul_neg_iff, or_comm]

theorem refines_le_factor (l r x y : Option ℝ)
    (h : Refines (not (nonzero (add (add l (mul (some (-1)) r)) (mul (some (-1)) (mul x y))))) (some true))
    (hx : Defined x) (hy : Defined y) :
    Refines (le l r) (or (and (le x (some 0)) (le (some 0) y)) (and (le (some 0) x) (le y (some 0)))) := by
  classical
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  cases l with
  | none => intro v hv; cases hv
  | some l =>
    cases r with
    | none => intro v hv; cases hv
    | some r =>
      have he : l-r = x*y := by
        simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using h
      apply refines_of_eq
      simp only [le, Option.bind_eq_bind, Option.bind, Option.pure_def, and_decide, or_decide, Option.some.injEq, decide_eq_decide]
      rw [← sub_nonpos, he, mul_nonpos_iff, or_comm]

theorem refines_power_negative (x y : Option ℝ)
    (hy : Refines (lt y (some 0)) (some true)) :
    Refines (Functions.powerR.apply x y)
      (inv (Functions.powerR.apply x (mul (some (-1)) y))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    cases y with
    | none => intro v hv; cases hv
    | some y =>
      have hn : y<0 := by simpa [Refines, lt] using hy
      intro v hv
      simp only [Function2.apply, Option.bind] at hv
      split at hv
      · rename_i hd
        have h := Elementary.negative_power hn hd
        simp only [Function2.apply, mul, Option.bind, neg_one_mul, if_pos h.1, inv, if_neg h.2.1]
        change (if x^(-y)=0 then none else some ((x^(-y))⁻¹))=some v
        rw [if_neg h.2.1, h.2.2]
        exact hv
      · cases hv

theorem refines_real_nonzero_quadratic (v_p : Option ℝ) (v_x : Option ℝ) (v_a : Option ℝ) (v_b : Option ℝ) (v_d : Option ℝ)
    (hp0 : Refines (not (nonzero (add v_p (mul (some (-1)) (mul v_a (add ((add v_x v_b).map (fun x => x^2)) (mul (some (-1)) v_d))))))) (some true))
    (hp1 : Refines (nonzero v_a) (some true))
    (hp2 : Refines (le (some 0) v_d) (some true))
    (hp3 : Defined v_a)
    (hp4 : Defined v_b)
    (hp5 : Defined v_d)
    (hp6 : Defined v_x) :
    Refines (nonzero v_p) (and (nonzero (add v_x (mul (some (-1)) (add (mul (some (-1)) v_b) (mul (some (-1)) (Functions.sqrtR.apply v_d)))))) (nonzero (add v_x (mul (some (-1)) (add (mul (some (-1)) v_b) (Functions.sqrtR.apply v_d)))))) := by
  classical
  obtain ⟨a, rfl⟩ := hp3
  obtain ⟨b, rfl⟩ := hp4
  obtain ⟨d, rfl⟩ := hp5
  obtain ⟨x, rfl⟩ := hp6
  cases v_p with
  | none => intro v hv; cases hv
  | some p =>
    have hp : p=a*((x+b)^2-d) := by
      simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using hp0
    have ha : a≠0 := by simpa [Refines, nonzero] using hp1
    have hd : 0≤d := by simpa [Refines, le] using hp2
    subst p
    have h := Elementary.real_quadratic_nonzero x a b d hd
    apply refines_of_eq
    have hand (p q : Bool) : and (some p) (some q)=some (p && q) := by cases p <;> rfl
    have he : decide (a*((x+b)^2-d)≠0)=decide (x+b+Real.sqrt d≠0 ∧ x+b-Real.sqrt d≠0) :=
      decide_eq_decide.mpr (h.trans (and_iff_right ha))
    simpa [nonzero, hand, add, mul, Function1.apply, Functions.sqrtR, ha, hd,
      sub_eq_add_neg, neg_add_rev, add_assoc, add_comm, add_left_comm]
      using congrArg (fun b : Bool => some b) he

theorem refines_complex_nonzero_quadratic (v_p : Option ℂ) (v_x : Option ℂ) (v_a : Option ℂ) (v_b : Option ℂ) (v_d : Option ℂ)
    (hp0 : Refines (not (nonzero (add v_p (mul (some (-1)) (mul v_a (add ((add v_x v_b).map (fun x => x^2)) (mul (some (-1)) v_d))))))) (some true))
    (hp1 : Refines (nonzero v_a) (some true))
    (hp2 : Defined v_a)
    (hp3 : Defined v_b)
    (hp4 : Defined v_d)
    (hp5 : Defined v_x) :
    Refines (nonzero v_p) (and (nonzero (add v_x (mul (some (-1)) (add (mul (some (-1)) v_b) (mul (some (-1)) (Functions.sqrtC.apply v_d)))))) (nonzero (add v_x (mul (some (-1)) (add (mul (some (-1)) v_b) (Functions.sqrtC.apply v_d)))))) := by
  classical
  obtain ⟨a, rfl⟩ := hp2
  obtain ⟨b, rfl⟩ := hp3
  obtain ⟨d, rfl⟩ := hp4
  obtain ⟨x, rfl⟩ := hp5
  cases v_p with
  | none => intro v hv; cases hv
  | some p =>
    have hp : p=a*((x+b)^2-d) := by
      simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using hp0
    have ha : a≠0 := by simpa [Refines, nonzero] using hp1
    subst p
    have h := Elementary.complex_quadratic_nonzero x a b d
    apply refines_of_eq
    have hand (p q : Bool) : and (some p) (some q)=some (p && q) := by cases p <;> rfl
    have he : decide (a*((x+b)^2-d)≠0)=decide (x+b+d^(2⁻¹ : ℂ)≠0 ∧ x+b-d^(2⁻¹ : ℂ)≠0) :=
      decide_eq_decide.mpr (h.trans (and_iff_right ha))
    simpa [nonzero, hand, add, mul, Function1.apply, Functions.sqrtC, ha,
      sub_eq_add_neg, neg_add_rev, add_assoc, add_comm, add_left_comm]
      using congrArg (fun b : Bool => some b) he

theorem refines_tan_cos (x : Option ℝ) :
    Refines (mul (Functions.tanR.apply x) (Functions.cosR.apply x)) (Functions.sinR.apply x) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases h : Real.cos x=0
    · simp [Refines, Function1.apply, Functions.tanR, Functions.cosR, mul, h]
    · apply refines_of_eq
      simp [Function1.apply, Functions.tanR, Functions.cosR, Functions.sinR, mul, h, Real.tan_mul_cos]

theorem refines_complex_tan_cos (x : Option ℂ) :
    Refines (mul (Functions.tanC.apply x) (Functions.cosC.apply x)) (Functions.sinC.apply x) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases h : Complex.cos x=0
    · simp [Refines, Function1.apply, Functions.tanC, Functions.cosC, mul, h]
    · apply refines_of_eq
      simp [Function1.apply, Functions.tanC, Functions.cosC, Functions.sinC, mul, h, Complex.tan_mul_cos]

theorem refines_complex_tanh_cosh (x : Option ℂ) :
    Refines (mul (Functions.tanhC.apply x) (Functions.coshC.apply x)) (Functions.sinhC.apply x) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases h : Complex.cosh x=0
    · simp [Refines, Function1.apply, Functions.tanhC, Functions.coshC, mul, h]
    · apply refines_of_eq
      simp [Function1.apply, Functions.tanhC, Functions.coshC, Functions.sinhC, mul, h, Complex.tanh_eq_sinh_div_cosh]

theorem refines_sin_atan (x : Option ℝ) :
    Refines (Functions.sinR.apply (Functions.atanR.apply x))
      (mul x (inv (Functions.sqrtR.apply (add (some 1) (x.map (fun v => v^2)))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    have hp : 0≤1+x^2 := by positivity
    have hn : Real.sqrt (1+x^2)≠0 := by positivity
    apply refines_of_eq
    simp [Function1.apply, Functions.sinR, Functions.atanR, Functions.sqrtR, mul, add, inv, hp, hn, Real.sin_arctan, div_eq_mul_inv]

theorem refines_cos_atan (x : Option ℝ) :
    Refines (Functions.cosR.apply (Functions.atanR.apply x))
      (inv (Functions.sqrtR.apply (add (some 1) (x.map (fun v => v^2))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    have hp : 0≤1+x^2 := by positivity
    have hn : Real.sqrt (1+x^2)≠0 := by positivity
    apply refines_of_eq
    simp [Function1.apply, Functions.cosR, Functions.atanR, Functions.sqrtR, add, inv, hp, hn, Real.cos_arctan]

theorem cbrt_apply (x : Option ℝ) : Functions.cbrtR.apply x=x.map Functions.cbrtR.value := by
  cases x <;> simp [Function1.apply, Functions.cbrtR]

theorem refines_power_scale (v_x v_a v_b v_t : Option ℝ) (v_m v_n : Nat)
    (hp0 : Refines (not (nonzero (add v_t (mul (some (-1)) (mul (some (v_m : ℝ)) (inv (add (some (v_n : ℝ)) (some 2)))))))) (some true))
    (hp1 : Refines (not (nonzero (add v_x (mul (some (-1)) (mul (v_a.map (fun x => x^(v_n+2))) v_b))))) (some true))
    (hp2 : Refines (le (some 0) v_a) (some true))
    (hp3 : Refines (le (some 0) v_b) (some true))
    (hp4 : Defined v_a) (hp5 : Defined v_b) :
    Refines (Functions.powerR.apply v_x v_t) (mul (v_a.map (fun x => x^v_m)) (Functions.powerR.apply v_b v_t)) := by
  classical
  obtain ⟨a, rfl⟩ := hp4
  obtain ⟨b, rfl⟩ := hp5
  cases v_x with
  | none => intro v hv; cases hv
  | some x =>
    cases v_t with
    | none => intro v hv; cases hv
    | some t =>
      have hn : (v_n : ℝ)+2≠0 := by positivity
      have ht : t=(v_m : ℝ)/((v_n : ℝ)+2) := by
        simpa [Refines, not, nonzero, add, mul, inv, hn, ← sub_eq_add_neg, sub_eq_zero, div_eq_mul_inv] using hp0
      have hx : x=a^(v_n+2)*b := by
        simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using hp1
      have ha : 0≤a := by simpa [Refines, le] using hp2
      have hb : 0≤b := by simpa [Refines, le] using hp3
      subst x; subst t
      have hq : 0≤(v_m : ℝ)/((v_n : ℝ)+2) := by positivity
      have dom (r : ℝ) (hr : 0≤r) : Functions.powerR.domain r ((v_m : ℝ)/((v_n : ℝ)+2)) := by
        rcases eq_or_lt_of_le hr with h | h
        · simp [Functions.powerR, ← h, hq]
        · exact Or.inl h
      apply refines_of_eq
      simpa only [Function2.apply, Option.bind, if_pos (dom _ (mul_nonneg (pow_nonneg ha _) hb)),
        if_pos (dom b hb), mul, Option.map]
        using congrArg some (Elementary.power_scale a b v_m v_n ha hb)

theorem refines_cbrt_power (x : Option ℝ) (n : ℕ) :
    Refines (Functions.cbrtR.apply (x.map (fun v => v^(n+n+n+3)))) (x.map (fun v => v^(n+1))) := by
  apply refines_of_eq
  cases x <;> simp only [cbrt_apply, Option.map, FunctionOrder.cbrt_power]

theorem refines_cbrt_cube (x : Option ℝ) :
    Refines ((Functions.cbrtR.apply x).map (fun v => v^3)) x := by
  apply refines_of_eq
  cases x <;> simp only [cbrt_apply, Option.map, FunctionOrder.cbrt_cube]

theorem refines_cbrt_neg (x : Option ℝ) :
    Refines (Functions.cbrtR.apply (mul (some (-1)) x)) (mul (some (-1)) (Functions.cbrtR.apply x)) := by
  apply refines_of_eq
  cases x <;> simp [cbrt_apply, mul, FunctionOrder.cbrt_neg]

theorem refines_cbrt_product (x y : Option ℝ) :
    Refines (mul (Functions.cbrtR.apply x) (Functions.cbrtR.apply y)) (Functions.cbrtR.apply (mul x y)) := by
  apply refines_of_eq
  cases x <;> cases y <;> simp [cbrt_apply, mul, FunctionOrder.cbrt_mul]

theorem refines_sqrt_even_power (x : Option ℝ) (n : ℕ) :
    Refines (Functions.sqrtR.apply (x.map (fun v => v^(n+n+2)))) ((abs x).map (fun v => v^(n+1))) := by
  apply refines_of_eq
  cases x <;> simp [Function1.apply, Functions.sqrtR, abs, Elementary.even_power_nonnegative, Elementary.sqrt_even_power]

theorem refines_sqrt_even_factor (x y : Option ℝ) (n : ℕ)
    (hy : Refines (le (some 0) y) (some true)) :
    Refines (Functions.sqrtR.apply (mul (x.map (fun v => v^(n+n+2))) y))
      (mul ((abs x).map (fun v => v^(n+1))) (Functions.sqrtR.apply y)) := by
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    cases y with
    | none => intro v hv; cases hv
    | some y =>
      have h : 0≤y := by simpa [Refines, le] using hy
      apply refines_of_eq
      simp [Function1.apply, Functions.sqrtR, mul, abs, h,
        mul_nonneg (Elementary.even_power_nonnegative x n) h, Elementary.sqrt_even_factor, Elementary.sqrt_even_power]

end QSym.Value

namespace QSym

open Lean Meta Elab Tactic in
elab "qsym_split_and" : tactic => liftMetaTactic fun goal => goal.withContext do
  for decl in ← getLCtx do
    if decl.type.isAppOfArity ``And 2 || decl.type.isAppOfArity ``Exists 2 then
      return (← goal.cases decl.fvarId).toList.map (·.mvarId)
  throwError "no conjunction"

open Lean Meta Elab Tactic in
elab "qsym_split_bool" : tactic => liftMetaTactic fun goal => goal.withContext do
  for decl in ← getLCtx do
    if (← whnf decl.type).isConstOf ``Bool then
      return (← goal.cases decl.fvarId).toList.map (·.mvarId)
  throwError "no Boolean"

-- Search is untrusted: every successful tactic emits a kernel-checked proof.
open Lean Meta Elab Tactic in
elab "qsym_order_goal" : tactic => do
  let t ← getMainTarget
  unless t.isAppOfArity ``Value.Refines 3 && (← whnf t.getAppArgs[0]!).isConstOf ``Bool do
    throwError "not a Boolean refinement"

macro "qsym_order_core" mode:ident : tactic => do
  let early := mode.getId.eraseMacroScopes==`early
  let enter ← if early then `(tactic| intro v hv) else `(tactic| skip)
  let domains ← if early then `(tactic| all_goals try split_ifs at *) else `(tactic| skip)
  let powers ← if early then `(tactic| (
  all_goals repeat' qsym_split_and
  all_goals try simp_all only [← sub_eq_add_neg, sub_eq_zero, ← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  all_goals try simp (disch := (first | assumption | (simp only [Functions.powerR]; assumption))) only [
    Real.rpow_right_inj, Real.rpow_lt_rpow_iff, Real.rpow_le_rpow_iff, Real.rpow_left_inj,
    Order.power_not_negative, Order.power_not_nonpositive,
    Order.power_negative_lt, Order.power_negative_le, Order.power_noninteger_lt, Order.power_noninteger_le,
    Order.power_noninteger_negative_lt, Order.power_noninteger_negative_le, Order.power_noninteger_eq,
    Elementary.cpow_contract_eq, Elementary.cpow_negative_contract_eq, Complex.cpow_eq_zero_iff,
    Order.nonnegative_inverse_lt, Order.nonnegative_inverse_le, Order.nonpositive_inverse_lt, Order.nonpositive_inverse_le] at *
  all_goals try assumption
  )) else `(tactic| (
  all_goals try simp_all only [← sub_eq_add_neg, sub_eq_zero, ← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide]
  ))
  `(tactic| (
  qsym_order_goal
  classical
  $enter:tactic
  simp only [Value.Refines, Value.Defined, Function1.apply, Function2.apply,
    Functions.expR, Functions.logR, Functions.sqrtR, Functions.powerR, Functions.powerC, Functions.isIntR,
    Functions.minR, Functions.maxR, Functions.absC, Functions.reC, Functions.imC,
    Functions.expC, Functions.logC, Functions.sqrtC, Functions.pi, Functions.sinR, Functions.cosR,
    Value.inv, Value.conj, Value.add, Value.mul, Value.nonzero, Value.not, Value.lt, Value.le, Value.abs,
    Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind] at *
  try simp only [Option.some.injEq, forall_eq, forall_eq', Bool.true_eq, decide_eq_true_eq] at *
  $domains:tactic
  repeat' first
    | simp_all (config := {failIfUnchanged := true}) [Value.and_some, Value.or_some, Value.mask, Real.sin_le_one, Real.neg_one_le_sin, Real.cos_le_one, Real.neg_one_le_cos, -Real.log_eq_zero]
    | qsym_split_bool
    | split_ifs at *
  $powers:tactic
  all_goals try simp_all [Identities.min_eq_max, Identities.clog_inj, Identities.clog_zero,
    Identities.csqrt_inj, Identities.cexp_inj, Identities.conj_eq,
    min_lt_iff, min_le_iff, lt_min_iff, le_min_iff, max_lt_iff, max_le_iff, lt_max_iff, le_max_iff,
    Order.nonnegative_add_eq_zero, Order.nonpositive_add_eq_zero,
    Order.odd_power_lt, Order.odd_power_le, Order.odd_power_eq,
    Order.odd_negative, Order.odd_nonpositive, Order.odd_positive, Order.odd_nonnegative,
    Order.even_lt_nonpositive, Order.even_le_negative, Order.negative_lt_even, Order.nonpositive_le_even,
    Order.odd_mul_negative, Order.odd_mul_nonpositive, Order.odd_mul_positive, Order.odd_mul_nonnegative,
    Order.even_mul_negative, Order.even_mul_nonpositive, Order.even_mul_positive, Order.even_mul_nonnegative,
    Order.even_power_lt, Order.even_power_le, Order.even_power_eq,
    Order.nonnegative_power_lt, Order.nonnegative_power_le,
    Real.exp_lt_exp, Real.exp_le_exp, Real.exp_eq_exp, Real.exp_eq_one_iff, Real.exp_ne_zero,
    Real.exp_lt_one_iff, Real.exp_le_one_iff, Real.one_lt_exp_iff, Real.one_le_exp_iff,
    Real.log_lt_log_iff, Real.log_le_log_iff, Real.log_injOn_pos.eq_iff, Order.log_eq_exp,
    Real.log_neg_iff, Order.log_nonpositive, Order.log_positive, Real.log_nonneg_iff,
    Real.sqrt_lt_sqrt_iff, Real.sqrt_le_sqrt_iff, Real.sqrt_inj, Real.sqrt_eq_zero,
    Real.rpow_lt_rpow_left_iff, Real.rpow_le_rpow_left_iff,
    Real.rpow_lt_rpow_left_iff_of_base_lt_one, Real.rpow_le_rpow_left_iff_of_base_lt_one,
    abs_lt, abs_le, Order.lt_abs_cases, Order.le_abs_cases, Order.abs_eq_cases, not_and_or, -Real.log_eq_zero]
  all_goals try simp_all only [← decide_not, ← Bool.decide_and, ← Bool.decide_or, decide_eq_decide,
    eq_neg_iff_add_eq_zero, imp_iff_not_or, not_le, not_lt]
  all_goals first
    | solve | apply Order.quadratic_lt_pos <;> assumption
    | solve | symm; apply Order.quadratic_lt_pos <;> assumption
    | solve | apply Order.quadratic_le_pos <;> assumption
    | solve | symm; apply Order.quadratic_le_pos <;> assumption
    | solve | apply Order.quadratic_lt_neg <;> assumption
    | solve | symm; apply Order.quadratic_lt_neg <;> assumption
    | solve | apply Order.quadratic_le_neg <;> assumption
    | solve | symm; apply Order.quadratic_le_neg <;> assumption
    | solve | simp only [Order.sqrt_lt_bound (by assumption), Order.le_sqrt_bound (by assumption),
        Real.sqrt_le_iff, Order.lt_sqrt_bound, ← not_lt]; tauto
    | solve | simp_all only [Order.sqrt_lt_bound, Real.sqrt_le_iff, Order.lt_sqrt_bound, Order.le_sqrt_bound, ← not_lt]; tauto
    | solve | simp_all [mul_neg_iff, mul_nonpos_iff, mul_pos_iff, mul_nonneg_iff]; tauto
    | solve | constructor <;> intro h <;> nlinarith
    | solve | nlinarith
    | solve | positivity
    | solve | tauto
))

open Lean Meta Elab Tactic in
elab "qsym_order" : tactic => do
  evalTactic (← `(tactic| qsym_order_goal))
  let source := (← getMainTarget).getAppArgs[1]!
  let early := (source.find? fun e => e.isConstOf ``Functions.powerR ||
    e.isConstOf ``Functions.powerC || e.isConstOf ``Value.inv).isSome
  if early then evalTactic (← `(tactic| qsym_order_core early))
  else evalTactic (← `(tactic| qsym_order_core plain))

open Lean Meta Elab Tactic in
elab "qsym_function_order_goal" : tactic => do
  evalTactic (← `(tactic| qsym_order_goal))
  let source := (← getMainTarget).getAppArgs[1]!
  let names := [``Functions.erfR, ``Functions.erfcR, ``Functions.sinhR, ``Functions.asinhR,
    ``Functions.tanhR, ``Functions.atanR, ``Functions.asinR, ``Functions.acosR,
    ``Functions.cbrtR, ``Functions.acoshR, ``Functions.atanhR]
  unless (source.find? fun e => names.any e.isConstOf).isSome do
    throwError "not a supported unary function comparison"

macro "qsym_function_monotonicity" : tactic => `(tactic| (
  first
    | exact FunctionOrder.erf
    | exact FunctionOrder.erfc
    | exact FunctionOrder.sinh
    | exact FunctionOrder.asinh
    | exact FunctionOrder.tanh
    | exact FunctionOrder.atan
    | exact FunctionOrder.asin
    | exact FunctionOrder.acos
    | exact FunctionOrder.cbrt
    | exact FunctionOrder.acosh
    | exact FunctionOrder.atanh
))

macro "qsym_function_order" : tactic => `(tactic| (
  qsym_function_order_goal
  try simp only [Int.cast_neg, Int.cast_one] at *
  first
    | (apply Value.refines_increasing_lt; qsym_function_monotonicity)
    | (apply Value.refines_increasing_le; qsym_function_monotonicity)
    | (apply Value.refines_increasing_ne; qsym_function_monotonicity)
    | (apply Value.refines_decreasing_lt; qsym_function_monotonicity)
    | (apply Value.refines_decreasing_le; qsym_function_monotonicity)
    | (apply Value.refines_decreasing_ne; qsym_function_monotonicity)
))

open Lean Meta Elab Tactic in
elab "qsym_trig_goal" : tactic => do
  let functions := #[``Real.sin, ``Real.cos, ``Real.tan, ``Real.sinh, ``Real.cosh, ``Real.tanh,
    ``Complex.sin, ``Complex.cos, ``Complex.tan, ``Complex.sinh, ``Complex.cosh, ``Complex.tanh, ``Complex.exp]
  let target ← getMainTarget
  unless (target.find? fun e => functions.any (fun n => e.isConstOf n)).isSome do
    throwError "not a trigonometric goal"

macro "qsym_scalar" : tactic => `(tactic| (
  first
  | exact Value.refines_quotient_add_nonzero _ _ _
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one] at *; apply Value.refines_log_rational <;> assumption)
  | solve | qsym_function_order
  | solve | qsym_order
  | solve | apply Value.refines_cbrt_power
  | solve | apply Value.refines_cbrt_cube
  | solve | (simp only [Int.cast_neg, Int.cast_one]; apply Value.refines_cbrt_neg)
  | solve | apply Value.refines_cbrt_product
  | solve | apply Value.refines_sqrt_even_power
  | solve | (simp only [Int.cast_zero] at *; apply Value.refines_sqrt_even_factor; assumption)
  | exact Value.refines_inv_inv _
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, add_zero] at *; apply Value.refines_real_nonzero_quadratic <;> assumption)
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, add_zero] at *; apply Value.refines_complex_nonzero_quadratic <;> assumption)
  | solve | (simp only [Int.cast_zero] at *; apply Value.refines_log_product <;> assumption)
  | solve | apply Value.refines_power_exact <;> assumption
  | solve | (simp only [Int.cast_natCast, Int.cast_zero, Int.cast_neg, Int.cast_one, Int.cast_ofNat] at *; apply Value.refines_power_scale <;> assumption)
  | solve | apply Value.refines_phase_period <;> assumption
  | solve | apply Value.refines_tan_cos
  | solve | apply Value.refines_complex_tan_cos
  | solve | apply Value.refines_complex_tanh_cosh
  | solve | (simp only [Int.cast_one]; apply Value.refines_sin_atan)
  | solve | (simp only [Int.cast_one]; apply Value.refines_cos_atan)
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one] at *; apply Value.refines_power_negative <;> assumption)
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one] at *; apply Value.refines_lt_factor <;> assumption)
  | solve | (simp only [Int.cast_zero, Int.cast_neg, Int.cast_one] at *; apply Value.refines_le_factor <;> assumption)
  | (
    classical
    intro v hv
    try simp only [Value.Refines, Value.Defined] at *
    try simp only [Function1.apply, Function2.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC, Functions.addN,
      Functions.mulN, Functions.ltN, Functions.leN, Functions.nonzeroN, Functions.addZ,
      Functions.mulZ, Functions.ltZ, Functions.leZ, Functions.nonzeroZ, Functions.addQ,
      Functions.mulQ, Functions.ltQ, Functions.leQ, Functions.nonzeroQ, Functions.invQ,
      Functions.eqB, Functions.powNN, Functions.powZN, Functions.powQN, Functions.powRN, Functions.powCN,
      Functions.powQZ, Functions.powRZ, Functions.powCZ, Functions.cbrtR, Functions.exp2R, Functions.log2R, Functions.log10R,
      Functions.floorR, Functions.ceilR, Functions.roundR, Functions.isIntR, Functions.hypotR, Functions.argC,
      Functions.expiC, Functions.polarC, Functions.atan2R, Functions.asinhR, Functions.acoshR, Functions.atanhR,
      Functions.asinC, Functions.acosC, Functions.atanC, Functions.asinhC, Functions.acoshC, Functions.atanhC,
      Functions.erfR, Functions.erfcR, Functions.gammaR, Functions.gammaC, Functions.lgammaR, Elementary.half_domain, Functions.powerR, Functions.powerC, Functions.sqrtR, Functions.sqrtC,
      Functions.expR, Functions.expC, Functions.sinR, Functions.sinC, Functions.cosR,
      Functions.cosC, Functions.sinhR, Functions.sinhC, Functions.coshR, Functions.coshC,
      Functions.tanhR, Functions.tanhC, Functions.logR, Functions.logC, Functions.tanR,
      Functions.tanC, Functions.minR, Functions.maxR, Functions.signR, Functions.asinR,
      Functions.acosR, Functions.atanR, Functions.absC, Functions.pi, Functions.e, Functions.makeC, Functions.reC, Functions.imC, Functions.cisR,
      Value.add, Value.mul, Value.inv, Value.nonzero, Value.mask, Value.conj,
      Value.not, Value.and, Value.or, Value.lt, Value.le, Value.abs,
      Option.bind_eq_bind, Option.pure_def, Option.map, Option.bind] at *
    try simp only [Option.some.injEq, forall_eq, forall_eq', Bool.true_eq, decide_eq_true_eq] at *
    repeat' first
      | simp_all (config := {failIfUnchanged := true}) [Real.exp_pos, Real.sqrt_nonneg, Real.sqrt_pos, Real.pi_pos, Elementary.half_ne_int, Elementary.inv_two_ne_int, Elementary.sqrt_not_neg]
      | qsym_split_and
      | qsym_split_bool
      | split at *
    all_goals try (simp_all only [← sub_eq_add_neg, sub_eq_zero])
    all_goals subst_vars
    all_goals try (qsym_trig_goal; solve | simp_all [Elementary.sin_quarter_turn, Elementary.cos_quarter_turn,
      Elementary.phase_quarter_turn, Elementary.phase_cartesian, Elementary.tan_period, Elementary.tan_period_domain,
      Real.tan_eq_sin_div_cos, Complex.tan_eq_sin_div_cos, Real.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh,
      Real.cosh_add_sinh, Real.cosh_sub_sinh, Complex.cosh_add_sinh, Complex.cosh_sub_sinh,
      Real.sin_add, Real.cos_sub, Complex.sin_add, Complex.cos_sub,
      Real.sin_arctan, Real.cos_arctan, Real.cosh_arsinh,
      ← Complex.tan_conj, ← Complex.tanh_conj, ← Complex.cos_conj, ← Complex.cosh_conj,
      Real.sin_pi_div_three, Real.cos_pi_div_six, Elementary.cosh_ne_zero,
      Real.cos_two_mul', Complex.cos_two_mul', div_eq_mul_inv])
    all_goals try (qsym_trig_goal; solve | simp_all [Elementary.sin_re, Elementary.sin_im, Elementary.cos_re, Elementary.cos_im,
      Elementary.sinh_re, Elementary.sinh_im, Elementary.cosh_re, Elementary.cosh_im])
    all_goals try (have h := Elementary.log_product_domain (by assumption) (by assumption); rcases h with ⟨_, _⟩)
    all_goals try (have h := Elementary.log_product_domain_right (by assumption) (by assumption); rcases h with ⟨_, _⟩)
    all_goals try (have h := Elementary.log_odd_domain _ (by assumption))
    all_goals try (simp_all [Int.floor_neg, Int.ceil_neg, Int.floor_add_intCast, Int.ceil_add_intCast,
      Int.floor_lt, Int.floor_le_iff, Int.lt_floor_iff, Int.le_floor,
      Int.ceil_lt_iff, Int.ceil_le, Int.lt_ceil, Int.le_ceil_iff,
      Elementary.floor_ne, Elementary.ceil_ne, Int.floor_le, Int.le_ceil,
      Elementary.not_lt_floor, Elementary.not_ceil_lt, Elementary.not_add_one_le_ceil,
      Elementary.log_odd_power, Elementary.log_positive_real, Elementary.log_scale,
      Elementary.log_scale_right, Complex.log_inv])
    all_goals try (simp_all [Identities.abs_even_power, Identities.log_even_power,
      Identities.log_even_domain, Identities.exp_log_scale, Identities.cexp_log_scale,
      Identities.exp_log_scale_right, Identities.cexp_log_scale_right, Real.exp_add, Complex.exp_add, Real.sqrt_mul,
      Real.mul_rpow, min_add_max, Identities.min_mul_max,
      Real.sin_le_one, Real.neg_one_le_sin, Real.cos_le_one, Real.neg_one_le_cos,
      Real.sin_two_mul, Complex.sin_two_mul, Real.tanh_neg, Complex.tanh_neg,
      Complex.cosh_sq_sub_sinh_sq, Complex.mul_conj', Complex.ofReal_pow,
      Identities.square_re, Identities.square_im, Complex.conj_ofReal])
    all_goals try (solve | simp only [← mul_eq_zero]; apply Identities.power_product_domain <;> assumption)
    all_goals try (simp_all [Elementary.sqrt_scale, Elementary.sqrt_real_nonnegative, Elementary.sqrt_real_negative])
    all_goals try (simp_all [Elementary.log_mul_pos, Elementary.root_power, Real.sqrt_sq_eq_abs,
      Real.rpow_add, Elementary.rpow_mul_pos, Elementary.rpow_half, ← Real.sqrt_eq_rpow,
      Real.sin_sub_int_mul_two_pi, Real.cos_sub_int_mul_two_pi, Elementary.sin_period, Elementary.cos_period,
      Elementary.sin_three_half_pi, Elementary.cos_three_half_pi, Elementary.exp_phase,
      Elementary.phase_period, Complex.exp_pi_div_two_mul_I,
      Complex.ofReal_add, add_mul, Complex.exp_add])
    all_goals try (simp_all [pow_add, pow_mul, mul_pow, inv_pow, Real.rpow_natCast, Complex.cpow_natCast,
      Real.exp_log, Complex.exp_log, Real.log_exp, Real.sqrt_sq_eq_abs,
      Real.exp_add, Complex.exp_add, Real.exp_sub, Complex.exp_sub, Real.exp_neg, Complex.exp_neg,
      Real.exp_nat_mul, Complex.exp_nat_mul, Real.exp_one_rpow,
      Real.log_mul, Real.log_pow, Real.log_inv, Real.log_abs, Real.log_sqrt,
      Real.sin_sq_add_cos_sq, Complex.sin_sq_add_cos_sq,
      Real.cosh_sq_sub_sinh_sq, Real.tan_arctan, Real.sin_arcsin, Real.cos_arccos,
      Real.arcsin_sin, Real.arccos_cos, min_eq_left, min_eq_right, max_eq_left, max_eq_right,
      Complex.exp_conj, Complex.mul_re, Complex.mul_im, Complex.re_add_im, norm_mul])
    all_goals try (simp_all [Elementary.log_cpow_contract, Elementary.arg_cpow_contract,
      Elementary.log_sqrt, Elementary.arg_sqrt, Elementary.norm_cpow_real, Elementary.norm_sqrt,
      Elementary.arg_exp, Complex.log_exp, Complex.log_re, Complex.log_im, Complex.norm_exp,
      norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_pos_iff,
      Complex.cpow_ne_zero_iff, Complex.cpow_ofNat_inv_pow,
      Real.sinh_arsinh, Real.arsinh_sinh, Real.cos_arcsin, Real.sin_arccos,
      Complex.sin_conj, Complex.cos_conj, Complex.sinh_conj, Complex.cosh_conj])
    all_goals try (simp_all [Elementary.sin_imaginary, Elementary.cos_imaginary, Elementary.tan_imaginary,
      Elementary.sinh_imaginary, Elementary.cosh_imaginary, Elementary.tanh_imaginary])
    all_goals try (simp_all only [← Complex.ofReal_cos, Complex.ofReal_eq_zero])
    all_goals try (solve | simp_all only [Elementary.exp_real, ← Complex.ofReal_exp])
    all_goals try (simp_all [Elementary.real_exp_zpow, Elementary.sqrt_exp, Real.pi_pos,
      Elementary.exp_cpow, Elementary.real_exp_cpow, Elementary.sqrt_cexp,
      Elementary.phase_pow, Elementary.phase_zpow, Elementary.phase_inverse, Elementary.phase_conjugate,
      ← Real.exp_mul, ← Complex.exp_int_mul, Complex.ofReal_exp, Complex.ofReal_inv, Complex.ofReal_zpow,
      Complex.exp_re, Complex.exp_im])
    all_goals try (simp_all [abs_mul, abs_inv, abs_pow])
    all_goals try (simp_all [Int.floor_eq_iff, Int.ceil_eq_iff, Real.rpow_neg, Complex.cpow_neg,
      zpow_natCast, zpow_neg, Real.norm_eq_abs, Complex.norm_def, Complex.normSq_apply,
      Real.arcsin_zero, Real.arcsin_one, Real.arccos_zero, Real.arccos_one, Real.arccos_neg_one,
      Real.arctan_zero, Real.arctan_one, Real.arsinh_zero, Real.Gamma_one, Complex.Gamma_one,
      Real.log_exp, Complex.zero_cpow, Complex.one_cpow])
    all_goals try norm_num at *
    all_goals try field_simp
    all_goals try ring_nf at *
    all_goals try (qsym_trig_goal; simp_all [Elementary.sin_quarter_turn_normal, Elementary.cos_quarter_turn_normal,
      Elementary.phase_quarter_turn_normal, Elementary.tan_period_normal, Elementary.tan_period_domain_normal,
      Complex.tan_conj, Complex.tanh_conj])
    all_goals try simp_all [Complex.I_sq, Elementary.phase_half_pi, Elementary.phase_period_normal]
    all_goals try norm_num [Complex.I_pow_eq_pow_mod] at *
    all_goals try ring
    all_goals try (simp only [abs_eq_max_neg, max_def] at *; split_ifs at * <;> nlinarith)
    all_goals try ring
    all_goals try (simp only [← decide_not, decide_eq_decide] at *)
    all_goals try (simp_all [← div_eq_mul_inv, lt_div_iff₀, le_div_iff₀,
      div_lt_iff₀, div_le_iff₀, lt_div_iff_of_neg, le_div_iff_of_neg,
      div_lt_iff_of_neg, div_le_iff_of_neg, mul_comm])
    all_goals try (simp only [pow_mul] at *; nlinarith)
    all_goals try (simp_all [neg_eq_iff_add_eq_zero, add_comm])
    all_goals try (solve | (apply Eq.symm; apply Real.arcsin_sin <;> linarith))
    all_goals try (simp_all [Elementary.sqrt_not_neg])
    all_goals try (solve | have h := Real.sqrt_pos.mpr (by assumption); linarith [h])
    all_goals try (apply Elementary.nonnegative_of_pos_or_zero; assumption)
    all_goals try (solve | (convert Elementary.phase_half_pi.symm using 2 <;> push_cast <;> ring))
    all_goals try (solve | apply Elementary.floor_exact <;> assumption)
    all_goals try (solve | apply Elementary.ceil_exact <;> assumption)
    all_goals try (solve | exact (Complex.sq_cpow_two_inv (by assumption)).symm)
    all_goals try (solve | apply Elementary.sqrt_imaginary; assumption)
    all_goals try (solve | apply Elementary.cartesian_ne_zero; assumption)
    all_goals try (solve | apply Elementary.gamma_real_next; assumption)
    all_goals try (solve | apply Elementary.gamma_complex_next; assumption)
    all_goals try (solve | exact (Elementary.complex_nat_succ_ne_neg _ _) (by assumption))
    all_goals try (solve | apply Elementary.indexed_negative <;> assumption)
    all_goals try (solve | apply Elementary.complex_negative <;> assumption)
    all_goals try (solve | apply lt_of_le_of_ne <;> assumption)
    all_goals try (simp [Real.log_rpow (by norm_num : (0 : ℝ)<2), Real.log_rpow (by norm_num : (0 : ℝ)<10)])
    all_goals try (solve | apply Eq.symm; apply Complex.arg_eq_zero_iff.mpr; constructor <;> first | assumption | linarith)
    all_goals try (solve | apply Eq.symm; apply Complex.arg_eq_pi_iff.mpr; constructor <;> assumption)
    all_goals try (solve | have h := Complex.arg_eq_pi_div_two_iff.mpr ⟨by assumption, by assumption⟩; linarith [h])
    all_goals try (solve | have h := Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨by assumption, by assumption⟩; linarith [h])
    all_goals try (solve | exact (Elementary.rpow_half _).symm)
    all_goals try (solve | apply Elementary.norm_power_domain; assumption)
    all_goals try (solve | apply Elementary.nonnegative_cases; assumption)
    all_goals try positivity
    all_goals try nlinarith
    all_goals try (qsym_trig_goal; simp_all [Elementary.cos_quarter_turn_normal,
      Elementary.tan_period_normal, Elementary.tan_period_domain_normal])
    all_goals try (solve | have h := eq_neg_of_add_eq_zero_left (by assumption); subst_vars; ring)
    all_goals try (solve | exact Or.resolve_left (by assumption) (not_lt.mpr (by assumption)))
    all_goals try (solve | exact Or.resolve_left (by assumption) (not_le.mpr (by assumption)))
    all_goals try (constructor <;> intro h <;> nlinarith)
  )
))

macro "qsym_defined" : tactic => `(tactic| (
  classical
  try simp only [Value.add, Value.mul, Value.inv, Value.nonzero, Value.mask, Value.conj,
    Value.not, Value.and, Value.or, Value.lt, Value.le, Value.abs,
    Option.map, Option.bind]
  repeat' first
    | simp_all (config := {failIfUnchanged := true})
    | split at *
  all_goals try (simp only [← not_lt]; tauto)
))

macro "qsym_rule" : tactic => `(tactic| (
  first
  | solve
    | apply Value.refines_of_eq
      simp only [Expr.eval, Int.cast_zero, Int.cast_one, zero_mul, add_zero,
        Value.add_zero_right, Value.add_zero_left, Value.mul_one_right, Value.mul_one_left,
        Value.mask_true, Value.mask_false, Value.conj_conj,
        Option.map_map, Function.comp_def, Density.forget_puncture]
  | try simp only [Expr.eval]
    qsym_scalar
))

end QSym
