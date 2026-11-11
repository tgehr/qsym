import QSym.Expr
import QSym.Elementary
import QSym.Order
import QSym.FunctionOrder
import QSym.Identities
import QSym.Inverse

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

theorem refines_composition {α β γ} (f : Function1 β γ) (g : Function1 α β)
    (k : α → γ) (x : Option α)
    (h : ∀ a, g.domain a → f.domain (g.value a) → f.value (g.value a)=k a) :
    Refines (f.apply (g.apply x)) (x.map k) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some a =>
    by_cases hg : g.domain a
    · by_cases hf : f.domain (g.value a)
      · apply refines_of_eq
        simp [Function1.apply, hg, hf, h a hg hf]
      · intro v hv; simp [Function1.apply, hg, hf] at hv
    · intro v hv; simp [Function1.apply, hg] at hv

theorem refines_inverse {α β} (f : Function1 β α) (g : Function1 α β) (x : Option α)
    (h : ∀ a, g.domain a → f.domain (g.value a) → f.value (g.value a)=a) :
    Refines (f.apply (g.apply x)) x := by
  simpa only [Option.map_id] using refines_composition f g id x h

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

theorem refines_real_tanh_asinh (x : Option ℝ) :
    Refines (Functions.tanhR.apply (Functions.asinhR.apply x))
      (mul x (inv (Functions.sqrtR.apply (add (some 1) (x.map (fun v => v^2)))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    have hp : 0≤1+x^2 := by positivity
    have hn : Real.sqrt (1+x^2)≠0 := by positivity
    apply refines_of_eq
    simp [Function1.apply, Functions.tanhR, Functions.asinhR, Functions.sqrtR, mul, add, inv,
      hp, hn, Real.tanh_eq_sinh_div_cosh, Real.sinh_arsinh, Real.cosh_arsinh, div_eq_mul_inv]

theorem refines_real_tanh_acosh (x : Option ℝ) :
    Refines (Functions.tanhR.apply (Functions.acoshR.apply x))
      (mul (Functions.sqrtR.apply (add (x.map (fun v => v^2)) (mul (some (-1)) (some 1)))) (inv x)) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases hx : 1≤x
    · have hp : 0≤x^2-1 := by nlinarith
      have hn : x≠0 := by linarith
      have hs := Inverse.real_sinh_acosh x hx
      have hc := Inverse.real_cosh_acosh x hx
      dsimp [Functions.acoshR] at hs hc
      apply refines_of_eq
      simp [Function1.apply, Functions.tanhR, Functions.acoshR, Functions.sqrtR, mul, add, inv,
        hx, hp, hn, ← sub_eq_add_neg, Real.tanh_eq_sinh_div_cosh, hs, hc, div_eq_mul_inv]
    · intro v hv; simp [Function1.apply, Functions.acoshR, hx] at hv

theorem refines_complex_tanh_asinh (z : Option ℂ) :
    Refines (Functions.tanhC.apply (Functions.asinhC.apply z))
      (mul z (inv (Functions.sqrtC.apply (add (z.map (fun z => z^2)) (some 1))))) := by
  classical
  cases z with
  | none => intro v hv; cases hv
  | some z =>
    have hs := Inverse.complex_sinh_asinh z
    have hc := Inverse.complex_cosh_asinh z
    dsimp [Functions.asinhC] at hs hc
    simp only [one_div] at hs hc
    by_cases h : (z^2+1)^((2 : ℂ)⁻¹)=0
    · simp [h] at hc
      intro v hv
      simp [Function1.apply, Functions.tanhC, Functions.asinhC, hc, h] at hv
    · have hn : z^2+1≠0 := by
        intro hz
        apply h
        simp [hz]
      apply refines_of_eq
      simp [Function1.apply, Functions.tanhC, Functions.asinhC, Functions.sqrtC, add, mul, inv,
        Complex.tanh_eq_sinh_div_cosh, hs, hc, h, hn, div_eq_mul_inv]

theorem refines_complex_tanh_acosh (z : Option ℂ) :
    Refines (Functions.tanhC.apply (Functions.acoshC.apply z))
      (mul (mul (Functions.sqrtC.apply (add z (mul (some (-1)) (some 1))))
        (Functions.sqrtC.apply (add z (some 1)))) (inv z)) := by
  classical
  cases z with
  | none => intro v hv; cases hv
  | some z =>
    have hs := Inverse.complex_sinh_acosh z
    have hc := Inverse.complex_cosh_acosh z
    dsimp [Functions.acoshC] at hs hc
    simp only [one_div] at hs hc
    by_cases h : z=0
    · simp [h] at hc
      intro v hv
      simp [Function1.apply, Functions.tanhC, Functions.acoshC, hc, h] at hv
    · apply refines_of_eq
      simp [Function1.apply, Functions.tanhC, Functions.acoshC, Functions.sqrtC, add, mul, inv,
        Complex.tanh_eq_sinh_div_cosh, hs, hc, h, div_eq_mul_inv, ← sub_eq_add_neg]

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

theorem refines_real_acosh_cosh (x : Option ℝ) :
    Refines (Functions.acoshR.apply (Functions.coshR.apply x)) (abs x) :=
  refines_composition Functions.acoshR Functions.coshR (fun x => |x|) x
    (fun x _ _ => Inverse.real_acosh_cosh x)

theorem refines_real_sinh_acosh (x : Option ℝ) :
    Refines (Functions.sinhR.apply (Functions.acoshR.apply x))
      (Functions.sqrtR.apply (add (x.map (fun x => x^2)) (mul (some (-1)) (some 1)))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases hx : 1≤x
    · have hn : 0≤x^2-1 := by nlinarith
      apply refines_of_eq
      simpa [Function1.apply, Functions.sinhR, Functions.acoshR, Functions.sqrtR, add, mul, hx, hn, ← sub_eq_add_neg]
        using congrArg some (Inverse.real_sinh_acosh x hx)
    · intro v hv; simp [Function1.apply, Functions.acoshR, hx] at hv

theorem refines_complex_cos_asin (z : Option ℂ) :
    Refines (Functions.cosC.apply (Functions.asinC.apply z))
      (Functions.sqrtC.apply (add (some 1) (mul (some (-1)) (z.map (fun z => z^2))))) := by
  apply refines_of_eq
  cases z with
  | none => rfl
  | some z =>
    simpa [Function1.apply, Functions.cosC, Functions.asinC, Functions.sqrtC, add, mul, sub_eq_add_neg]
      using congrArg some (Inverse.complex_cos_asin z)

theorem refines_complex_sin_acos (z : Option ℂ) :
    Refines (Functions.sinC.apply (Functions.acosC.apply z))
      (Functions.sqrtC.apply (add (some 1) (mul (some (-1)) (z.map (fun z => z^2))))) := by
  apply refines_of_eq
  cases z with
  | none => rfl
  | some z =>
    simpa [Function1.apply, Functions.sinC, Functions.acosC, Functions.sqrtC, add, mul, sub_eq_add_neg]
      using congrArg some (Inverse.complex_sin_acos z)

theorem refines_complex_cosh_asinh (z : Option ℂ) :
    Refines (Functions.coshC.apply (Functions.asinhC.apply z))
      (Functions.sqrtC.apply (add (z.map (fun z => z^2)) (some 1))) := by
  apply refines_of_eq
  cases z with
  | none => rfl
  | some z =>
    simpa [Function1.apply, Functions.coshC, Functions.asinhC, Functions.sqrtC, add]
      using congrArg some (Inverse.complex_cosh_asinh z)

theorem refines_complex_sinh_acosh (z : Option ℂ) :
    Refines (Functions.sinhC.apply (Functions.acoshC.apply z))
      (mul (Functions.sqrtC.apply (add z (mul (some (-1)) (some 1))))
        (Functions.sqrtC.apply (add z (some 1)))) := by
  apply refines_of_eq
  cases z with
  | none => rfl
  | some z =>
    simpa [Function1.apply, Functions.sinhC, Functions.acoshC, Functions.sqrtC, add, mul, sub_eq_add_neg]
      using congrArg some (Inverse.complex_sinh_acosh z)

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

theorem refines_real_exp_asinh (x : Option ℝ) :
    Refines (Functions.expR.apply (Functions.asinhR.apply x))
      (add x (Functions.sqrtR.apply (add (some 1) (x.map (fun v => v^2))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    have hp : 0≤1+x^2 := by positivity
    apply refines_of_eq
    simp [Function1.apply, Functions.expR, Functions.asinhR, Functions.sqrtR, add, hp,
      ← Real.sinh_add_cosh, Real.sinh_arsinh, Real.cosh_arsinh]

theorem refines_real_exp_acosh (x : Option ℝ) :
    Refines (Functions.expR.apply (Functions.acoshR.apply x))
      (add x (Functions.sqrtR.apply (add (x.map (fun v => v^2)) (mul (some (-1)) (some 1))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases hx : 1≤x
    · have hp : 0≤x^2-1 := by nlinarith
      have hs := Inverse.real_sinh_acosh x hx
      have hc := Inverse.real_cosh_acosh x hx
      dsimp [Functions.acoshR] at hs hc
      apply refines_of_eq
      simp [Function1.apply, Functions.expR, Functions.acoshR, Functions.sqrtR, add, mul,
        hx, hp, ← sub_eq_add_neg, ← Real.cosh_add_sinh, hs, hc]
    · intro v hv; simp [Function1.apply, Functions.acoshR, hx] at hv

theorem refines_complex_exp_asinh (x : Option ℂ) :
    Refines (Functions.expC.apply (Functions.asinhC.apply x))
      (add x (Functions.sqrtC.apply (add (x.map (fun v => v^2)) (some 1)))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    have hs := Inverse.complex_sinh_asinh x
    have hc := Inverse.complex_cosh_asinh x
    dsimp [Functions.asinhC] at hs hc
    simp only [one_div] at hs hc
    apply refines_of_eq
    simp [Function1.apply, Functions.expC, Functions.asinhC, Functions.sqrtC, add, mul,
      ← sub_eq_add_neg, ← Complex.sinh_add_cosh, hs, hc]

theorem refines_complex_exp_acosh (x : Option ℂ) :
    Refines (Functions.expC.apply (Functions.acoshC.apply x))
      (add x (mul (Functions.sqrtC.apply (add x (mul (some (-1)) (some 1)))) (Functions.sqrtC.apply (add x (some 1))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    have hs := Inverse.complex_sinh_acosh x
    have hc := Inverse.complex_cosh_acosh x
    dsimp [Functions.acoshC] at hs hc
    simp only [one_div] at hs hc
    apply refines_of_eq
    simp [Function1.apply, Functions.expC, Functions.acoshC, Functions.sqrtC, add, mul,
      ← sub_eq_add_neg, ← Complex.cosh_add_sinh, hs, hc]

theorem refines_real_cosh_atanh (x : Option ℝ) :
    Refines (Functions.coshR.apply (Functions.atanhR.apply x))
      (mul (some 1) (inv (Functions.sqrtR.apply (add (some 1) (mul (some (-1)) (x.map (fun v => v^2))))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases hx : -1<x ∧ x<1
    · have hp : 0<1-x^2 := by nlinarith [hx.1,hx.2]
      have hn : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.2 hp).ne'
      have he := Inverse.real_cosh_atanh x hx.1 hx.2
      dsimp [Functions.atanhR] at he
      apply refines_of_eq
      simp [Function1.apply, Functions.coshR, Functions.atanhR, Functions.sqrtR, add, mul, inv,
        hx, hp.le, hn, ← sub_eq_add_neg, he]
    · intro v hv; simp [Function1.apply, Functions.atanhR, hx] at hv

theorem refines_real_sinh_atanh (x : Option ℝ) :
    Refines (Functions.sinhR.apply (Functions.atanhR.apply x))
      (mul x (inv (Functions.sqrtR.apply (add (some 1) (mul (some (-1)) (x.map (fun v => v^2))))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases hx : -1<x ∧ x<1
    · have hp : 0<1-x^2 := by nlinarith [hx.1,hx.2]
      have hn : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.2 hp).ne'
      have he := Inverse.real_sinh_atanh x hx.1 hx.2
      dsimp [Functions.atanhR] at he
      apply refines_of_eq
      simp [Function1.apply, Functions.sinhR, Functions.atanhR, Functions.sqrtR, add, mul, inv,
        hx, hp.le, hn, ← sub_eq_add_neg, he]
    · intro v hv; simp [Function1.apply, Functions.atanhR, hx] at hv

theorem refines_real_sinh_log (x : Option ℝ) :
    Refines (Functions.sinhR.apply (Functions.logR.apply x))
      (mul (add x (mul (some (-1)) (inv x))) (inv (some 2))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases hx : 0<x
    · apply refines_of_eq
      simp [Function1.apply, Functions.sinhR, Functions.logR, add, mul, inv,
        hx, hx.ne', Real.sinh_log hx, div_eq_mul_inv, sub_eq_add_neg]
    · intro v hv; simp [Function1.apply, Functions.logR, hx] at hv

theorem refines_complex_tanh_log (x : Option ℂ) :
    Refines (Functions.tanhC.apply (Functions.logC.apply x))
      (mul (add (x.map (fun z => z^2)) (mul (some (-1)) (some 1)))
        (inv (add (x.map (fun z => z^2)) (some 1)))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some z =>
    by_cases hz : z=0
    · intro v hv; simp [Function1.apply, Functions.logC, hz] at hv
    · by_cases hc : Complex.cosh (Complex.log z)=0
      · intro v hv; simp [Function1.apply, Functions.logC, Functions.tanhC, hz, hc] at hv
      · have hd := Elementary.tanh_log_domain z hz hc
        apply refines_of_eq
        simp [Function1.apply, Functions.logC, Functions.tanhC, add, mul, inv,
          hz, hc, hd, Elementary.tanh_log_complex z hz hc, div_eq_mul_inv, sub_eq_add_neg]

theorem refines_cbrt_inverse (x : Option ℝ) :
    Refines (inv (Functions.cbrtR.apply x)) (Functions.cbrtR.apply (inv x)) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    by_cases hx : x=0
    · have hc : Functions.cbrtR.value x=0 := not_not.mp (by simpa [hx] using (FunctionOrder.cbrt_nonzero x).not)
      intro v hv; simp [cbrt_apply, inv, hc] at hv
    · have hc := (FunctionOrder.cbrt_nonzero x).2 hx
      apply refines_of_eq
      simp [cbrt_apply, inv, hx, hc, FunctionOrder.cbrt_inverse]

theorem refines_cbrt_power_multiple (x : Option ℝ) (n : ℕ) :
    Refines ((Functions.cbrtR.apply x).map (fun v => v^(3*n+3))) (x.map (fun v => v^(n+1))) := by
  apply refines_of_eq
  cases x <;> simp [cbrt_apply, mul, FunctionOrder.cbrt_power_multiple]

theorem refines_cbrt_power_one (x : Option ℝ) (n : ℕ) :
    Refines ((Functions.cbrtR.apply x).map (fun v => v^(3*n+4))) (mul (x.map (fun v => v^(n+1))) (Functions.cbrtR.apply x)) := by
  apply refines_of_eq
  cases x <;> simp [cbrt_apply, mul, FunctionOrder.cbrt_power_one]

theorem refines_cbrt_power_two (x : Option ℝ) (n : ℕ) :
    Refines ((Functions.cbrtR.apply x).map (fun v => v^(3*n+5))) (mul (x.map (fun v => v^(n+1))) ((Functions.cbrtR.apply x).map (fun v => v^2))) := by
  apply refines_of_eq
  cases x <;> simp [cbrt_apply, mul, FunctionOrder.cbrt_power_two]

theorem refines_cbrt_factor_left (x y : Option ℝ) :
    Refines (Functions.cbrtR.apply (mul (x.map (fun v => v^3)) y)) (mul x (Functions.cbrtR.apply y)) := by
  apply refines_of_eq
  cases x <;> cases y <;> simp [cbrt_apply, mul, FunctionOrder.cbrt_mul, FunctionOrder.cbrt_cube_input]

theorem refines_cbrt_factor_right (x y : Option ℝ) :
    Refines (Functions.cbrtR.apply (mul x (y.map (fun v => v^3)))) (mul (Functions.cbrtR.apply x) y) := by
  apply refines_of_eq
  cases x <;> cases y <;> simp [cbrt_apply, mul, FunctionOrder.cbrt_mul, FunctionOrder.cbrt_cube_input]

theorem refines_real_tan_asin (x : Option ℝ) :
    Refines (Functions.tanR.apply (Functions.asinR.apply x))
      (mul x (Value.inv (Functions.sqrtR.apply (add (some 1) (mul (some (-1)) (x.map (fun v => v^2))))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some z =>
    by_cases hz : -1≤z ∧ z≤1
    · have hp : 0≤1-z^2 := by nlinarith [hz.1,hz.2]
      have hs := Real.sin_arcsin hz.1 hz.2
      have hc := Real.cos_arcsin z
      by_cases hn : Real.cos (Functions.asinR.value z)=0
      · dsimp [Functions.asinR] at hn
        intro v hv; simp [Function1.apply, Functions.tanR, Functions.asinR, hz, hn] at hv
      · dsimp [Functions.asinR] at hn
        have hn' := hn
        rw [hc] at hn'
        apply refines_of_eq
        simp [Function1.apply, Functions.tanR, Functions.asinR, Functions.sqrtR,
          add, mul, Value.inv, hz, hp, hn, hn', Real.tan_eq_sin_div_cos,
          hs, hc, div_eq_mul_inv, ← sub_eq_add_neg]
    · intro v hv; simp [Function1.apply, Functions.asinR, hz] at hv

theorem refines_real_tan_acos (x : Option ℝ) :
    Refines (Functions.tanR.apply (Functions.acosR.apply x))
      (mul (Functions.sqrtR.apply (add (some 1) (mul (some (-1)) (x.map (fun v => v^2))))) (Value.inv x)) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some z =>
    by_cases hz : -1≤z ∧ z≤1
    · have hp : 0≤1-z^2 := by nlinarith [hz.1,hz.2]
      have hs := Real.sin_arccos z
      have hc := Real.cos_arccos hz.1 hz.2
      by_cases hn : Real.cos (Functions.acosR.value z)=0
      · dsimp [Functions.acosR] at hn
        intro v hv; simp [Function1.apply, Functions.tanR, Functions.acosR, hz, hn] at hv
      · dsimp [Functions.acosR] at hn
        have hn' := hn
        rw [hc] at hn'
        apply refines_of_eq
        simp [Function1.apply, Functions.tanR, Functions.acosR, Functions.sqrtR,
          add, mul, Value.inv, hz, hp, hn, hn', Real.tan_eq_sin_div_cos,
          hs, hc, div_eq_mul_inv, ← sub_eq_add_neg]
    · intro v hv; simp [Function1.apply, Functions.acosR, hz] at hv

theorem refines_complex_tan_asin (x : Option ℂ) :
    Refines (Functions.tanC.apply (Functions.asinC.apply x))
      (mul x (Value.inv (Functions.sqrtC.apply (add (some 1) (mul (some (-1)) (x.map (fun v => v^2))))))) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some z =>
    have hs := Inverse.complex_sin_asin z
    have hc := Inverse.complex_cos_asin z
    dsimp [Functions.asinC] at hs hc
    simp only [one_div, neg_mul, Complex.cos_neg, Complex.sin_neg] at hs hc
    by_cases hn : Complex.cos (Functions.asinC.value z)=0
    · dsimp [Functions.asinC] at hn
      try simp only [one_div, neg_mul, Complex.cos_neg, Complex.sin_neg] at hn
      intro v hv; simp [Function1.apply, Functions.tanC, Functions.asinC, hn] at hv
    · dsimp [Functions.asinC] at hn
      try simp only [one_div, neg_mul, Complex.cos_neg, Complex.sin_neg] at hn
      have hn' := hn
      rw [hc] at hn'
      try simp only [div_eq_mul_inv, neg_mul, Complex.cos_neg, Complex.sin_neg] at hs hc hn hn'
      apply refines_of_eq
      simp [Function1.apply, Functions.tanC, Functions.asinC, Functions.sqrtC,
        add, mul, Value.inv, hn, hn', Complex.tan_eq_sin_div_cos,
        hs, hc, div_eq_mul_inv, ← sub_eq_add_neg]

theorem refines_complex_tan_acos (x : Option ℂ) :
    Refines (Functions.tanC.apply (Functions.acosC.apply x))
      (mul (Functions.sqrtC.apply (add (some 1) (mul (some (-1)) (x.map (fun v => v^2))))) (Value.inv x)) := by
  classical
  cases x with
  | none => intro v hv; cases hv
  | some z =>
    have hs := Inverse.complex_sin_acos z
    have hc := Inverse.complex_cos_acos z
    dsimp [Functions.acosC] at hs hc
    simp only [one_div, neg_mul, Complex.cos_neg, Complex.sin_neg] at hs hc
    by_cases hn : Complex.cos (Functions.acosC.value z)=0
    · dsimp [Functions.acosC] at hn
      try simp only [one_div, neg_mul, Complex.cos_neg, Complex.sin_neg] at hn
      intro v hv; simp [Function1.apply, Functions.tanC, Functions.acosC, hn] at hv
    · dsimp [Functions.acosC] at hn
      try simp only [one_div, neg_mul, Complex.cos_neg, Complex.sin_neg] at hn
      have hn' := hn
      rw [hc] at hn'
      try simp only [div_eq_mul_inv, neg_mul, Complex.cos_neg, Complex.sin_neg] at hs hc hn hn'
      apply refines_of_eq
      simp [Function1.apply, Functions.tanC, Functions.acosC, Functions.sqrtC,
        add, mul, Value.inv, hn, hn', Complex.tan_eq_sin_div_cos,
        hs, hc, div_eq_mul_inv, ← sub_eq_add_neg]

theorem refines_log2_product (x y : Option ℝ)
    (hx : Refines (lt (some 0) x) (some true))
    (hy : Refines (lt (some 0) y) (some true)) :
    Refines (Functions.log2R.apply (mul x y)) (add (Functions.log2R.apply x) (Functions.log2R.apply y)) := by
  cases x with
  | none => cases y <;> intro v hv <;> simp [mul, Function1.apply, Functions.log2R] at hv
  | some x =>
    cases y with
    | none => intro v hv; simp [mul, Function1.apply, Functions.log2R] at hv
    | some y =>
      have hx' : 0<x := by simpa [Refines, lt] using hx
      have hy' : 0<y := by simpa [Refines, lt] using hy
      apply refines_of_eq
      simp [Function1.apply, Functions.log2R, mul, add, hx', hy', mul_pos hx' hy',
        Real.log_mul hx'.ne' hy'.ne', add_div]

theorem refines_log2_power (x : Option ℝ) (n : ℕ)
    (hx : Refines (lt (some 0) x) (some true)) :
    Refines (Functions.log2R.apply (x.map (fun v => v^(n+1))))
      (mul (some ((n : ℝ)+1)) (Functions.log2R.apply x)) := by
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    have hx' : 0<x := by simpa [Refines, lt] using hx
    apply refines_of_eq
    simp [Function1.apply, Functions.log2R, mul, hx', pow_pos hx' (n+1), Real.log_pow,
      Nat.cast_add, Nat.cast_one, mul_div_assoc]

theorem refines_log10_product (x y : Option ℝ)
    (hx : Refines (lt (some 0) x) (some true))
    (hy : Refines (lt (some 0) y) (some true)) :
    Refines (Functions.log10R.apply (mul x y)) (add (Functions.log10R.apply x) (Functions.log10R.apply y)) := by
  cases x with
  | none => cases y <;> intro v hv <;> simp [mul, Function1.apply, Functions.log10R] at hv
  | some x =>
    cases y with
    | none => intro v hv; simp [mul, Function1.apply, Functions.log10R] at hv
    | some y =>
      have hx' : 0<x := by simpa [Refines, lt] using hx
      have hy' : 0<y := by simpa [Refines, lt] using hy
      apply refines_of_eq
      simp [Function1.apply, Functions.log10R, mul, add, hx', hy', mul_pos hx' hy',
        Real.log_mul hx'.ne' hy'.ne', add_div]

theorem refines_log10_power (x : Option ℝ) (n : ℕ)
    (hx : Refines (lt (some 0) x) (some true)) :
    Refines (Functions.log10R.apply (x.map (fun v => v^(n+1))))
      (mul (some ((n : ℝ)+1)) (Functions.log10R.apply x)) := by
  cases x with
  | none => intro v hv; cases hv
  | some x =>
    have hx' : 0<x := by simpa [Refines, lt] using hx
    apply refines_of_eq
    simp [Function1.apply, Functions.log10R, mul, hx', pow_pos hx' (n+1), Real.log_pow,
      Nat.cast_add, Nat.cast_one, mul_div_assoc]

end QSym.Value
