import QSym.RefinementBase

namespace QSym.Value

theorem refines_real_lt_quadratic_pos (v_l : Option ℝ) (v_r : Option ℝ) (v_x : Option ℝ) (v_a : Option ℝ) (v_b : Option ℝ) (v_d : Option ℝ)
    (hp0 : Refines (not (nonzero (add (add v_l (mul (some (-1)) v_r)) (mul (some (-1)) (mul v_a (add ((add v_x v_b).map (fun x => x ^ (2))) (mul (some (-1)) v_d))))))) (some true))
    (hp1 : Refines (lt (some 0) v_a) (some true))
    (hp2 : Refines (le (some 0) v_d) (some true))
    (hp3 : Defined v_a)
    (hp4 : Defined v_b)
    (hp5 : Defined v_d)
    (hp6 : Defined v_x) :
    Refines (lt v_l v_r) (and (lt (add (mul (some (-1)) v_b) (mul (some (-1)) (Functions.sqrtR.apply v_d))) v_x) (lt v_x (add (mul (some (-1)) v_b) (Functions.sqrtR.apply v_d)))) := by
  classical
  obtain ⟨a, rfl⟩ := hp3
  obtain ⟨b, rfl⟩ := hp4
  obtain ⟨d, rfl⟩ := hp5
  obtain ⟨x, rfl⟩ := hp6
  cases v_l with
  | none => intro v hv; cases hv
  | some l =>
    cases v_r with
    | none => intro v hv; cases hv
    | some r =>
      have hp : l-r=a*((x+b)^2-d) := by
        simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using hp0
      have ha : 0<a := by simpa [Refines, lt] using hp1
      have hd : 0≤d := by simpa [Refines, le] using hp2
      have h := Order.quadratic_lt_pos hp ha
      have he : l<r ↔ -b-Real.sqrt d<x ∧ x< -b+Real.sqrt d := by
        constructor
        · intro hl
          obtain ⟨h₁,h₂⟩ := h.mp hl
          constructor <;> linarith
        · intro hr
          apply h.mpr
          obtain ⟨h₁,h₂⟩ := hr
          constructor <;> linarith
      have hb : decide (l < r)=decide (-b-Real.sqrt d < x ∧ x < -b+Real.sqrt d) := decide_eq_decide.mpr he
      apply refines_of_eq
      simpa [lt, and_some, add, mul, Function1.apply, Functions.sqrtR, hd,
        ← Bool.decide_and, ← sub_eq_add_neg] using
        congrArg (fun b : Bool => some b) hb

theorem refines_real_le_quadratic_pos (v_l : Option ℝ) (v_r : Option ℝ) (v_x : Option ℝ) (v_a : Option ℝ) (v_b : Option ℝ) (v_d : Option ℝ)
    (hp0 : Refines (not (nonzero (add (add v_l (mul (some (-1)) v_r)) (mul (some (-1)) (mul v_a (add ((add v_x v_b).map (fun x => x ^ (2))) (mul (some (-1)) v_d))))))) (some true))
    (hp1 : Refines (lt (some 0) v_a) (some true))
    (hp2 : Refines (le (some 0) v_d) (some true))
    (hp3 : Defined v_a)
    (hp4 : Defined v_b)
    (hp5 : Defined v_d)
    (hp6 : Defined v_x) :
    Refines (le v_l v_r) (and (le (add (mul (some (-1)) v_b) (mul (some (-1)) (Functions.sqrtR.apply v_d))) v_x) (le v_x (add (mul (some (-1)) v_b) (Functions.sqrtR.apply v_d)))) := by
  classical
  obtain ⟨a, rfl⟩ := hp3
  obtain ⟨b, rfl⟩ := hp4
  obtain ⟨d, rfl⟩ := hp5
  obtain ⟨x, rfl⟩ := hp6
  cases v_l with
  | none => intro v hv; cases hv
  | some l =>
    cases v_r with
    | none => intro v hv; cases hv
    | some r =>
      have hp : l-r=a*((x+b)^2-d) := by
        simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using hp0
      have ha : 0<a := by simpa [Refines, lt] using hp1
      have hd : 0≤d := by simpa [Refines, le] using hp2
      have h := Order.quadratic_le_pos hp ha hd
      have he : l≤r ↔ -b-Real.sqrt d≤x ∧ x≤-b+Real.sqrt d := by
        constructor
        · intro hl
          obtain ⟨h₁,h₂⟩ := h.mp hl
          constructor <;> linarith
        · intro hr
          apply h.mpr
          obtain ⟨h₁,h₂⟩ := hr
          constructor <;> linarith
      have hb : decide (l ≤ r)=decide (-b-Real.sqrt d ≤ x ∧ x ≤ -b+Real.sqrt d) := decide_eq_decide.mpr he
      apply refines_of_eq
      simpa [le, and_some, add, mul, Function1.apply, Functions.sqrtR, hd,
        ← Bool.decide_and, ← sub_eq_add_neg] using
        congrArg (fun b : Bool => some b) hb

theorem refines_real_lt_quadratic_neg (v_l : Option ℝ) (v_r : Option ℝ) (v_x : Option ℝ) (v_a : Option ℝ) (v_b : Option ℝ) (v_d : Option ℝ)
    (hp0 : Refines (not (nonzero (add (add v_l (mul (some (-1)) v_r)) (mul (some (-1)) (mul v_a (add ((add v_x v_b).map (fun x => x ^ (2))) (mul (some (-1)) v_d))))))) (some true))
    (hp1 : Refines (lt v_a (some 0)) (some true))
    (hp2 : Refines (le (some 0) v_d) (some true))
    (hp3 : Defined v_a)
    (hp4 : Defined v_b)
    (hp5 : Defined v_d)
    (hp6 : Defined v_x) :
    Refines (lt v_l v_r) (or (lt v_x (add (mul (some (-1)) v_b) (mul (some (-1)) (Functions.sqrtR.apply v_d)))) (lt (add (mul (some (-1)) v_b) (Functions.sqrtR.apply v_d)) v_x)) := by
  classical
  obtain ⟨a, rfl⟩ := hp3
  obtain ⟨b, rfl⟩ := hp4
  obtain ⟨d, rfl⟩ := hp5
  obtain ⟨x, rfl⟩ := hp6
  cases v_l with
  | none => intro v hv; cases hv
  | some l =>
    cases v_r with
    | none => intro v hv; cases hv
    | some r =>
      have hp : l-r=a*((x+b)^2-d) := by
        simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using hp0
      have ha : a<0 := by simpa [Refines, lt] using hp1
      have hd : 0≤d := by simpa [Refines, le] using hp2
      have h := Order.quadratic_lt_neg hp ha hd
      have he : l<r ↔ x< -b-Real.sqrt d ∨ -b+Real.sqrt d<x := by
        constructor
        · intro hl
          rcases h.mp hl with h₁ | h₂
          · left; linarith
          · right; linarith
        · intro hr
          apply h.mpr
          rcases hr with h₁ | h₂
          · left; linarith
          · right; linarith
      have hb : decide (l < r)=decide (x < -b-Real.sqrt d ∨ -b+Real.sqrt d < x) := decide_eq_decide.mpr he
      apply refines_of_eq
      simpa [lt, or_some, add, mul, Function1.apply, Functions.sqrtR, hd,
        ← Bool.decide_or, ← sub_eq_add_neg] using
        congrArg (fun b : Bool => some b) hb

theorem refines_real_le_quadratic_neg (v_l : Option ℝ) (v_r : Option ℝ) (v_x : Option ℝ) (v_a : Option ℝ) (v_b : Option ℝ) (v_d : Option ℝ)
    (hp0 : Refines (not (nonzero (add (add v_l (mul (some (-1)) v_r)) (mul (some (-1)) (mul v_a (add ((add v_x v_b).map (fun x => x ^ (2))) (mul (some (-1)) v_d))))))) (some true))
    (hp1 : Refines (lt v_a (some 0)) (some true))
    (hp2 : Refines (le (some 0) v_d) (some true))
    (hp3 : Defined v_a)
    (hp4 : Defined v_b)
    (hp5 : Defined v_d)
    (hp6 : Defined v_x) :
    Refines (le v_l v_r) (or (le v_x (add (mul (some (-1)) v_b) (mul (some (-1)) (Functions.sqrtR.apply v_d)))) (le (add (mul (some (-1)) v_b) (Functions.sqrtR.apply v_d)) v_x)) := by
  classical
  obtain ⟨a, rfl⟩ := hp3
  obtain ⟨b, rfl⟩ := hp4
  obtain ⟨d, rfl⟩ := hp5
  obtain ⟨x, rfl⟩ := hp6
  cases v_l with
  | none => intro v hv; cases hv
  | some l =>
    cases v_r with
    | none => intro v hv; cases hv
    | some r =>
      have hp : l-r=a*((x+b)^2-d) := by
        simpa [Refines, not, nonzero, add, mul, ← sub_eq_add_neg, sub_eq_zero] using hp0
      have ha : a<0 := by simpa [Refines, lt] using hp1
      have hd : 0≤d := by simpa [Refines, le] using hp2
      have h := Order.quadratic_le_neg hp ha
      have he : l≤r ↔ x≤-b-Real.sqrt d ∨ -b+Real.sqrt d≤x := by
        constructor
        · intro hl
          rcases h.mp hl with h₁ | h₂
          · left; linarith
          · right; linarith
        · intro hr
          apply h.mpr
          rcases hr with h₁ | h₂
          · left; linarith
          · right; linarith
      have hb : decide (l ≤ r)=decide (x ≤ -b-Real.sqrt d ∨ -b+Real.sqrt d ≤ x) := decide_eq_decide.mpr he
      apply refines_of_eq
      simpa [le, or_some, add, mul, Function1.apply, Functions.sqrtR, hd,
        ← Bool.decide_or, ← sub_eq_add_neg] using
        congrArg (fun b : Bool => some b) hb

theorem refines_complex_half_power_negative (v_z : Option ℂ) (v_w : Option ℂ)
    (hp0 : Refines (not (nonzero (add v_w (mul (some (-1)) (Functions.castRC.apply (some (1/2))))))) (some true))
    (hp1 : Refines (not (nonzero (Functions.imC.apply v_z))) (some true))
    (hp2 : Refines (lt (Functions.reC.apply v_z) (some 0)) (some true)) :
    Refines (Functions.powerC.apply v_z v_w) (mul (some Complex.I) (Functions.castRC.apply (Functions.sqrtR.apply (mul (some (-1)) (Functions.reC.apply v_z))))) := by
  classical
  cases v_z with
  | none => intro v hv; cases hv
  | some z =>
    cases v_w with
    | none => intro v hv; cases hv
    | some w =>
      have hw : w=(2⁻¹ : ℂ) := by
        simpa [Refines, not, nonzero, add, mul, Function1.apply, Functions.castRC,
          ← sub_eq_add_neg, sub_eq_zero] using hp0
      have hi : z.im=0 := by
        simpa [Refines, not, nonzero, Function1.apply, Functions.imC] using hp1
      have hr : z.re<0 := by
        simpa [Refines, lt, Function1.apply, Functions.reC] using hp2
      subst w
      have hz : z≠0 := by intro h; simp [h] at hr
      apply refines_of_eq
      simp [Function2.apply, Functions.powerC, Function1.apply, Functions.sqrtR,
        Functions.castRC, Functions.reC, mul, hz, (neg_pos.mpr hr).le,
        Elementary.sqrt_real_negative hi hr]

end QSym.Value

namespace QSym

open Lean Meta Elab Tactic in
elab "qsym_branch_goal" : tactic => do
  let t ← getMainTarget
  unless t.isAppOfArity ``Value.Refines 3 do throwError "not a refinement"
  let source := t.getAppArgs[1]!
  let target := t.getAppArgs[2]!
  let root := source.getAppFn
  let realRoot := root.isConstOf ``Value.lt || root.isConstOf ``Value.le
  let nonzeroRoot := root.isConstOf ``Value.nonzero
  let power := (source.find? fun e => e.isConstOf ``Functions.powerC).isSome &&
    target.getAppFn.isConstOf ``Value.mul
  let sqrt := (target.find? fun e => e.isConstOf ``Functions.sqrtR || e.isConstOf ``Functions.sqrtC).isSome
  unless sqrt && (realRoot || nonzeroRoot || power) do throwError "not a quadratic or half-power refinement"

macro "qsym_branch" : tactic => `(tactic| (
  qsym_branch_goal
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, one_mul,
    zero_add, add_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at *
  first
  | (apply Value.refines_real_nonzero_quadratic <;> assumption)
  | (apply Value.refines_complex_nonzero_quadratic <;> assumption)
  | (apply Value.refines_real_lt_quadratic_pos <;> assumption)
  | (apply Value.refines_real_le_quadratic_pos <;> assumption)
  | (apply Value.refines_real_lt_quadratic_neg <;> assumption)
  | (apply Value.refines_real_le_quadratic_neg <;> assumption)
  | (apply Value.refines_complex_half_power_negative <;> assumption)
))

end QSym
