import QSym.Generated
import QSym.AC

namespace QSym.Value

theorem refines_mask_under {α : Type} [Zero α] (p : Option Bool) (x y : Option α)
    (h : p = some true → Refines x y) : Refines (mask p x) (mask p y) := by
  cases p with
  | none => exact refines_refl _
  | some b => cases b with
    | false => exact refines_refl _
    | true => exact h rfl

theorem refines_and_under (p x y : Option Bool)
    (h : p = some true → Refines x y) : Refines (and p x) (and p y) := by
  cases p with
  | none => exact refines_refl _
  | some b => cases b with
    | false => exact refines_refl _
    | true => exact h rfl

theorem refines_or_under (p x y : Option Bool)
    (h : p = some false → Refines x y) : Refines (or p x) (or p y) := by
  cases p with
  | none => exact refines_refl _
  | some b => cases b with
    | false => exact h rfl
    | true => exact refines_refl _

theorem and_true_left {p q : Option Bool} (h : and p q = some true) : p = some true := by
  cases p with
  | none => simp [and] at h
  | some b => cases b <;> simp_all [and]
theorem and_true_right {p q : Option Bool} (h : and p q = some true) : q = some true := by
  cases p with
  | none => simp [and] at h
  | some b => cases b <;> simp_all [and]
theorem or_false_left {p q : Option Bool} (h : or p q = some false) : p = some false := by
  cases p with
  | none => simp [or] at h
  | some b => cases b <;> simp_all [or]
theorem or_false_right {p q : Option Bool} (h : or p q = some false) : q = some false := by
  cases p with
  | none => simp [or] at h
  | some b => cases b <;> simp_all [or]
theorem of_not {p : Option Bool} {b : Bool} (h : not p = some b) : p = some (!b) := by
  cases p with
  | none => simp [not] at h
  | some p => cases p <;> cases b <;> simp_all [not]
theorem not_eq {p : Option Bool} {b : Bool} (h : p = some b) : not p = some (!b) := by
  rw [h]; rfl

theorem defined_inv_arg {α : Type} [Zero α] [Inv α] (x : Option α)
    (h : Defined (inv x)) : Defined x := by
  obtain ⟨v, hv, _⟩ := (defined_inv x).mp h
  exact ⟨v, hv⟩
theorem defined_mask_guard {α : Type} [Zero α] (p : Option Bool) (x : Option α)
    (h : Defined (mask p x)) : Defined p := by
  rcases (defined_mask p x).mp h with h | ⟨h, _⟩
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩
theorem defined_and_guard (p q : Option Bool) (h : Defined (and p q)) : Defined p := by
  rcases (defined_and p q).mp h with h | ⟨h, _⟩
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩
theorem defined_or_guard (p q : Option Bool) (h : Defined (or p q)) : Defined p := by
  rcases (defined_or p q).mp h with h | ⟨h, _⟩
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

theorem defined_and_total (p q : Option Bool) (hp : Defined p) (hq : Defined q) :
    Defined (and p q) := by
  obtain ⟨b, rfl⟩ := hp
  cases b
  · exact ⟨false, rfl⟩
  · exact hq
theorem defined_or_total (p q : Option Bool) (hp : Defined p) (hq : Defined q) :
    Defined (or p q) := by
  obtain ⟨b, rfl⟩ := hp
  cases b
  · exact hq
  · exact ⟨true, rfl⟩
end QSym.Value

namespace QSym.Replay

noncomputable def addR : AC (Option ℝ) :=
  ⟨Value.add, some ((0 : Int) : ℝ), Generated.r_real_add_assoc, Generated.r_real_add_comm,
    Generated.r_real_add_unit⟩
noncomputable def mulR : AC (Option ℝ) :=
  ⟨Value.mul, some ((1 : Int) : ℝ), Generated.r_real_mul_assoc, Generated.r_real_mul_comm,
    Generated.r_real_mul_unit⟩
noncomputable def addC : AC (Option ℂ) :=
  ⟨Value.add, some (((0 : Int) : ℂ) + ((0 : Int) : ℂ) * Complex.I),
    Generated.r_complex_add_assoc, Generated.r_complex_add_comm, Generated.r_complex_add_unit⟩
noncomputable def mulC : AC (Option ℂ) :=
  ⟨Value.mul, some (((1 : Int) : ℂ) + ((0 : Int) : ℂ) * Complex.I),
    Generated.r_complex_mul_assoc, Generated.r_complex_mul_comm, Generated.r_complex_mul_unit⟩

end QSym.Replay
