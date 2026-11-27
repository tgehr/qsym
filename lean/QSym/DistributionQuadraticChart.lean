import QSym.DistributionInverseCover

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates
open Classical

/-- Inverse sheets with a gap cannot describe a total finite-piece coordinate.
Their relation determines the entire forward distribution, including its pointwise fibres. -/
theorem image_of_cover_gap {ι : Type} {gs : ι → ℝ → Option ℝ} {f : ℝ → Option ℝ}
    {gap : ℝ} (absent : ∀ i, gs i gap = none)
    (cover : ∀ x y, (∃ i, gs i y = some x) ↔ f x = some y) :
    realPushforwardOnValue (some fun _ => some true) (some f) = value (some gs) :=
  (inverseCover_eq cover).symm.trans (of_gap absent).symm

/-- A bijection of target coordinates transports every inverse sheet. It also
transports a gap, so the same interpretation applies after the change of coordinates. -/
theorem image_reparam {ι : Type} {gs : ι → ℝ → Option ℝ} {f : ℝ → Option ℝ}
    (e : ℝ ≃ ℝ) {gap : ℝ} (absent : ∀ i, gs i gap = none)
    (cover : ∀ x y, (∃ i, gs i y = some x) ↔ f x = some y) :
    realPushforwardOnValue (some fun _ => some true) (some fun x => (f x).map e) =
      value (some fun i y => gs i (e.symm y)) := by
  apply image_of_cover_gap (gap := e gap)
  · simpa using absent
  · intro x y
    rw [cover]
    cases h : f x with
    | none => simp
    | some v => simp [Equiv.eq_symm_apply]

namespace Quadratic

private def sheet (lower : Bool) (h t u : Option ℝ) (y : ℝ) : Option ℝ :=
  let root := Functions.sqrtR.apply (Value.add (Value.mul t (some y)) u)
  Value.add h (if lower then Value.mul (some ((-1 : ℤ) : ℝ)) root else root)

-- Suppress neutral affine coefficients before a partial square root is formed.
private def shortSheet (c a b : ℚ) (lower : Bool) (h t u : Option ℝ) (y : ℝ) : Option ℝ :=
  let scale := if a = 1 then some y else Value.mul t (some y)
  let linear := if b = 0 then scale else Value.add scale u
  let root := Functions.sqrtR.apply linear
  let signed := if lower then Value.mul (some ((-1 : ℤ) : ℝ)) root else root
  if c = 0 then signed else Value.add h signed

private theorem shortSheet_eq (c a b : ℚ) (lower : Bool) :
    shortSheet c a b lower (some c) (some a) (some b) = sheet lower (some c) (some a) (some b) := by
  funext y
  by_cases hc : c = 0 <;> by_cases ha : a = 1 <;> by_cases hb : b = 0 <;>
    simp [shortSheet, sheet, *, Value.add_zero_left, Value.add_zero_right, Value.mul_one_left]

private def pair (l r : ℝ → Option ℝ) :=
  Tensor.consValue (some l) (Tensor.consValue (some r) Tensor.nilValue)

/-- A checked polynomial identity for a partial source determines its total forward map. -/
theorem equation (c a b : ℝ) (ha : a ≠ 0) {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul (some a) (f x)) (some b))
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) (some c))))) = some 0) :
    ∀ x, f x = some (((x-c)^2-b)/a) := by
  intro x
  have e := equal x
  cases hx : f x with
  | none => simp [hx, Value.add, Value.mul] at e
  | some y =>
    simp [hx, Value.add, Value.mul, squareInput] at e
    exact congrArg some ((eq_div_iff ha).2 (by linarith))

/-- The polynomial equality checked at the source is t f(x) + u = (x-h)².
Both signs of t use the same two sheets. The two roots coincide at the vertex. -/
theorem image (c a b : ℚ) (ha : a ≠ 0) {h t u : Option ℝ}
    (hc : h = some (c : ℝ)) (ht : t = some (a : ℝ)) (hu : u = some (b : ℝ))
    {f : ℝ → Option ℝ}
    (equal : ∀ x, Value.add (Value.add (Value.mul t (f x)) u)
      (Value.mul (some ((-1 : ℤ) : ℝ)) (squareInput false
        (Value.add (some x) (Value.mul (some ((-1 : ℤ) : ℝ)) h)))) = some 0) :
    realPushforwardOnValue (some fun _ => some true) (some f) =
      value (pair (shortSheet c a b true h t u) (shortSheet c a b false h t u)) := by
  subst h; subst t; subst u
  rw [shortSheet_eq, shortSheet_eq]
  let A : ℝ := a
  let B : ℝ := b
  let C : ℝ := c
  have hn : A ≠ 0 := by change (a : ℝ) ≠ 0; exact_mod_cast ha
  let F (x : ℝ) := ((x-C)^2-B)/A
  have eq : ∀ x, f x = some (F x) := equation C A B hn equal
  let lo := sheet true (some C) (some A) (some B)
  let hi := sheet false (some C) (some A) (some B)
  let gs : Fin 2 → ℝ → Option ℝ := Fin.cases lo (Fin.cases hi Fin.elim0)
  change _ = value (some gs)
  apply image_of_cover_gap (gap := (-1-B)/A)
  · have hneg : A*((-1-B)/A)+B < 0 := by field_simp [hn]
    intro i
    have absent (lower : Bool) : sheet lower (some C) (some A) (some B) ((-1-B)/A) = none := by
      cases lower <;> simp [sheet, Value.add, Value.mul, Functions.sqrtR, Function1.apply, not_le.mpr hneg]
    fin_cases i
    · exact absent true
    · exact absent false
  · intro x y
    rw [eq]
    have two : (∃ i, gs i y = some x) ↔ lo y = some x ∨ hi y = some x := by
      constructor
      · rintro ⟨i, hi'⟩; fin_cases i <;> tauto
      · exact fun h' => h'.elim (fun p => ⟨0, p⟩) (fun p => ⟨1, p⟩)
    rw [two, Option.some.injEq]
    by_cases hv : 0 ≤ A*y+B
    · simp [lo, hi, sheet, Value.add, Value.mul, Functions.sqrtR, Function1.apply, hv]
      have sq := Real.sq_sqrt hv
      constructor
      · rintro (hx | hx) <;> rw [← hx] <;> apply (div_eq_iff hn).2 <;> nlinarith only [sq]
      · intro hy
        have e := (div_eq_iff hn).1 hy
        have z : (x-C-√(A*y+B)) * (x-C+√(A*y+B)) = 0 := by nlinarith
        rcases mul_eq_zero.mp z with z | z
        · right; linarith
        · left; linarith
    · simp [lo, hi, sheet, Value.add, Value.mul, Functions.sqrtR, Function1.apply, hv]
      intro hy
      have e := (div_eq_iff hn).1 hy
      nlinarith [sq_nonneg (x-C)]

end Quadratic
end QSym.Distribution.GraphFibre.Coordinates
