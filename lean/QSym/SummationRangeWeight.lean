import QSym.Summation

noncomputable section
namespace QSym.Summation

/-- On each visited index the scalar coefficient is defined exactly when its
captured parameter is. Nothing is required of indices outside the range. -/
def RangeDefined {β : Type} (token : Option β) (w : ℕ → Option ℝ) (n : Option ℕ) :=
  ∀ k, n = some k → ∀ i < k, (w i).isSome = token.isSome

namespace RangeDefined

private theorem power (r : Option ℝ) (e : Option ℕ) (h : e.isSome) :
    (Functions.powRN.apply r e).isSome = r.isSome := by
  rcases e with _ | i
  · contradiction
  · cases r <;> simp [Functions.powRN, Function2.apply]

theorem index (r : Option ℝ) (n : Option ℕ) :
    RangeDefined r (fun i => Functions.powRN.apply r (some i)) n := fun _ _ _ _ => power r _ rfl

theorem successor (r : Option ℝ) (n : Option ℕ) :
    RangeDefined r (fun i => Functions.powRN.apply r (Functions.addN.apply (some i) (some 1))) n := by
  intro _ _ i _
  apply power r _
  simp [Functions.addN, Function2.apply]

theorem remaining (r : Option ℝ) (n : Option ℕ) :
    RangeDefined r (fun i => Functions.powRN.apply r
      (Functions.subN.apply n (Functions.addN.apply (some i) (some 1)))) n := by
  rintro k rfl i hi
  apply power r _
  simp [Functions.subN, Functions.addN, Function2.apply, Nat.succ_le_of_lt hi]

private def times (right : Bool) (w x : Option ℝ) := if right then Value.mul x w else Value.mul w x

private theorem absent {token : Option β} {w : ℕ → Option ℝ} {n : ℕ} (ht : token = none)
    (h : RangeDefined token w (some (n+1))) (right : Bool) (f : ℕ → Option ℝ) :
    finite (Finset.range (n+1)) (fun i => times right (w i) (f i)) = none := by
  have last := h (n+1) rfl n (Nat.lt_succ_self n)
  rw [ht] at last
  have eq : w n = none := by cases he : w n <;> simp_all
  rw [range_succ, eq]
  generalize finite (α := ℝ) (Finset.range n) _ = previous
  cases previous <;> cases right <;> cases f n <;> rfl

/-- A mask can move outside a strict product inside the finite sum. The
parameter is forced once on a nonempty range, even when every mask is false. -/
theorem mask {β : Type} (right : Bool) (token : Option β) (w f : ℕ → Option ℝ) (p : ℕ → Option Bool) (n : Option ℕ)
    (h : RangeDefined token w n) :
    rangeValue (some fun i => times right (w i) (Value.mask (p i) (f i))) n =
      Value.mask (Functions.nonzeroN.apply n) (token.bind fun _ =>
        rangeValue (some fun i => Value.mask (p i) (times right (w i) (f i))) n) := by
  rcases n with _ | n
  · rfl
  · cases n with
    | zero => simp [rangeValue, finite_empty, Functions.nonzeroN, Function1.apply, Value.mask]
    | succ n =>
      rcases token with _ | t
      · simpa [rangeValue, Value.mask, Functions.nonzeroN, Function1.apply] using
          absent rfl h right (fun i => Value.mask (p i) (f i))
      · simp [rangeValue, Value.mask, Functions.nonzeroN, Function1.apply]
        apply finite_congr
        intro i hi
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h (n+1) rfl i (Finset.mem_range.mp hi))
        rw [hv]
        cases right <;> rcases p i with _ | _ | _ <;> cases f i <;> simp [times, Value.mul, Value.mask]

theorem zero {β : Type} (right : Bool) (token : Option β) (w : ℕ → Option ℝ) (n : Option ℕ)
    (h : RangeDefined token w n) (z : Option ℝ) (hz : z = some 0) :
    rangeValue (some fun i => times right (w i) z) n =
      Value.mask (Functions.nonzeroN.apply n) (token.bind fun _ => z) := by
  subst z
  rcases n with _ | n
  · rfl
  · cases n with
    | zero => simp [rangeValue, finite_empty, Functions.nonzeroN, Function1.apply, Value.mask]
    | succ n =>
      rcases token with _ | t
      · simpa [rangeValue, Value.mask, Functions.nonzeroN, Function1.apply] using absent rfl h right (fun _ => some 0)
      · simp [rangeValue, Value.mask, Functions.nonzeroN, Function1.apply]
        trans finite (Finset.range (n+1)) (fun _ => some (0:ℝ))
        · apply finite_congr
          intro i hi
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h (n+1) rfl i (Finset.mem_range.mp hi))
          cases right <;> simp [times, hv, Value.mul]
        · simp [finite]

end RangeDefined
end QSym.Summation
