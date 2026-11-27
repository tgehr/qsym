import QSym.DistributionInverseCover

namespace QSym.Distribution.GraphFibre.Coordinates

private abbrev Sheet := ℝ → Option ℝ

/-- Both vectors are missing, or their coordinate relations agree. A missing
function value in the vector is distinct from a function with an empty domain. -/
inductive SameSheets {m n : ℕ} : Option (Fin m → Sheet) → Option (Fin n → Sheet) → Prop
  | missing : SameSheets none none
  | present {g h} : SameRelation g h → SameSheets (some g) (some h)

private theorem cons_occurs {n : ℕ} (f : Sheet) (gs : Fin n → Sheet) (y x : ℝ) :
    (∃ i, Fin.cases f gs i y = some x) ↔ f y = some x ∨ ∃ i, gs i y = some x := by
  constructor
  · rintro ⟨i, h⟩
    exact Fin.cases (motive := fun j => Fin.cases f gs j y = some x → _)
      Or.inl (fun j hj => Or.inr ⟨j, hj⟩) i h
  · rintro (h | ⟨i, h⟩)
    · exact ⟨0, h⟩
    · exact ⟨i.succ, h⟩

private theorem SameSheets.trans {k m n : ℕ} {as : Option (Fin k → Sheet)}
    {bs : Option (Fin m → Sheet)} {cs : Option (Fin n → Sheet)}
    (ab : SameSheets as bs) (bc : SameSheets bs cs) : SameSheets as cs := by
  cases ab with
  | missing => cases bc; exact .missing
  | present hab =>
    cases bc with
    | present hbc => exact .present (fun y x => (hab y x).trans (hbc y x))

private theorem SameSheets.swap {n : ℕ} (f g : Option Sheet) (gs : Option (Fin n → Sheet)) :
    SameSheets (Tensor.consValue f (Tensor.consValue g gs)) (Tensor.consValue g (Tensor.consValue f gs)) := by
  cases f <;> cases g <;> cases gs <;> first | exact .missing | skip
  apply SameSheets.present
  intro y x
  simp only [cons_occurs]
  tauto

theorem SameSheets.duplicate {n : ℕ} (f : Option Sheet) (gs : Option (Fin n → Sheet)) :
    SameSheets (Tensor.consValue f (Tensor.consValue f gs)) (Tensor.consValue f gs) := by
  cases f <;> cases gs <;> first | exact .missing | skip
  apply SameSheets.present
  intro y x
  simp only [cons_occurs]
  tauto

theorem SameSheets.keep {m n : ℕ} {gs : Option (Fin m → Sheet)} {hs : Option (Fin n → Sheet)}
    (f : Option Sheet) (h : SameSheets gs hs) : SameSheets (Tensor.consValue f gs) (Tensor.consValue f hs) := by
  cases h with
  | missing =>
    simp only [Tensor.cons_none_right]
    exact .missing
  | present h =>
    cases f with
    | none => exact .missing
    | some f =>
      apply SameSheets.present
      intro y x
      exact (cons_occurs _ _ _ _).trans ((or_congr Iff.rfl (h y x)).trans (cons_occurs _ _ _ _).symm)

/-- Keep an intervening sheet in place when deleting a later copy of the head. -/
theorem SameSheets.between {m n : ℕ} {f : Option Sheet} {gs : Option (Fin m → Sheet)}
    {hs : Option (Fin n → Sheet)} (g : Option Sheet)
    (h : SameSheets (Tensor.consValue f gs) (Tensor.consValue f hs)) :
    SameSheets (Tensor.consValue f (Tensor.consValue g gs)) (Tensor.consValue f (Tensor.consValue g hs)) :=
  (swap f g gs).trans ((keep g h).trans (swap g f hs))

theorem SameSheets.value {m n : ℕ} {gs : Option (Fin m → Sheet)} {hs : Option (Fin n → Sheet)}
    (h : SameSheets gs hs) : value gs = value hs := by
  cases h with
  | missing => rfl
  | present eq => exact eq.value

theorem SameSheets.restricted {m n : ℕ} {gs : Option (Fin m → Sheet)} {hs : Option (Fin n → Sheet)}
    (h : SameSheets gs hs) (p) : restricted p gs = restricted p hs := by
  cases h with
  | missing => cases p <;> rfl
  | present eq => exact eq.restricted p

end QSym.Distribution.GraphFibre.Coordinates
