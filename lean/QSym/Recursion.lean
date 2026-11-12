import QSym.FixedPoint

namespace QSym.Recursion
open OmegaCompletePartialOrder
attribute [local instance] Classical.propDecidable

inductive Program (α β : Type) : Type → Type 1 where
  | constant : (α → Option γ) → Program α β γ
  | call : Program α β α → Program α β β
  | unary (f : Option γ → Option δ) (hn : f none = none) : Program α β γ → Program α β δ
  | binary (f : Option γ → Option δ → Option ε)
      (hl : ∀ y, f none y = none) (hr : ∀ x, f x none = none) :
      Program α β γ → Program α β δ → Program α β ε
  | branch : Program α β Bool → Program α β γ → Program α β γ → Program α β γ

variable {α β γ δ ε : Type}

theorem mask_branch [Zero α] (p : Option Bool) (x : Option α) :
    Value.mask p x = p.bind (fun b => if b then x else some 0) := by
  cases p with
  | none => rfl
  | some b => cases b <;> rfl

theorem and_branch (p q : Option Bool) :
    Value.and p q = p.bind (fun b => if b then q else some false) := by
  cases p with
  | none => rfl
  | some b => cases b <;> rfl

theorem or_branch (p q : Option Bool) :
    Value.or p q = p.bind (fun b => if b then some true else q) := by
  cases p with
  | none => rfl
  | some b => cases b <;> rfl

def Program.eval (g : α → Option β) (x : α) : {γ : Type} → Program α β γ → Option γ
  | _, .constant f => f x
  | _, .call a => (a.eval g x).bind g
  | _, .unary f _ a => f (a.eval g x)
  | _, .binary f _ _ a b => f (a.eval g x) (b.eval g x)
  | _, .branch p a b => (p.eval g x).bind (fun c => if c then a.eval g x else b.eval g x)

noncomputable def lookup (x : α) : (α → Part β) →𝒄 Part β :=
  ⟨Pi.evalOrderHom x, fun _ => rfl⟩

noncomputable def Program.continuous (x : α) : {γ : Type} → Program α β γ → (α → Part β) →𝒄 Part γ
  | _, .constant f => .const (Part.ofOption (f x))
  | _, .call a => .bind (a.continuous x) (.flip lookup)
  | _, .unary f _ a => .bind (a.continuous x) (.const (fun y => Part.ofOption (f (some y))))
  | _, .binary f _ _ a b => .bind (a.continuous x)
      (.flip (fun y => .bind (b.continuous x) (.const (fun z => Part.ofOption (f (some y) (some z))))))
  | _, .branch p a b => .bind (p.continuous x) (.flip (fun c => if c then a.continuous x else b.continuous x))

theorem toOption_bind (x : Part α) (f : α → Part β) :
    (x.bind f).toOption = x.toOption.bind (fun y => (f y).toOption) := by
  classical
  induction x using Part.induction_on <;> simp [Part.none_toOption, Part.some_toOption]

theorem toOption_ofOption (x : Option α) [Decidable (Part.ofOption x).Dom] : (Part.ofOption x).toOption = x := by
  cases x <;> simp [Part.ofOption, Part.none_toOption, Part.some_toOption]

theorem Program.toOption_continuous (p : Program α β γ) (x : α) (g : α → Part β) :
    (p.continuous x g).toOption = p.eval (fun y => (g y).toOption) x := by
  classical
  induction p with
  | constant f => simp [continuous, eval, ContinuousHom.const_apply, toOption_ofOption]
  | call a ih => simpa [continuous, eval, ContinuousHom.bind_apply, ContinuousHom.flip_apply,
      lookup, toOption_bind] using congrArg (fun z => z.bind (fun y => (g y).toOption)) ih
  | unary f hn a ih =>
    simp only [continuous, ContinuousHom.bind_apply, ContinuousHom.const_apply, toOption_bind, ih, Part.to_ofOption, eval]
    cases a.eval (fun y => (g y).toOption) x <;> simp [hn, toOption_ofOption]
  | binary f hl hr a b ia ib =>
    simp only [continuous, ContinuousHom.bind_apply, ContinuousHom.const_apply, ContinuousHom.flip_apply,
      toOption_bind, ia, ib, Part.to_ofOption, eval]
    cases a.eval (fun y => (g y).toOption) x <;> cases b.eval (fun y => (g y).toOption) x <;> simp [hl, hr, toOption_ofOption]
  | branch p a b ip ia ib =>
    simp only [continuous, ContinuousHom.bind_apply, ContinuousHom.flip_apply, toOption_bind, ip, eval]
    cases p.eval (fun y => (g y).toOption) x with
    | none => rfl
    | some c => cases c <;> simp [ia, ib]

noncomputable def Program.functional (p : Program α β β) : (α → Part β) →𝒄 (α → Part β) :=
  .flip (fun x => p.continuous x)

noncomputable def transform (f : Option ((α → Option β) → Option (α → Option β)))
    (g : α → Part β) (x : α) : Part β := by
  classical
  exact Part.ofOption (f.bind (fun h => (h (fun y => (g y).toOption)).bind (fun k => k x)))

noncomputable def fixedValue (f : Option ((α → Option β) → Option (α → Option β))) :
    Option (α → Option β) := by
  classical
  exact f.bind (fun k => if h : ωScottContinuous (transform (some k)) then
    some (FixedPoint.value ⟨⟨transform (some k), h.monotone⟩, h.map_ωSup⟩) else none)

theorem fixed_program (p : Program α β β) (f : (α → Option β) → Option (α → Option β))
    (h : ∀ g, f g = some (fun x => p.eval g x)) :
    fixedValue (some f) = some (FixedPoint.value p.functional) := by
  classical
  have ht : transform (some f) = p.functional := by
    funext g x
    simp only [transform, Option.some_bind, h, Program.functional, ContinuousHom.flip_apply]
    rw [← p.toOption_continuous x g, Part.of_toOption]
  have hc : ωScottContinuous (transform (some f)) := ht ▸ p.functional.ωScottContinuous
  simp only [fixedValue, Option.some_bind, dif_pos hc]
  have he : (⟨⟨transform (some f), hc.monotone⟩, hc.map_ωSup⟩ : (α → Part β) →𝒄 (α → Part β)) = p.functional :=
    ContinuousHom.ext _ _ (congrFun ht)
  exact congrArg (fun k => some (FixedPoint.value k)) he

theorem Program.unfold (p : Program α β β) (x : α) :
    p.eval (FixedPoint.value p.functional) x = FixedPoint.value p.functional x := by
  classical
  change p.eval (fun y => (FixedPoint.least p.functional y).toOption) x = _
  rw [← p.toOption_continuous x (FixedPoint.least p.functional)]
  exact congrArg (fun g => (g x).toOption) (FixedPoint.unfold p.functional)

theorem program_unfold (p : Program α β β) (f : (α → Option β) → Option (α → Option β))
    (h : ∀ g, f g = some (fun x => p.eval g x)) :
    fixedValue (some f) = (fixedValue (some f)).bind f := by
  rw [fixed_program p f h, Option.some_bind, h]
  exact congrArg some (funext (fun x => (p.unfold x).symm))

theorem fixed_constant (k : α → Option β) :
    fixedValue (some (fun _ => some k)) = some k := by
  rw [fixed_program (.constant k) (fun _ => some k) (fun _ => rfl)]
  have hp : (Program.constant k : Program α β β).functional =
      ContinuousHom.const (fun x => Part.ofOption (k x)) :=
    ContinuousHom.ext _ _ (fun _ => rfl)
  rw [hp]
  congr 1
  funext x
  simp only [FixedPoint.value, FixedPoint.least_const, toOption_ofOption]

theorem fixed_identity : fixedValue (some (fun g : α → Option β => some g)) = some (fun _ => none) := by
  rw [fixed_program (.call (.constant some)) (fun g => some g) (fun _ => rfl)]
  have hp : (Program.call (.constant some) : Program α β β).functional = ContinuousHom.id := by
    apply ContinuousHom.ext
    intro g
    funext x
    simp [Program.functional, Program.continuous, ContinuousHom.flip_apply, ContinuousHom.bind_apply,
      ContinuousHom.const_apply, lookup, ContinuousHom.id_apply]
  rw [hp]
  congr 1
  funext x
  simp only [FixedPoint.value, FixedPoint.least_id]
  exact @Part.none_toOption β (Classical.propDecidable _)

end QSym.Recursion
