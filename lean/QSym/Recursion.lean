import QSym.FixedPoint
import QSym.Functions

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

noncomputable def natStep (op : Option ℕ → Option ℕ → Option ℕ)
    (a d : Option ℕ) (g : ℕ → Option ℕ) (n : ℕ) : Option ℕ :=
  let p := Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))
  Functions.addN.apply (Value.mask p a)
    (Value.mask (Value.not p) (op ((Functions.subN.apply (some n) (some 1)).bind g) d))

theorem nat_successor (n : ℕ) : Functions.addN.apply (some n) (some 1) = some (n+1) := by
  simp [Function2.apply, Functions.addN]

theorem natStep_zero (op : Option ℕ → Option ℕ → Option ℕ)
    (a d : Option ℕ) (g : ℕ → Option ℕ) : natStep op a d g 0 = a := by
  cases a <;> simp [natStep, Function1.apply, Function2.apply, Functions.nonzeroZ,
    Functions.castNZ, Functions.addN, Value.mask, Value.not]

theorem natStep_succ (op : Option ℕ → Option ℕ → Option ℕ)
    (a d : Option ℕ) (g : ℕ → Option ℕ) (n : ℕ) :
    natStep op a d g (n+1) = op (g n) d := by
  have ht : Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some (n+1)))) = some false := by
    have hn : (↑n + 1 : ℤ) ≠ 0 := by omega
    simp [Function1.apply, Functions.nonzeroZ, Functions.castNZ, Value.not, hn]
  have hp : Functions.subN.apply (some (n+1)) (some 1) = some n := by
    simp [Function2.apply, Functions.subN]
  unfold natStep
  rw [ht, hp]
  simp only [Option.some_bind, Value.not, Value.mask, Bool.not_false]
  cases op (g n) d <;> simp [Function2.apply, Functions.addN]

theorem solve_nat_step (p : Program ℕ ℕ ℕ) (op : Option ℕ → Option ℕ → Option ℕ)
    (a d : Option ℕ) (k : ℕ → Option ℕ)
    (hp : ∀ g n, p.eval g n = natStep op a d g n)
    (h0 : k 0 = a) (hs : ∀ n, k (n+1) = op (k n) d) :
    FixedPoint.value p.functional = k := by
  funext n
  induction n with
  | zero => rw [← p.unfold 0, hp, natStep_zero, h0]
  | succ n ih => rw [← p.unfold (n+1), hp, natStep_succ, ih, hs]

noncomputable def natCutoff (a b : ℕ) (g : ℕ → Option ℕ) (n : ℕ) : Option ℕ :=
  let p := Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))
  let q := Functions.leN.apply (some n) (some b)
  Functions.addN.apply (Value.mask p (some a)) (Value.mask (Value.not p)
    (Functions.addN.apply
      (Value.mask q ((Functions.subN.apply (some n) (some 1)).bind g))
      (Value.mask (Value.not q) ((Functions.addN.apply (some n) (some 1)).bind g))))

theorem natCutoff_eq (a b : ℕ) (g : ℕ → Option ℕ) (n : ℕ) :
    natCutoff a b g n = if n = 0 then some a else if n ≤ b then g (n-1) else g (n+1) := by
  rcases n with _ | n
  · simp [natCutoff, Function1.apply, Function2.apply, Functions.nonzeroZ,
      Functions.castNZ, Functions.addN, Value.mask, Value.not]
  · have hn : (↑n + 1 : ℤ) ≠ 0 := by omega
    by_cases hb : n+1 ≤ b <;>
      simp [natCutoff, Function1.apply, Function2.apply, Functions.nonzeroZ, Functions.castNZ,
        Functions.addN, Functions.subN, Functions.leN, Value.mask, Value.not, hn, hb]

theorem solve_nat_cutoff (p : Program ℕ ℕ ℕ) (a b : ℕ)
    (hp : ∀ g n, p.eval g n = natCutoff a b g n) :
    FixedPoint.value p.functional = fun n =>
      if Functions.leN.apply (some n) (some b) == some true then some a else none := by
  classical
  let k : ℕ → Option ℕ := fun n => if n ≤ b then some a else none
  have hk : p.functional (fun n => Part.ofOption (k n)) = fun n => Part.ofOption (k n) := by
    funext n
    apply Part.equivOption.injective
    simp only [Part.equivOption, Equiv.coe_fn_mk]
    change (p.functional (fun n => Part.ofOption (k n)) n).toOption = _
    rw [Program.functional, ContinuousHom.flip_apply, Program.toOption_continuous]
    simp only [toOption_ofOption, hp, natCutoff_eq]
    by_cases hz : n = 0
    · subst n; simp [k]
    · by_cases hb : n ≤ b
      · simp [hz, hb, k, Nat.sub_le n 1 |>.trans hb]
      · have hs : ¬ n+1 ≤ b := by omega
        simp [hz, hb, hs, k]
  have hle := FixedPoint.least_le p.functional (le_of_eq hk)
  funext n
  have he : FixedPoint.value p.functional n = k n := by
    by_cases hb : n ≤ b
    · have ha : ∀ n, n ≤ b → FixedPoint.value p.functional n = some a := by
        intro n
        induction n with
        | zero => intro _; rw [← p.unfold 0, hp, natCutoff_eq]; simp
        | succ n ih =>
          intro hn
          rw [← p.unfold (n+1), hp, natCutoff_eq]
          simp [hn, ih (by omega)]
      simpa [k, hb] using ha n hb
    · have hn : FixedPoint.least p.functional n = Part.none := by
        apply le_antisymm
        · simpa [k, hb] using hle n
        · exact bot_le
      simp [FixedPoint.value, hn, k, hb, Part.none_toOption]
  rw [he]
  simp [k, Function2.apply, Functions.leN]

noncomputable def natBand (a l u : ℕ) (g : ℕ → Option ℕ) (n : ℕ) : Option ℕ :=
  if n = l then some a else if n < u then if n = 0 then none else g (n-1) else g (n+1)

theorem solve_nat_band (p : Program ℕ ℕ ℕ) (a l u : ℕ) (hlu : l < u)
    (hp : ∀ g n, p.eval g n = natBand a l u g n) :
    FixedPoint.value p.functional = fun n => if l ≤ n ∧ n < u then some a else none := by
  classical
  let k : ℕ → Option ℕ := fun n => if l ≤ n ∧ n < u then some a else none
  have hk : p.functional (fun n => Part.ofOption (k n)) = fun n => Part.ofOption (k n) := by
    funext n
    apply Part.equivOption.injective
    simp only [Part.equivOption, Equiv.coe_fn_mk]
    change (p.functional (fun n => Part.ofOption (k n)) n).toOption = _
    rw [Program.functional, ContinuousHom.flip_apply, Program.toOption_continuous]
    simp only [toOption_ofOption, hp, natBand]
    by_cases he : n = l
    · subst n; simp [k, hlu]
    · by_cases hu : n < u
      · by_cases hz : n = 0
        · subst n; have hl : ¬ l ≤ 0 := by omega
          simp [he, k, hu, hl]
        · by_cases hl : l ≤ n
          · have hl' : l ≤ n-1 := by omega
            have hu' : n-1 < u := by omega
            simp [he, hu, hz, k, hl, hl', hu']
          · have hl' : ¬ l ≤ n-1 := by omega
            simp [he, hu, hz, k, hl, hl']
      · have hu' : ¬ n+1 < u := by omega
        simp [he, hu, k, hu']
  have hle := FixedPoint.least_le p.functional (le_of_eq hk)
  funext n
  by_cases h : l ≤ n ∧ n < u
  · have ha : ∀ n, l ≤ n → n < u → FixedPoint.value p.functional n = some a := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hl hu
        rw [← p.unfold n, hp, natBand]
        by_cases he : n = l
        · simp [he]
        · have hz : n ≠ 0 := by omega
          have hn : n-1 < n := by omega
          have hl' : l ≤ n-1 := by omega
          have hu' : n-1 < u := by omega
          simp [he, hu, hz, ih (n-1) hn hl' hu']
    simpa [h] using ha n h.1 h.2
  · have hn : FixedPoint.least p.functional n = Part.none := by
      apply le_antisymm
      · simpa [k, h] using hle n
      · exact bot_le
    simp [FixedPoint.value, hn, h, Part.none_toOption]

noncomputable def natChoose (p : Option Bool) (x y : Option ℕ) : Option ℕ :=
  Functions.addN.apply (Value.mask p x) (Value.mask (Value.not p) y)

theorem natChoose_some (b : Bool) (x y : Option ℕ) : natChoose (some b) x y = if b then x else y := by
  cases b <;> cases x <;> cases y <;> simp [natChoose, Value.mask, Value.not, Function2.apply, Functions.addN]

noncomputable def natCutoffLt (a u : ℕ) (g : ℕ → Option ℕ) (n : ℕ) : Option ℕ :=
  natChoose (Value.not (Functions.nonzeroZ.apply (Functions.castNZ.apply (some n)))) (some a)
    (natChoose (Functions.ltN.apply (some n) (some u))
      ((Functions.subN.apply (some n) (some 1)).bind g)
      ((Functions.addN.apply (some n) (some 1)).bind g))

theorem natCutoffLt_eq (a u : ℕ) (g : ℕ → Option ℕ) (n : ℕ) :
    natCutoffLt a u g n = natBand a 0 u g n := by
  rcases n with _ | n
  · simp [natCutoffLt, natChoose, natBand, Function1.apply, Function2.apply,
      Functions.castNZ, Functions.nonzeroZ, Functions.addN, Value.mask, Value.not]
  · have hn : (↑n + 1 : ℤ) ≠ 0 := by omega
    by_cases hu : n+1 < u <;>
      simp [natCutoffLt, natChoose, natBand, Function1.apply, Function2.apply,
        Functions.castNZ, Functions.nonzeroZ, Functions.addN, Functions.subN, Functions.ltN, Value.mask, Value.not, hn, hu]

theorem solve_nat_cutoff_lt (p : Program ℕ ℕ ℕ) (a u : ℕ) (hu : 0 < u)
    (hp : ∀ g n, p.eval g n = natCutoffLt a u g n) :
    FixedPoint.value p.functional = fun n =>
      if Functions.ltN.apply (some n) (some u) == some true then some a else none := by
  have h := solve_nat_band p a 0 u hu (fun g n => (hp g n).trans (natCutoffLt_eq a u g n))
  simpa [Function2.apply, Functions.ltN] using h

noncomputable def natInterval (a l u : ℕ) (g : ℕ → Option ℕ) (n : ℕ) : Option ℕ :=
  let down := (Functions.subN.apply (some n) (some 1)).bind g
  let up := (Functions.addN.apply (some n) (some 1)).bind g
  let eq := Value.not (Functions.nonzeroZ.apply (Functions.addZ.apply (Functions.castNZ.apply (some n))
    (Functions.mulZ.apply (some (-1)) (some (l : ℤ)))))
  natChoose (Functions.ltN.apply (some n) (some l)) down
    (natChoose eq (some a) (natChoose (Functions.ltN.apply (some n) (some u)) down up))

theorem natInterval_eq (a l u : ℕ) (hlu : l < u) (g : ℕ → Option ℕ) (n : ℕ) :
    natInterval a l u g n = natBand a l u g n := by
  have he : ((n : ℤ) + -(l : ℤ) = 0) ↔ n = l := by omega
  have hd : (Functions.subN.apply (some n) (some 1)).bind g = if n = 0 then none else g (n-1) := by
    rcases n with _ | n <;> simp [Function2.apply, Functions.subN]
  simp only [natInterval]
  rw [hd]
  by_cases hl : n < l <;> by_cases hn : n = l <;> by_cases hu : n < u <;>
    simp [natChoose, natBand, Function1.apply, Function2.apply, Functions.castNZ,
      Functions.nonzeroZ, Functions.addZ, Functions.mulZ, Functions.addN, Functions.ltN,
      Value.mask, Value.not, he, hl, hn, hu] <;> try omega

theorem solve_nat_interval (p : Program ℕ ℕ ℕ) (a l u : ℕ) (hlu : l < u)
    (hp : ∀ g n, p.eval g n = natInterval a l u g n) :
    FixedPoint.value p.functional = fun n =>
      if Value.and (Functions.leN.apply (some l) (some n)) (Functions.ltN.apply (some n) (some u)) == some true
      then some a else none := by
  have h := solve_nat_band p a l u hlu (fun g n => (hp g n).trans (natInterval_eq a l u hlu g n))
  rw [h]
  funext n
  by_cases hl : l ≤ n <;> by_cases hu : n < u <;>
    simp [Function2.apply, Functions.ltN, Functions.leN, Value.and, hl, hu]

end QSym.Recursion
