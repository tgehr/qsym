import QSym.Value

noncomputable section
namespace QSym.Distribution
open MeasureTheory Set

/-- Measurability of the domain and of the zero extension is enough to
compose partial real expressions. Their pointwise denotations stay partial. -/
structure BorelReal (f : ℝ → Option ℝ) : Prop where
  domain : MeasurableSet {x | Value.Defined (f x)}
  val : Measurable fun x => (f x).getD 0

def BorelPred (p : ℝ → Option Bool) := ∀ b, MeasurableSet {x | p x = some b}

namespace BorelReal
variable {f g : ℝ → Option ℝ}

theorem var : BorelReal (fun x : ℝ => some x) := ⟨by simp [Value.Defined], measurable_id⟩
theorem const (v : Option ℝ) : BorelReal (fun _ => v) := ⟨by simp, measurable_const⟩

private theorem binary (hf : BorelReal f) (hg : BorelReal g) (k : ℝ → ℝ → ℝ)
    (hm : Measurable (Function.uncurry k)) :
    BorelReal (fun x => (f x).bind fun a => (g x).map (k a)) := by
  classical
  let s := {x | Value.Defined (f x)} ∩ {x | Value.Defined (g x)}
  have hs : MeasurableSet s := hf.domain.inter hg.domain
  constructor
  · convert hs using 1
    ext x
    cases h : f x <;> cases j : g x <;> simp [s, h, j, Value.Defined]
  · have eq : (fun x => ((f x).bind fun a => (g x).map (k a)).getD 0) =
        s.indicator (fun x => k ((f x).getD 0) ((g x).getD 0)) := by
      funext x
      cases h : f x <;> cases j : g x <;> simp [s, Set.indicator, h, j, Value.Defined]
    rw [eq]
    exact (hm.comp (hf.val.prodMk hg.val)).indicator hs

theorem add (hf : BorelReal f) (hg : BorelReal g) : BorelReal (fun x => Value.add (f x) (g x)) := by
  convert binary hf hg (· + ·) measurable_add using 1
  funext x; cases f x <;> cases g x <;> rfl

theorem mul (hf : BorelReal f) (hg : BorelReal g) : BorelReal (fun x => Value.mul (f x) (g x)) := by
  convert binary hf hg (· * ·) measurable_mul using 1
  funext x; cases f x <;> cases g x <;> rfl

theorem map (k : ℝ → ℝ) (hk : Measurable k) (hf : BorelReal f) :
    BorelReal (fun x => (f x).map k) := by
  classical
  constructor
  · convert hf.domain using 1
    ext x; cases h : f x <;> simp [h, Value.Defined]
  · have eq : (fun x => ((f x).map k).getD 0) =
        {x | Value.Defined (f x)}.indicator (fun x => k ((f x).getD 0)) := by
      funext x; cases h : f x <;> simp [h, Value.Defined, Set.indicator]
    rw [eq]
    exact (hk.comp hf.val).indicator hf.domain

theorem pow (n : ℕ) (hf : BorelReal f) : BorelReal (fun x => (f x).map (· ^ n)) :=
  hf.map _ (by fun_prop)

theorem abs (hf : BorelReal f) : BorelReal (fun x => Value.abs (f x)) := hf.map _ continuous_abs.measurable

theorem mask {p : ℝ → Option Bool} (hp : BorelPred p) (hf : BorelReal f) :
    BorelReal (fun x => Value.mask (p x) (f x)) := by
  classical
  constructor
  · convert (hp false).union ((hp true).inter hf.domain) using 1
    ext x
    cases h : p x with
    | none => simp [h, Value.mask, Value.Defined]
    | some b => cases b <;> simp [h, Value.mask, Value.Defined]
  · have eq : (fun x => (Value.mask (p x) (f x)).getD 0) =
        {x | p x = some true}.indicator (fun x => (f x).getD 0) := by
      funext x
      cases h : p x with
      | none => simp [h, Value.mask, Set.indicator]
      | some b => cases b <;> simp [h, Value.mask, Set.indicator]
    rw [eq]
    exact hf.val.indicator (hp true)

theorem inv (hf : BorelReal f) : BorelReal (fun x => Value.inv (f x)) := by
  classical
  constructor
  · have eq : {x | Value.Defined (Value.inv (f x))} = {x | (f x).getD 0 ≠ 0} := by
      ext x; cases h : f x <;> simp [h, Value.Defined, Value.inv]
    rw [eq]
    exact (measurableSet_eq_fun hf.val measurable_const).compl
  · convert hf.val.inv using 1
    funext x
    cases h : f x with
    | none => simp [Value.inv, h]
    | some a => by_cases ha : a = 0 <;> simp [Value.inv, ha, h]
end BorelReal

namespace BorelPred
variable {p q : ℝ → Option Bool} {f g : ℝ → Option ℝ}
theorem const (v : Option Bool) : BorelPred (fun _ => v) := fun b => by simp

private theorem relation (r : ℝ → ℝ → Prop) [∀ a b, Decidable (r a b)]
    (hf : BorelReal f) (hg : BorelReal g) (hm : MeasurableSet {x | r ((f x).getD 0) ((g x).getD 0)}) :
    BorelPred (fun x => (f x).bind fun a => (g x).map fun b => decide (r a b)) := by
  intro b
  let s := {x | Value.Defined (f x)} ∩ {x | Value.Defined (g x)}
  let t := {x | r ((f x).getD 0) ((g x).getD 0)}
  have hs : MeasurableSet s := hf.domain.inter hg.domain
  convert hs.inter (show MeasurableSet (if b then t else tᶜ) by cases b <;> simp [t, hm, hm.compl]) using 1
  ext x
  cases h : f x <;> cases j : g x <;> cases b <;> simp [s, t, h, j, Value.Defined]

theorem lt (hf : BorelReal f) (hg : BorelReal g) : BorelPred (fun x => Value.lt (f x) (g x)) := by
  convert relation (· < ·) hf hg (measurableSet_lt hf.val hg.val) using 1
  funext x; cases f x <;> cases g x <;> rfl
theorem le (hf : BorelReal f) (hg : BorelReal g) : BorelPred (fun x => Value.le (f x) (g x)) := by
  convert relation (· ≤ ·) hf hg (measurableSet_le hf.val hg.val) using 1
  funext x; cases f x <;> cases g x <;> rfl
theorem nonzero (hf : BorelReal f) : BorelPred (fun x => Value.nonzero (f x)) := by
  have h := relation (· ≠ ·) hf (BorelReal.const (some 0)) (measurableSet_eq_fun hf.val measurable_const).compl
  convert h using 1
  funext x; cases f x <;> rfl

theorem not (hp : BorelPred p) : BorelPred (fun x => Value.not (p x)) := by
  intro b
  convert hp (!b) using 1
  ext x; cases h : p x <;> cases b <;> simp [Value.not, h]

theorem and (hp : BorelPred p) (hq : BorelPred q) : BorelPred (fun x => Value.and (p x) (q x)) := by
  intro b
  have hs := (hp true).inter (hq b)
  cases b
  · convert (hp false).union hs using 1
    ext x; cases h : p x <;> simp [Value.and, h]; cases ‹Bool› <;> simp [Value.and]
  · convert hs using 1
    ext x; cases h : p x <;> simp [Value.and, h]; cases ‹Bool› <;> simp [Value.and]

theorem or (hp : BorelPred p) (hq : BorelPred q) : BorelPred (fun x => Value.or (p x) (q x)) := by
  intro b
  have hs := (hp false).inter (hq b)
  cases b
  · convert hs using 1
    ext x; cases h : p x <;> simp [Value.or, h]; cases ‹Bool› <;> simp [Value.or]
  · convert (hp true).union hs using 1
    ext x; cases h : p x <;> simp [Value.or, h]; cases ‹Bool› <;> simp [Value.or]
end BorelPred
end QSym.Distribution
