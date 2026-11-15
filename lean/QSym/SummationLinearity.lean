import QSym.SummationAlgebra

noncomputable section
namespace QSym.SummationLinearity
open Summation
variable {ι α : Type} [NormedAddCommGroup α]

private theorem norm_add (f g : ι → α) (hf : Summable (fun i => ‖f i‖))
    (hg : Summable (fun i => ‖g i‖)) : Summable (fun i => ‖f i+g i‖) :=
  (hf.add hg).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _)

theorem add_known (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b)))
    (f g : ι → Option α) (hknown : (value norm (some f)).isSome) :
    value norm (some (fun i => op (f i) (g i))) = op (value norm (some f)) (value norm (some g)) := by
  classical
  have hop' : op = Value.add := by funext a b; rw [hop,Summation.add]
  subst op
  have hf : (∀ i, (f i).isSome) ∧ Summable (fun i => ‖(f i).getD 0‖) ∧ Summable (fun i => (f i).getD 0) := by
    by_contra h; simp [value,h] at hknown
  by_cases hg : ∀ i, (g i).isSome
  · have he (i : ι) : (Value.add (f i) (g i)).getD 0 = (f i).getD 0 + (g i).getD 0 := by
      have hfi0 := hf.1 i; have hgi0 := hg i
      cases hfi : f i <;> cases hgi : g i <;> simp_all [Value.add]
    have ht : ∀ i, (Value.add (f i) (g i)).isSome := by
      intro i; have hfi0 := hf.1 i; have hgi0 := hg i
      cases hfi : f i <;> cases hgi : g i <;> simp_all [Value.add]
    have hs : Summable (fun i => (f i).getD 0 + (g i).getD 0) ↔ Summable (fun i => (g i).getD 0) := by
      constructor
      · intro h; simpa using h.sub hf.2.2
      · exact hf.2.2.add
    have hn : Summable (fun i => ‖(f i).getD 0 + (g i).getD 0‖) ↔ Summable (fun i => ‖(g i).getD 0‖) := by
      constructor
      · intro h
        have hneg : Summable (fun i => ‖-((f i).getD 0)‖) := by simpa using hf.2.1
        simpa using norm_add (fun i => -((f i).getD 0)) (fun i => (f i).getD 0 + (g i).getD 0) hneg h
      · exact norm_add _ _ hf.2.1
    simp only [value,Option.bind,if_pos hf]
    simp only [ht,hg,true_and,he,hn,hs]
    split_ifs with h
    · simp only [Value.add,Option.bind,Option.map_some,Option.some.injEq]
      exact hf.2.2.tsum_add h.2.2
    · rfl
  · have ht : ¬ ∀ i, (Value.add (f i) (g i)).isSome := by
      intro h; apply hg; intro i
      have hi := h i
      cases hfi : f i <;> cases hgi : g i <;> simp_all [Value.add]
    simp only [value,Option.bind,if_neg (not_and_of_not_left _ ht),if_neg (not_and_of_not_left _ hg),if_pos hf]
    rfl

theorem add_known_right (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b)))
    (f g : ι → Option α) (hknown : (value norm (some g)).isSome) :
    value norm (some (fun i => op (f i) (g i))) = op (value norm (some f)) (value norm (some g)) := by
  have hc (a b : Option α) : op a b = op b a := by cases a <;> cases b <;> simp [hop,_root_.add_comm]
  simp_rw [hc (f _) (g _)]
  rw [add_known op hop g f hknown, hc]

theorem distribute {R : Type} [Semiring R]
    (add mul : Option R → Option R → Option R) (ha : add = Value.add) (hm : mul = Value.mul)
    (a b c : Option R) (reverse : Bool) :
    (if reverse then mul c (add a b) else mul (add a b) c) =
    add (if reverse then mul c a else mul a c) (if reverse then mul c b else mul b c) := by
  rw [ha,hm]
  cases a <;> cases b <;> cases c <;> cases reverse <;> simp [Value.add,Value.mul,mul_add,add_mul]

theorem undefined_bound {R : Type} [AddCommMonoid R]
    (f : Option (ℕ → Option R)) (n : Option ℕ) (h : Domain.Correct n (some false)) :
    rangeValue f n = none := by
  cases n with
  | none => cases f <;> rfl
  | some n => simp [Domain.Correct] at h

end QSym.SummationLinearity
