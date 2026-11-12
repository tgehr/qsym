import QSym.Value
import Mathlib.Order.OmegaCompletePartialOrder

namespace QSym.FixedPoint
open OmegaCompletePartialOrder

variable {α : Type*} [OmegaCompletePartialOrder α] [OrderBot α]

def approx (f : α →𝒄 α) (n : ℕ) : α := f^[n] ⊥

noncomputable def least (f : α →𝒄 α) : α :=
  ωSup (fixedPoints.iterateChain f ⊥ bot_le)

theorem unfold (f : α →𝒄 α) : f (least f) = least f :=
  fixedPoints.ωSup_iterate_mem_fixedPoint f ⊥ bot_le

theorem least_le (f : α →𝒄 α) {x : α} (hx : f x ≤ x) : least f ≤ x :=
  fixedPoints.ωSup_iterate_le_prefixedPoint f ⊥ bot_le hx bot_le

theorem approx_le (f : α →𝒄 α) (n : ℕ) : approx f n ≤ least f := by
  unfold approx least
  exact le_ωSup (fixedPoints.iterateChain f.toOrderHom ⊥ bot_le) n

theorem least_eq_of_le (f : α →𝒄 α) {x : α} (hx : f x ≤ x) (hl : x ≤ least f) :
    least f = x := le_antisymm (least_le f hx) hl

theorem least_id : least (ContinuousHom.id : α →𝒄 α) = ⊥ :=
  le_antisymm (least_le _ le_rfl) bot_le

theorem least_const (x : α) : least (ContinuousHom.const x : α →𝒄 α) = x :=
  (unfold (ContinuousHom.const x)).symm

variable {ι β : Type}

theorem mem_least_iff (f : (ι → Part β) →𝒄 (ι → Part β)) (x : ι) (y : β) :
    y ∈ least f x ↔ ∃ n, y ∈ approx f n x := by
  change y ∈ (ωSup ((fixedPoints.iterateChain f.toOrderHom ⊥ bot_le).map (Pi.evalOrderHom x)) : Part β) ↔ _
  rw [Part.mem_ωSup]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Part.eq_some_iff.mp hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (Part.eq_some_iff.mpr hn).symm⟩

theorem domain_least_iff (f : (ι → Part β) →𝒄 (ι → Part β)) (x : ι) :
    (least f x).Dom ↔ ∃ n, (approx f n x).Dom := by
  simp only [Part.dom_iff_mem, mem_least_iff]
  exact exists_comm

noncomputable def value (f : (ι → Part β) →𝒄 (ι → Part β)) (x : ι) : Option β := by
  classical
  exact (least f x).toOption

theorem value_eq_some_iff (f : (ι → Part β) →𝒄 (ι → Part β)) (x : ι) (y : β) :
    value f x = some y ↔ ∃ n, y ∈ approx f n x := by
  classical
  exact Part.toOption_eq_some_iff.trans (mem_least_iff f x y)

theorem defined_value (f : (ι → Part β) →𝒄 (ι → Part β)) (x : ι) :
    Value.Defined (value f x) ↔ (least f x).Dom := by
  classical
  simp only [Value.Defined, value, Part.toOption_eq_some_iff, Part.dom_iff_mem]

theorem defined_value_iff (f : (ι → Part β) →𝒄 (ι → Part β)) (x : ι) :
    Value.Defined (value f x) ↔ ∃ n, (approx f n x).Dom :=
  (defined_value f x).trans (domain_least_iff f x)

end QSym.FixedPoint
