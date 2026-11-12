import QSym.Tensor

namespace QSym.Dependent

abbrev Globals := (α : Type) → ℕ → α

def apply {β : ℕ → Type} (f : Option ((n : ℕ) → Option (β n))) (n : ℕ) : Option (β n) :=
  f.bind (fun g => g n)

def inputDomain {β : ℕ → Type} (f : Option ((n : ℕ) → Option (β n))) : Option (Set ℕ) :=
  some {n | (apply f n).isSome}

theorem beta {β : ℕ → Type} (f : (n : ℕ) → Option (β n)) (n : ℕ) : apply (some f) n = f n := rfl

theorem apply_none {β : ℕ → Type} (n : ℕ) : @apply β none n = none := rfl

theorem domain_iff {β : ℕ → Type} (f : Option ((n : ℕ) → Option (β n))) (n : ℕ) :
    n ∈ (inputDomain f).getD ∅ ↔ ∃ v, apply f n = some v := by
  simp [inputDomain, Option.isSome_iff_exists]

end QSym.Dependent
