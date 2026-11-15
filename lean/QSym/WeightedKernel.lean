import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod

/-! Pointwise weighted kernels, before imposing any measurable-space or
integrability conditions. The parameter type is explicit: composition currently
supports fixed fibres, not arbitrary families `A → Σ Ω, Kernel Ω ...`.
No quotient by almost-everywhere equality is used. -/
namespace QSym.WeightedParameter

universe u v w t r s

structure Kernel (Ω : Type u) (A : Type v) (B : Type w) where
  weight : A → Ω → ℝ
  value : A → Ω → B

namespace Kernel

@[ext] theorem ext {Ω : Type u} {A : Type v} {B : Type w}
    {p q : Kernel Ω A B} (hw : ∀ a ω, p.weight a ω = q.weight a ω)
    (hv : ∀ a ω, p.value a ω = q.value a ω) : p = q := by
  cases p; cases q
  simp_all [mk.injEq, funext_iff]

def pure {A : Type v} {B : Type w} (f : A → B) : Kernel PUnit A B :=
  ⟨fun _ _ => 1, fun a _ => f a⟩

def comp {Ω : Type u} {Ψ : Type v} {A : Type w} {B : Type t} {C : Type r}
    (p : Kernel Ω A B) (q : Kernel Ψ B C) : Kernel (Ω × Ψ) A C :=
  ⟨fun a ω => p.weight a ω.1 * q.weight (p.value a ω.1) ω.2,
   fun a ω => q.value (p.value a ω.1) ω.2⟩

def pull {Ω : Type u} {Ψ : Type v} {A : Type w} {B : Type t}
    (e : Ψ ≃ Ω) (p : Kernel Ω A B) : Kernel Ψ A B :=
  ⟨fun a ω => p.weight a (e ω), fun a ω => p.value a (e ω)⟩

def reweight {Ω : Type u} {A : Type v} {B : Type w}
    (g : A → B → ℝ) (p : Kernel Ω A B) : Kernel Ω A B :=
  ⟨fun a ω => p.weight a ω * g a (p.value a ω), p.value⟩

theorem comp_pure {Ω : Type u} {A : Type v} {B : Type w} (p : Kernel Ω A B) :
    comp p (pure id) = pull (Equiv.prodPUnit Ω) p := by
  ext a ω <;> simp [comp, pure, pull]

theorem pure_comp {Ω : Type u} {A : Type v} {B : Type w} (p : Kernel Ω A B) :
    comp (pure id) p = pull (Equiv.punitProd Ω) p := by
  ext a ω <;> simp [comp, pure, pull]

theorem comp_assoc {Ω : Type u} {Ψ : Type v} {Ξ : Type w}
    {A : Type t} {B : Type r} {C : Type s} {D : Type*}
    (p : Kernel Ω A B) (q : Kernel Ψ B C) (r : Kernel Ξ C D) :
    comp (comp p q) r = pull (Equiv.prodAssoc Ω Ψ Ξ) (comp p (comp q r)) := by
  ext a ω <;> simp [comp, pull, mul_assoc]

theorem pull_comp {Ω : Type u} {Ψ : Type v} {Ξ : Type w} {Ζ : Type t}
    {A B C : Type*} (e : Ξ ≃ Ω) (f : Ζ ≃ Ψ)
    (p : Kernel Ω A B) (q : Kernel Ψ B C) :
    pull (Equiv.prodCongr e f) (comp p q) = comp (pull e p) (pull f q) := rfl

theorem pull_trans {Ω : Type u} {Ψ : Type v} {Ξ : Type w} {A B : Type*}
    (e : Ψ ≃ Ω) (f : Ξ ≃ Ψ) (p : Kernel Ω A B) :
    pull f (pull e p) = pull (f.trans e) p := rfl

theorem reweight_one {Ω : Type u} {A : Type v} {B : Type w} (p : Kernel Ω A B) :
    reweight (fun _ _ => 1) p = p := by
  ext a ω <;> simp [reweight]

theorem reweight_mul {Ω : Type u} {A : Type v} {B : Type w}
    (g h : A → B → ℝ) (p : Kernel Ω A B) :
    reweight g (reweight h p) = reweight (fun a b => h a b * g a b) p := by
  ext a ω <;> simp [reweight, mul_assoc]

theorem reweight_pull {Ω : Type u} {Ψ : Type v} {A B : Type*}
    (e : Ψ ≃ Ω) (g : A → B → ℝ) (p : Kernel Ω A B) :
    reweight g (pull e p) = pull e (reweight g p) := rfl

end Kernel

/-- A representation-independent law package for the fixed-fibre fragment.
All laws are proof fields. The parameter isomorphisms remain explicit, so this
does not assert an ordinary ungraded monad or any Fubini/disintegration law.
The implementation above is universe polymorphic; this interface specializes
to small carriers, including the frontend's type-code carrier. -/
structure KernelTheory where
  K : Type → Type → Type → Type
  pure : {A B : Type} → (A → B) → K PUnit A B
  comp : {Ω Ψ A B C : Type} → K Ω A B → K Ψ B C → K (Ω × Ψ) A C
  pull : {Ω Ψ A B : Type} → (Ψ ≃ Ω) → K Ω A B → K Ψ A B
  reweight : {Ω A B : Type} → (A → B → ℝ) → K Ω A B → K Ω A B
  comp_pure : ∀ {Ω A B} (p : K Ω A B),
    comp p (pure id) = pull (Equiv.prodPUnit Ω) p
  pure_comp : ∀ {Ω A B} (p : K Ω A B),
    comp (pure id) p = pull (Equiv.punitProd Ω) p
  comp_assoc : ∀ {Ω Ψ Ξ A B C D} (p : K Ω A B) (q : K Ψ B C) (r : K Ξ C D),
    comp (comp p q) r = pull (Equiv.prodAssoc Ω Ψ Ξ) (comp p (comp q r))
  pull_comp : ∀ {Ω Ψ Ξ Ζ A B C} (e : Ξ ≃ Ω) (f : Ζ ≃ Ψ)
    (p : K Ω A B) (q : K Ψ B C),
    pull (Equiv.prodCongr e f) (comp p q) = comp (pull e p) (pull f q)
  reweight_one : ∀ {Ω A B} (p : K Ω A B), reweight (fun _ _ => 1) p = p
  reweight_mul : ∀ {Ω A B} (g h : A → B → ℝ) (p : K Ω A B),
    reweight g (reweight h p) = reweight (fun a b => h a b * g a b) p

/-- A closed implementation of every field of `KernelTheory`. -/
def kernelTheory : KernelTheory where
  K := Kernel
  pure := Kernel.pure
  comp := Kernel.comp
  pull := Kernel.pull
  reweight := Kernel.reweight
  comp_pure := Kernel.comp_pure
  pure_comp := Kernel.pure_comp
  comp_assoc := Kernel.comp_assoc
  pull_comp := Kernel.pull_comp
  reweight_one := Kernel.reweight_one
  reweight_mul := Kernel.reweight_mul

end QSym.WeightedParameter
