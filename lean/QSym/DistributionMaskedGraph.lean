import QSym.DistributionAffine

noncomputable section
namespace QSym.Distribution.GraphFibre
open Classical MeasureTheory

def maskedAtom (p : ℝ → Option Bool) (f : ℝ → ℝ) (x : ℝ) : Option (ℝ × ℝ) := do
  let active ← p x
  if active then
    if HasStrictDerivAt f (deriv f x) x ∧ deriv f x ≠ 0
    then some (x, |deriv f x|⁻¹) else none
  else some (x, 0)

/-- The complete finite preimage is retained so a strict test still visits
zero-weight points. Only active points require an inverse Jacobian. -/
def maskedAtoms (p : ℝ → Option Bool) (f : ℝ → ℝ) (y : ℝ) : Option (List (ℝ × ℝ)) :=
  if h : ∃ xs : List ℝ, xs.Sorted (· < ·) ∧ ∀ x, x ∈ xs ↔ f x = y then
    h.choose.mapM (maskedAtom p f)
  else none

theorem maskedAtoms_of_roots (p : ℝ → Option Bool) {f : ℝ → ℝ} {y : ℝ} {xs : List ℝ}
    (sorted : xs.Sorted (· < ·)) (complete : ∀ x, x ∈ xs ↔ f x = y) :
    maskedAtoms p f y = xs.mapM (maskedAtom p f) := by
  have ex : ∃ zs : List ℝ, zs.Sorted (· < ·) ∧ ∀ x, x ∈ zs ↔ f x = y := ⟨xs, sorted, complete⟩
  rw [maskedAtoms, dif_pos ex, ex.choose_spec.1.eq_of_mem_iff sorted
    (fun x => (ex.choose_spec.2 x).trans (complete x).symm)]

def maskedKernel (p : Option (ℝ → Option Bool)) (f : Option (ℝ → Option ℝ)) :
    Option (ℝ → Option (D ℝ)) := do
  let pred ← p
  let map ← f
  return fun y => if (∀ x, Value.Defined (map x)) ∧ Measurable (fun x => (map x).getD 0) then
    (maskedAtoms pred (fun x => (map x).getD 0) y).map presentation else none

theorem maskedKernel_total (p : ℝ → Option Bool) (f : ℝ → ℝ) (hf : Measurable f) :
    maskedKernel (some p) (some fun x => some (f x)) =
      some (fun y => (maskedAtoms p f y).map presentation) := by
  simp [maskedKernel, Value.Defined, hf]

theorem masked_affine_atoms (p : ℝ → Option Bool) (a b : ℝ) (ha : a ≠ 0) (y : ℝ) :
    maskedAtoms p (fun x => a*x+b) y =
      (p ((y-b)/a)).map (fun active => [((y-b)/a, if active then |a|⁻¹ else 0)]) := by
  let z := (y-b)/a
  have complete : ∀ x, x ∈ [z] ↔ a*x+b = y := by
    intro x
    simp only [List.mem_singleton, z, eq_div_iff ha]
    constructor <;> intro h <;> linarith [mul_comm x a]
  have hd := affine_derivative a b z
  rw [maskedAtoms_of_roots p (by simp [List.Sorted]) complete]
  change [z].mapM _ = (p z).map _
  cases hp : p z with
  | none => simp [maskedAtom, List.mapM_cons, hp]
  | some active => cases active <;> simp [maskedAtom, List.mapM_cons, hp, hd.hasDerivAt.deriv, hd, ha] <;> rfl

/-- Reconstruct the strict joint integral even when the predicate or test is
partial. An excluded inverse point retains its test obligation with weight zero. -/
theorem masked_affine_disintegrates (p : ℝ → Option Bool) (a b : ℝ) (ha : a ≠ 0)
    (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mul (Value.mask (p x) (some 1)) (h x (a*x+b))) =
      partialIntegral volume (fun y => (maskedKernel (some p) (some fun x => some (a*x+b))).bind
        (fun k => (k y).bind (fun d => integrate d (fun x => h x y)))) := by
  rw [maskedKernel_total p _ (by fun_prop)]
  apply affine_integral a b ha
  intro x
  simp only [Option.some_bind]
  rw [masked_affine_atoms _ a b ha, show (a*x+b-b)/a = x by field_simp [ha]]
  cases hp : p x with
  | none => simp [Value.mask, Value.mul]
  | some active => cases active <;> cases ht : h x (a*x+b) <;>
      simp [hp, ht, presentation, integrate, Value.mask, Value.mul]

end QSym.Distribution.GraphFibre
