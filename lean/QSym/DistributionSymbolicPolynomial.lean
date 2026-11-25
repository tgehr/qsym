import QSym.DistributionPolynomialGrid

/-! Polynomials in the variable whose coefficients do not mention it. A
coefficient is a partial value, or is absent and counts as zero; the
polynomial is defined where every coefficient that is present is. Sums and
products are computed on the coefficients, so that a rule can build the same
terms. -/
namespace QSym.Distribution.StepSource

/-- A coefficient of a polynomial in the variable is a partial value that
does not mention it, or is absent; then it counts as zero. -/
def coefValue : Option (Option ℝ) → Option ℝ
  | none => some 0
  | some c => c

/-- Sums and products of coefficients; an absent one is skipped in a sum and
absorbs a product. -/
def coefAdd : Option (Option ℝ) → Option (Option ℝ) → Option (Option ℝ)
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Value.add a b)

def coefMul : Option (Option ℝ) → Option (Option ℝ) → Option (Option ℝ)
  | some a, some b => some (Value.mul a b)
  | _, _ => none

theorem coefValue_add (a b : Option (Option ℝ)) :
    coefValue (coefAdd a b) = Value.add (coefValue a) (coefValue b) := by
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp [coefValue, coefAdd, Value.add]

/-- A polynomial in the variable by its coefficients, lowest degree first.
A coefficient is a partial value that does not mention the variable, or is
absent and counts as zero. -/
def symEval : List (Option (Option ℝ)) → ℝ → Option ℝ
  | [], _ => some 0
  | c :: cs, x => Value.add (coefValue c) (Value.mul (some x) (symEval cs x))

def symAdd : List (Option (Option ℝ)) → List (Option (Option ℝ)) → List (Option (Option ℝ))
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => coefAdd a b :: symAdd p q

def symScale (c : Option (Option ℝ)) : List (Option (Option ℝ)) → List (Option (Option ℝ))
  | [] => []
  | a :: p => coefMul c a :: symScale c p

/-- `u + x·w`. -/
def symShift : List (Option (Option ℝ)) → List (Option (Option ℝ)) → List (Option (Option ℝ))
  | [], w => none :: w
  | a :: u, w => a :: symAdd u w

/-- `(a + x·p)·q = a·q + x·(p·q)`. -/
def symMul : List (Option (Option ℝ)) → List (Option (Option ℝ)) → List (Option (Option ℝ))
  | [], _ => []
  | a :: p, q => symShift (symScale a q) (symMul p q)

/-- Some coefficient is present. -/
def symSupport : List (Option (Option ℝ)) → Bool
  | [] => false
  | c :: cs => c.isSome || symSupport cs

private theorem add_none_iff (a b : Option ℝ) : Value.add a b = none ↔ a = none ∨ b = none := by
  cases a <;> cases b <;> simp [Value.add]

private theorem mul_none_iff (a b : Option ℝ) : Value.mul a b = none ↔ a = none ∨ b = none := by
  cases a <;> cases b <;> simp [Value.mul]

private theorem coefValue_none_iff (c : Option (Option ℝ)) : coefValue c = none ↔ c = some none := by
  rcases c with _ | _ | c <;> simp [coefValue]

/-- A polynomial is undefined exactly where a coefficient that is present
is. -/
theorem symEval_none_iff (cs : List (Option (Option ℝ))) (x : ℝ) :
    symEval cs x = none ↔ some none ∈ cs := by
  induction cs with
  | nil => simp [symEval]
  | cons c cs ih =>
    simp only [symEval, add_none_iff, mul_none_iff, coefValue_none_iff, ih, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h.symm
      · cases h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr h)

private theorem coefAdd_none_iff (a b : Option (Option ℝ)) :
    coefAdd a b = some none ↔ a = some none ∨ b = some none := by
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp [coefAdd, Value.add]

private theorem coefMul_none_iff (a b : Option (Option ℝ)) :
    coefMul a b = some none ↔ (a = some none ∧ b.isSome) ∨ (a.isSome ∧ b = some none) := by
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp [coefMul, Value.mul]

theorem symAdd_undefined (p q : List (Option (Option ℝ))) :
    some none ∈ symAdd p q ↔ some none ∈ p ∨ some none ∈ q := by
  induction p generalizing q with
  | nil => simp [symAdd]
  | cons a p ih =>
    cases q with
    | nil => simp [symAdd]
    | cons b q =>
      simp only [symAdd, List.mem_cons, ih]
      have h := coefAdd_none_iff a b
      constructor
      · rintro (h1 | h1 | h1)
        · rcases h.1 h1.symm with h2 | h2
          · exact Or.inl (Or.inl h2.symm)
          · exact Or.inr (Or.inl h2.symm)
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Or.inr h1)
      · rintro ((h1 | h1) | (h1 | h1))
        · exact Or.inl (h.2 (Or.inl h1.symm)).symm
        · exact Or.inr (Or.inl h1)
        · exact Or.inl (h.2 (Or.inr h1.symm)).symm
        · exact Or.inr (Or.inr h1)

theorem symScale_undefined (c : Option (Option ℝ)) (q : List (Option (Option ℝ))) :
    some none ∈ symScale c q ↔
      (c = some none ∧ symSupport q = true) ∨ (c.isSome = true ∧ some none ∈ q) := by
  induction q with
  | nil => simp [symScale, symSupport]
  | cons a q ih =>
    simp only [symScale, List.mem_cons, ih, symSupport, Bool.or_eq_true]
    have h := coefMul_none_iff c a
    constructor
    · rintro (h1 | h1 | h1)
      · rcases h.1 h1.symm with h2 | h2
        · exact Or.inl ⟨h2.1, Or.inl h2.2⟩
        · exact Or.inr ⟨h2.1, Or.inl h2.2.symm⟩
      · exact Or.inl ⟨h1.1, Or.inr h1.2⟩
      · exact Or.inr ⟨h1.1, Or.inr h1.2⟩
    · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
      · exact Or.inl (h.2 (Or.inl ⟨h1, h2⟩)).symm
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inl (h.2 (Or.inr ⟨h1, h2.symm⟩)).symm
      · exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem symShift_undefined (u w : List (Option (Option ℝ))) :
    some none ∈ symShift u w ↔ some none ∈ u ∨ some none ∈ w := by
  cases u with
  | nil => simp [symShift]
  | cons a u => simp [symShift, symAdd_undefined, or_assoc]

theorem symAdd_support (p q : List (Option (Option ℝ))) :
    symSupport (symAdd p q) = (symSupport p || symSupport q) := by
  induction p generalizing q with
  | nil => simp [symAdd, symSupport]
  | cons a p ih =>
    cases q with
    | nil => simp [symAdd, symSupport]
    | cons b q =>
      simp only [symAdd, symSupport, ih]
      rcases a with _ | a <;> rcases b with _ | b <;> simp [coefAdd]

theorem symScale_support (c : Option (Option ℝ)) (q : List (Option (Option ℝ))) :
    symSupport (symScale c q) = (c.isSome && symSupport q) := by
  induction q with
  | nil => simp [symScale, symSupport]
  | cons a q ih =>
    simp only [symScale, symSupport, ih]
    rcases c with _ | c <;> rcases a with _ | a <;> simp [coefMul]

theorem symShift_support (u w : List (Option (Option ℝ))) :
    symSupport (symShift u w) = (symSupport u || symSupport w) := by
  cases u with
  | nil => simp [symShift, symSupport]
  | cons a u => simp [symShift, symSupport, symAdd_support, Bool.or_assoc]

theorem symMul_support (p q : List (Option (Option ℝ))) :
    symSupport (symMul p q) = (symSupport p && symSupport q) := by
  induction p with
  | nil => simp [symMul, symSupport]
  | cons a p ih =>
    simp only [symMul, symShift_support, symScale_support, ih, symSupport]
    cases a.isSome <;> cases symSupport p <;> cases symSupport q <;> rfl

theorem symMul_undefined (p q : List (Option (Option ℝ))) :
    some none ∈ symMul p q ↔
      (some none ∈ p ∧ symSupport q = true) ∨ (symSupport p = true ∧ some none ∈ q) := by
  induction p with
  | nil => simp [symMul, symSupport]
  | cons a p ih =>
    simp only [symMul, symShift_undefined, symScale_undefined, ih, List.mem_cons, symSupport,
      Bool.or_eq_true]
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩))
      · exact Or.inl ⟨Or.inl h1.symm, h2⟩
      · exact Or.inr ⟨Or.inl h1, h2⟩
      · exact Or.inl ⟨Or.inr h1, h2⟩
      · exact Or.inr ⟨Or.inr h1, h2⟩
    · rintro (⟨h1 | h1, h2⟩ | ⟨h1 | h1, h2⟩)
      · exact Or.inl (Or.inl ⟨h1.symm, h2⟩)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)

theorem symEval_add (p q : List (Option (Option ℝ))) (x : ℝ) :
    symEval (symAdd p q) x = Value.add (symEval p x) (symEval q x) := by
  induction p generalizing q with
  | nil => cases h : symEval q x <;> simp [symAdd, symEval, Value.add, h]
  | cons a p ih =>
    cases q with
    | nil => cases h : symEval (a :: p) x <;> simp [symAdd, symEval, Value.add, h]
    | cons b q =>
      simp only [symAdd, symEval, ih, coefValue_add]
      cases coefValue a <;> cases coefValue b <;> cases symEval p x <;> cases symEval q x <;>
        simp [Value.add, Value.mul]
      ring

theorem symEval_shift (u w : List (Option (Option ℝ))) (x : ℝ) :
    symEval (symShift u w) x = Value.add (symEval u x) (Value.mul (some x) (symEval w x)) := by
  cases u with
  | nil => cases h : symEval w x <;> simp [symShift, symEval, coefValue, Value.add, Value.mul, h]
  | cons a u =>
    simp only [symShift, symEval, symEval_add]
    cases coefValue a <;> cases symEval u x <;> cases symEval w x <;> simp [Value.add, Value.mul]
    ring

private theorem symEval_some {cs : List (Option (Option ℝ))} (h : some none ∉ cs) (x : ℝ) :
    ∃ r, symEval cs x = some r := by
  cases hv : symEval cs x with
  | none => exact absurd ((symEval_none_iff cs x).1 hv) h
  | some r => exact ⟨r, rfl⟩

private theorem symEval_scale {c : Option (Option ℝ)} {q : List (Option (Option ℝ))}
    (hc : c ≠ some none) (hq : some none ∉ q) (x : ℝ) :
    symEval (symScale c q) x = Value.mul (coefValue c) (symEval q x) := by
  induction q with
  | nil => rcases c with _ | _ | c <;> simp_all [symScale, symEval, coefValue, Value.mul]
  | cons a q ih =>
    have ha : a ≠ some none := fun h => hq (by simp [h])
    have hq' : some none ∉ q := fun h => hq (by simp [h])
    obtain ⟨r, hr⟩ := symEval_some hq' x
    simp only [symScale, symEval, ih hq', hr]
    rcases c with _ | _ | c <;> rcases a with _ | _ | a <;>
      (simp_all [coefMul, coefValue, Value.add, Value.mul]; first | done | ring)

private theorem symEval_mul_defined {p q : List (Option (Option ℝ))} (hp : some none ∉ p)
    (hq : some none ∉ q) (x : ℝ) :
    symEval (symMul p q) x = Value.mul (symEval p x) (symEval q x) := by
  induction p with
  | nil => obtain ⟨r, hr⟩ := symEval_some hq x; simp [symMul, symEval, Value.mul, hr]
  | cons a p ih =>
    have ha : a ≠ some none := fun h => hp (by simp [h])
    have hp' : some none ∉ p := fun h => hp (by simp [h])
    obtain ⟨r, hr⟩ := symEval_some hq x
    obtain ⟨t, ht⟩ := symEval_some hp' x
    simp only [symMul, symEval_shift, symEval_scale ha hq, ih hp', symEval, hr, ht]
    rcases a with _ | _ | a <;>
      (simp_all [coefValue, Value.add, Value.mul]; first | done | ring)

/-- The product of two polynomials that each have a coefficient: every
coefficient of either meets one of the other, so the product is undefined
with any of them. -/
theorem symEval_mul {p q : List (Option (Option ℝ))} (hp : symSupport p = true)
    (hq : symSupport q = true) (x : ℝ) :
    symEval (symMul p q) x = Value.mul (symEval p x) (symEval q x) := by
  by_cases hu : some none ∈ p ∨ some none ∈ q
  · have h1 : symEval (symMul p q) x = none := by
      rw [symEval_none_iff, symMul_undefined]
      rcases hu with h | h
      · exact Or.inl ⟨h, hq⟩
      · exact Or.inr ⟨hp, h⟩
    rw [h1]
    rcases hu with h | h
    · rw [(symEval_none_iff p x).2 h]; rfl
    · rw [(symEval_none_iff q x).2 h]; cases symEval p x <;> rfl
  · exact symEval_mul_defined (fun h => hu (Or.inl h)) (fun h => hu (Or.inr h)) x

/-- A function of the variable is a polynomial with such coefficients, of
which at least one is present. -/
structure Symbolic (f : ℝ → Option ℝ) (cs : List (Option (Option ℝ))) : Prop where
  equation : ∀ x, f x = symEval cs x
  support : symSupport cs = true

theorem Symbolic.constant (c : Option ℝ) : Symbolic (fun _ => c) [some c] :=
  ⟨fun x => by cases c <;> simp [symEval, coefValue, Value.add, Value.mul], rfl⟩

theorem Symbolic.variable {one : Option ℝ}
    (h : one = some (Numeric.denote (s := .real) (1 : ℚ))) :
    Symbolic (fun x => some x) [none, some one] :=
  ⟨fun x => by rw [h]; simp [symEval, coefValue, Value.add, Value.mul, Numeric.denote], rfl⟩

theorem Symbolic.add {f g : ℝ → Option ℝ} {p q : List (Option (Option ℝ))}
    (hf : Symbolic f p) (hg : Symbolic g q) :
    Symbolic (fun x => Value.add (f x) (g x)) (symAdd p q) :=
  ⟨fun x => by rw [symEval_add, ← hf.equation, ← hg.equation],
    by rw [symAdd_support, hf.support]; rfl⟩

theorem Symbolic.mul {f g : ℝ → Option ℝ} {p q : List (Option (Option ℝ))}
    (hf : Symbolic f p) (hg : Symbolic g q) :
    Symbolic (fun x => Value.mul (f x) (g x)) (symMul p q) :=
  ⟨fun x => by rw [symEval_mul hf.support hg.support, ← hf.equation, ← hg.equation],
    by rw [symMul_support, hf.support, hg.support]; rfl⟩

/-- The same polynomial with its coefficients written out. A certificate
writes them out after every sum and product, so that each list is one step
from lists that are already written out. -/
theorem Symbolic.cast {f : ℝ → Option ℝ} {cs : List (Option (Option ℝ))}
    (ds : List (Option (Option ℝ))) (h : Symbolic f cs) (e : cs = ds) : Symbolic f ds :=
  e ▸ h

/-- The coefficients of the powers of a polynomial, each written out and one
product from the one before: those of exponent `n + 1`. -/
inductive Powers (p : List (Option (Option ℝ))) : ℕ → List (Option (Option ℝ)) → Prop
  | one : Powers p 0 p
  | step {n : ℕ} {q : List (Option (Option ℝ))} (r : List (Option (Option ℝ)))
      (h : Powers p n q) (e : symMul p q = r) : Powers p (n + 1) r

/-- The power of exponent `n + 1` is a repeated product. -/
theorem Symbolic.pow {f : ℝ → Option ℝ} {p q : List (Option (Option ℝ))} {n : ℕ}
    (hf : Symbolic f p) (hq : Powers p n q) :
    Symbolic (fun x => Option.map (fun y : ℝ => y ^ (n + 1)) (f x)) q := by
  induction hq with
  | one =>
    refine ⟨fun x => ?_, hf.support⟩
    show _ = symEval p x
    rw [← hf.equation]
    cases f x <;> simp
  | step r _ e ih =>
    subst e
    have h := hf.mul ih
    refine ⟨fun x => ?_, h.support⟩
    rw [← h.equation]
    cases f x <;> simp [Value.mul, pow_succ, mul_comm]

/-- The real value of a coefficient that is present and defined. -/
def coefReal : Option (Option ℝ) → ℝ
  | some (some a) => a
  | _ => 0

def realEval : List (Option (Option ℝ)) → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => coefReal c + x * realEval cs x

theorem symEval_real {cs : List (Option (Option ℝ))} (h : some none ∉ cs) (x : ℝ) :
    symEval cs x = some (realEval cs x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ some none := fun hc => h (by simp [hc])
    have hcs : some none ∉ cs := fun hcs => h (by simp [hcs])
    simp only [symEval, realEval, ih hcs]
    rcases c with _ | _ | c <;> simp_all [coefValue, coefReal, Value.add, Value.mul]

end QSym.Distribution.StepSource
