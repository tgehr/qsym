import QSym.AlgebraCertificate

/-! Unreduced rational arithmetic for kernel certificates. No gcd or rational
normalization is performed by the checker: it checks integer cross-products.
Denominators are stored minus one, so even malformed inputs denote a fraction
with a positive denominator. -/
namespace QSym.AlgebraCertificate.Raw
abbrev Fraction := ℤ × ℕ
abbrev Coefficient := Fraction × Fraction
abbrev Polynomial := List (Monomial × Coefficient)

def denominator (x : Fraction) : ℕ := x.2+1
noncomputable def fractionValue (x : Fraction) : ℂ := x.1 / (denominator x : ℂ)
def fractionAdd (x y : Fraction) : Fraction :=
  (x.1 * denominator y + y.1 * denominator x, denominator x * denominator y - 1)
def fractionNeg (x : Fraction) : Fraction := (-x.1, x.2)
def fractionMul (x y : Fraction) : Fraction :=
  (x.1 * y.1, denominator x * denominator y - 1)
def fractionSame (x y : Fraction) : Bool := x.1 * denominator y == y.1 * denominator x

theorem denominator_ne (x : Fraction) : (denominator x : ℂ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero x.2)

theorem denominator_product (x y : Fraction) :
    denominator x * denominator y - 1 + 1 = denominator x * denominator y := by
  exact Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))

theorem fractionAdd_value (x y : Fraction) : fractionValue (fractionAdd x y) = fractionValue x + fractionValue y := by
  simp only [fractionValue, fractionAdd, denominator, Prod.fst, Prod.snd]
  rw [show (x.2+1)*(y.2+1)-1+1 = (x.2+1)*(y.2+1) from denominator_product x y]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  simpa only [denominator, mul_comm] using (div_add_div (x.1 : ℂ) (y.1 : ℂ) (denominator_ne x) (denominator_ne y)).symm

theorem fractionNeg_value (x : Fraction) : fractionValue (fractionNeg x) = -fractionValue x := by
  simp [fractionValue, fractionNeg, denominator, neg_div]

theorem fractionMul_value (x y : Fraction) : fractionValue (fractionMul x y) = fractionValue x * fractionValue y := by
  simp only [fractionValue, fractionMul, denominator, Prod.fst, Prod.snd]
  rw [show (x.2+1)*(y.2+1)-1+1 = (x.2+1)*(y.2+1) from denominator_product x y]
  simp only [Int.cast_mul, Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

theorem fractionSame_value {x y : Fraction} (h : fractionSame x y = true) : fractionValue x = fractionValue y := by
  have he : x.1 * (denominator y : ℤ) = y.1 * (denominator x : ℤ) := by simpa [fractionSame] using h
  apply (div_eq_div_iff (denominator_ne x) (denominator_ne y)).mpr
  exact_mod_cast he

noncomputable def coefficientValue (c : Coefficient) : ℂ := fractionValue c.1 + fractionValue c.2 * Complex.I
def addC (c d : Coefficient) : Coefficient := (fractionAdd c.1 d.1, fractionAdd c.2 d.2)
def mulC (c d : Coefficient) : Coefficient :=
  (fractionAdd (fractionMul c.1 d.1) (fractionNeg (fractionMul c.2 d.2)),
   fractionAdd (fractionMul c.1 d.2) (fractionMul c.2 d.1))
def zeroC (c : Coefficient) : Bool := c.1.1 == 0 && c.2.1 == 0
def sameC (c d : Coefficient) : Bool := fractionSame c.1 d.1 && fractionSame c.2 d.2

theorem addC_value (c d : Coefficient) : coefficientValue (addC c d) = coefficientValue c + coefficientValue d := by
  simp only [coefficientValue, addC, fractionAdd_value]; ring

theorem mulC_value (c d : Coefficient) : coefficientValue (mulC c d) = coefficientValue c * coefficientValue d := by
  simp only [coefficientValue, mulC, fractionAdd_value, fractionMul_value, fractionNeg_value]
  linear_combination -fractionValue c.2 * fractionValue d.2 * Complex.I_sq

theorem zeroC_value {c : Coefficient} (h : zeroC c = true) : coefficientValue c = 0 := by
  simp only [zeroC, Bool.and_eq_true, beq_iff_eq] at h
  simp [coefficientValue, fractionValue, h.1, h.2]

theorem sameC_value {c d : Coefficient} (h : sameC c d = true) : coefficientValue c = coefficientValue d := by
  simp only [sameC, Bool.and_eq_true] at h
  simp only [coefficientValue, fractionSame_value h.1, fractionSame_value h.2]

def insert (m : Monomial) (c : Coefficient) : Polynomial → Polynomial
  | [] => if zeroC c then [] else [(m,c)]
  | (n,d)::ps => if zeroC c then (n,d)::ps
      else if m = n then let e := addC c d; if zeroC e then ps else (m,e)::ps
      else if compareMonomial m n = .lt then (m,c)::(n,d)::ps else (n,d)::insert m c ps

def merge : ℕ → Polynomial → Polynomial → Polynomial
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | fuel+1, (m,c)::ps, (n,d)::qs =>
    if m = n then
      let e := addC c d
      if zeroC e then merge fuel ps qs else (m,e)::merge fuel ps qs
    else if compareMonomial m n = .lt then (m,c)::merge fuel ps ((n,d)::qs)
    else (n,d)::merge fuel ((m,c)::ps) qs

def add (p q : Polynomial) : Polynomial := merge (p.length+q.length) p q

def scale (c : Coefficient) : Polynomial → Polynomial
  | [] => []
  | (n,d)::ps => let e := mulC c d
    if zeroC e then scale c ps else (n,e)::scale c ps

def termAux (m : Monomial) (c : Coefficient) : Polynomial → Polynomial
  | [] => []
  | (n,d)::ps => insert (multiplyPowers m n) (mulC c d) (termAux m c ps)

def multiplyTerm (m : Monomial) (c : Coefficient) (p : Polynomial) : Polynomial :=
  if m = [] then scale c p else termAux m c p
def mul : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | (m,c)::ps, q => add (multiplyTerm m c q) (mul ps q)
noncomputable def value (σ : ℕ → ℂ) : Polynomial → ℂ
  | [] => 0
  | (m,c)::ps => coefficientValue c * monomialValue σ m + value σ ps

theorem insert_value (σ : ℕ → ℂ) (m : Monomial) (c : Coefficient) (p : Polynomial) :
    value σ (insert m c p) = coefficientValue c * monomialValue σ m + value σ p := by
  induction p with
  | nil =>
    simp only [insert]; split_ifs with h
    · simp [value, zeroC_value h]
    · rfl
  | cons t ps ih =>
    rcases t with ⟨n,d⟩
    simp only [insert]; split_ifs with hc hm he hlt
    · simp [value, zeroC_value hc]
    · subst n
      have hz := zeroC_value he
      rw [addC_value] at hz
      simp only [value]; linear_combination -monomialValue σ m * hz
    · subst n; simp only [value, addC_value]; ring
    · rfl
    · simp only [value, ih]; ring

theorem append_value (σ : ℕ → ℂ) (p q : Polynomial) : value σ (p ++ q) = value σ p + value σ q := by
  induction p with
  | nil => simp [value]
  | cons t ps ih => simp [value, ih, add_assoc]

theorem merge_value (σ : ℕ → ℂ) (fuel : ℕ) (p q : Polynomial) : value σ (merge fuel p q) = value σ p + value σ q := by
  induction fuel generalizing p q with
  | zero => exact append_value σ p q
  | succ fuel ih =>
    cases p with
    | nil => simp [merge, value]
    | cons t ps =>
      cases q with
      | nil => simp [merge, value]
      | cons u qs =>
        rcases t with ⟨m,c⟩; rcases u with ⟨n,d⟩
        simp only [merge]; split_ifs with hm he hlt
        · subst n
          have hz := zeroC_value he
          rw [addC_value] at hz
          simp only [ih, value]; linear_combination -monomialValue σ m * hz
        · subst n; simp only [value, ih, addC_value]; ring
        · simp only [value, ih]; ring
        · simp only [value, ih]; ring

theorem add_value (σ : ℕ → ℂ) (p q : Polynomial) : value σ (add p q) = value σ p + value σ q := merge_value σ _ p q

theorem scale_value (σ : ℕ → ℂ) (c : Coefficient) (p : Polynomial) : value σ (scale c p) = coefficientValue c * value σ p := by
  induction p with
  | nil => simp [scale, value]
  | cons t ps ih =>
    rcases t with ⟨m,d⟩
    simp only [scale]; split_ifs with he
    · have hz := zeroC_value he
      rw [mulC_value] at hz
      simp only [ih, value]; linear_combination -monomialValue σ m * hz
    · simp only [value, ih, mulC_value]; ring

theorem termAux_value (σ : ℕ → ℂ) (m : Monomial) (c : Coefficient) (p : Polynomial) :
    value σ (termAux m c p) = coefficientValue c * monomialValue σ m * value σ p := by
  induction p with
  | nil => simp [termAux, value]
  | cons t ps ih =>
    simp only [termAux, insert_value, mulC_value, multiplyPowers_value, ih, value]; ring

theorem multiplyTerm_value (σ : ℕ → ℂ) (m : Monomial) (c : Coefficient) (p : Polynomial) :
    value σ (multiplyTerm m c p) = coefficientValue c * monomialValue σ m * value σ p := by
  unfold multiplyTerm; split_ifs with h
  · subst m; simpa [monomialValue] using scale_value σ c p
  · exact termAux_value σ m c p

theorem mul_value (σ : ℕ → ℂ) (p q : Polynomial) : value σ (mul p q) = value σ p * value σ q := by
  induction p with
  | nil => simp [mul, value]
  | cons t ps ih => simp only [mul, add_value, multiplyTerm_value, ih, value]; ring

def fraction (q : ℚ) : Fraction := (q.num, q.den-1)
def coefficient (c : AlgebraCertificate.Coefficient) : Coefficient := (fraction c.1, fraction c.2)
def polynomial (p : AlgebraCertificate.Polynomial) : Polynomial := p.map (fun t => (t.1, coefficient t.2))

theorem fraction_value (q : ℚ) : fractionValue (fraction q) = (q : ℂ) := by
  simp only [fractionValue, fraction, denominator, Prod.fst, Prod.snd]
  rw [Nat.sub_add_cancel q.den_pos, Rat.cast_def]

theorem coefficient_value (c : AlgebraCertificate.Coefficient) : coefficientValue (coefficient c) = Numeric.complex c := by
  simp [coefficientValue, coefficient, fraction_value, Numeric.complex]

theorem polynomial_value (σ : ℕ → ℂ) (p : AlgebraCertificate.Polynomial) : value σ (polynomial p) = AlgebraCertificate.value σ p := by
  induction p with
  | nil => rfl
  | cons t ps ih => simp only [polynomial, List.map_cons, value, AlgebraCertificate.value, coefficient_value, ← ih]

def same : Polynomial → Polynomial → Bool
  | [], [] => true
  | (m,c)::ps, (n,d)::qs => m == n && sameC c d && same ps qs
  | _, _ => false

theorem same_value (σ : ℕ → ℂ) {p q : Polynomial} (h : same p q = true) : value σ p = value σ q := by
  induction p generalizing q with
  | nil => cases q <;> simp_all [same, value]
  | cons t ps ih =>
    cases q with
    | nil => simp [same] at h
    | cons u qs =>
      simp only [same, Bool.and_eq_true, beq_iff_eq] at h
      simp only [value, h.1.1, sameC_value h.1.2, ih h.2]

theorem add_check (p q r : AlgebraCertificate.Polynomial)
    (h : same (add (polynomial p) (polynomial q)) (polynomial r) = true) : ArithmeticEquality (AlgebraCertificate.add p q) r := by
  constructor; intro σ
  have he := same_value σ h
  simpa only [add_value, polynomial_value, AlgebraCertificate.add_value] using he

theorem mul_check (p q r : AlgebraCertificate.Polynomial)
    (h : same (mul (polynomial p) (polynomial q)) (polynomial r) = true) : ArithmeticEquality (AlgebraCertificate.mul p q) r := by
  constructor; intro σ
  have he := same_value σ h
  simpa only [mul_value, polynomial_value, AlgebraCertificate.mul_value] using he

theorem term_check (m : Monomial) (c : AlgebraCertificate.Coefficient) (p r : AlgebraCertificate.Polynomial)
    (h : same (multiplyTerm m (coefficient c) (polynomial p)) (polynomial r) = true) : ArithmeticEquality (AlgebraCertificate.multiplyTerm m c p) r := by
  constructor; intro σ
  have he := same_value σ h
  simpa only [multiplyTerm_value, polynomial_value, coefficient_value, AlgebraCertificate.multiplyTerm_value] using he
-- Native merge certificates avoid recomputing a polynomial normalization.
-- No sortedness invariant is trusted: every constructor preserves the value.
inductive Added : AlgebraCertificate.Polynomial → AlgebraCertificate.Polynomial → AlgebraCertificate.Polynomial → Prop
  | nilLeft (q) : Added [] q q
  | nilRight (p) : Added p [] p
  | left {m c p q r} : Added p q r → Added ((m,c)::p) q ((m,c)::r)
  | right {m c p q r} : Added p q r → Added p ((m,c)::q) ((m,c)::r)
  | both {m c d e p q r}
      (h : sameC (addC (coefficient c) (coefficient d)) (coefficient e) = true) :
      Added p q r → Added ((m,c)::p) ((m,d)::q) ((m,e)::r)
  | cancel {m c d p q r}
      (h : zeroC (addC (coefficient c) (coefficient d)) = true) :
      Added p q r → Added ((m,c)::p) ((m,d)::q) r

theorem Added.sound {p q r} (h : Added p q r) : ArithmeticEquality (AlgebraCertificate.add p q) r := by
  constructor; intro σ
  rw [AlgebraCertificate.add_value]
  induction h with
  | nilLeft => simp [AlgebraCertificate.value]
  | nilRight => simp [AlgebraCertificate.value]
  | left h ih => simp only [AlgebraCertificate.value]; linear_combination ih
  | right h ih => simp only [AlgebraCertificate.value]; linear_combination ih
  | @both m c d e p q r hc h ih =>
    have he := sameC_value hc
    simp only [addC_value, coefficient_value] at he
    simp only [AlgebraCertificate.value]
    linear_combination ih + monomialValue σ m * he
  | @cancel m c d p q r hc h ih =>
    have he := zeroC_value hc
    simp only [addC_value, coefficient_value] at he
    simp only [AlgebraCertificate.value]
    linear_combination ih + monomialValue σ m * he

-- The native merger's decisions are rechecked by a fused traversal. Fuel is
-- structural and exhausted fuel rejects; no sorting invariant is assumed.
def addedSame : ℕ → AlgebraCertificate.Polynomial → AlgebraCertificate.Polynomial →
    AlgebraCertificate.Polynomial → Bool
  | 0, _, _, _ => false
  | _+1, [], q, r => q == r
  | _+1, p, [], r => p == r
  | fuel+1, (m,c)::ps, (n,d)::qs, r =>
    if m = n then
      let e := addC (coefficient c) (coefficient d)
      if zeroC e then addedSame fuel ps qs r else
        match r with
        | [] => false
        | (k,f)::rs => m == k && sameC e (coefficient f) && addedSame fuel ps qs rs
    else if compareMonomial m n = .lt then
      match r with
      | [] => false
      | t::rs => (m,c) == t && addedSame fuel ps ((n,d)::qs) rs
    else
      match r with
      | [] => false
      | t::rs => (n,d) == t && addedSame fuel ((m,c)::ps) qs rs

theorem addedSame_sound {fuel p q r} (h : addedSame fuel p q r = true) : Added p q r := by
  induction fuel generalizing p q r with
  | zero => cases h
  | succ fuel ih =>
    cases p with
    | nil =>
      have he : q = r := by simpa only [addedSame, beq_iff_eq] using h
      subst r; exact Added.nilLeft q
    | cons t ps =>
      cases q with
      | nil =>
        have he : t::ps = r := by simpa only [addedSame, beq_iff_eq] using h
        subst r; exact Added.nilRight (t::ps)
      | cons u qs =>
        rcases t with ⟨m,c⟩; rcases u with ⟨n,d⟩
        simp only [addedSame] at h
        split_ifs at h with hm hz hlt
        · subst n; exact Added.cancel hz (ih h)
        · subst n
          cases r with
          | nil => cases h
          | cons v rs =>
            rcases v with ⟨k,f⟩
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨⟨rfl, hc⟩, hr⟩
            exact Added.both hc (ih hr)
        · cases r with
          | nil => cases h
          | cons v rs =>
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨rfl, hr⟩
            exact Added.left (ih hr)
        · cases r with
          | nil => cases h
          | cons v rs =>
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            rcases h with ⟨rfl, hr⟩
            exact Added.right (ih hr)

theorem addition_check (p q r : AlgebraCertificate.Polynomial)
    (h : addedSame (p.length+q.length+1) p q r = true) :
    ArithmeticEquality (AlgebraCertificate.add p q) r := (addedSame_sound h).sound

inductive Scaled (c : AlgebraCertificate.Coefficient) : AlgebraCertificate.Polynomial → AlgebraCertificate.Polynomial → Prop
  | nil : Scaled c [] []
  | cons {m d e p q}
      (h : sameC (mulC (coefficient c) (coefficient d)) (coefficient e) = true) :
      Scaled c p q → Scaled c ((m,d)::p) ((m,e)::q)
  | cancel {m d p q} (h : zeroC (mulC (coefficient c) (coefficient d)) = true) :
      Scaled c p q → Scaled c ((m,d)::p) q

theorem Scaled.sound {c p q} (h : Scaled c p q) : ArithmeticEquality (AlgebraCertificate.multiplyTerm [] c p) q := by
  constructor; intro σ
  simp only [AlgebraCertificate.multiplyTerm_value, monomialValue, mul_one]
  induction h with
  | nil => simp [AlgebraCertificate.value]
  | @cons m d e p q hc h ih =>
    have he := sameC_value hc
    simp only [mulC_value, coefficient_value] at he
    simp only [AlgebraCertificate.value]
    linear_combination ih + monomialValue σ m * he
  | @cancel m d p q hc h ih =>
    have he := zeroC_value hc
    simp only [mulC_value, coefficient_value] at he
    simp only [AlgebraCertificate.value]
    linear_combination ih + monomialValue σ m * he

inductive Mapped (m : Monomial) (c : AlgebraCertificate.Coefficient) :
    AlgebraCertificate.Polynomial → AlgebraCertificate.Polynomial → Prop
  | nil : Mapped m c [] []
  | cons {n d k e p q} (hm : multiplyPowers m n = k)
      (hc : sameC (mulC (coefficient c) (coefficient d)) (coefficient e) = true) :
      Mapped m c p q → Mapped m c ((n,d)::p) ((k,e)::q)
  | cancel {n d p q} (hc : zeroC (mulC (coefficient c) (coefficient d)) = true) :
      Mapped m c p q → Mapped m c ((n,d)::p) q

theorem Mapped.sound {m c p q} (h : Mapped m c p q) :
    ArithmeticEquality (AlgebraCertificate.multiplyTerm m c p) q := by
  constructor; intro σ
  rw [AlgebraCertificate.multiplyTerm_value]
  induction h with
  | nil => simp [AlgebraCertificate.value]
  | @cons n d k e p q hm hc h ih =>
    have he := sameC_value hc
    simp only [mulC_value, coefficient_value] at he
    simp only [AlgebraCertificate.value, ← hm, multiplyPowers_value, ← he]
    linear_combination ih
  | @cancel n d p q hc h ih =>
    have he := zeroC_value hc
    simp only [mulC_value, coefficient_value] at he
    simp only [AlgebraCertificate.value]
    linear_combination ih + monomialValue σ m * monomialValue σ n * he

-- Fuse checking with traversal: do not elaborate a constructor at every
-- coefficient or build an intermediate polynomial of unreduced fractions.
def mappedSame (m : Monomial) (c : AlgebraCertificate.Coefficient) :
    AlgebraCertificate.Polynomial → AlgebraCertificate.Polynomial → Bool
  | [], q => q.isEmpty
  | (n,d)::ps, q =>
    let e := mulC (coefficient c) (coefficient d)
    if zeroC e then mappedSame m c ps q else
      match q with
      | [] => false
      | (k,f)::qs => multiplyPowers m n == k && sameC e (coefficient f) && mappedSame m c ps qs

theorem mappedSame_sound {m c p q} (h : mappedSame m c p q = true) : Mapped m c p q := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => exact Mapped.nil
    | cons => simp [mappedSame] at h
  | cons t ps ih =>
    rcases t with ⟨n,d⟩
    simp only [mappedSame] at h
    split_ifs at h with hz
    · exact Mapped.cancel hz (ih h)
    · cases q with
      | nil => cases h
      | cons u qs =>
        rcases u with ⟨k,f⟩
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact Mapped.cons h.1.1 h.1.2 (ih h.2)

-- Structural recursion is intentional: the standard well-founded merge sort
-- does not reduce on closed inputs with an exported `rfl` witness.
def arrangeInsert (t : Monomial × AlgebraCertificate.Coefficient) :
    AlgebraCertificate.Polynomial → AlgebraCertificate.Polynomial
  | [] => [t]
  | u::ps => if compareMonomial t.1 u.1 = .lt then t::u::ps
      else u::arrangeInsert t ps

def arrange : AlgebraCertificate.Polynomial → AlgebraCertificate.Polynomial
  | [] => []
  | t::ps => arrangeInsert t (arrange ps)

theorem arrangeInsert_value (σ : ℕ → ℂ) (t : Monomial × AlgebraCertificate.Coefficient)
    (p : AlgebraCertificate.Polynomial) :
    AlgebraCertificate.value σ (arrangeInsert t p) =
      Numeric.complex t.2 * monomialValue σ t.1 + AlgebraCertificate.value σ p := by
  induction p with
  | nil => rfl
  | cons u ps ih =>
    simp only [arrangeInsert]; split_ifs
    · rfl
    · simp only [AlgebraCertificate.value, ih]; ring

theorem arrange_value (σ : ℕ → ℂ) (p : AlgebraCertificate.Polynomial) :
    AlgebraCertificate.value σ (arrange p) = AlgebraCertificate.value σ p := by
  induction p with
  | nil => rfl
  | cons t ps ih => simp only [arrange, arrangeInsert_value, ih, AlgebraCertificate.value]

theorem mapped_check (m c p q r) (h : Mapped m c p q) (hs : arrange q = r) :
    ArithmeticEquality (AlgebraCertificate.multiplyTerm m c p) r := by
  constructor; intro σ
  exact (h.sound.equation σ).trans ((arrange_value σ q).symm.trans (congrArg (AlgebraCertificate.value σ) hs))

-- A unit monomial only shifts exponents. Coefficient terms stay shared, so
-- kernel conversion checks the output row without any rational arithmetic.
def shift (m : Monomial) (p : AlgebraCertificate.Polynomial) : AlgebraCertificate.Polynomial :=
  p.map fun t => (multiplyPowers m t.1, t.2)

private theorem shift_value (σ : ℕ → ℂ) (m : Monomial) (p : AlgebraCertificate.Polynomial) :
    AlgebraCertificate.value σ (shift m p) = monomialValue σ m * AlgebraCertificate.value σ p := by
  induction p with
  | nil => simp [shift, AlgebraCertificate.value]
  | cons t ps ih =>
    change Numeric.complex t.2 * monomialValue σ (multiplyPowers m t.1) +
      AlgebraCertificate.value σ (shift m ps) = _
    rw [ih, multiplyPowers_value]; simp only [AlgebraCertificate.value]; ring

theorem shift_check (m : Monomial) (p q : AlgebraCertificate.Polynomial) (h : shift m p = q) :
    ArithmeticEquality (AlgebraCertificate.multiplyTerm m (1, 0) p) q := by
  subst q; constructor; intro σ
  simp [AlgebraCertificate.multiplyTerm_value, shift_value, Numeric.complex]

theorem unitTerm (p : AlgebraCertificate.Polynomial) :
    ArithmeticEquality (AlgebraCertificate.multiplyTerm [] (1, 0) p) p := by
  constructor; intro σ; simp [AlgebraCertificate.multiplyTerm_value, Numeric.complex, monomialValue]

theorem add_nil (p : AlgebraCertificate.Polynomial) : ArithmeticEquality (AlgebraCertificate.add p []) p := by
  constructor; intro σ; simp [AlgebraCertificate.add_value, AlgebraCertificate.value]

theorem mul_nil (p : AlgebraCertificate.Polynomial) : ArithmeticEquality (AlgebraCertificate.mul p []) [] := by
  constructor; intro σ; simp [AlgebraCertificate.mul_value, AlgebraCertificate.value]

theorem mul_single (source q r : AlgebraCertificate.Polynomial) {m c}
    (hs : source = [(m,c)]) (ht : ArithmeticEquality (AlgebraCertificate.multiplyTerm m c q) r) :
    ArithmeticEquality (AlgebraCertificate.mul source q) r := by
  subst source; constructor; intro σ
  rw [AlgebraCertificate.mul, AlgebraCertificate.add_value, ht.equation]
  simp [AlgebraCertificate.mul, AlgebraCertificate.value]

theorem mul_swap {p q r} (h : ArithmeticEquality (AlgebraCertificate.mul q p) r) : ArithmeticEquality (AlgebraCertificate.mul p q) r := by
  constructor; intro σ
  rw [AlgebraCertificate.mul_value, mul_comm, ← AlgebraCertificate.mul_value]
  exact h.equation σ

theorem mul_cons {m c p q a b r}
    (ht : ArithmeticEquality (AlgebraCertificate.multiplyTerm m c q) a)
    (hp : ArithmeticEquality (AlgebraCertificate.mul p q) b)
    (ha : ArithmeticEquality (AlgebraCertificate.add a b) r) :
    ArithmeticEquality (AlgebraCertificate.mul ((m,c)::p) q) r := by
  constructor; intro σ
  rw [AlgebraCertificate.mul, AlgebraCertificate.add_value, ht.equation, hp.equation, ← AlgebraCertificate.add_value]
  exact ha.equation σ

-- Keep the named input in the conclusion. Matching a constructed list against
-- a named input under `mul` can otherwise unfold the entire multiplication
-- during elaboration and kernel conversion.
theorem mul_cons_check (source : AlgebraCertificate.Polynomial) {m c p q a b r}
    (ht : ArithmeticEquality (AlgebraCertificate.multiplyTerm m c q) a)
    (hp : ArithmeticEquality (AlgebraCertificate.mul p q) b)
    (ha : ArithmeticEquality (AlgebraCertificate.add a b) r)
    (hs : source = (m,c)::p) :
    ArithmeticEquality (AlgebraCertificate.mul source q) r := by
  subst source
  exact mul_cons ht hp ha

end QSym.AlgebraCertificate.Raw
