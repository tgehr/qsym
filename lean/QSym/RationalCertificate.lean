import QSym.RawPolynomial

namespace QSym.AlgebraCertificate
noncomputable section

theorem equal_checked (σ : ℕ → ℂ) {p q : Polynomial}
    (h : ArithmeticEquality (add p (multiplyTerm [] (-1, 0) q)) []) : value σ p = value σ q := by
  have he := h.equation σ
  simp only [add_value, multiplyTerm_value, monomialValue, value] at he
  norm_num [Numeric.complex] at he
  linear_combination he

theorem reduce_checked (σ : ℕ → ℂ) {p e t r : Polynomial}
    (he : value σ e = 0) (h : ArithmeticEquality (add p (mul e t)) r) : value σ p = value σ r := by
  have hv := h.equation σ
  simpa only [add_value, mul_value, he, zero_mul, add_zero] using hv

theorem equal_reduced (σ : ℕ → ℂ) {p q d : Polynomial}
    (hd : value σ d = 0) (h : ArithmeticEquality (add p (multiplyTerm [] (-1, 0) q)) d) : value σ p = value σ q := by
  have he := (h.equation σ).trans hd
  simp only [add_value, multiplyTerm_value, monomialValue] at he
  norm_num [Numeric.complex] at he
  linear_combination he

theorem coefficient_ne_zero {c : Coefficient} (h : c ≠ (0, 0)) : Numeric.complex c ≠ 0 :=
  fun hz => h ((Numeric.complex_zero c).mp hz)

theorem nonzero_constant (σ : ℕ → ℂ) {c : Coefficient} (h : c ≠ (0, 0)) :
    value σ (constant c) ≠ 0 := (constant_value σ c) ▸ coefficient_ne_zero h

theorem nonzero_scale {x y : ℂ} {c : Coefficient} (he : x = Numeric.complex c * y)
    (hc : c ≠ (0, 0)) (hy : y ≠ 0) : x ≠ 0 := he ▸ mul_ne_zero (coefficient_ne_zero hc) hy

theorem nonzero_multiple (σ : ℕ → ℂ) {p q r : Polynomial} {c : Coefficient}
    (he : value σ p = value σ r) (hr : ArithmeticEquality (multiplyTerm [] c q) r)
    (hc : c ≠ (0, 0)) (hq : value σ q ≠ 0) : value σ p ≠ 0 := by
  apply nonzero_scale (c := c) (y := value σ q) _ hc hq
  exact he.trans ((hr.equation σ).symm.trans (by simp [multiplyTerm_value, monomialValue]))

theorem nonzero_mul (σ : ℕ → ℂ) {p q r : Polynomial}
    (hp : value σ p ≠ 0) (hq : value σ q ≠ 0) (h : ArithmeticEquality (mul p q) r) : value σ r ≠ 0 :=
  (checked_mul σ h) ▸ mul_ne_zero hp hq

theorem Powered.nonzero {σ p n q} (h : Powered σ p n q) (hp : value σ p ≠ 0) : value σ q ≠ 0 :=
  h.equation ▸ pow_ne_zero n hp

theorem inverse_nonzero (σ : ℕ → ℂ) {p q r s u v : Polynomial}
    (hq : value σ q ≠ 0) (hs : value σ s ≠ 0)
    (he : value σ u = value σ v) (hu : ArithmeticEquality (mul p r) u) (hv : ArithmeticEquality (mul q s) v) : value σ p ≠ 0 := by
  intro hp
  have h := (checked_mul σ hu).trans (he.trans (checked_mul σ hv).symm)
  rw [hp, zero_mul] at h
  exact mul_ne_zero hq hs h.symm

structure Fractional {α : Type} [Semiring α] (σ : ℕ → ℂ) (f : α →+* ℂ)
    (v : Option α) (p q : Polynomial) : Prop where
  equation : v.map f = some (value σ p / value σ q)
  denominator : value σ q ≠ 0

namespace Fractional
variable {α β : Type} [Semiring α] [Semiring β] {σ : ℕ → ℂ} {f : α →+* ℂ}
    {a b : Option α} {p q r s u v : Polynomial}

theorem defined (h : Fractional σ f a p q) : Value.Defined a := by
  cases a with
  | none => cases h.equation
  | some x => exact ⟨x, rfl⟩

theorem ofNormalized (h : Normalized σ f a p) : Fractional σ f a p [([], (1, 0))] := by
  constructor
  · simpa [value, monomialValue, Numeric.complex] using h.equation
  · simp [value, monomialValue, Numeric.complex]

theorem toNormalized (ha : Fractional σ f a p [([], (1, 0))]) : Normalized σ f a p := by
  constructor
  simpa [value, monomialValue, Numeric.complex] using ha.equation

theorem ratio (σ : ℕ → ℂ) (p q : Polynomial) (h : value σ q ≠ 0) :
    Fractional σ embedC (some (value σ p / value σ q)) p q := ⟨rfl, h⟩

theorem change (h : Fractional σ f a p q) (hs : value σ s ≠ 0)
    (he : value σ p * value σ s = value σ r * value σ q) : Fractional σ f a r s := by
  refine ⟨?_, hs⟩
  rw [h.equation]
  exact congrArg some ((div_eq_div_iff h.denominator hs).mpr he)

theorem change_checked (h : Fractional σ f a p q) (hs : value σ s ≠ 0)
    (he : value σ u = value σ v) (hu : ArithmeticEquality (mul p s) u) (hv : ArithmeticEquality (mul r q) v) : Fractional σ f a r s :=
  h.change hs ((checked_mul σ hu).trans (he.trans (checked_mul σ hv).symm))

theorem zero (hf : Function.Injective f) (h : Fractional σ f a [] q) : a = some 0 := by
  apply Normalized.zero (σ := σ) hf
  exact ⟨by simpa [value] using h.equation⟩

theorem add (ha : Fractional σ f a p q) (hb : Fractional σ f b r s)
    (hu : ArithmeticEquality (AlgebraCertificate.add (mul p s) (mul r q)) u) (hv : ArithmeticEquality (mul q s) v) :
    Fractional σ f (Value.add a b) u v := by
  obtain ⟨x, hx⟩ := ha.defined; obtain ⟨y, hy⟩ := hb.defined
  have he : value σ u = value σ p * value σ s + value σ r * value σ q := by
    simpa only [add_value, mul_value] using (hu.equation σ).symm
  have hd : value σ v = value σ q * value σ s := by simpa only [mul_value] using (hv.equation σ).symm
  constructor
  · have ex := Option.some.inj (show some (f x) = _ from hx ▸ ha.equation)
    have ey := Option.some.inj (show some (f y) = _ from hy ▸ hb.equation)
    simp only [hx, hy, Value.add, Option.map_some', map_add, ex, ey, he, hd]
    congr 1
    rw [div_add_div _ _ ha.denominator hb.denominator]
    congr 1; ring
  · rw [hd]; exact mul_ne_zero ha.denominator hb.denominator

-- Common-denominator certificates avoid expanding the product of two already
-- overlapping denominators merely to cancel it again.
theorem rescale (ha : Fractional σ f a p q) {l}
    (hn : ArithmeticEquality (AlgebraCertificate.mul p l) u)
    (hd : ArithmeticEquality (AlgebraCertificate.mul q l) v)
    (hv : value σ v ≠ 0) : Fractional σ f a u v := by
  apply ha.change hv
  rw [← checked_mul σ hn, ← checked_mul σ hd]
  ring

theorem add_same (ha : Fractional σ f a p q) (hb : Fractional σ f b r q)
    (hu : ArithmeticEquality (AlgebraCertificate.add p r) u) :
    Fractional σ f (Value.add a b) u q := by
  obtain ⟨x, hx⟩ := ha.defined; obtain ⟨y, hy⟩ := hb.defined
  refine ⟨?_, ha.denominator⟩
  have ex := Option.some.inj (show some (f x) = _ from hx ▸ ha.equation)
  have ey := Option.some.inj (show some (f y) = _ from hy ▸ hb.equation)
  simp only [hx, hy, Value.add, Option.map_some', map_add, ex, ey]
  exact congrArg some ((add_div _ _ _).symm.trans (congrArg (· / value σ q) (checked_add σ hu)))

theorem mul (ha : Fractional σ f a p q) (hb : Fractional σ f b r s)
    (hu : ArithmeticEquality (AlgebraCertificate.mul p r) u) (hv : ArithmeticEquality (AlgebraCertificate.mul q s) v) :
    Fractional σ f (Value.mul a b) u v := by
  obtain ⟨x, hx⟩ := ha.defined; obtain ⟨y, hy⟩ := hb.defined
  have he : value σ u = value σ p * value σ r := by simpa only [mul_value] using (hu.equation σ).symm
  have hd : value σ v = value σ q * value σ s := by simpa only [mul_value] using (hv.equation σ).symm
  constructor
  · have ex : f x = value σ p / value σ q := by simpa only [hx, Option.map_some', Option.some.injEq] using ha.equation
    have ey : f y = value σ r / value σ s := by simpa only [hy, Option.map_some', Option.some.injEq] using hb.equation
    simp only [hx, hy, Value.mul, Option.map_some', map_mul, ex, ey, he, hd]
    exact congrArg some (div_mul_div_comm _ _ _ _)
  · rw [hd]; exact mul_ne_zero ha.denominator hb.denominator

theorem powered (ha : Fractional σ f a p q) {n : ℕ}
    (hp : Powered σ p n r) (hq : Powered σ q n s) : Fractional σ f (a.map (· ^ n)) r s := by
  obtain ⟨x, hx⟩ := ha.defined
  have he : f x = value σ p / value σ q := by simpa only [hx, Option.map_some', Option.some.injEq] using ha.equation
  constructor
  · simp only [hx, Option.map_some', map_pow, he, div_pow, hp.equation, hq.equation]
  · rw [← hq.equation]; exact pow_ne_zero _ ha.denominator

theorem cast (g : β →+* ℂ) (op : Function1 α β)
    (ho : ∀ x, g (op.value x) = f x) (hd : ∀ x, op.domain x)
    (ha : Fractional σ f a p q) : Fractional σ g (op.apply a) p q := by
  obtain ⟨x, hx⟩ := ha.defined
  exact ⟨by simpa [hx, Function1.apply, hd, ho] using ha.equation, ha.denominator⟩

theorem mask_false (g : Option Bool) (a : Option α) (hg : g = some false) :
    Fractional σ f (Value.mask g a) [] [([], (1, 0))] := by
  rw [hg]; constructor <;> simp [Value.mask, value, monomialValue, Numeric.complex]

theorem mask_true {g : Option Bool} (hg : g = some true) (ha : Fractional σ f a p q) :
    Fractional σ f (Value.mask g a) p q := hg ▸ ha

end Fractional

theorem fraction_inverse {α : Type} [Field α] {σ : ℕ → ℂ} {f : α →+* ℂ}
    {a : Option α} {p q : Polynomial} (ha : Fractional σ f a p q) (hp : value σ p ≠ 0) :
    Fractional σ f (Value.inv a) q p := by
  obtain ⟨x, hx⟩ := ha.defined
  have he : f x = value σ p / value σ q := by simpa only [hx, Option.map_some', Option.some.injEq] using ha.equation
  have hn : x ≠ 0 := by intro hz; rw [hz, map_zero] at he; exact (div_ne_zero hp ha.denominator) he.symm
  exact ⟨by simp [hx, Value.inv, hn, map_inv₀, he, inv_div], hp⟩

theorem Fractional.inverseQ {σ a p q} (ha : Fractional σ embedQ a p q) (hp : value σ p ≠ 0) :
    Fractional σ embedQ (Functions.invQ.apply a) q p := by
  have h : Functions.invQ.apply a = Value.inv a := by
    cases a <;> simp [Function1.apply, Functions.invQ, Value.inv]
  rw [h]; exact fraction_inverse ha hp

theorem Fractional.totalAdd {α : Type} [Semiring α] {σ : ℕ → ℂ} {f : α →+* ℂ}
    (op : Function2 α α α) (ho : ∀ x y, op.value x y = x+y) (hd : ∀ x y, op.domain x y)
    {a b p q r s u v} (ha : Fractional σ f a p q) (hb : Fractional σ f b r s)
    (hu : ArithmeticEquality (AlgebraCertificate.add (AlgebraCertificate.mul p s) (AlgebraCertificate.mul r q)) u) (hv : ArithmeticEquality (AlgebraCertificate.mul q s) v) : Fractional σ f (op.apply a b) u v := by
  obtain ⟨x, hx⟩ := ha.defined; obtain ⟨y, hy⟩ := hb.defined
  have he : op.apply a b = Value.add a b := by simp [hx, hy, Function2.apply, hd, ho, Value.add]
  rw [he]; exact ha.add hb hu hv

theorem Fractional.totalAddSame {α : Type} [Semiring α] {σ : ℕ → ℂ} {f : α →+* ℂ}
    (op : Function2 α α α) (ho : ∀ x y, op.value x y = x+y) (hd : ∀ x y, op.domain x y)
    {a b p q r u} (ha : Fractional σ f a p q) (hb : Fractional σ f b r q)
    (hu : ArithmeticEquality (AlgebraCertificate.add p r) u) :
    Fractional σ f (op.apply a b) u q := by
  obtain ⟨x, hx⟩ := ha.defined; obtain ⟨y, hy⟩ := hb.defined
  have he : op.apply a b = Value.add a b := by simp [hx, hy, Function2.apply, hd, ho, Value.add]
  rw [he]; exact ha.add_same hb hu

theorem Fractional.totalMul {α : Type} [Semiring α] {σ : ℕ → ℂ} {f : α →+* ℂ}
    (op : Function2 α α α) (ho : ∀ x y, op.value x y = x*y) (hd : ∀ x y, op.domain x y)
    {a b p q r s u v} (ha : Fractional σ f a p q) (hb : Fractional σ f b r s)
    (hu : ArithmeticEquality (AlgebraCertificate.mul p r) u) (hv : ArithmeticEquality (AlgebraCertificate.mul q s) v) : Fractional σ f (op.apply a b) u v := by
  obtain ⟨x, hx⟩ := ha.defined; obtain ⟨y, hy⟩ := hb.defined
  have he : op.apply a b = Value.mul a b := by simp [hx, hy, Function2.apply, hd, ho, Value.mul]
  rw [he]; exact ha.mul hb hu hv

theorem Fractional.castNZ {σ a p q} (h : Fractional σ embedN a p q) : Fractional σ embedZ (Functions.castNZ.apply a) p q :=
  h.cast embedZ Functions.castNZ (fun x => Int.cast_natCast x) (fun _ => True.intro)
theorem Fractional.castZQ {σ a p q} (h : Fractional σ embedZ a p q) : Fractional σ embedQ (Functions.castZQ.apply a) p q :=
  h.cast embedQ Functions.castZQ (fun x => Rat.cast_intCast x) (fun _ => True.intro)
theorem Fractional.castQR {σ a p q} (h : Fractional σ embedQ a p q) : Fractional σ embedR (Functions.castQR.apply a) p q :=
  h.cast (f := embedQ) embedR Functions.castQR (fun x => Complex.ofReal_ratCast x) (fun _ => True.intro)
theorem Fractional.castRC {σ a p q} (h : Fractional σ embedR a p q) : Fractional σ embedC (Functions.castRC.apply a) p q :=
  h.cast embedC Functions.castRC (fun _ => rfl) (fun _ => True.intro)

theorem Fractional.replaceValue {σ x y p q} (ha : Fractional σ embedC (some x) p q) (he : y = x) :
    Fractional σ embedC (some y) p q := he ▸ ha

theorem Fractional.some_eq {σ x p q} (ha : Fractional σ embedC (some x) p q) :
    x = value σ p / value σ q := Option.some.inj ha.equation

theorem Fractional.totalPower {α : Type} [Semiring α] {σ : ℕ → ℂ} {f : α →+* ℂ}
    (op : Function2 α ℕ α) (ho : ∀ x n, op.value x n = x^n) (hd : ∀ x n, op.domain x n)
    {a p q b n r s} (ha : Fractional σ f a p q) (hb : b = some n)
    (hp : Fractional σ embedC (some ((value σ p / value σ q)^n)) r s) :
    Fractional σ f (op.apply a b) r s := by
  obtain ⟨x, hx⟩ := ha.defined
  have he : f x = value σ p / value σ q := by simpa only [hx, Option.map_some', Option.some.injEq] using ha.equation
  refine ⟨?_, hp.denominator⟩
  simpa [hx, hb, Function2.apply, hd, ho, map_pow, he] using hp.equation

theorem Fractional.powerScale {σ x k n p q r s}
    (hk : Fractional σ embedC (some (x^k)) p q)
    (hn : Fractional σ embedC (some ((value σ p / value σ q)^n)) r s) :
    Fractional σ embedC (some (x^(k*n))) r s :=
  hn.replaceValue ((pow_mul x k n).trans (congrArg (· ^ n) hk.some_eq))

theorem Normalized.valuation {α : Type} [Semiring α] {σ τ : ℕ → ℂ} {f : α →+* ℂ} {a p}
    (h : Normalized σ f a p) (he : value σ p = value τ p) : Normalized τ f a p :=
  ⟨h.equation.trans (congrArg some he)⟩

theorem Normalized.equal {α : Type} [Semiring α] {σ : ℕ → ℂ} {f : α →+* ℂ} {a b p}
    (hf : Function.Injective f) (ha : Normalized σ f a p) (hb : Normalized σ f b p) : a = b := by
  obtain ⟨x, hx⟩ := ha.defined; obtain ⟨y, hy⟩ := hb.defined
  have he : f x = f y := by simpa [hx, hy] using ha.equation.trans hb.equation.symm
  rw [hx, hy, hf he]

theorem powerOne (σ : ℕ → ℂ) (n : ℕ) :
    Fractional σ embedC
      (some ((value σ [([], (1, 0))] / value σ [([], (1, 0))])^n))
      [([], (1, 0))] [([], (1, 0))] := by
  constructor <;> simp [value, monomialValue, Numeric.complex, embedC]

theorem Normalized.nonzero_false {α : Type} [Semiring α] {σ : ℕ → ℂ} {f : α →+* ℂ} {a p}
    (hf : Function.Injective f) (h : Normalized σ f a p) (hz : value σ p = 0) :
    Value.nonzero a = some false := by
  obtain ⟨x, hx⟩ := h.defined
  have he : f x = 0 := by simpa [hx, hz] using h.equation
  have hzero : x = 0 := hf (he.trans (map_zero f).symm)
  simp [hx, hzero, Value.nonzero]

theorem Normalized.nonzero_true {α : Type} [Semiring α] {σ : ℕ → ℂ} {f : α →+* ℂ} {a p}
    (h : Normalized σ f a p) (hz : value σ p ≠ 0) : Value.nonzero a = some true := by
  obtain ⟨x, hx⟩ := h.defined
  have he : f x = value σ p := by simpa [hx] using h.equation
  have hn : x ≠ 0 := by intro hx0; apply hz; rw [hx0, map_zero] at he; exact he.symm
  simp [hx, hn, Value.nonzero]

theorem nonzeroN_eq (a : Option ℕ) : Functions.nonzeroN.apply a = Value.nonzero a := by
  cases a <;> simp [Function1.apply, Functions.nonzeroN, Value.nonzero]
theorem nonzeroZ_eq (a : Option ℤ) : Functions.nonzeroZ.apply a = Value.nonzero a := by
  cases a <;> simp [Function1.apply, Functions.nonzeroZ, Value.nonzero]
theorem nonzeroQ_eq (a : Option ℚ) : Functions.nonzeroQ.apply a = Value.nonzero a := by
  cases a <;> simp [Function1.apply, Functions.nonzeroQ, Value.nonzero]

theorem known_not {a : Option Bool} {b : Bool} (h : a = some b) : Value.not a = some (!b) := h ▸ rfl
theorem known_and_false {a : Option Bool} (b : Option Bool) (h : a = some false) : Value.and a b = some false := by rw [h]; rfl
theorem known_and_true {a b : Option Bool} {c : Bool} (ha : a = some true) (hb : b = some c) : Value.and a b = some c := ha ▸ hb
theorem known_or_true {a : Option Bool} (b : Option Bool) (h : a = some true) : Value.or a b = some true := by rw [h]; rfl
theorem known_or_false {a b : Option Bool} {c : Bool} (ha : a = some false) (hb : b = some c) : Value.or a b = some c := ha ▸ hb

theorem known_function2 {α β γ : Type} (op : Function2 α β γ) {a : Option α} {b : Option β}
    {x : α} {y : β} (ha : a = some x) (hb : b = some y) (hd : op.domain x y) :
    op.apply a b = some (op.value x y) := by simp [ha, hb, Function2.apply, hd]

end
end QSym.AlgebraCertificate
