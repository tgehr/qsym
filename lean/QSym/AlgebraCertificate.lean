import QSym.Numeric

/-! Kernel-checked sparse arithmetic. The native exporter supplies the result
of each operation; the kernel only checks its finite arithmetic witness.
There is no tactic execution or trusted native evaluation in a certificate. -/
namespace QSym.AlgebraCertificate

abbrev Coefficient := ℚ × ℚ
abbrev Monomial := List (ℕ × ℕ)
abbrev Polynomial := List (Monomial × Coefficient)

-- Pair order is explicit: the generic product order is not lexicographic.
def compareMonomial (m n : Monomial) : Ordering :=
  List.compareLex (fun x y => (compare x.1 y.1).then (compare x.2 y.2)) m n

def insertPower (x : ℕ × ℕ) : Monomial → Monomial
  | [] => [x]
  | y :: ys => if x.1 = y.1 then (x.1, x.2+y.2) :: ys
      else if x.1 < y.1 then x :: y :: ys else y :: insertPower x ys

def multiplyPowers : Monomial → Monomial → Monomial
  | [], n => n
  | x :: xs, n => insertPower x (multiplyPowers xs n)

def insert (m : Monomial) (c : Coefficient) : Polynomial → Polynomial
  | [] => if c = (0, 0) then [] else [(m, c)]
  | (n, d) :: ps =>
    if c = (0, 0) then (n, d) :: ps
    else if m = n then
      let e := Numeric.addC c d
      if e = (0, 0) then ps else (m, e) :: ps
    else if compareMonomial m n = .lt then (m, c) :: (n, d) :: ps
    else (n, d) :: insert m c ps

def add : Polynomial → Polynomial → Polynomial
  | [], q => q
  | (m, c) :: ps, q => insert m c (add ps q)

def multiplyTerm (m : Monomial) (c : Coefficient) : Polynomial → Polynomial
  | [] => []
  | (n, d) :: ps => insert (multiplyPowers m n) (Numeric.mulC c d) (multiplyTerm m c ps)

def mul : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | (m, c) :: ps, q => add (multiplyTerm m c q) (mul ps q)

def power : ℕ → Polynomial → ℕ → Polynomial
  | 0, _, _ => [([], (1, 0))]
  | fuel+1, p, n =>
    if n = 0 then [([], (1, 0))] else
    let q := power fuel (mul p p) (n/2)
    if n%2 = 0 then q else mul q p

noncomputable def monomialValue (σ : ℕ → ℂ) : Monomial → ℂ
  | [] => 1
  | (x, k) :: xs => σ x ^ k * monomialValue σ xs

noncomputable def value (σ : ℕ → ℂ) : Polynomial → ℂ
  | [] => 0
  | (m, c) :: ps => Numeric.complex c * monomialValue σ m + value σ ps

theorem insertPower_value (σ : ℕ → ℂ) (x : ℕ × ℕ) (m : Monomial) :
    monomialValue σ (insertPower x m) = σ x.1 ^ x.2 * monomialValue σ m := by
  induction m with
  | nil => rfl
  | cons y ys ih =>
    simp only [insertPower]
    split_ifs with h h
    · simp [monomialValue, h, pow_add, mul_assoc]
    · rfl
    · simp only [monomialValue, ih]; ring

theorem multiplyPowers_value (σ : ℕ → ℂ) (m n : Monomial) :
    monomialValue σ (multiplyPowers m n) = monomialValue σ m * monomialValue σ n := by
  induction m with
  | nil => simp [multiplyPowers, monomialValue]
  | cons x xs ih => simp [multiplyPowers, insertPower_value, ih, monomialValue, mul_assoc]

theorem insert_value (σ : ℕ → ℂ) (m : Monomial) (c : Coefficient) (p : Polynomial) :
    value σ (insert m c p) = Numeric.complex c * monomialValue σ m + value σ p := by
  induction p with
  | nil =>
    simp only [insert]; split_ifs with h
    · simp [h, value, Numeric.complex]
    · rfl
  | cons t ps ih =>
    rcases t with ⟨n, d⟩
    simp only [insert]; split_ifs with hc hm he hlt
    · simp [hc, value, Numeric.complex]
    · subst n
      have hz : Numeric.complex c + Numeric.complex d = 0 := by
        rw [← Numeric.complex_add, he]; simp [Numeric.complex]
      simp only [value]; linear_combination -monomialValue σ m * hz
    · subst n
      simp only [value, Numeric.complex_add]; ring
    · rfl
    · simp only [value, ih]; ring

theorem add_value (σ : ℕ → ℂ) (p q : Polynomial) : value σ (add p q) = value σ p + value σ q := by
  induction p with
  | nil => simp [add, value]
  | cons t ps ih => simp [add, insert_value, ih, value, add_assoc]

theorem multiplyTerm_value (σ : ℕ → ℂ) (m : Monomial) (c : Coefficient) (p : Polynomial) :
    value σ (multiplyTerm m c p) = Numeric.complex c * monomialValue σ m * value σ p := by
  induction p with
  | nil => simp [multiplyTerm, value]
  | cons t ps ih =>
    simp only [multiplyTerm, insert_value, Numeric.complex_mul, multiplyPowers_value, ih, value]
    ring

theorem mul_value (σ : ℕ → ℂ) (p q : Polynomial) : value σ (mul p q) = value σ p * value σ q := by
  induction p with
  | nil => simp [mul, value]
  | cons t ps ih => simp only [mul, add_value, multiplyTerm_value, ih, value]; ring

theorem power_value (σ : ℕ → ℂ) (fuel : ℕ) (p : Polynomial) (n : ℕ) (hn : n ≤ fuel) :
    value σ (power fuel p n) = value σ p ^ n := by
  induction fuel generalizing p n with
  | zero => have hn' : n = 0 := by omega
            subst n; simp [power, value, monomialValue, Numeric.complex]
  | succ fuel ih =>
    simp only [power]
    split_ifs with hz he
    · subst n; simp [value, monomialValue, Numeric.complex]
    · rw [ih _ _ (by omega), mul_value, ← pow_two, ← pow_mul]
      congr 1; omega
    · rw [mul_value, ih _ _ (by omega), mul_value, ← pow_two, ← pow_mul, ← pow_succ]
      congr 1; omega

structure ArithmeticEquality (p q : Polynomial) : Prop where
  equation : ∀ σ : ℕ → ℂ, value σ p = value σ q

theorem ArithmeticEquality.refl (p : Polynomial) : ArithmeticEquality p p := ⟨fun _ => rfl⟩

theorem add_computed {p q a b r} (hp : ArithmeticEquality p a) (hq : ArithmeticEquality q b)
    (h : ArithmeticEquality (add a b) r) : ArithmeticEquality (add p q) r := by
  constructor; intro σ
  rw [add_value, hp.equation, hq.equation, ← add_value]
  exact h.equation σ

theorem checked_add (σ : ℕ → ℂ) {p q r : Polynomial} (h : ArithmeticEquality (add p q) r) :
    value σ p + value σ q = value σ r := (add_value σ p q).symm.trans (h.equation σ)

theorem checked_mul (σ : ℕ → ℂ) {p q r : Polynomial} (h : ArithmeticEquality (mul p q) r) :
    value σ p * value σ q = value σ r := (mul_value σ p q).symm.trans (h.equation σ)

theorem checked_power (σ : ℕ → ℂ) {p q : Polynomial} (n : ℕ) (h : ArithmeticEquality (power n p n) q) :
    value σ p ^ n = value σ q := (power_value σ n p n le_rfl).symm.trans (h.equation σ)

def constant (c : Coefficient) : Polynomial := if c = (0, 0) then [] else [([], c)]

theorem constant_value (σ : ℕ → ℂ) (c : Coefficient) : value σ (constant c) = Numeric.complex c := by
  unfold constant; split_ifs with h <;> simp [value, monomialValue, h, Numeric.complex]

structure Powered (σ : ℕ → ℂ) (p : Polynomial) (n : ℕ) (q : Polynomial) : Prop where
  equation : value σ p ^ n = value σ q

theorem Powered.zero (σ : ℕ → ℂ) (p : Polynomial) : Powered σ p 0 [([], (1, 0))] := by
  constructor; simp [value, monomialValue, Numeric.complex]

theorem Powered.succ {σ p n q r} (h : Powered σ p n q) (hm : ArithmeticEquality (mul q p) r) : Powered σ p (n+1) r :=
  ⟨(pow_succ _ _).trans ((congrArg (· * value σ p) h.equation).trans (checked_mul σ hm))⟩

theorem Powered.double {σ p n q r} (h : Powered σ p n q) (hm : ArithmeticEquality (mul q q) r) : Powered σ p (n+n) r :=
  ⟨(pow_add _ _ _).trans ((congrArg₂ (· * ·) h.equation h.equation).trans (checked_mul σ hm))⟩

noncomputable section

def embedN : ℕ →+* ℂ := Nat.castRingHom ℂ
def embedZ : ℤ →+* ℂ := Int.castRingHom ℂ
def embedQ : ℚ →+* ℂ := Rat.castHom ℂ
def embedR : ℝ →+* ℂ := Complex.ofRealHom
def embedC : ℂ →+* ℂ := RingHom.id ℂ

structure Normalized {α : Type} [Semiring α] (σ : ℕ → ℂ) (f : α →+* ℂ)
    (v : Option α) (p : Polynomial) : Prop where
  equation : v.map f = some (value σ p)

namespace Normalized
variable {α β : Type} [Semiring α] [Semiring β] {σ : ℕ → ℂ} {f : α →+* ℂ}
    {a b : Option α} {p q r : Polynomial}

theorem reindex (h : Normalized σ f a p) (he : p = q) : Normalized σ f a q := he ▸ h

theorem defined (h : Normalized σ f a p) : Value.Defined a := by
  cases a with
  | none => cases h.equation
  | some x => exact ⟨x, rfl⟩

theorem zero (hf : Function.Injective f) (h : Normalized σ f a []) : a = some 0 := by
  obtain ⟨x, hx⟩ := h.defined
  have he : f x = 0 := by simpa only [hx, Option.map_some', value, Option.some.injEq] using h.equation
  have hz : x = 0 := hf (he.trans (map_zero f).symm)
  simpa [hz] using hx

theorem atom (σ : ℕ → ℂ) (f : α →+* ℂ) (x : α) (i : ℕ) (h : f x = σ i) :
    Normalized σ f (some x) [([(i, 1)], (1, 0))] := by
  constructor; simp [value, monomialValue, Numeric.complex, h]

theorem defined_atom (σ : ℕ → ℂ) (f : α →+* ℂ) (a : Option α) (i : ℕ)
    (hd : Value.Defined a) (h : f (a.getD 0) = σ i) :
    Normalized σ f a [([(i, 1)], (1, 0))] := by
  obtain ⟨x, rfl⟩ := hd
  exact atom σ f x i h

theorem add (ha : Normalized σ f a p) (hb : Normalized σ f b q)
    (h : ArithmeticEquality (AlgebraCertificate.add p q) r) : Normalized σ f (Value.add a b) r := by
  obtain ⟨x, rfl⟩ := ha.defined; obtain ⟨y, rfl⟩ := hb.defined
  constructor
  simpa only [Value.add, Option.map_some', map_add] using
    congrArg some ((congrArg₂ (· + ·) (Option.some.inj ha.equation)
      (Option.some.inj hb.equation)).trans (checked_add σ h))

theorem mul (ha : Normalized σ f a p) (hb : Normalized σ f b q)
    (h : ArithmeticEquality (AlgebraCertificate.mul p q) r) : Normalized σ f (Value.mul a b) r := by
  obtain ⟨x, rfl⟩ := ha.defined; obtain ⟨y, rfl⟩ := hb.defined
  constructor
  simpa only [Value.mul, Option.map_some', map_mul] using
    congrArg some ((congrArg₂ (· * ·) (Option.some.inj ha.equation)
      (Option.some.inj hb.equation)).trans (checked_mul σ h))

theorem power (ha : Normalized σ f a p) (n : ℕ)
    (h : ArithmeticEquality (AlgebraCertificate.power n p n) q) : Normalized σ f (a.map (· ^ n)) q := by
  obtain ⟨x, rfl⟩ := ha.defined
  constructor
  simp only [Option.map_some', map_pow]
  exact congrArg some ((congrArg (· ^ n) (Option.some.inj ha.equation)).trans (checked_power σ n h))

theorem powered (ha : Normalized σ f a p) {n : ℕ} (h : Powered σ p n q) :
    Normalized σ f (a.map (· ^ n)) q := by
  obtain ⟨x, rfl⟩ := ha.defined
  constructor
  simp only [Option.map_some', map_pow]
  exact congrArg some ((congrArg (· ^ n) (Option.some.inj ha.equation)).trans h.equation)

theorem totalAdd (op : Function2 α α α) (ho : ∀ x y, op.value x y = x+y)
    (hd : ∀ x y, op.domain x y) (ha : Normalized σ f a p) (hb : Normalized σ f b q)
    (h : ArithmeticEquality (AlgebraCertificate.add p q) r) : Normalized σ f (op.apply a b) r := by
  obtain ⟨x, hx⟩ := ha.defined; obtain ⟨y, hy⟩ := hb.defined
  have he : op.apply a b = Value.add a b := by simp [hx, hy, Function2.apply, hd, ho, Value.add]
  rw [he]; exact ha.add hb h

theorem totalMul (op : Function2 α α α) (ho : ∀ x y, op.value x y = x*y)
    (hd : ∀ x y, op.domain x y) (ha : Normalized σ f a p) (hb : Normalized σ f b q)
    (h : ArithmeticEquality (AlgebraCertificate.mul p q) r) : Normalized σ f (op.apply a b) r := by
  obtain ⟨x, hx⟩ := ha.defined; obtain ⟨y, hy⟩ := hb.defined
  have he : op.apply a b = Value.mul a b := by simp [hx, hy, Function2.apply, hd, ho, Value.mul]
  rw [he]; exact ha.mul hb h

theorem totalPower (op : Function2 α ℕ α) (ho : ∀ x n, op.value x n = x^n)
    (hd : ∀ x n, op.domain x n) (ha : Normalized σ f a p) {b : Option ℕ} (n : ℕ)
    (hb : b = some n) (h : ArithmeticEquality (AlgebraCertificate.power n p n) q) :
    Normalized σ f (op.apply a b) q := by
  obtain ⟨x, hx⟩ := ha.defined
  have he : op.apply a b = a.map (· ^ n) := by simp [hx, hb, Function2.apply, hd, ho]
  rw [he]; exact ha.power n h

theorem totalPowered (op : Function2 α ℕ α) (ho : ∀ x n, op.value x n = x^n)
    (hd : ∀ x n, op.domain x n) (ha : Normalized σ f a p) {b : Option ℕ} (n : ℕ)
    (hb : b = some n) (h : Powered σ p n q) :
    Normalized σ f (op.apply a b) q := by
  obtain ⟨x, hx⟩ := ha.defined
  have he : op.apply a b = a.map (· ^ n) := by simp [hx, hb, Function2.apply, hd, ho]
  rw [he]; exact ha.powered h

theorem cast (g : β →+* ℂ) (op : Function1 α β)
    (ho : ∀ x, g (op.value x) = f x) (hd : ∀ x, op.domain x)
    (ha : Normalized σ f a p) : Normalized σ g (op.apply a) p := by
  obtain ⟨x, hx⟩ := ha.defined
  constructor
  simpa [hx, Function1.apply, hd, ho] using ha.equation

end Normalized

theorem castNZ {σ a p} (h : Normalized σ embedN a p) : Normalized σ embedZ (Functions.castNZ.apply a) p :=
  h.cast embedZ Functions.castNZ (fun x => Int.cast_natCast x) (fun _ => True.intro)
theorem castZQ {σ a p} (h : Normalized σ embedZ a p) : Normalized σ embedQ (Functions.castZQ.apply a) p :=
  h.cast embedQ Functions.castZQ (fun x => Rat.cast_intCast x) (fun _ => True.intro)
theorem castQR {σ a p} (h : Normalized σ embedQ a p) : Normalized σ embedR (Functions.castQR.apply a) p :=
  h.cast (f := embedQ) embedR Functions.castQR (fun x => Complex.ofReal_ratCast x) (fun _ => True.intro)
theorem castRC {σ a p} (h : Normalized σ embedR a p) : Normalized σ embedC (Functions.castRC.apply a) p :=
  h.cast embedC Functions.castRC (fun _ => rfl) (fun _ => True.intro)

theorem numericN (σ : ℕ → ℂ) (ρ : Env) (t : Expr .natural) (q : ℕ) (h : Numeric.calculate t = some q) :
    Normalized σ embedN (t.eval ρ) (constant (q, 0)) := by
  constructor; rw [Numeric.calculate_sound ρ t q h, Option.map_some', constant_value]
  simp [embedN, Numeric.denote, Numeric.complex]
theorem numericZ (σ : ℕ → ℂ) (ρ : Env) (t : Expr .integer) (q : ℤ) (h : Numeric.calculate t = some q) :
    Normalized σ embedZ (t.eval ρ) (constant (q, 0)) := by
  constructor; rw [Numeric.calculate_sound ρ t q h, Option.map_some', constant_value]
  simp [embedZ, Numeric.denote, Numeric.complex]
theorem numericQ (σ : ℕ → ℂ) (ρ : Env) (t : Expr .rational) (q : ℚ) (h : Numeric.calculate t = some q) :
    Normalized σ embedQ (t.eval ρ) (constant (q, 0)) := by
  constructor; rw [Numeric.calculate_sound ρ t q h, Option.map_some', constant_value]
  simp [embedQ, Numeric.denote, Numeric.complex]
theorem numericR (σ : ℕ → ℂ) (ρ : Env) (t : Expr .real) (q : ℚ) (h : Numeric.calculate t = some q) :
    Normalized σ embedR (t.eval ρ) (constant (q, 0)) := by
  constructor; rw [Numeric.calculate_sound ρ t q h, Option.map_some', constant_value]
  simp [embedR, Numeric.denote, Numeric.complex]
theorem numericC (σ : ℕ → ℂ) (ρ : Env) (t : Expr .complex) (q : Coefficient) (h : Numeric.calculate t = some q) :
    Normalized σ embedC (t.eval ρ) (constant q) := by
  constructor; rw [Numeric.calculate_sound ρ t q h, Option.map_some', constant_value]; rfl

theorem inverse {α : Type} [Field α] {σ : ℕ → ℂ} {f : α →+* ℂ} {a : Option α} {c : Coefficient}
    (ha : Normalized σ f a (constant c)) (hc : c ≠ (0, 0)) :
    Normalized σ f (Value.inv a) (constant (Numeric.invC c)) := by
  obtain ⟨x, hx⟩ := ha.defined
  have he : f x = Numeric.complex c := by simpa [hx, constant_value] using ha.equation
  have hn : x ≠ 0 := by intro hz; simp [hz] at he; exact hc ((Numeric.complex_zero c).mp he.symm)
  constructor
  simp [hx, Value.inv, hn, map_inv₀, he, constant_value]

theorem inverseQ {σ a c} (ha : Normalized σ embedQ a (constant c)) (hc : c ≠ (0, 0)) :
    Normalized σ embedQ (Functions.invQ.apply a) (constant (Numeric.invC c)) := by
  have h : Functions.invQ.apply a = Value.inv a := by
    cases a <;> simp [Function1.apply, Functions.invQ, Value.inv]
  rw [h]; exact inverse ha hc

end
end QSym.AlgebraCertificate
