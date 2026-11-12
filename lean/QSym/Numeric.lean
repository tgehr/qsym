import QSym.RefinementBase

namespace QSym.Numeric

-- A successful result certifies a defined closed value. `none` also covers
-- unsupported syntax, so two failures must never certify an equality.
abbrev Data : Ty → Type
  | .natural => ℕ
  | .integer => ℤ
  | .rational => ℚ
  | .real => ℚ
  | .complex => ℚ × ℚ
  | .bool => Bool
  | .density | .measure => Empty

instance (s : Ty) : DecidableEq (Data s) := by cases s <;> dsimp [Data] <;> infer_instance

noncomputable def complex (z : ℚ × ℚ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I
noncomputable def denote : {s : Ty} → Data s → s.denote
  | .natural, n => n
  | .integer, n => n
  | .rational, q => q
  | .real, q => (q : ℝ)
  | .complex, z => complex z
  | .bool, b => b
  | .density, e => e.elim
  | .measure, e => e.elim

def addC (x y : ℚ × ℚ) : ℚ × ℚ := (x.1 + y.1, x.2 + y.2)
def mulC (x y : ℚ × ℚ) : ℚ × ℚ := (x.1*y.1-x.2*y.2, x.1*y.2+x.2*y.1)
def invC (x : ℚ × ℚ) : ℚ × ℚ :=
  let d := x.1*x.1+x.2*x.2
  (x.1/d, -x.2/d)
def conjC (x : ℚ × ℚ) : ℚ × ℚ := (x.1, -x.2)

def binary {α β γ : Type} (f : α → β → γ) (x : Option α) (y : Option β) : Option γ := do
  return f (← x) (← y)

def inverse (q : ℚ) : Option ℚ := if q = 0 then none else some q⁻¹
def inverseC (z : ℚ × ℚ) : Option (ℚ × ℚ) :=
  if z = (0, 0) then none else some (invC z)

-- Structural fuel keeps kernel reduction independent of well-founded proofs.
def power {α : Type} [One α] [Mul α] : ℕ → α → ℕ → α
  | 0, _, _ => 1
  | fuel+1, x, n =>
    if n=0 then 1 else
    let y := power fuel (x*x) (n/2)
    if n%2=0 then y else y*x

def calculate : {s : Ty} → Expr s → Option (Data s)
  | _, .nat v => some v
  | _, .int v => some v
  | _, .rat v => some v
  | _, .subN a b => do
    let x ← calculate a; let y ← calculate b
    if y ≤ x then some (x - y) else none
  | _, .addN a b => binary (· + ·) (calculate a) (calculate b)
  | _, .mulN a b => binary (· * ·) (calculate a) (calculate b)
  | _, .ltN a b => binary (fun x y => decide (x < y)) (calculate a) (calculate b)
  | _, .leN a b => binary (fun x y => decide (x ≤ y)) (calculate a) (calculate b)
  | _, .nonzeroN a => (calculate a).map (fun x => decide (x ≠ 0))
  | _, .addZ a b => binary (· + ·) (calculate a) (calculate b)
  | _, .mulZ a b => binary (· * ·) (calculate a) (calculate b)
  | _, .ltZ a b => binary (fun x y => decide (x < y)) (calculate a) (calculate b)
  | _, .leZ a b => binary (fun x y => decide (x ≤ y)) (calculate a) (calculate b)
  | _, .nonzeroZ a => (calculate a).map (fun x => decide (x ≠ 0))
  | _, .addQ a b => binary (· + ·) (calculate a) (calculate b)
  | _, .mulQ a b => binary (· * ·) (calculate a) (calculate b)
  | _, .ltQ a b => binary (fun x y => decide (x < y)) (calculate a) (calculate b)
  | _, .leQ a b => binary (fun x y => decide (x ≤ y)) (calculate a) (calculate b)
  | _, .nonzeroQ a => (calculate a).map (fun x => decide (x ≠ 0))
  | _, .castNZ a => (calculate a).map Int.ofNat
  | _, .castZQ a => (calculate a).map (fun x : ℤ => (x : ℚ))
  | _, .castQR a => (calculate a).map id
  | _, .castRC a => (calculate a).map (fun x => (x, 0))
  | _, .reC a => (calculate a).map Prod.fst
  | _, .imC a => (calculate a).map Prod.snd
  | _, .makeC a b => binary Prod.mk (calculate a) (calculate b)
  | _, .gcdZ a b => binary Int.gcd (calculate a) (calculate b)
  | _, .eqB a b => binary (· == ·) (calculate a) (calculate b)
  | _, .numQ a => (calculate a).map Rat.num
  | _, .denQ a => (calculate a).map Rat.den
  | _, .powN a n => (calculate a).map (fun x => power n x n)
  | _, .powZ a n => (calculate a).map (fun x => power n x n)
  | _, .powQ a n => (calculate a).map (fun x => power n x n)
  | _, .powR a n => (calculate a).map (fun x => power n x n)
  | _, .invQ a => (calculate a).bind inverse
  | _, .makeQ a b => do
    let x ← calculate a; let y ← calculate b
    if y = 0 then none else some ((x : ℚ) / y)
  | _, .real n => some (n : ℚ)
  | _, .complex r i => some ((r : ℚ), (i : ℚ))
  | _, .ratR q => some q
  | _, .ratC r i => some (r, i)
  | _, .bool b => some b
  | _, .addR a b => binary (· + ·) (calculate a) (calculate b)
  | _, .addC a b => binary addC (calculate a) (calculate b)
  | _, .mulR a b => binary (· * ·) (calculate a) (calculate b)
  | _, .mulC a b => binary mulC (calculate a) (calculate b)
  | _, .invR a => (calculate a).bind inverse
  | _, .invC a => (calculate a).bind inverseC
  | _, .absR a => (calculate a).map abs
  | _, .conj a => (calculate a).map conjC
  | _, .nonzeroR a => (calculate a).map (fun q => decide (q ≠ 0))
  | _, .nonzeroC a => (calculate a).map (fun z => decide (z ≠ (0, 0)))
  | _, .ltR a b => binary (fun x y => decide (x < y)) (calculate a) (calculate b)
  | _, .leR a b => binary (fun x y => decide (x ≤ y)) (calculate a) (calculate b)
  | _, _ => none

@[simp] theorem complex_re (z : ℚ × ℚ) : (complex z).re = (z.1 : ℝ) := by
  simp [complex, Complex.add_re, Complex.mul_re]
@[simp] theorem complex_im (z : ℚ × ℚ) : (complex z).im = (z.2 : ℝ) := by
  simp [complex, Complex.add_im, Complex.mul_im]
@[simp] theorem complex_zero (z : ℚ × ℚ) : complex z = 0 ↔ z = (0, 0) := by
  simp [Complex.ext_iff, Prod.ext_iff]
@[simp] theorem complex_add (x y : ℚ × ℚ) : complex (addC x y) = complex x + complex y := by
  apply Complex.ext <;> simp [addC]
@[simp] theorem complex_mul (x y : ℚ × ℚ) : complex (mulC x y) = complex x * complex y := by
  apply Complex.ext <;> simp [mulC, Complex.mul_re, Complex.mul_im]
@[simp] theorem complex_inv (x : ℚ × ℚ) : complex (invC x) = (complex x)⁻¹ := by
  apply Complex.ext <;> simp [invC, Complex.inv_re, Complex.inv_im, Complex.normSq_apply, div_eq_mul_inv]
@[simp] theorem complex_conj (x : ℚ × ℚ) : complex (conjC x) = star (complex x) := by
  apply Complex.ext <;> simp [conjC]

private theorem binary_some {α β γ : Type} {f : α → β → γ} {x : Option α} {y : Option β} {v : γ}
    (h : binary f x y = some v) : ∃ a b, x = some a ∧ y = some b ∧ f a b = v := by
  cases x <;> cases y <;> simp_all [binary]
private theorem map_some {α β : Type} {f : α → β} {x : Option α} {v : β}
    (h : x.map f = some v) : ∃ a, x = some a ∧ f a = v := by
  cases x <;> simp_all

private theorem power_sound {α : Type} [Monoid α] (fuel : ℕ) (x : α) (n : ℕ) (h : n≤fuel) : power fuel x n = x^n := by
  induction fuel generalizing x n with
  | zero =>
    have hn : n=0 := by omega
    subst n
    simp [power]
  | succ fuel ih =>
    simp only [power]
    split
    · next hn => simp [hn]
    · next hn =>
      rw [ih (x*x) (n/2) (by omega), ← pow_two, ← pow_mul]
      split
      · next he => congr 1; omega
      · next he => rw [← pow_succ]; congr 1; omega

-- Shared induction; certificates contain only `sound ... rfl`.
set_option maxHeartbeats 1000000 in
theorem calculate_sound (ρ : Env) {s : Ty} (term : Expr s) (v : Data s)
    (h : calculate term = some v) : Expr.eval ρ term = some (denote v) := by
  induction term with
  | nat x => exact h
  | int x => exact h
  | rat x => exact h
  | subN a b ha hb =>
    obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, hv⟩ := Option.bind_eq_some_iff.mp hv
    by_cases hle : y ≤ x
    · have hv' : x - y = v := by simpa [hle] using hv
      subst v
      simp [Expr.eval, ha x hx, hb y hy, Functions.subN, Function2.apply, denote, hle]
    · simp [hle] at hv
  | addN a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.addN, Function2.apply, denote, complex]
  | mulN a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.mulN, Function2.apply, denote, complex]
  | ltN a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.ltN, Function2.apply, denote, complex]
  | leN a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.leN, Function2.apply, denote, complex]
  | nonzeroN a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.nonzeroN, Function1.apply, denote, complex, id]
  | addZ a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.addZ, Function2.apply, denote, complex]
  | mulZ a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.mulZ, Function2.apply, denote, complex]
  | ltZ a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.ltZ, Function2.apply, denote, complex]
  | leZ a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.leZ, Function2.apply, denote, complex]
  | nonzeroZ a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.nonzeroZ, Function1.apply, denote, complex, id]
  | addQ a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.addQ, Function2.apply, denote, complex]
  | mulQ a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.mulQ, Function2.apply, denote, complex]
  | ltQ a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.ltQ, Function2.apply, denote, complex]
  | leQ a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.leQ, Function2.apply, denote, complex]
  | nonzeroQ a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.nonzeroQ, Function1.apply, denote, complex, id]
  | castNZ a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.castNZ, Function1.apply, denote, complex, id]
  | castZQ a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some (f := fun x : ℤ => (x : ℚ)) h
    simp [Expr.eval, ha x hx, Functions.castZQ, Function1.apply, denote, complex, id]
  | castQR a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.castQR, Function1.apply, denote, complex, id]
  | castRC a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.castRC, Function1.apply, denote, complex, id]
  | reC a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.reC, Function1.apply, denote, complex, id]
  | imC a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.imC, Function1.apply, denote, complex, id]
  | makeC a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.makeC, Function2.apply, denote, complex]
  | gcdZ a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.gcdZ, Function2.apply, denote]
  | eqB a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Functions.eqB, Function2.apply, denote]
  | numQ a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.numQ, Function1.apply, denote, complex, id]
  | denQ a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Functions.denQ, Function1.apply, denote, complex, id]
  | powN a n ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, denote, power_sound n x n (le_refl n)]
  | powZ a n ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, denote, power_sound n x n (le_refl n)]
  | powQ a n ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, denote, power_sound n x n (le_refl n)]
  | powR a n ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, denote, power_sound n x n (le_refl n), Rat.cast_pow]
  | invQ a ha =>
    obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.mp h
    by_cases hz : x = 0
    · simp [inverse, hz] at hv
    · have hv' : x⁻¹ = v := by simpa [inverse, hz] using hv
      subst v
      simp [Expr.eval, ha x hx, Functions.invQ, Function1.apply, denote, hz]
  | makeQ a b ha hb =>
    obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, hv⟩ := Option.bind_eq_some_iff.mp hv
    by_cases hz : y = 0
    · simp [hz] at hv
    · have hv' : (x : ℚ) / y = v := by simpa [hz] using hv
      subst v
      simp [Expr.eval, ha x hx, hb y hy, Functions.makeQ, Function2.apply, denote, hz]
  | real n =>
    have hv := Option.some.inj h
    subst v
    simp [Expr.eval, denote]
  | complex r i =>
    have hv := Option.some.inj h
    subst v
    simp [Expr.eval, denote, complex]
  | ratR q =>
    have hv := Option.some.inj h
    subst v
    rfl
  | ratC r i =>
    have hv := Option.some.inj h
    subst v
    rfl
  | bool b => exact h
  | addR a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Value.add, denote, Rat.cast_add]
  | addC a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Value.add, denote]
  | mulR a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Value.mul, denote, Rat.cast_mul]
  | mulC a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Value.mul, denote]
  | invR a ha =>
    obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.mp h
    by_cases hz : x = 0
    · simp [inverse, hz] at hv
    · have hv' : x⁻¹ = v := by simpa [inverse, hz] using hv
      subst v
      simp [Expr.eval, ha x hx, Value.inv, denote, hz]
  | invC a ha =>
    obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.mp h
    by_cases hz : x = (0, 0)
    · simp [inverseC, hz] at hv
    · have hv' : invC x = v := by simpa only [inverseC, if_neg hz, Option.some.injEq] using hv
      subst v
      simp only [Expr.eval, ha x hx, denote, Value.inv, Option.some_bind, complex_zero, if_neg hz, complex_inv]
  | absR a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Value.abs, denote, Rat.cast_abs]
  | conj a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Value.conj, denote]
  | nonzeroR a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Value.nonzero, denote]
  | nonzeroC a ha =>
    obtain ⟨x, hx, rfl⟩ := map_some h
    simp [Expr.eval, ha x hx, Value.nonzero, denote]
  | ltR a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Value.lt, denote]
  | leR a b ha hb =>
    obtain ⟨x, y, hx, hy, rfl⟩ := binary_some h
    simp [Expr.eval, ha x hx, hb y hy, Value.le, denote]
  | _ => cases h

def check {s : Ty} (a b : Expr s) : Bool :=
  match calculate a, calculate b with
  | some x, some y => decide (x = y)
  | _, _ => false

theorem sound (ρ : Env) {s : Ty} (a b : Expr s) (h : check a b = true) :
    Value.Refines (Expr.eval ρ a) (Expr.eval ρ b) := by
  cases ha : calculate a with
  | none => simp [check, ha] at h
  | some x => cases hb : calculate b with
    | none => simp [check, hb] at h
    | some y =>
      have hxy : x = y := by simpa [check, ha, hb] using h
      subst y
      exact Value.refines_of_eq ((calculate_sound ρ a x ha).trans (calculate_sound ρ b x hb).symm)

end QSym.Numeric
