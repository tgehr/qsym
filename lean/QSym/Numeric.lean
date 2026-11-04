import QSym.Refinement

namespace QSym.Numeric

-- A successful result certifies a defined closed value. `none` also covers
-- unsupported syntax, so two failures must never certify an equality.
abbrev Data : Ty → Type
  | .real => ℚ
  | .complex => ℚ × ℚ
  | .bool => Bool
  | .density | .measure => Empty

instance (s : Ty) : DecidableEq (Data s) := by cases s <;> dsimp [Data] <;> infer_instance

noncomputable def complex (z : ℚ × ℚ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I
noncomputable def denote : {s : Ty} → Data s → s.denote
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

def calculate : {s : Ty} → Expr s → Option (Data s)
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

-- Shared induction; certificates contain only `sound ... rfl`.
theorem calculate_sound (ρ : Env) {s : Ty} (e : Expr s) (v : Data s)
    (h : calculate e = some v) : Expr.eval ρ e = some (denote v) := by
  induction e with
  | real n =>
    have hv := Option.some.inj h
    subst v
    simp [Expr.eval, denote]
  | complex r i =>
    have hv := Option.some.inj h
    subst v
    simp [Expr.eval, denote, complex]
  | ratR q => simpa [calculate, Expr.eval, denote] using h
  | ratC r i =>
    have hv := Option.some.inj h
    subst v
    rfl
  | bool b => simpa [calculate, Expr.eval, denote] using h
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
  | _ => simp [calculate] at h

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
