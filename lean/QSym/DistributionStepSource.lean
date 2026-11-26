import QSym.DistributionStepModel
import QSym.Numeric

/-! Compositional source evidence for finite step integration. Exporters build
applications of these lemmas; the tactics in this module run only when the
shared library is compiled. All arithmetic witnesses in exported terms concern
rationals and are checked by ordinary kernel reduction. -/
noncomputable section
namespace QSym.Distribution.StepSource
open Classical

inductive Region where
  | before : ℚ → Region
  | between : ℚ → ℚ → Region
  | after : ℚ → Region

def Region.contains : Region → ℝ → Prop
  | .before b, x => x < b
  | .between a b, x => (a : ℝ) < x ∧ x < b
  | .after a, x => (a : ℝ) < x

def Region.sample : Region → ℚ
  | .before b => b - 1
  | .between a b => (a + b) / 2
  | .after a => a + 1

def Region.valid : Region → Prop
  | .between a b => a < b
  | _ => True

instance (r : Region) : Decidable r.valid := by cases r <;> dsimp [Region.valid] <;> infer_instance

theorem Region.sample_mem (r : Region) (h : r.valid) : r.contains (r.sample : ℝ) := by
  cases r <;> simp only [Region.contains, Region.sample, Region.valid] at *
  · push_cast; linarith
  · have := Rat.cast_lt (K := ℝ).mpr h
    push_cast; constructor <;> linarith
  · push_cast; linarith

structure Uniform {α : Type} (r : Region) (f : ℝ → α) : Prop where
  equation : ∀ x, r.contains x → f x = f (r.sample : ℝ)

instance {α : Type} {r : Region} {f : ℝ → α} :
    CoeFun (Uniform r f) (fun _ => ∀ x, r.contains x → f x = f (r.sample : ℝ)) := ⟨Uniform.equation⟩

theorem uniform_const {α : Type} (r : Region) (v : α) : Uniform r (fun _ => v) :=
  ⟨fun _ _ => rfl⟩

theorem uniform_unary {α β : Type} {r : Region} (op : α → β)
    {f : ℝ → α} (h : Uniform r f) : Uniform r (fun x => op (f x)) :=
  ⟨fun x hx => congrArg op (h x hx)⟩

theorem uniform_binary {α β γ : Type} {r : Region} (op : α → β → γ)
    {f : ℝ → α} {g : ℝ → β} (hf : Uniform r f) (hg : Uniform r g) :
    Uniform r (fun x => op (f x) (g x)) :=
  ⟨fun x hx => congrArg₂ op (hf x hx) (hg x hx)⟩

structure Affine (f : ℝ → Option ℝ) (a b : ℚ) : Prop where
  equation : ∀ x, f x = some ((a : ℝ) * x + b)

instance {f : ℝ → Option ℝ} {a b : ℚ} :
    CoeFun (Affine f a b) (fun _ => ∀ x, f x = some ((a : ℝ)*x+b)) := ⟨Affine.equation⟩

/-- An affine nonzero test excludes exactly its root. The weighted value
can be partial at other points. -/
theorem affine_mask_of_zero {β : Type} [Zero β] (f : ℝ → Option ℝ) (a b z : ℚ)
    (hf : Affine f a b) (ha : a ≠ 0) (hz : a*z+b = 0)
    (w : Option ℝ → Option β) (v : Option ℝ) (hv : v = some (z : ℝ))
    (hw : w v = some 0) (x : ℝ) :
    Value.mask (Value.nonzero (f x)) (w (some x)) = w (some x) := by
  subst v
  rw [hf x]
  have root : (a : ℝ) * (z : ℝ) + b = 0 := by exact_mod_cast hz
  by_cases h : x = (z : ℝ)
  · subst x
    simp [Value.nonzero, Value.mask, root, hw]
  · have slope : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have ne : (a : ℝ)*x+b ≠ 0 := by
      intro eq
      apply h
      apply mul_left_cancel₀ slope
      linarith
    simp [Value.nonzero, Value.mask, ne]

theorem affine_variable : Affine (fun x => some x) 1 0 := by
  constructor
  intro x; simp

theorem affine_constant (v : Option ℝ) (q : ℚ) (h : v = some (q : ℝ)) :
    Affine (fun _ => v) 0 q := by
  constructor
  intro x; simpa using h

theorem affine_add {f g a b c d} (hf : Affine f a b) (hg : Affine g c d) :
    Affine (fun x => Value.add (f x) (g x)) (a + c) (b + d) := by
  constructor
  intro x; dsimp only; rw [hf x, hg x]; simp only [Value.add, Rat.cast_add]; congr 1; ring

theorem affine_mul_left {f a b} (q : ℚ) (hf : Affine f a b) :
    Affine (fun x => Value.mul (some (q : ℝ)) (f x)) (q*a) (q*b) := by
  constructor
  intro x; dsimp only; rw [hf x]; simp only [Value.mul, Rat.cast_mul]; congr 1; ring

theorem affine_mul_right {f a b} (q : ℚ) (hf : Affine f a b) :
    Affine (fun x => Value.mul (f x) (some (q : ℝ))) (a*q) (b*q) := by
  constructor
  intro x; dsimp only; rw [hf x]; simp only [Value.mul, Rat.cast_mul]; congr 1; ring

theorem affine_mul_constant_left {f a b} {v : Option ℝ} (q : ℚ)
    (hv : v = some (q : ℝ)) (hf : Affine f a b) :
    Affine (fun x => Value.mul v (f x)) (q*a) (q*b) := by
  rw [hv]; exact affine_mul_left q hf

theorem affine_mul_constant_right {f a b} {v : Option ℝ} (q : ℚ)
    (hf : Affine f a b) (hv : v = some (q : ℝ)) :
    Affine (fun x => Value.mul (f x) v) (a*q) (b*q) := by
  rw [hv]; exact affine_mul_right q hf

inductive Sign where
  | negative | zero | positive

def Sign.holds : Sign → ℝ → Prop
  | .negative, v => v < 0
  | .zero, v => v = 0
  | .positive, v => 0 < v

-- Open endpoints allow a non-strict rational endpoint test to certify a
-- strict sign throughout the region, including punctured intervals.
def negativeCheck (r : Region) (a b : ℚ) : Bool :=
  if a = 0 then decide (b < 0)
  else if 0 < a then
    match r with
    | .before u | .between _ u => decide (a*u+b ≤ 0)
    | .after _ => false
  else
    match r with
    | .after l | .between l _ => decide (a*l+b ≤ 0)
    | .before _ => false

def signCheck (r : Region) (a b : ℚ) : Sign → Bool
  | .negative => negativeCheck r a b
  | .zero => decide (a = 0 ∧ b = 0)
  | .positive => negativeCheck r (-a) (-b)

theorem negativeCheck_sound {r a b} (h : negativeCheck r a b = true)
    {x : ℝ} (hx : r.contains x) : (a : ℝ)*x+b < 0 := by
  unfold negativeCheck at h
  split_ifs at h with ha hp
  · have hb : b < 0 := of_decide_eq_true h
    simpa [ha] using (Rat.cast_lt (K := ℝ)).mpr hb
  · have hp' : (0 : ℝ) < a := by exact_mod_cast hp
    cases r <;> simp only [Region.contains] at hx <;> simp only at h
    · have hb := (Rat.cast_le (K := ℝ)).mpr (of_decide_eq_true h)
      push_cast at hb; nlinarith
    · have hb := (Rat.cast_le (K := ℝ)).mpr (of_decide_eq_true h)
      push_cast at hb; nlinarith [hx.2]
    · contradiction
  · have ha' : (a : ℝ) < 0 := by exact_mod_cast (lt_of_le_of_ne (le_of_not_gt hp) ha)
    cases r <;> simp only [Region.contains] at hx <;> simp only at h
    · contradiction
    · have hb := (Rat.cast_le (K := ℝ)).mpr (of_decide_eq_true h)
      push_cast at hb; nlinarith [hx.1]
    · have hb := (Rat.cast_le (K := ℝ)).mpr (of_decide_eq_true h)
      push_cast at hb; nlinarith

theorem signCheck_sound {r a b s} (h : signCheck r a b s = true)
    {x : ℝ} (hx : r.contains x) : s.holds ((a : ℝ)*x+b) := by
  cases s with
  | negative => exact negativeCheck_sound h hx
  | zero =>
    obtain ⟨ha, hb⟩ := of_decide_eq_true h
    simp [Sign.holds, ha, hb]
  | positive =>
    have := negativeCheck_sound h hx
    simp only [Sign.holds]; push_cast at this; linarith

theorem sign_le {s : Sign} {x y : ℝ} (hx : s.holds x) (hy : s.holds y) :
    (x ≤ 0 ↔ y ≤ 0) := by cases s <;> simp only [Sign.holds] at * <;> constructor <;> intro h <;> linarith

theorem sign_lt {s : Sign} {x y : ℝ} (hx : s.holds x) (hy : s.holds y) :
    (x < 0 ↔ y < 0) := by cases s <;> simp only [Sign.holds] at * <;> constructor <;> intro h <;> linarith

theorem sign_ne {s : Sign} {x y : ℝ} (hx : s.holds x) (hy : s.holds y) :
    (x ≠ 0 ↔ y ≠ 0) := by cases s <;> simp only [Sign.holds] at * <;> constructor <;> intro h <;> intro hn <;> subst_vars <;> simp_all

theorem uniform_le {r f g a b c d s} (hr : r.valid)
    (hf : Affine f a b) (hg : Affine g c d) (hs : signCheck r (a-c) (b-d) s = true) :
    Uniform r (fun x => Value.le (f x) (g x)) := by
  constructor
  intro x hx
  have he := sign_le (signCheck_sound hs hx) (signCheck_sound hs (r.sample_mem hr))
  try dsimp only
  rw [hf x, hg x, hf _, hg _]
  simp only [Value.le, Option.bind_eq_bind, Option.some_bind, Option.pure_def,
    Option.some.injEq, decide_eq_decide]
  push_cast at he
  constructor <;> intro h
  · have := he.mp (by linarith); linarith
  · have := he.mpr (by linarith); linarith

theorem uniform_lt {r f g a b c d s} (hr : r.valid)
    (hf : Affine f a b) (hg : Affine g c d) (hs : signCheck r (a-c) (b-d) s = true) :
    Uniform r (fun x => Value.lt (f x) (g x)) := by
  constructor
  intro x hx
  have he := sign_lt (signCheck_sound hs hx) (signCheck_sound hs (r.sample_mem hr))
  try dsimp only
  rw [hf x, hg x, hf _, hg _]
  simp only [Value.lt, Option.bind_eq_bind, Option.some_bind, Option.pure_def,
    Option.some.injEq, decide_eq_decide]
  push_cast at he
  constructor <;> intro h
  · have := he.mp (by linarith); linarith
  · have := he.mpr (by linarith); linarith

theorem uniform_nonzero {r f a b s} (hr : r.valid)
    (hf : Affine f a b) (hs : signCheck r a b s = true) :
    Uniform r (fun x => Value.nonzero (f x)) := by
  constructor
  intro x hx
  have he := sign_ne (signCheck_sound hs hx) (signCheck_sound hs (r.sample_mem hr))
  try dsimp only
  rw [hf x, hf _]
  simp only [Value.nonzero, Option.map_some', Option.some.injEq, decide_eq_decide]
  exact he

end QSym.Distribution.StepSource
