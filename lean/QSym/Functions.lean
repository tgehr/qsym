import QSym.Value
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace QSym
structure Function1 (α β : Type) where
  value : α → β
  domain : α → Prop
structure Function2 (α β γ : Type) where
  value : α → β → γ
  domain : α → β → Prop

noncomputable def Function1.apply {α β} (f : Function1 α β) (x : Option α) : Option β := by
  classical
  exact x.bind (fun v => if f.domain v then some (f.value v) else none)
noncomputable def Function2.apply {α β γ} (f : Function2 α β γ) (x : Option α) (y : Option β) : Option γ := by
  classical
  exact x.bind (fun a => y.bind (fun b => if f.domain a b then some (f.value a b) else none))

theorem Function1.defined {α β} (f : Function1 α β) (x : Option α) :
    Value.Defined (f.apply x) ↔ ∃ v, x = some v ∧ f.domain v := by
  classical
  cases x <;> simp [Function1.apply, Value.Defined]
theorem Function2.defined {α β γ} (f : Function2 α β γ) (x : Option α) (y : Option β) :
    Value.Defined (f.apply x y) ↔ ∃ a b, x = some a ∧ y = some b ∧ f.domain a b := by
  classical
  cases x <;> cases y <;> simp [Function2.apply, Value.Defined]

theorem Function1.defined_arg {α β} (f : Function1 α β) (x : Option α)
    (h : Value.Defined (f.apply x)) : Value.Defined x := by
  obtain ⟨v, hv, _⟩ := (f.defined x).mp h
  exact ⟨v, hv⟩
theorem Function2.defined_left {α β γ} (f : Function2 α β γ) (x : Option α) (y : Option β)
    (h : Value.Defined (f.apply x y)) : Value.Defined x := by
  obtain ⟨a, _, ha, _, _⟩ := (f.defined x y).mp h
  exact ⟨a, ha⟩
theorem Function2.defined_right {α β γ} (f : Function2 α β γ) (x : Option α) (y : Option β)
    (h : Value.Defined (f.apply x y)) : Value.Defined y := by
  obtain ⟨_, b, _, hb, _⟩ := (f.defined x y).mp h
  exact ⟨b, hb⟩
theorem Function1.total {α β} (f : Function1 α β) (ht : ∀ v, f.domain v) (x : Option α)
    (hx : Value.Defined x) : Value.Defined (f.apply x) := by
  obtain ⟨v, hv⟩ := hx
  exact (f.defined x).mpr ⟨v, hv, ht v⟩
theorem Function2.total {α β γ} (f : Function2 α β γ) (ht : ∀ a b, f.domain a b)
    (x : Option α) (y : Option β) (hx : Value.Defined x) (hy : Value.Defined y) :
    Value.Defined (f.apply x y) := by
  obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
  exact (f.defined x y).mpr ⟨a, b, ha, hb, ht a b⟩

namespace Functions
noncomputable section
def castNZ : Function1 ℕ ℤ :=
  ⟨fun x => (x : ℤ), fun _ => True⟩
def castZQ : Function1 ℤ ℚ :=
  ⟨fun x => (x : ℚ), fun _ => True⟩
def castQR : Function1 ℚ ℝ :=
  ⟨fun x => (x : ℝ), fun _ => True⟩
def castRC : Function1 ℝ ℂ :=
  ⟨fun x => (x : ℂ), fun _ => True⟩
def addN : Function2 ℕ ℕ ℕ :=
  ⟨fun x y => x + y, fun _ _ => True⟩
def mulN : Function2 ℕ ℕ ℕ :=
  ⟨fun x y => x * y, fun _ _ => True⟩
def ltN : Function2 ℕ ℕ Bool :=
  ⟨fun x y => decide (x < y), fun _ _ => True⟩
def leN : Function2 ℕ ℕ Bool :=
  ⟨fun x y => decide (x ≤ y), fun _ _ => True⟩
def nonzeroN : Function1 ℕ Bool :=
  ⟨fun x => decide (x ≠ 0), fun _ => True⟩
def addZ : Function2 ℤ ℤ ℤ :=
  ⟨fun x y => x + y, fun _ _ => True⟩
def mulZ : Function2 ℤ ℤ ℤ :=
  ⟨fun x y => x * y, fun _ _ => True⟩
def ltZ : Function2 ℤ ℤ Bool :=
  ⟨fun x y => decide (x < y), fun _ _ => True⟩
def leZ : Function2 ℤ ℤ Bool :=
  ⟨fun x y => decide (x ≤ y), fun _ _ => True⟩
def nonzeroZ : Function1 ℤ Bool :=
  ⟨fun x => decide (x ≠ 0), fun _ => True⟩
def addQ : Function2 ℚ ℚ ℚ :=
  ⟨fun x y => x + y, fun _ _ => True⟩
def mulQ : Function2 ℚ ℚ ℚ :=
  ⟨fun x y => x * y, fun _ _ => True⟩
def ltQ : Function2 ℚ ℚ Bool :=
  ⟨fun x y => decide (x < y), fun _ _ => True⟩
def leQ : Function2 ℚ ℚ Bool :=
  ⟨fun x y => decide (x ≤ y), fun _ _ => True⟩
def nonzeroQ : Function1 ℚ Bool :=
  ⟨fun x => decide (x ≠ 0), fun _ => True⟩
def invQ : Function1 ℚ ℚ :=
  ⟨fun x => x⁻¹, fun x => x ≠ 0⟩
def eqB : Function2 Bool Bool Bool :=
  ⟨fun x y => x == y, fun _ _ => True⟩
def powNN : Function2 ℕ ℕ ℕ :=
  ⟨fun x n => x ^ n, fun _ _ => True⟩
def powZN : Function2 ℤ ℕ ℤ :=
  ⟨fun x n => x ^ n, fun _ _ => True⟩
def powQN : Function2 ℚ ℕ ℚ :=
  ⟨fun x n => x ^ n, fun _ _ => True⟩
def powRN : Function2 ℝ ℕ ℝ :=
  ⟨fun x n => x ^ n, fun _ _ => True⟩
def powCN : Function2 ℂ ℕ ℂ :=
  ⟨fun x n => x ^ n, fun _ _ => True⟩
def powQZ : Function2 ℚ ℤ ℚ :=
  ⟨fun x n => x ^ n, fun x n => x ≠ 0 ∨ 0 ≤ n⟩
def powRZ : Function2 ℝ ℤ ℝ :=
  ⟨fun x n => x ^ n, fun x n => x ≠ 0 ∨ 0 ≤ n⟩
def powCZ : Function2 ℂ ℤ ℂ :=
  ⟨fun x n => x ^ n, fun x n => x ≠ 0 ∨ 0 ≤ n⟩
def powerR : Function2 ℝ ℝ ℝ :=
  ⟨Real.rpow, fun x y => (0 < x) ∨ (x = 0 ∧ 0 ≤ y) ∨ (x < 0 ∧ ∃ n : ℤ, y = n)⟩
def powerC : Function2 ℂ ℂ ℂ :=
  ⟨Complex.cpow, fun x y => x ≠ 0 ∨ y = 0 ∨ (0 < y.re ∧ y.im = 0)⟩
def sqrtR : Function1 ℝ ℝ :=
  ⟨Real.sqrt, fun x => 0 ≤ x⟩
def sqrtC : Function1 ℂ ℂ :=
  ⟨fun z => z ^ (1 / 2 : ℂ), fun _ => True⟩
def cbrtR : Function1 ℝ ℝ :=
  ⟨fun x => if x < 0 then -((-x) ^ (1 / 3 : ℝ)) else x ^ (1 / 3 : ℝ), fun _ => True⟩
def expR : Function1 ℝ ℝ :=
  ⟨Real.exp, fun _ => True⟩
def expC : Function1 ℂ ℂ :=
  ⟨Complex.exp, fun _ => True⟩
def sinR : Function1 ℝ ℝ :=
  ⟨Real.sin, fun _ => True⟩
def sinC : Function1 ℂ ℂ :=
  ⟨Complex.sin, fun _ => True⟩
def cosR : Function1 ℝ ℝ :=
  ⟨Real.cos, fun _ => True⟩
def cosC : Function1 ℂ ℂ :=
  ⟨Complex.cos, fun _ => True⟩
def sinhR : Function1 ℝ ℝ :=
  ⟨Real.sinh, fun _ => True⟩
def sinhC : Function1 ℂ ℂ :=
  ⟨Complex.sinh, fun _ => True⟩
def coshR : Function1 ℝ ℝ :=
  ⟨Real.cosh, fun _ => True⟩
def coshC : Function1 ℂ ℂ :=
  ⟨Complex.cosh, fun _ => True⟩
def tanhR : Function1 ℝ ℝ :=
  ⟨Real.tanh, fun _ => True⟩
def tanhC : Function1 ℂ ℂ :=
  ⟨Complex.tanh, fun z => Complex.cosh z ≠ 0⟩
def logR : Function1 ℝ ℝ :=
  ⟨Real.log, fun x => 0 < x⟩
def logC : Function1 ℂ ℂ :=
  ⟨Complex.log, fun z => z ≠ 0⟩
def tanR : Function1 ℝ ℝ :=
  ⟨Real.tan, fun x => Real.cos x ≠ 0⟩
def tanC : Function1 ℂ ℂ :=
  ⟨Complex.tan, fun z => Complex.cos z ≠ 0⟩
def asinR : Function1 ℝ ℝ :=
  ⟨Real.arcsin, fun x => -1 ≤ x ∧ x ≤ 1⟩
def acosR : Function1 ℝ ℝ :=
  ⟨Real.arccos, fun x => -1 ≤ x ∧ x ≤ 1⟩
def atanR : Function1 ℝ ℝ :=
  ⟨Real.arctan, fun _ => True⟩
def asinC : Function1 ℂ ℂ :=
  ⟨fun z => -Complex.I * Complex.log (Complex.I * z + (1 - z^2) ^ (1 / 2 : ℂ)), fun _ => True⟩
def acosC : Function1 ℂ ℂ :=
  ⟨fun z => Real.pi / 2 - asinC.value z, fun _ => True⟩
def atanC : Function1 ℂ ℂ :=
  ⟨fun z => Complex.I / 2 * (Complex.log (1 - Complex.I*z) - Complex.log (1 + Complex.I*z)), fun z => z ≠ Complex.I ∧ z ≠ -Complex.I⟩
def asinhR : Function1 ℝ ℝ :=
  ⟨Real.arsinh, fun _ => True⟩
def acoshR : Function1 ℝ ℝ :=
  ⟨fun x => Real.log (x + Real.sqrt (x^2 - 1)), fun x => 1 ≤ x⟩
def atanhR : Function1 ℝ ℝ :=
  ⟨fun x => (Real.log (1+x) - Real.log (1-x)) / 2, fun x => -1 < x ∧ x < 1⟩
def asinhC : Function1 ℂ ℂ :=
  ⟨fun z => Complex.log (z + (z^2 + 1) ^ (1 / 2 : ℂ)), fun _ => True⟩
def acoshC : Function1 ℂ ℂ :=
  ⟨fun z => Complex.log (z + (z-1)^(1 / 2 : ℂ) * (z+1)^(1 / 2 : ℂ)), fun _ => True⟩
def atanhC : Function1 ℂ ℂ :=
  ⟨fun z => (Complex.log (1+z) - Complex.log (1-z)) / 2, fun z => z ≠ 1 ∧ z ≠ -1⟩
def exp2R : Function1 ℝ ℝ :=
  ⟨fun x => (2 : ℝ) ^ x, fun _ => True⟩
def log2R : Function1 ℝ ℝ :=
  ⟨fun x => Real.log x / Real.log 2, fun x => 0 < x⟩
def log10R : Function1 ℝ ℝ :=
  ⟨fun x => Real.log x / Real.log 10, fun x => 0 < x⟩
def makeC : Function2 ℝ ℝ ℂ :=
  ⟨fun x y => (x : ℂ) + y * Complex.I, fun _ _ => True⟩
def reC : Function1 ℂ ℝ :=
  ⟨Complex.re, fun _ => True⟩
def imC : Function1 ℂ ℝ :=
  ⟨Complex.im, fun _ => True⟩
def absC : Function1 ℂ ℝ :=
  ⟨norm, fun _ => True⟩
def argC : Function1 ℂ ℝ :=
  ⟨Complex.arg, fun z => z ≠ 0⟩
def cisR : Function1 ℝ ℂ :=
  ⟨fun x => Complex.exp (x * Complex.I), fun _ => True⟩
def expiC : Function1 ℂ ℂ :=
  ⟨fun z => Complex.exp (Complex.I * z), fun _ => True⟩
def polarC : Function2 ℝ ℝ ℂ :=
  ⟨fun r θ => r * Complex.exp (θ * Complex.I), fun _ _ => True⟩
def atan2R : Function2 ℝ ℝ ℝ :=
  ⟨fun y x => Complex.arg ((x : ℂ) + y * Complex.I), fun y x => x ≠ 0 ∨ y ≠ 0⟩
def floorR : Function1 ℝ ℤ :=
  ⟨Int.floor, fun _ => True⟩
def ceilR : Function1 ℝ ℤ :=
  ⟨Int.ceil, fun _ => True⟩
def roundR : Function1 ℝ ℤ :=
  ⟨fun x => ⌊x + 1/2⌋, fun _ => True⟩
def signR : Function1 ℝ ℤ :=
  ⟨fun x => if x < 0 then -1 else if 0 < x then 1 else 0, fun _ => True⟩
def isIntR : Function1 ℝ Bool :=
  ⟨fun x => decide (x = (⌊x⌋ : ℤ)), fun _ => True⟩
def minR : Function2 ℝ ℝ ℝ :=
  ⟨min, fun _ _ => True⟩
def maxR : Function2 ℝ ℝ ℝ :=
  ⟨max, fun _ _ => True⟩
def hypotR : Function2 ℝ ℝ ℝ :=
  ⟨fun x y => Real.sqrt (x^2 + y^2), fun _ _ => True⟩
def gcdZ : Function2 ℤ ℤ ℕ :=
  ⟨Int.gcd, fun _ _ => True⟩
def makeQ : Function2 ℤ ℤ ℚ :=
  ⟨fun x y => (x : ℚ) / y, fun _ y => y ≠ 0⟩
def numQ : Function1 ℚ ℤ :=
  ⟨Rat.num, fun _ => True⟩
def denQ : Function1 ℚ ℕ :=
  ⟨Rat.den, fun _ => True⟩
def erfR : Function1 ℝ ℝ :=
  ⟨fun x => 2 / Real.sqrt Real.pi * ∫ t in (0 : ℝ)..x, Real.exp (-t^2), fun _ => True⟩
def erfcR : Function1 ℝ ℝ :=
  ⟨fun x => 1 - erfR.value x, fun _ => True⟩
def gammaR : Function1 ℝ ℝ :=
  ⟨Real.Gamma, fun x => ∀ n : ℕ, x ≠ -(n : ℝ)⟩
def lgammaR : Function1 ℝ ℝ :=
  ⟨fun x => Real.log |Real.Gamma x|, fun x => (∀ n : ℕ, x ≠ -(n : ℝ)) ∧ Real.Gamma x ≠ 0⟩
def gammaC : Function1 ℂ ℂ :=
  ⟨Complex.Gamma, fun z => ∀ n : ℕ, z ≠ -(n : ℂ)⟩
def pi : ℝ := Real.pi
def e : ℝ := Real.exp 1
end
end Functions
end QSym
