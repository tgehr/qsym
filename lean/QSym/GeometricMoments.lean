import QSym.Summation
import QSym.DistributionPolynomialGrid
import Mathlib.Algebra.Polynomial.Roots

/-! Exact certificates for absolutely convergent polynomial-geometric sums.
The candidate primitive is checked by arithmetic on rational coefficients. -/
noncomputable section
namespace QSym.GeometricMoments
open Distribution.StepSource Polynomial

-- At integer sample points the Horner numerator and denominator can be
-- evaluated without normalizing a rational at every multiply and add.
private def denominator : List ℚ → ℕ
  | [] => 1
  | c :: p => c.den * denominator p

private def numerator (x : ℕ) : List ℚ → ℤ
  | [] => 0
  | c :: p => c.num * denominator p + (x : ℤ) * c.den * numerator x p

private theorem denominator_ne (p : List ℚ) : denominator p ≠ 0 := by
  induction p with
  | nil => decide
  | cons c p ih => exact Nat.mul_ne_zero c.den_nz ih

private theorem cast_num (c : ℚ) : (c.num : ℝ) = (c : ℝ) * c.den := by
  rw [Rat.cast_def, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr c.den_nz)]

private theorem numerator_eval (p : List ℚ) (n : ℕ) :
    (numerator n p : ℝ) = denominator p * polyEval p n := by
  induction p with
  | nil => simp [numerator, denominator, polyEval]
  | cons c p ih =>
    simp only [numerator, Int.cast_add, Int.cast_mul, Int.cast_natCast, denominator, Nat.cast_mul,
      polyEval, ih, cast_num c]
    ring

/-- A mathematical polynomial with an exact integer evaluator at natural
arguments. The evaluator follows the source operations, so checking a power
never requires kernel expansion of its coefficients. -/
structure SampledPolynomial where
  poly : Polynomial ℝ
  degree : ℕ
  bounded : poly.natDegree ≤ degree
  den : ℕ
  nonzero : den ≠ 0
  num : ℕ → ℤ
  exact_num (n : ℕ) : (num n : ℝ) = den * poly.eval (n : ℝ)

def SampledPolynomial.index : SampledPolynomial :=
  ⟨X, 1, by simp, 1, by decide, fun n => n, by simp⟩

def SampledPolynomial.constant (c : ℚ) : SampledPolynomial :=
  ⟨C (c : ℝ), 0, by simp, c.den, c.den_nz, fun _ => c.num, by simp [cast_num c, mul_comm]⟩

def SampledPolynomial.add (p s : SampledPolynomial) : SampledPolynomial :=
  ⟨p.poly + s.poly, max p.degree s.degree, natDegree_add_le_of_le p.bounded s.bounded,
    p.den * s.den, Nat.mul_ne_zero p.nonzero s.nonzero, fun n => p.num n * s.den + s.num n * p.den, by
      intro n; push_cast; rw [p.exact_num, s.exact_num, eval_add]; ring⟩

def SampledPolynomial.mul (p s : SampledPolynomial) : SampledPolynomial :=
  ⟨p.poly * s.poly, p.degree + s.degree, natDegree_mul_le_of_le p.bounded s.bounded,
    p.den * s.den, Nat.mul_ne_zero p.nonzero s.nonzero, fun n => p.num n * s.num n, by
      intro n; push_cast; rw [p.exact_num, s.exact_num, eval_mul]; ring⟩

def SampledPolynomial.pow (p : SampledPolynomial) (k : ℕ) : SampledPolynomial :=
  ⟨p.poly^k, k*p.degree, natDegree_pow_le_of_le k p.bounded,
    p.den^k, pow_ne_zero _ p.nonzero, fun n => (p.num n)^k, by
      intro n; push_cast; rw [p.exact_num, eval_pow, mul_pow]⟩

private def sample (p : SampledPolynomial) (primitive : List ℚ) (q w : ℚ) (a k n : ℕ) : Bool :=
  decide ((w.den : ℤ) * p.den * (q.num * numerator (n+1) primitive - q.den * numerator n primitive) =
    w.num * q.den * denominator primitive * p.num (a+n*k))

private theorem sample_sound {p : SampledPolynomial} {primitive : List ℚ} {q w : ℚ} {a k n : ℕ}
    (h : sample p primitive q w a k n = true) :
    (q : ℝ) * polyEval primitive ((n : ℝ)+1) - polyEval primitive n = w * p.poly.eval (a+(n : ℝ)*k) := by
  have e := congrArg (fun z : ℤ => (z : ℝ)) (of_decide_eq_true h)
  push_cast at e
  simp only [numerator_eval, p.exact_num, Nat.cast_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, cast_num q, cast_num w] at e
  have nz : (w.den : ℝ) * p.den * q.den * denominator primitive ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr w.den_nz)
      (Nat.cast_ne_zero.mpr p.nonzero)) (Nat.cast_ne_zero.mpr q.den_nz))
      (Nat.cast_ne_zero.mpr (denominator_ne primitive))
  apply mul_left_cancel₀ nz
  linear_combination e

/-- Checking at more distinct integers than the degree determines the polynomial
identity everywhere, including for a non-unit stride or a shifted start. -/
def checks (p : SampledPolynomial) (primitive : List ℚ) (q w : ℚ) (a k : ℕ) : Bool :=
  (List.range (max p.degree primitive.length + 1)).all (sample p primitive q w a k)


private def atLinear (v : Polynomial ℝ) : List ℚ → Polynomial ℝ
  | [] => 0
  | c :: p => C (c : ℝ) + v * atLinear v p

private theorem atLinear_eval (v : Polynomial ℝ) (p : List ℚ) (x : ℝ) :
    (atLinear v p).eval x = polyEval p (v.eval x) := by
  induction p with
  | nil => simp [atLinear, polyEval]
  | cons c p ih => simp [atLinear, polyEval, ih]

private theorem atLinear_degree {v : Polynomial ℝ} (hv : v.natDegree ≤ 1) (p : List ℚ) :
    (atLinear v p).natDegree ≤ p.length := by
  induction p with
  | nil => simp [atLinear]
  | cons c p ih =>
    apply natDegree_add_le_of_degree_le (by simp)
    simpa [Nat.add_comm] using natDegree_mul_le_of_le hv ih

private theorem difference {p : SampledPolynomial} {primitive : List ℚ} {q w : ℚ} {a k : ℕ}
    (h : checks p primitive q w a k = true) (x : ℝ) :
    (q : ℝ) * polyEval primitive (x+1) - polyEval primitive x = w * p.poly.eval (a+x*k) := by
  let v : Polynomial ℝ := C (a : ℝ) + X * C (k : ℝ)
  let d := C (q : ℝ) * atLinear (X+1) primitive - atLinear X primitive - C (w : ℝ) * p.poly.comp v
  have hd : d.natDegree ≤ max p.degree primitive.length := by
    have hv : v.natDegree ≤ 1 := natDegree_add_le_of_degree_le (by simp) ((natDegree_mul_C_le _ _).trans (by simp))
    have hu : ((X : Polynomial ℝ)+1).natDegree ≤ 1 := natDegree_add_le_of_degree_le (by simp) (by simp)
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply (natDegree_sub_le _ _).trans
      exact (max_le ((natDegree_C_mul_le _ _).trans (atLinear_degree hu _))
        (atLinear_degree (by simp) _)).trans (Nat.le_max_right ..)
    · have bound : (p.poly.comp v).natDegree ≤ p.degree := by
        simpa using natDegree_comp_le.trans (Nat.mul_le_mul p.bounded hv)
      exact ((natDegree_C_mul_le _ _).trans bound).trans (Nat.le_max_left ..)
  have hz : d = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero d
      (f := fun i : Fin (max p.degree primitive.length + 1) => (i.val : ℝ))
    · intro i j he
      exact Fin.ext (Nat.cast_injective he)
    · intro i
      have hi := sample_sound ((List.all_eq_true.mp h) i.val (List.mem_range.mpr i.isLt))
      simpa [d, v, atLinear_eval, eval_comp, sub_eq_zero] using hi
    · simpa using Nat.lt_succ_of_le hd
  have hx := congrArg (fun z : Polynomial ℝ => z.eval x) hz
  simpa [d, v, atLinear_eval, eval_comp, sub_eq_zero] using hx

private def tail (q : ℝ) : List ℚ → ℕ → Summation.Tail ℝ
  | [], _ => .nil
  | c :: cs, k => .cons (c : ℝ) q k (tail q cs (k+1))

private theorem tail_converges {q : ℝ} (hq : ‖q‖ < 1) (cs : List ℚ) (k : ℕ) :
    (tail q cs k).converges := by
  induction cs generalizing k with
  | nil => trivial
  | cons c cs ih => exact ⟨hq, ih (k+1)⟩

private theorem tail_eval (q : ℝ) (cs : List ℚ) (k n : ℕ) :
    (tail q cs k).eval n = (n : ℝ)^k * polyEval cs n * q^n := by
  induction cs generalizing k with
  | nil => simp [tail, Summation.Tail.eval, polyEval]
  | cons c cs ih =>
    simp only [tail, Summation.Tail.eval, ih, polyEval, pow_succ]
    ring

private theorem at_zero (p : List ℚ) : polyEval p 0 = ((p.headD 0 : ℚ) : ℝ) := by
  cases p <;> simp [polyEval]

theorem evaluate (p : SampledPolynomial) (primitive : List ℚ) (q w z : ℚ) (a k : ℕ) (hq : |q| < 1)
    (check : checks p primitive q w a k = true) (answer : -primitive.headD 0 = z) (f : ℕ → Option ℝ)
    (row : ∀ n, f n = some (w * p.poly.eval (a+(n : ℝ)*k) * (q : ℝ)^n)) :
    Summation.value norm (some f) = some (z : ℝ) := by
  let t := tail (q : ℝ) primitive 0
  have converges : t.converges := tail_converges (by rw [Real.norm_eq_abs]; exact_mod_cast hq) _ _
  have te (n : ℕ) : t.eval n = polyEval primitive n * (q : ℝ)^n := by simp [t, tail_eval]
  have h := Summation.telescope f t.eval (t.summable converges) (t.summable_norm converges) (fun n => by
    rw [row, te, te, Nat.cast_succ, pow_succ, ← difference check (n : ℝ)]
    congr 1
    ring)
  rw [h, te]
  simp only [Nat.cast_zero, pow_zero, mul_one, Option.some.injEq]
  rw [← answer, Rat.cast_neg, at_zero]

/-- A total real polynomial observation of an emitted natural. -/
def NatTest (test : ℕ → Option ℝ) (p : SampledPolynomial) : Prop :=
  ∀ n, test n = some (p.poly.eval (n : ℝ))

theorem NatTest.index : NatTest (fun n => Functions.castQR.apply
    (Functions.castZQ.apply (Functions.castNZ.apply (some n)))) .index := by
  intro n
  simp [SampledPolynomial.index, Function1.apply, Functions.castQR, Functions.castZQ, Functions.castNZ]

theorem NatTest.constant (v : Option ℝ) (q : ℚ) (h : v = some (q : ℝ)) : NatTest (fun _ => v) (.constant q) := by
  intro n; simp [h, SampledPolynomial.constant]

theorem NatTest.add {f g : ℕ → Option ℝ} {p q : SampledPolynomial} (hf : NatTest f p) (hg : NatTest g q) :
    NatTest (fun n => Value.add (f n) (g n)) (p.add q) := by
  intro n; simp [hf n, hg n, Value.add, SampledPolynomial.add]

theorem NatTest.mul {f g : ℕ → Option ℝ} {p q : SampledPolynomial} (hf : NatTest f p) (hg : NatTest g q) :
    NatTest (fun n => Value.mul (f n) (g n)) (p.mul q) := by
  intro n; simp [hf n, hg n, Value.mul, SampledPolynomial.mul]

theorem NatTest.pow (k : ℕ) {f : ℕ → Option ℝ} {p : SampledPolynomial} (h : NatTest f p) :
    NatTest (fun n => (f n).map (fun x => x^k)) (p.pow k) := by
  intro n; simp [h n, SampledPolynomial.pow]

/-- A total polynomial probe does not affect the pointwise presence of a
geometric row, including at the zeroth power. -/
theorem NatTest.geometric_present {test : ℕ → Option ℝ} {p : SampledPolynomial}
    (h : NatTest test p) (left : Bool) (r : Option ℝ) (n : ℕ) :
    (if left then Value.mul (test n) (Functions.powRN.apply r (some n))
      else Value.mul (Functions.powRN.apply r (some n)) (test n)).isSome = r.isSome := by
  rw [h n]
  cases left <;> cases r <;> simp [Value.mul, Functions.powRN, Functions.powQN, Functions.castQR, Function2.apply, Function1.apply]

theorem NatTest.geometric_cast_present {test : ℕ → Option ℝ} {p : SampledPolynomial}
    (h : NatTest test p) (left : Bool) (r : Option ℚ) (n : ℕ) :
    let power := Functions.castQR.apply (Functions.powQN.apply r (some n))
    (if left then Value.mul (test n) power else Value.mul power (test n)).isSome = (Functions.castQR.apply r).isSome := by
  rw [h n]
  cases left <;> cases r <;> simp [Value.mul, Functions.powRN, Functions.powQN, Functions.castQR, Function2.apply, Function1.apply]

end QSym.GeometricMoments
