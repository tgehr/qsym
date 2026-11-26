import QSym.DistributionStepGrid
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Piecewise polynomial densities on a finite rational grid. The source
evidence is compositional, as for step densities: every open cell carries a
rational coefficient list, both tails carry the zero polynomial, and the
finitely many cut points are probed for definedness separately. Coefficient
arithmetic and the integrals of the cells are computed by kernel reduction on
rationals. No density is replaced by an almost-everywhere equal one. -/
noncomputable section
namespace QSym.Distribution.StepSource
open MeasureTheory Set

/-- Horner evaluation of a coefficient list, lowest degree first. -/
def polyEval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: p, x => c + x * polyEval p x

def polyAdd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: polyAdd p q

def polyScale (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => (c * a) :: polyScale c p

def polyMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => polyAdd (polyScale a q) (0 :: polyMul p q)

def polyPow (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => polyMul p (polyPow p n)

def polyZero : List ℚ → Bool
  | [] => true
  | c :: p => decide (c = 0) && polyZero p

/-- Coefficients of the antiderivative divided by the variable: the entry
for degree `k` is divided by `k + 1`. The index is a rational accumulator. -/
def polyPrimitive : ℚ → List ℚ → List ℚ
  | _, [] => []
  | k, c :: p => c / k :: polyPrimitive (k + 1) p

def polyEvalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: p, x => c + x * polyEvalQ p x

def polyIntegral (p : List ℚ) (a b : ℚ) : ℚ :=
  b * polyEvalQ (polyPrimitive 1 p) b - a * polyEvalQ (polyPrimitive 1 p) a

theorem polyEval_add (p q : List ℚ) (x : ℝ) :
    polyEval (polyAdd p q) x = polyEval p x + polyEval q x := by
  induction p generalizing q with
  | nil => simp [polyAdd, polyEval]
  | cons a p ih =>
    cases q with
    | nil => simp [polyAdd, polyEval]
    | cons b q => simp only [polyAdd, polyEval, ih, Rat.cast_add]; ring

theorem polyEval_scale (c : ℚ) (p : List ℚ) (x : ℝ) :
    polyEval (polyScale c p) x = c * polyEval p x := by
  induction p with
  | nil => simp [polyScale, polyEval]
  | cons a p ih => simp only [polyScale, polyEval, ih, Rat.cast_mul]; ring

theorem polyEval_mul (p q : List ℚ) (x : ℝ) :
    polyEval (polyMul p q) x = polyEval p x * polyEval q x := by
  induction p with
  | nil => simp [polyMul, polyEval]
  | cons a p ih =>
    simp only [polyMul, polyEval, polyEval_add, polyEval_scale, ih, Rat.cast_zero]; ring

theorem polyEval_pow (p : List ℚ) (n : ℕ) (x : ℝ) :
    polyEval (polyPow p n) x = polyEval p x ^ n := by
  induction n with
  | zero => simp [polyPow, polyEval]
  | succ n ih => simp only [polyPow, polyEval_mul, ih]; ring

/-- The coefficients of `p(y + s)`. -/
def polyTranslate (s : ℚ) : List ℚ → List ℚ
  | [] => []
  | c :: p => polyAdd [c] (polyMul [s, 1] (polyTranslate s p))

theorem polyEval_translate (s : ℚ) (p : List ℚ) (y : ℝ) :
    polyEval (polyTranslate s p) y = polyEval p (y + s) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [polyTranslate, polyEval_add, polyEval_mul, polyEval, ih]
    push_cast
    ring

theorem polyEval_zero {p : List ℚ} (h : polyZero p = true) (x : ℝ) : polyEval p x = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [polyZero, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [polyEval, h.1, ih h.2]

theorem polyEval_continuous (p : List ℚ) : Continuous (polyEval p) := by
  induction p with
  | nil => exact continuous_const
  | cons c p ih => exact continuous_const.add (continuous_id.mul ih)

theorem polyEvalQ_cast (p : List ℚ) (x : ℚ) : ((polyEvalQ p x : ℚ) : ℝ) = polyEval p x := by
  induction p with
  | nil => simp [polyEvalQ, polyEval]
  | cons c p ih => simp only [polyEvalQ, polyEval, Rat.cast_add, Rat.cast_mul, ih]

theorem polyPrimitive_deriv (p : List ℚ) (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ (m + 1) * polyEval (polyPrimitive ((m : ℚ) + 1) p) y)
      (x ^ m * polyEval p x) x := by
  induction p generalizing m with
  | nil => simpa [polyPrimitive, polyEval] using hasDerivAt_const x (0 : ℝ)
  | cons c p ih =>
    have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
    have hc := (hasDerivAt_pow (m + 1) x).const_mul ((c : ℝ) / ((m : ℝ) + 1))
    have hp := ih (m + 1)
    have he : (fun y : ℝ => y ^ (m + 1) *
        polyEval (polyPrimitive ((m : ℚ) + 1) (c :: p)) y) =
        fun y : ℝ => (c : ℝ) / ((m : ℝ) + 1) * y ^ (m + 1) +
          y ^ (m + 1 + 1) * polyEval (polyPrimitive (((m + 1 : ℕ) : ℚ) + 1) p) y := by
      funext y
      simp only [polyPrimitive, polyEval, Rat.cast_div, Rat.cast_add, Rat.cast_natCast,
        Rat.cast_one, Nat.cast_add, Nat.cast_one]
      ring
    rw [he]
    convert hc.add hp using 1
    simp only [polyEval, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

theorem polyEval_intervalIntegral (p : List ℚ) (a b : ℚ) :
    ∫ x in (a : ℝ)..(b : ℝ), polyEval p x = ((polyIntegral p a b : ℚ) : ℝ) := by
  have hd : ∀ x ∈ Set.uIcc (a : ℝ) (b : ℝ),
      HasDerivAt (fun y : ℝ => y * polyEval (polyPrimitive 1 p) y) (polyEval p x) x := by
    intro x _
    simpa using polyPrimitive_deriv p 0 x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((polyEval_continuous p).intervalIntegrable _ _)]
  simp only [polyIntegral, Rat.cast_sub, Rat.cast_mul, polyEvalQ_cast]

theorem polyCell_integral (p : List ℚ) {a b : ℚ} (hab : a < b) :
    Integrable ((Ioo (a : ℝ) (b : ℝ)).indicator (polyEval p)) volume ∧
      ∫ x, (Ioo (a : ℝ) (b : ℝ)).indicator (polyEval p) x = ((polyIntegral p a b : ℚ) : ℝ) := by
  have hi : IntegrableOn (polyEval p) (Ioo (a : ℝ) (b : ℝ)) volume :=
    (polyEval_continuous p).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).mpr hi, ?_⟩
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (le_of_lt (Rat.cast_lt.mpr hab))]
  exact polyEval_intervalIntegral p a b

/-- Where the predicate holds, the partial function is this polynomial; in
particular it is defined there. Grid cells use the predicate of a region. -/
structure PolynomialOn (s : ℝ → Prop) (f : ℝ → Option ℝ) (p : List ℚ) : Prop where
  equation : ∀ x, s x → f x = some (polyEval p x)

theorem polynomial_variable (s : ℝ → Prop) : PolynomialOn s (fun x => some x) [0, 1] :=
  ⟨fun x _ => by simp [polyEval]⟩

theorem polynomial_constant (s : ℝ → Prop) (v : Option ℝ) (q : ℚ) (h : v = some (q : ℝ)) :
    PolynomialOn s (fun _ => v) [q] :=
  ⟨fun x _ => by simp [polyEval, h]⟩

theorem polynomial_one (s : ℝ → Prop) : PolynomialOn s DensityProgram.lebesgue.density [1] :=
  ⟨fun x _ => by simp [DensityProgram.density, polyEval]⟩

theorem polynomial_add {s : ℝ → Prop} {f g : ℝ → Option ℝ} {p q : List ℚ}
    (hf : PolynomialOn s f p) (hg : PolynomialOn s g q) :
    PolynomialOn s (fun x => Value.add (f x) (g x)) (polyAdd p q) :=
  ⟨fun x hx => by simp only [hf.equation x hx, hg.equation x hx, Value.add, polyEval_add]⟩

theorem polynomial_mul {s : ℝ → Prop} {f g : ℝ → Option ℝ} {p q : List ℚ}
    (hf : PolynomialOn s f p) (hg : PolynomialOn s g q) :
    PolynomialOn s (fun x => Value.mul (f x) (g x)) (polyMul p q) :=
  ⟨fun x hx => by simp only [hf.equation x hx, hg.equation x hx, Value.mul, polyEval_mul]⟩

theorem polynomial_pow {s : ℝ → Prop} {f : ℝ → Option ℝ} {p : List ℚ} (n : ℕ)
    (hf : PolynomialOn s f p) :
    PolynomialOn s (fun x => (f x).map (fun y : ℝ => y ^ n)) (polyPow p n) :=
  ⟨fun x hx => by simp only [hf.equation x hx, Option.map_some', polyEval_pow]⟩

/-- A step expression, for example a cast Iverson bracket, is a constant
polynomial on a cell. The sample is spelled as a rational literal. -/
theorem polynomial_uniform {r : Region} {f : ℝ → Option ℝ} (s q : ℚ) (hr : r.sample = s)
    (hu : Uniform r f) (hs : f (s : ℝ) = some (q : ℝ)) : PolynomialOn r.contains f [q] :=
  ⟨fun x hx => by subst hr; rw [hu x hx, hs]; simp [polyEval]⟩

/-- A guard that is constant on the region selects its value there. -/
theorem polynomial_mask_true {r : Region} {c : ℝ → Option Bool} {f : ℝ → Option ℝ}
    {p : List ℚ} (s : ℚ) (hr : r.sample = s) (hc : Uniform r c)
    (hs : c (s : ℝ) = some true) (hf : PolynomialOn r.contains f p) :
    PolynomialOn r.contains (fun x => Value.mask (c x) (f x)) p :=
  ⟨fun x hx => by subst hr; rw [hc x hx, hs]; exact hf.equation x hx⟩

/-- Masking is not strict: a false guard needs nothing of the masked value. -/
theorem polynomial_mask_false {r : Region} {c : ℝ → Option Bool} (f : ℝ → Option ℝ)
    (s : ℚ) (hr : r.sample = s) (hc : Uniform r c) (hs : c (s : ℝ) = some false) :
    PolynomialOn r.contains (fun x => Value.mask (c x) (f x)) [] :=
  ⟨fun x hx => by subst hr; rw [hc x hx, hs]; rfl⟩

/-- The coefficients of the absolute value of an affine function whose
sign is fixed. -/
def absPoly : Sign → ℚ → ℚ → List ℚ
  | .negative, a, b => [-b, -a]
  | .zero, _, _ => []
  | .positive, a, b => [b, a]

/-- An absolute value is affine on a cell that does not contain its kink. -/
theorem polynomial_abs {r : Region} {f : ℝ → Option ℝ} {a b : ℚ} (s : Sign)
    (hf : Affine f a b) (hs : signCheck r a b s = true) :
    PolynomialOn r.contains (fun x => Value.abs (f x)) (absPoly s a b) :=
  ⟨fun x hx => by
    have h := signCheck_sound hs hx
    rw [hf x]
    cases s <;> simp only [Sign.holds] at h <;>
      simp only [Value.abs, Option.map_some', absPoly, polyEval, Option.some.injEq]
    · rw [abs_of_neg h]; push_cast; ring
    · rw [h, abs_zero]
    · rw [abs_of_pos h]; push_cast; ring⟩

/-- A rational factorization of the input and its absolute value on an open
cell. Each root occurs with multiplicity. The sample chooses a sign and
`signCheck` verifies it throughout the cell. -/
def linearFactors (k : ℚ) : List ℚ → List ℚ
  | [] => [k]
  | a :: as => polyMul [-a, 1] (linearFactors k as)

private def factorSign (r : Region) (a : ℚ) : Sign :=
  if a ≤ r.sample then .positive else .negative

def absFactors (r : Region) (k : ℚ) : List ℚ → List ℚ
  | [] => [|k|]
  | a :: as => polyMul (absPoly (factorSign r a) 1 (-a)) (absFactors r k as)

def factorsChecked (r : Region) (as : List ℚ) : Bool :=
  as.all fun a => signCheck r 1 (-a) (factorSign r a)

private theorem absFactors_eval {r k as} (h : factorsChecked r as = true) {x} (hx : r.contains x) :
    |polyEval (linearFactors k as) x| = polyEval (absFactors r k as) x := by
  induction as with
  | nil => simp [linearFactors, absFactors, polyEval]
  | cons a as ih =>
    change (signCheck r 1 (-a) (factorSign r a) && factorsChecked r as) = true at h
    obtain ⟨ha, ht⟩ := Bool.and_eq_true_iff.mp h
    have aff : Affine (fun z => some (((1:ℚ):ℝ)*z+((-a:ℚ):ℝ))) 1 (-a) := ⟨fun _ => rfl⟩
    have eq := (polynomial_abs (factorSign r a) aff ha).equation x hx
    simp only [Value.abs, Option.map_some', Option.some.injEq] at eq
    rw [linearFactors, absFactors, polyEval_mul, abs_mul, ih ht, polyEval_mul, ← eq]
    simp [polyEval, add_comm]

theorem polynomial_abs_factors {r : Region} {f p} (k : ℚ) (as : List ℚ)
    (hf : PolynomialOn r.contains f p)
    (he : polyZero (polyAdd p (polyScale (-1) (linearFactors k as))) = true)
    (hs : factorsChecked r as = true) :
    PolynomialOn r.contains (fun x => Value.abs (f x)) (absFactors r k as) := by
  constructor
  intro x hx
  have h := polyEval_zero he x
  rw [polyEval_add, polyEval_scale] at h
  have eq : polyEval p x = polyEval (linearFactors k as) x := by push_cast at h; linarith
  simp only [hf.equation x hx, Value.abs, Option.map_some', eq, absFactors_eval hs hx]

/-- The cells to the right of a cut, with their accumulated integral. -/
inductive PolynomialTail (f : ℝ → Option ℝ) : ℚ → List ℚ → ℚ → Prop
  | nil (a : ℚ) {p : List ℚ} (h : PolynomialOn (Region.after a).contains f p) (zero : polyZero p = true) :
      PolynomialTail f a [] 0
  | cons {a b w : ℚ} {bs : List ℚ} {p : List ℚ} (ordered : a < b)
      (h : PolynomialOn (Region.between a b).contains f p) (tail : PolynomialTail f b bs w) :
      PolynomialTail f a (b :: bs) (polyIntegral p a b + w)

theorem PolynomialTail.integral {f a bs w} (h : PolynomialTail f a bs w) :
    ∃ g : ℝ → ℝ, (∀ x : ℝ, (a : ℝ) < x → (∀ p ∈ bs, x ≠ ((p : ℚ) : ℝ)) → f x = some (g x)) ∧
      (∀ x : ℝ, x ≤ (a : ℝ) → g x = 0) ∧ Integrable g volume ∧ ∫ x, g x = ((w : ℚ) : ℝ) := by
  induction h with
  | @nil a p h zero =>
    refine ⟨fun _ => 0, ?_, fun _ _ => rfl, integrable_zero _ _ _, by simp⟩
    intro x hx _
    rw [h.equation x hx, polyEval_zero zero]
  | @cons a b w bs p hab h _ ih =>
    obtain ⟨g, hg, hz, hi, hv⟩ := ih
    have hab' : (a : ℝ) < b := Rat.cast_lt.mpr hab
    obtain ⟨ci, cv⟩ := polyCell_integral p hab
    refine ⟨fun x => (Ioo (a : ℝ) (b : ℝ)).indicator (polyEval p) x + g x, ?_, ?_, ci.add hi, ?_⟩
    · intro x hx hp
      beta_reduce
      by_cases hxb : x < b
      · rw [h.equation x ⟨hx, hxb⟩, hz x (le_of_lt hxb),
          Set.indicator_of_mem (show x ∈ Ioo (a : ℝ) (b : ℝ) from ⟨hx, hxb⟩), _root_.add_zero]
      · have hne := hp b (by simp)
        have hbx : (b : ℝ) < x := lt_of_le_of_ne (le_of_not_gt hxb) (Ne.symm hne)
        rw [hg x hbx (fun q hq => hp q (by simp [hq])),
          Set.indicator_of_not_mem (fun hm : x ∈ Ioo (a : ℝ) (b : ℝ) => hxb hm.2), _root_.zero_add]
    · intro x hx
      beta_reduce
      rw [hz x (hx.trans (le_of_lt hab')),
        Set.indicator_of_not_mem (fun hm : x ∈ Ioo (a : ℝ) (b : ℝ) => not_lt.mpr hx hm.1),
        _root_.zero_add]
    · rw [integral_add ci hi, cv, hv, Rat.cast_add]

theorem polynomial_grid {f : ℝ → Option ℝ} {a : ℚ} {bs : List ℚ} {q : List ℚ} {w : ℚ}
    (hl : PolynomialOn (Region.before a).contains f q) (zl : polyZero q = true)
    (ht : PolynomialTail f a bs w)
    (hd : ProbeFacts (fun x => Value.Defined (f x)) ((a :: bs).map (fun q : ℚ => (q : ℝ)))) :
    partialIntegral volume f = some ((w : ℚ) : ℝ) := by
  obtain ⟨g, hg, hz, hi, hv⟩ := ht.integral
  have away : ∀ x : ℝ, (∀ p ∈ (a :: bs).map (fun q : ℚ => (q : ℝ)), x ≠ p) → f x = some (g x) := by
    intro x hp
    by_cases hx : x < a
    · rw [hl.equation x hx, polyEval_zero zl, hz x (le_of_lt hx)]
    · have hne : x ≠ (a : ℝ) := hp _ (by simp)
      exact hg x (lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hne))
        (fun p hp' => hp (p : ℝ) (List.mem_map_of_mem (f := fun q : ℚ => (q : ℝ))
          (List.mem_cons_of_mem a hp')))
  have total : ∀ x, Value.Defined (f x) := by
    intro x
    by_cases hx : x ∈ (a :: bs).map (fun q : ℚ => (q : ℝ))
    · exact hd.all x hx
    · exact ⟨g x, away x (fun p hp he => hx (he ▸ hp))⟩
  have he : (fun x => (f x).getD 0) =ᵐ[volume] g := by
    filter_upwards [ae_away ((a :: bs).map (fun q : ℚ => (q : ℝ)))] with x hx
    simp only [away x hx, Option.getD_some]
  rw [partialIntegral_valid volume f total ((integrable_congr he).mpr hi),
    integral_congr_ae he, hv]

end QSym.Distribution.StepSource

namespace QSym.Distribution.DensityProgram

theorem presentation_mass_polynomial (p : DensityProgram) {a : ℚ} {bs : List ℚ}
    {q : List ℚ} {v w : ℚ}
    (hl : StepSource.PolynomialOn (StepSource.Region.before a).contains p.density q) (zl : StepSource.polyZero q = true)
    (ht : StepSource.PolynomialTail p.density a bs w)
    (hd : StepSource.ProbeFacts (fun x => Value.Defined (p.density x))
      ((a :: bs).map (fun q : ℚ => (q : ℝ))))
    (hv : w = v) :
    massValue p.presentation = some (Numeric.denote (s := .real) v) := by
  subst hv
  rw [mass_bridge, DensityProgram.mass, Model.densityMassValue_eq]
  exact StepSource.polynomial_grid hl zl ht hd

end QSym.Distribution.DensityProgram
