import QSym.Limit
import QSym.DistributionPolynomialGrid
import QSym.Numeric
import Mathlib.Analysis.Polynomial.Basic

/-! Limits at infinity of quotients of polynomials with rational coefficients.
Where the denominator has at least the degree of the numerator, the quotient
tends at both ends to the quotient of the coefficients of that degree. -/
namespace QSym.Limit
open Filter Topology Polynomial
open QSym.Distribution.StepSource

/-- The polynomial with these coefficients. -/
noncomputable def toPoly : List ℚ → ℝ[X]
  | [] => 0
  | c :: p => C (c : ℝ) + X * toPoly p

theorem eval_toPoly (p : List ℚ) (x : ℝ) : (toPoly p).eval x = polyEval p x := by
  induction p with
  | nil => simp [toPoly, polyEval]
  | cons c p ih => simp [toPoly, polyEval, ih]

theorem coeff_toPoly (p : List ℚ) (k : ℕ) : (toPoly p).coeff k = ((p.getD k 0 : ℚ) : ℝ) := by
  induction p generalizing k with
  | nil => simp [toPoly]
  | cons c p ih =>
    cases k with
    | zero => simp [toPoly]
    | succ k => simp [toPoly, ih, coeff_C_succ]

theorem polyZero_iff (p : List ℚ) : polyZero p = true ↔ ∀ k, p.getD k 0 = 0 := by
  induction p with
  | nil => simp [polyZero]
  | cons c p ih =>
    simp only [polyZero, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hc, hp⟩ k
      cases k with
      | zero => simpa using hc
      | succ k => simpa using hp k
    · intro h
      exact ⟨by simpa using h 0, fun k => by simpa using h (k + 1)⟩

theorem toPoly_ne_zero {c : List ℚ} (h : polyZero c = false) : toPoly c ≠ 0 := by
  intro hz
  have : polyZero c = true := (polyZero_iff c).2 fun k => by
    have hk := coeff_toPoly c k
    rw [hz, coeff_zero] at hk
    exact_mod_cast hk.symm
  rw [this] at h
  cases h

theorem natDegree_toPoly_le {p : List ℚ} {b : ℕ} (h : polyZero (p.drop (b + 1)) = true) :
    (toPoly p).natDegree ≤ b := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPoly]
  have hk := (polyZero_iff _).1 h (N - (b + 1))
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop] at hk
  rw [List.getD_eq_getElem?_getD]
  have he : b + 1 + (N - (b + 1)) = N := by omega
  rw [he] at hk
  exact_mod_cast hk

private theorem ratio_atTop (P Q : ℝ[X]) (b : ℕ) (hQ : Q.natDegree ≤ b) (hQb : Q.coeff b ≠ 0)
    (hP : P.natDegree ≤ b) :
    Tendsto (fun x => eval x P / eval x Q) atTop (𝓝 (P.coeff b / Q.coeff b)) := by
  have hQn : Q.natDegree = b := le_antisymm hQ (le_natDegree_of_ne_zero hQb)
  have hQ0 : Q ≠ 0 := fun h => hQb (by rw [h, coeff_zero])
  have hQd : Q.degree = b := by rw [degree_eq_natDegree hQ0, hQn]
  by_cases h : P.coeff b = 0
  · have hlt : P.degree < Q.degree := by
      rw [hQd, degree_lt_iff_coeff_zero]
      intro m hm
      rcases Nat.eq_or_lt_of_le hm with rfl | hm
      · exact h
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hm)
    rw [h, zero_div]
    exact div_tendsto_zero_of_degree_lt P Q hlt
  · have hPn : P.natDegree = b := le_antisymm hP (le_natDegree_of_ne_zero h)
    have hP0 : P ≠ 0 := fun h0 => h (by rw [h0, coeff_zero])
    have heq : P.degree = Q.degree := by rw [hQd, degree_eq_natDegree hP0, hPn]
    have ht := div_tendsto_leadingCoeff_div_of_degree_eq P Q heq
    rwa [leadingCoeff, leadingCoeff, hPn, hQn] at ht

private theorem coeff_reflect (P : ℝ[X]) (b : ℕ) (hP : P.natDegree ≤ b) :
    (P.comp (-X)).coeff b = (-1) ^ b * P.coeff b := by
  have hn : (P.comp (-X)).natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one]
  rcases Nat.eq_or_lt_of_le hP with h | h
  · have hl := comp_neg_X_leadingCoeff_eq P
    rw [leadingCoeff, leadingCoeff, hn, h] at hl
    exact hl
  · rw [coeff_eq_zero_of_natDegree_lt (hn ▸ h), coeff_eq_zero_of_natDegree_lt h, mul_zero]

private theorem ratio_atBot (P Q : ℝ[X]) (b : ℕ) (hQ : Q.natDegree ≤ b) (hQb : Q.coeff b ≠ 0)
    (hP : P.natDegree ≤ b) :
    Tendsto (fun x => eval x P / eval x Q) atBot (𝓝 (P.coeff b / Q.coeff b)) := by
  have hn : ∀ R : ℝ[X], (R.comp (-X)).natDegree = R.natDegree := fun R => by
    rw [natDegree_comp, natDegree_neg, natDegree_X, mul_one]
  have hs : ((-1 : ℝ) ^ b) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h := ratio_atTop (P.comp (-X)) (Q.comp (-X)) b (by rw [hn]; exact hQ)
    (by rw [coeff_reflect Q b hQ]; exact mul_ne_zero hs hQb) (by rw [hn]; exact hP)
  rw [coeff_reflect P b hP, coeff_reflect Q b hQ, mul_div_mul_left _ _ hs] at h
  refine (h.comp tendsto_neg_atBot_atTop).congr fun x => ?_
  simp [eval_comp]

/-- The two ends of the real line. -/
inductive Infinite : Filter ℝ → Prop
  | top : Infinite atTop
  | bottom : Infinite atBot

theorem Infinite.le_cofinite {l : Filter ℝ} (h : Infinite l) : l ≤ cofinite := by
  cases h
  · exact atTop_le_cofinite
  · exact atBot_le_cofinite

/-- Away from the roots of `c` the function is the quotient of two
polynomials, and the denominator has no other roots. -/
structure Quotient (v : ℝ → Option ℝ) (n d c : List ℚ) : Prop where
  equation : ∀ x, polyEval c x ≠ 0 → v x = some (polyEval n x / polyEval d x)
  defined : ∀ x, polyEval c x ≠ 0 → polyEval d x ≠ 0

theorem quotient_polynomial {v : ℝ → Option ℝ} {p : List ℚ}
    (h : PolynomialOn (fun _ => True) v p) : Quotient v p [1] [1] :=
  ⟨fun x _ => by rw [h.equation x trivial]; simp [polyEval], fun x _ => by simp [polyEval]⟩

theorem quotient_inv {v : ℝ → Option ℝ} {n d c : List ℚ} (h : Quotient v n d c) :
    Quotient (fun x => Value.inv (v x)) d n (polyMul c n) := by
  constructor
  · intro x hx
    rw [polyEval_mul] at hx
    have hc := left_ne_zero_of_mul hx
    have hn := right_ne_zero_of_mul hx
    have hd := h.defined x hc
    show Value.inv (v x) = _
    rw [h.equation x hc]
    simp [Value.inv, hn, hd]
  · intro x hx
    rw [polyEval_mul] at hx
    exact right_ne_zero_of_mul hx

theorem quotient_mul {v w : ℝ → Option ℝ} {n d c n' d' c' : List ℚ} (hv : Quotient v n d c)
    (hw : Quotient w n' d' c') :
    Quotient (fun x => Value.mul (v x) (w x)) (polyMul n n') (polyMul d d') (polyMul c c') := by
  constructor
  · intro x hx
    rw [polyEval_mul] at hx
    have hc := left_ne_zero_of_mul hx
    have hc' := right_ne_zero_of_mul hx
    show Value.mul (v x) (w x) = _
    rw [hv.equation x hc, hw.equation x hc']
    simp only [Value.mul, polyEval_mul, Option.some.injEq]
    rw [div_mul_div_comm]
  · intro x hx
    rw [polyEval_mul] at hx ⊢
    exact mul_ne_zero (hv.defined x (left_ne_zero_of_mul hx)) (hw.defined x (right_ne_zero_of_mul hx))

theorem quotient_pow {v : ℝ → Option ℝ} {n d c : List ℚ} (k : ℕ) (h : Quotient v n d c) :
    Quotient (fun x => (v x).map (fun y : ℝ => y ^ k)) (polyPow n k) (polyPow d k) c := by
  constructor
  · intro x hx
    show (v x).map (fun y : ℝ => y ^ k) = _
    rw [h.equation x hx]
    simp [polyEval_pow, div_pow]
  · intro x hx
    rw [polyEval_pow]
    exact pow_ne_zero _ (h.defined x hx)

/-- The check of a limit: the denominator has degree `b`, the numerator at
most `b`, the function is the quotient except at finitely many points, and
`q` is the quotient of the coefficients of degree `b`. -/
def quotientLimit (n d c : List ℚ) (b : ℕ) (q : ℚ) : Bool :=
  !polyZero c && polyZero (d.drop (b + 1)) && polyZero (n.drop (b + 1)) &&
    decide (d.getD b 0 ≠ 0) && decide (q * d.getD b 0 = n.getD b 0)

theorem Exact.quotient {l : Filter ℝ} (hl : Infinite l) {v : ℝ → Option ℝ} {n d c : List ℚ}
    (hv : Quotient v n d c) (b : ℕ) (q : ℚ) (h : quotientLimit n d c b q = true)
    {z : Option ℝ} (hz : z = some (Numeric.denote (s := .real) q)) : Exact l v z := by
  simp only [quotientLimit, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hc, hd⟩, hn⟩, hb⟩, hq⟩ := h
  have hroots : ∀ᶠ x in l, polyEval c x ≠ 0 := by
    have hfin := finite_setOf_isRoot (toPoly_ne_zero hc)
    have hr : ∀ᶠ x in l, ¬(toPoly c).IsRoot x := hl.le_cofinite hfin.compl_mem_cofinite
    refine hr.mono fun x hx => ?_
    simpa [IsRoot, eval_toPoly] using hx
  have hbR : (toPoly d).coeff b ≠ 0 := by
    rw [coeff_toPoly]; exact_mod_cast hb
  have hlim : Tendsto (fun x => polyEval n x / polyEval d x) l
      (𝓝 ((toPoly n).coeff b / (toPoly d).coeff b)) := by
    have he : (fun x => polyEval n x / polyEval d x) =
        fun x => eval x (toPoly n) / eval x (toPoly d) := by
      funext x; rw [eval_toPoly, eval_toPoly]
    rw [he]
    cases hl
    · exact ratio_atTop _ _ b (natDegree_toPoly_le hd) hbR (natDegree_toPoly_le hn)
    · exact ratio_atBot _ _ b (natDegree_toPoly_le hd) hbR (natDegree_toPoly_le hn)
  have hval : (toPoly n).coeff b / (toPoly d).coeff b = (q : ℝ) := by
    rw [coeff_toPoly, coeff_toPoly, div_eq_iff (by exact_mod_cast hb)]
    exact_mod_cast hq.symm
  have hz' : z = some (q : ℝ) := by rw [hz]; simp [Numeric.denote]
  rw [hz']
  rw [hval] at hlim
  exact ⟨_, hroots.mono fun x hx => hv.equation x hx, hlim⟩

end QSym.Limit
