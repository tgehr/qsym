import QSym.GeometricMoments
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.Polynomial.Basic

/-! Symbolic rates for polynomial-geometric moments. A finite table of
integer equalities certifies the Newton coefficients of the source polynomial. -/
noncomputable section
namespace QSym.GeometricMoments.Newton
open Polynomial Distribution.StepSource Summation

private def choosePolynomial (k : ℕ) : SampledPolynomial where
  poly := C (k.factorial : ℝ)⁻¹ * descPochhammer ℝ k
  degree := k
  bounded := (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree ℝ k).le
  den := 1
  nonzero := by decide
  num n := n.choose k
  exact_num n := by simp [Nat.cast_choose_eq_descPochhammer_div ℝ, div_eq_mul_inv, mul_comm]

private def expansion : List ℚ → ℕ → SampledPolynomial
  | [], _ => .constant 0
  | c :: cs, k => ((SampledPolynomial.constant c).mul (choosePolynomial k)).add (expansion cs (k+1))

/-- Both sides of each sample are compared as integers, including when
the source and its expansion have different denominators. -/
private def sameSamples (p b : SampledPolynomial) : Bool :=
  (List.range (max p.degree b.degree + 1)).all
    (fun n => decide (p.num n * b.den = b.num n * p.den))

def checks (p : SampledPolynomial) (cs : List ℚ) : Bool := sameSamples p (expansion cs 0)

private theorem samples_equal {p b : SampledPolynomial} (h : sameSamples p b = true) :
    p.poly = b.poly := by
  change (List.range (max p.degree b.degree + 1)).all _ = true at h
  apply sub_eq_zero.mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p.poly-b.poly)
    (f := fun i : Fin (max p.degree b.degree + 1) => (i.val : ℝ))
  · intro i j he
    exact Fin.ext (Nat.cast_injective he)
  · intro i
    have e := of_decide_eq_true ((List.all_eq_true.mp h) i.val (List.mem_range.mpr i.isLt))
    have ec := congrArg (fun z : ℤ => (z : ℝ)) e
    push_cast at ec
    rw [p.exact_num, b.exact_num] at ec
    have hd : (p.den : ℝ) * b.den ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr p.nonzero) (Nat.cast_ne_zero.mpr b.nonzero)
    rw [eval_sub, sub_eq_zero]
    apply mul_left_cancel₀ hd
    linear_combination ec
  · simpa using Nat.lt_succ_of_le ((natDegree_sub_le _ _).trans (max_le_max p.bounded b.bounded))

private def horner : List ℚ → SampledPolynomial
  | [] => .constant 0
  | c :: cs => (SampledPolynomial.constant c).add (SampledPolynomial.index.mul (horner cs))

private def numerator : List ℚ → SampledPolynomial
  | [] => .constant 0
  | c :: cs =>
    let y := (SampledPolynomial.constant 1).add ((SampledPolynomial.constant (-1)).mul .index)
    ((SampledPolynomial.constant c).mul (y.pow cs.length)).add (SampledPolynomial.index.mul (numerator cs))

/-- Check the common numerator as a polynomial in the original ratio. -/
def numeratorChecks (cs ns : List ℚ) : Bool := sameSamples (numerator cs) (horner ns)

private theorem horner_eval (ns : List ℚ) (x : ℝ) : (horner ns).poly.eval x = polyEval ns x := by
  induction ns with
  | nil => simp [horner, SampledPolynomial.constant, polyEval]
  | cons n ns ih => simp [horner, SampledPolynomial.constant, SampledPolynomial.add,
      SampledPolynomial.mul, SampledPolynomial.index, polyEval, ih]

private theorem numerator_identity (cs : List ℚ) (r : ℝ) (ne : 1-r ≠ 0) :
    (numerator cs).poly.eval r * (1-r) = (1-r)^cs.length * polyEval cs (r / (1-r)) := by
  induction cs with
  | nil => simp [numerator, SampledPolynomial.constant, polyEval]
  | cons c cs ih =>
    simp only [numerator, SampledPolynomial.constant, SampledPolynomial.add,
      SampledPolynomial.mul, SampledPolynomial.pow, SampledPolynomial.index,
      eval_add, eval_mul, eval_pow, eval_C, eval_X, Rat.cast_one, Rat.cast_neg, neg_one_mul,
      ← sub_eq_add_neg, polyEval, List.length_cons, pow_succ]
    field_simp [ne]
    linear_combination r * (1-r) * ih

private theorem common_value {cs ns : List ℚ} (h : numeratorChecks cs ns = true)
    (r : ℝ) (ne : 1-r ≠ 0) :
    polyEval ns r * ((1-r)⁻¹)^cs.length = (1-r)⁻¹ * polyEval cs (r / (1-r)) := by
  have e := samples_equal h
  have hnum := numerator_identity cs r ne
  rw [e,horner_eval] at hnum
  field_simp [ne]
  linear_combination hnum

private theorem choose_sum {r : ℝ} (hr : ‖r‖ < 1) (k : ℕ) :
    HasSum (fun n : ℕ => (n.choose k : ℝ) * r^n) (r^k / (1-r)^(k+1)) := by
  have tail := (hasSum_choose_mul_geometric_of_norm_lt_one k hr).mul_right (r^k)
  have initial : ∑ i ∈ Finset.range k, (i.choose k : ℝ) * r^i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi; simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
  apply (hasSum_nat_add_iff' k).mp
  rw [initial, sub_zero]
  simpa [pow_add, mul_assoc, div_eq_mul_inv, mul_comm, mul_left_comm] using tail

private theorem expansion_sum {r : ℝ} (hr : ‖r‖ < 1) (cs : List ℚ) (k : ℕ) :
    HasSum (fun n : ℕ => (expansion cs k).poly.eval (n : ℝ) * r^n)
      (r^k / (1-r)^(k+1) * polyEval cs (r / (1-r))) := by
  have ne : 1-r ≠ 0 := by
    intro e; have : r=1 := by linarith
    simp [this] at hr
  induction cs generalizing k with
  | nil => simp [expansion, SampledPolynomial.constant, polyEval, hasSum_zero]
  | cons c cs ih =>
    have hc := (choose_sum hr k).mul_left (c : ℝ)
    convert hc.add (ih (k+1)) using 1
    · funext n
      simp [expansion, SampledPolynomial.add, SampledPolynomial.mul, SampledPolynomial.constant,
        choosePolynomial, Nat.cast_choose_eq_descPochhammer_div ℝ, div_eq_mul_inv]
      ring
    · simp only [polyEval, pow_succ]
      field_simp
      ring

private theorem positive_degree (p : SampledPolynomial) (w : ℕ) (h : p.num 0 ≠ p.num w) :
    0 < p.poly.degree := by
  by_contra! d
  have e := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr d)
  have h0 := p.exact_num 0
  have hw := p.exact_num w
  rw [e, eval_C] at h0 hw
  apply h
  exact_mod_cast h0.trans hw.symm

private theorem divergent (p : SampledPolynomial) (hp : 0 < p.poly.degree) (r : ℝ) (hr : ¬‖r‖ < 1) :
    ¬ Summable (fun n : ℕ => ‖p.poly.eval (n : ℝ) * r^n‖) := by
  intro hs; apply hr
  apply summable_geometric_iff_norm_lt_one.mp
  apply Summable.of_norm_bounded_eventually_nat _ hs
  have growth := (p.poly.abs_tendsto_atTop hp).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [growth.eventually_ge_atTop 1] with n hn
  rw [norm_mul, Real.norm_eq_abs (p.poly.eval _)]
  exact le_mul_of_one_le_left (norm_nonneg _) hn

/-- A single nonzero sample rules out absolute summability of an unweighted
polynomial on all naturals. A nonconstant polynomial eventually dominates
one in magnitude. A nonzero constant gives a divergent constant series. -/
theorem not_summable (p : SampledPolynomial) (w : ℕ) (hn : p.num w ≠ 0) :
    ¬ Summable (fun n : ℕ => |p.poly.eval (n : ℝ)|) := by
  by_cases hd : 0 < p.poly.degree
  · simpa only [one_pow, mul_one, Real.norm_eq_abs] using divergent p hd 1 (by norm_num)
  · have hc := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_not_gt hd))
    have nz : p.poly.coeff 0 ≠ 0 := by
      intro z
      have e := p.exact_num w
      rw [hc, eval_C, z, mul_zero] at e
      exact hn (by exact_mod_cast e)
    rw [hc]
    simpa only [eval_C, summable_const_iff] using (abs_ne_zero.mpr nz)

def constantChecks (p : SampledPolynomial) (c : ℚ) : Bool := sameSamples p (.constant c)

theorem constant_rows {p : SampledPolynomial} {f : ℕ → Option ℝ} (ht : NatTest f p)
    (c : ℚ) (h : constantChecks p c = true) (v : Option ℝ) (hv : v = some (c : ℝ)) :
    f = (fun _ => v) := by
  funext n
  rw [ht n, samples_equal (b := .constant c) h, hv]
  simp [SampledPolynomial.constant]

theorem plain_nonzero {p : SampledPolynomial} {f : ℕ → Option ℝ} (ht : NatTest f p)
    (w : ℕ) (hn : p.num w ≠ 0) : value norm (some f) = none := by
  rw [funext ht]
  simp [value, Real.norm_eq_abs, not_summable p w hn]

theorem plain_zero {p : SampledPolynomial} {f : ℕ → Option ℝ} (ht : NatTest f p)
    (h : constantChecks p 0 = true) (z : Option ℝ) (hz : z = some 0) : value norm (some f) = z := by
  rw [constant_rows ht 0 h z (by simpa using hz), hz]
  exact zero norm norm_zero

theorem constant_factor {p : SampledPolynomial} {f : ℕ → Option ℝ} (ht : NatTest f p)
    (c : ℚ) (h : constantChecks p c = true) (v : Option ℝ) (hv : v = some (c : ℝ))
    (left : Bool) (g : ℕ → Option ℝ) :
    value norm (some (fun n => if left then Value.mul (f n) (g n) else Value.mul (g n) (f n))) =
      value norm (some (fun n => if left then Value.mul v (g n) else Value.mul (g n) v)) := by
  rw [constant_rows ht c h v hv]

/-- Horner evaluation is only inspected on the convergence domain. The
certificate can use scalar literals from the exported source expression. -/
def At (x : Option ℝ) (cs : List ℚ) (v : Option ℝ) : Prop :=
  ∀ u, x = some u → v = some (polyEval cs u)

theorem At.last (x : Option ℝ) {c : ℚ} {v : Option ℝ} (h : v = some (c : ℝ)) : At x [c] v := by
  intro u _; simpa [polyEval] using h

theorem At.step {x v t : Option ℝ} {c : ℚ} {cs : List ℚ} (h : v = some (c : ℝ)) (ht : At x cs t) :
    At x (c :: cs) (Value.add v (Value.mul x t)) := by
  intro u hu; rw [h, ht u hu, hu]; rfl

private def inverse (r one minus : Option ℝ) := Value.inv (Value.add one (Value.mul minus r))

private theorem evaluate {p : SampledPolynomial} {cs ns : List ℚ} (w : ℕ) (h : checks p cs = true)
    (hnum : numeratorChecks cs ns = true)
    (hn : p.num 0 ≠ p.num w) (r one minus answer : Option ℝ) (h1 : one = some 1) (hm : minus = some (-1))
    (ha : At r ns answer) (row : ℕ → Option ℝ)
    (he : ∀ n, row n = r.map (fun q => p.poly.eval (n : ℝ) * q^n)) :
    value norm (some row) = Binding.guardValue (Value.lt (Value.abs r) one)
      (Value.mul ((inverse r one minus).map (fun t => t^cs.length)) answer) := by
  subst one minus
  cases r with
  | none => exact undefined_term _ _ 0 (he 0)
  | some r =>
    rw [funext he]
    change value norm (some (fun n : ℕ => some (p.poly.eval (n : ℝ) * r^n))) = _
    by_cases hr : ‖r‖ < 1
    · have ne : 1-r ≠ 0 := by
        intro e
        have : r = 1 := by linarith
        simp [this] at hr
      have hi : inverse (some r) (some 1) (some (-1)) = some (1-r)⁻¹ := by
        simp [inverse, Value.inv, Value.add, Value.mul, ← sub_eq_add_neg, ne]
      have hv := ha r rfl
      have hs : HasSum (fun n : ℕ => p.poly.eval (n : ℝ) * r^n)
          ((1-r)⁻¹ * polyEval cs (r / (1-r))) := by
        rw [samples_equal (b := expansion cs 0) h]
        simpa using expansion_sum hr cs 0
      rw [of_hasSum _ _ _ _ (fun _ => rfl) hs.summable.norm hs, hi, hv]
      simp [Value.abs, Value.lt, Value.mul, Binding.guardValue, ← Real.norm_eq_abs, hr]
      simpa only [inv_pow] using (common_value hnum r ne).symm.trans (mul_comm ..)
    · have diverges := divergent p (positive_degree p w hn) r hr
      simp only [Real.norm_eq_abs] at hr diverges
      simp [value, Real.norm_eq_abs, diverges, Value.abs, Value.lt, Binding.guardValue, hr]

theorem powerR (r : Option ℝ) (n : ℕ) :
    Functions.powRN.apply r (some n) = r.map (fun q => q^n) := by
  cases r <;> simp [Functions.powRN, Function2.apply]

theorem powerQR (r : Option ℚ) (n : ℕ) :
    Functions.castQR.apply (Functions.powQN.apply r (some n)) =
      (Functions.castQR.apply r).map (fun q => q^n) := by
  cases r <;> simp [Functions.castQR, Functions.powQN, Function1.apply, Function2.apply]

theorem series {test power : ℕ → Option ℝ} {p : SampledPolynomial} {r : Option ℝ}
    (ht : NatTest test p) (hp : ∀ n, power n = r.map (fun q => q^n)) (left : Bool)
    (cs ns : List ℚ) (w : ℕ) (h : checks p cs = true) (hnum : numeratorChecks cs ns = true) (hn : p.num 0 ≠ p.num w)
    (one minus : Option ℝ) {answer : Option ℝ} (h1 : one = some 1) (hm : minus = some (-1))
    (ha : At r ns answer) :
    value norm (some (fun n => if left then Value.mul (test n) (power n) else Value.mul (power n) (test n))) =
      Binding.guardValue (Value.lt (Value.abs r) one) (Value.mul ((inverse r one minus).map (fun t => t^cs.length)) answer) := by
  apply evaluate w h hnum hn r one minus answer h1 hm ha
  intro n; rw [ht n, hp n]
  cases left <;> cases r <;> simp [Value.mul, mul_comm]

/-- Evaluate sparse Horner expressions directly in their printed order. -/
theorem At.index (x : Option ℝ) : At x [0,1] x := by
  intro u hu; simp [hu, polyEval]

theorem At.monic (x : Option ℝ) {c : ℚ} {v : Option ℝ} (hc : v = some (c : ℝ)) :
    At x [c,1] (Value.add x v) := by
  intro u hu; simp [hu, hc, Value.add, polyEval, _root_.add_comm]

theorem At.linear (x : Option ℝ) {c d : ℚ} {v w : Option ℝ} (hc : v = some (c : ℝ)) (hd : w = some (d : ℝ)) :
    At x [c,d] (Value.add (Value.mul w x) v) := by
  intro u hu; simp [hu, hc, hd, Value.add, Value.mul, polyEval, _root_.add_comm, mul_comm]

theorem At.scale (x : Option ℝ) {d : ℚ} {w : Option ℝ} (hd : w = some (d : ℝ)) :
    At x [0,d] (Value.mul w x) := by
  intro u hu; simp [hu, hd, Value.mul, polyEval, mul_comm]

theorem At.skip_zero {x v : Option ℝ} {cs : List ℚ} (ht : At x cs v) :
    At x (0::cs) (Value.mul x v) := by
  intro u hu; simp [ht u hu, hu, Value.mul, polyEval]

theorem At.append_constant {x v t : Option ℝ} {c : ℚ} {cs : List ℚ} (hc : v = some (c : ℝ)) (ht : At x cs t) :
    At x (c::cs) (Value.add (Value.mul x t) v) := by
  intro u hu; simp [ht u hu, hu, hc, Value.add, Value.mul, polyEval, _root_.add_comm]

private def interval (r one minus : Option ℝ) : Option Bool :=
  Value.and (Value.lt minus r) (Value.lt r one)

private def denominatorPower (r one minus : Option ℝ) (k : ℕ) : Option ℝ :=
  (Value.add one (Value.mul r minus)).map (fun d => d^k)

private theorem fraction_form (r one minus num : Option ℝ) (k : ℕ) (h1 : one = some 1) (hm : minus = some (-1)) :
    Binding.guardValue (Value.lt (Value.abs r) one) (Value.mul ((inverse r one minus).map (fun t => t^k)) num) =
    Binding.guardValue (interval r one minus) (Value.mul num (Value.inv (denominatorPower r one minus k))) := by
  subst one minus
  cases r with
  | none => rfl
  | some r =>
    by_cases lo : -1 < r <;> by_cases hi : r < 1
    · have nz : -r+1 ≠ 0 := by linarith
      have nz' : 1 + -r ≠ 0 := by linarith
      cases num <;> simp [interval, inverse, denominatorPower, abs_lt, lo, hi, nz, nz', pow_ne_zero _ nz,
        Value.lt, Value.and, Value.abs, Value.add, Value.mul, Value.inv, Binding.guardValue, _root_.add_comm, mul_comm]
    all_goals simp [interval, abs_lt, lo, hi, Value.abs, Value.lt, Value.and, Binding.guardValue]

theorem series_fraction {test power : ℕ → Option ℝ} {p : SampledPolynomial} {r : Option ℝ}
    (ht : NatTest test p) (hp : ∀ n, power n = r.map (fun q => q^n)) (left : Bool)
    (cs ns : List ℚ) (w : ℕ) (h : checks p cs = true) (hnum : numeratorChecks cs ns = true) (hn : p.num 0 ≠ p.num w)
    (one minus : Option ℝ) {answer : Option ℝ} (h1 : one = some 1) (hm : minus = some (-1)) (ha : At r ns answer) :
    value norm (some (fun n => if left then Value.mul (test n) (power n) else Value.mul (power n) (test n))) =
      Binding.guardValue (interval r one minus) (Value.mul answer (Value.inv (denominatorPower r one minus cs.length))) :=
  (series ht hp left cs ns w h hnum hn one minus h1 hm ha).trans (fraction_form r one minus answer _ h1 hm)

end QSym.GeometricMoments.Newton
