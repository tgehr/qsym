import QSym.GeometricMomentsNewton

/-! Certificates for polynomial probes computed in the exact scalar types
before they are promoted to a real distribution weight. -/
noncomputable section
namespace QSym.GeometricMoments

inductive ExactScalar where
  | natural | integer | rational

def ExactScalar.carrier : ExactScalar → Type
  | .natural => ℕ
  | .integer => ℤ
  | .rational => ℚ

def ExactScalar.embed : (s : ExactScalar) → Option s.carrier → Option ℝ
  | .natural, x => Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply x))
  | .integer, x => Functions.castQR.apply (Functions.castZQ.apply x)
  | .rational, x => Functions.castQR.apply x

def ExactScalar.add : (s : ExactScalar) → Option s.carrier → Option s.carrier → Option s.carrier
  | .natural => Functions.addN.apply
  | .integer => Functions.addZ.apply
  | .rational => Functions.addQ.apply

def ExactScalar.mul : (s : ExactScalar) → Option s.carrier → Option s.carrier → Option s.carrier
  | .natural => Functions.mulN.apply
  | .integer => Functions.mulZ.apply
  | .rational => Functions.mulQ.apply

def ExactScalar.pow : (s : ExactScalar) → ℕ → Option s.carrier → Option s.carrier
  | .natural, k, x => x.map (fun a : ℕ => a ^ k)
  | .integer, k, x => x.map (fun a : ℤ => a ^ k)
  | .rational, k, x => x.map (fun a : ℚ => a ^ k)

private theorem ExactScalar.embed_add (s : ExactScalar) (a b : Option s.carrier) :
    s.embed (s.add a b) = Value.add (s.embed a) (s.embed b) := by
  cases s <;> cases a <;> cases b <;>
    simp [ExactScalar.add, ExactScalar.embed, Value.add, Functions.addN, Functions.addZ, Functions.addQ,
      Functions.castQR, Functions.castZQ, Functions.castNZ, Function1.apply, Function2.apply]

private theorem ExactScalar.embed_mul (s : ExactScalar) (a b : Option s.carrier) :
    s.embed (s.mul a b) = Value.mul (s.embed a) (s.embed b) := by
  cases s <;> cases a <;> cases b <;>
    simp [ExactScalar.mul, ExactScalar.embed, Value.mul, Functions.mulN, Functions.mulZ, Functions.mulQ,
      Functions.castQR, Functions.castZQ, Functions.castNZ, Function1.apply, Function2.apply]

private theorem ExactScalar.embed_pow (s : ExactScalar) (k : ℕ) (a : Option s.carrier) :
    s.embed (s.pow k a) = (s.embed a).map (· ^ k) := by
  cases s <;> cases a <;>
    simp [ExactScalar.pow, ExactScalar.embed, Functions.castQR, Functions.castZQ, Functions.castNZ, Function1.apply]

def ExactTest (s : ExactScalar) (f : ℕ → Option s.carrier) (p : SampledPolynomial) : Prop :=
  NatTest (fun n => s.embed (f n)) p

theorem ExactTest.index : ExactTest .natural (fun n => some n) .index := NatTest.index

theorem ExactTest.constantN (v : Option ℕ) (k : ℕ) (h : v = some k) :
    ExactTest .natural (fun _ => v) (.constant (k : ℚ)) := by
  apply NatTest.constant; simp [h, ExactScalar.embed, Functions.castQR, Functions.castZQ, Functions.castNZ, Function1.apply]

theorem ExactTest.constantZ (v : Option ℤ) (k : ℤ) (h : v = some k) :
    ExactTest .integer (fun _ => v) (.constant (k : ℚ)) := by
  apply NatTest.constant; simp [h, ExactScalar.embed, Functions.castQR, Functions.castZQ, Function1.apply]

theorem ExactTest.constantQ (v : Option ℚ) (k : ℚ) (h : v = some k) :
    ExactTest .rational (fun _ => v) (.constant k) := by
  apply NatTest.constant; simp [h, ExactScalar.embed, Functions.castQR, Function1.apply]

theorem ExactTest.add (s : ExactScalar) {f g : ℕ → Option s.carrier} {p q : SampledPolynomial}
    (hf : ExactTest s f p) (hg : ExactTest s g q) :
    ExactTest s (fun n => s.add (f n) (g n)) (p.add q) := by
  intro n
  change s.embed (s.add (f n) (g n)) = _
  rw [s.embed_add]; exact NatTest.add hf hg n

theorem ExactTest.mul (s : ExactScalar) {f g : ℕ → Option s.carrier} {p q : SampledPolynomial}
    (hf : ExactTest s f p) (hg : ExactTest s g q) :
    ExactTest s (fun n => s.mul (f n) (g n)) (p.mul q) := by
  intro n
  change s.embed (s.mul (f n) (g n)) = _
  rw [s.embed_mul]; exact NatTest.mul hf hg n

theorem ExactTest.pow (s : ExactScalar) (k : ℕ) {f : ℕ → Option s.carrier} {p : SampledPolynomial}
    (hf : ExactTest s f p) : ExactTest s (fun n => s.pow k (f n)) (p.pow k) := by
  intro n
  change s.embed (s.pow k (f n)) = _
  rw [s.embed_pow]; exact NatTest.pow k hf n

/-- qsym uses the natural value itself as weight for a natural sum. Integer
and rational sums use their native norm. All three agree with the magnitude
of a present real embedding. -/
private def ExactScalar.weight : (s : ExactScalar) → s.carrier → ℝ
  | .natural => fun n : ℕ => (n : ℝ)
  | .integer => fun z : ℤ => ‖z‖
  | .rational => fun q : ℚ => ‖q‖

def ExactScalar.zero : (s : ExactScalar) → s.carrier
  | .natural => (0 : ℕ)
  | .integer => (0 : ℤ)
  | .rational => (0 : ℚ)

def ExactScalar.sum : (s : ExactScalar) → Option (ℕ → Option s.carrier) → Option s.carrier
  | .natural => Summation.value (α := ℕ) (ι := ℕ) (fun n => (n : ℝ))
  | .integer => Summation.value (α := ℤ) (ι := ℕ) norm
  | .rational => Summation.value (α := ℚ) (ι := ℕ) norm

private theorem ExactScalar.weight_embed (s : ExactScalar) (x : Option s.carrier) (v : ℝ)
    (h : s.embed x = some v) : s.weight (x.getD s.zero) = |v| := by
  cases s <;> cases x <;> simp [ExactScalar.embed, Functions.castQR, Functions.castZQ, Functions.castNZ, Function1.apply] at h
  all_goals rw [← h]; simp [ExactScalar.weight, ← Real.norm_eq_abs, Int.norm_cast_real, Rat.norm_cast_real]

private theorem ExactScalar.reflect_zero (s : ExactScalar) (x : Option s.carrier)
    (h : s.embed x = some 0) : x = some s.zero := by
  cases s <;> cases x <;> simp_all [ExactScalar.embed, ExactScalar.zero, Functions.castQR, Functions.castZQ,
    Functions.castNZ, Function1.apply]

theorem ExactTest.sum_nonzero (s : ExactScalar) {f : ℕ → Option s.carrier} {p : SampledPolynomial}
    (hf : ExactTest s f p) (w : ℕ) (hn : p.num w ≠ 0) : s.sum (some f) = none := by
  have e : (fun n => s.weight ((f n).getD s.zero)) = (fun n : ℕ => |p.poly.eval (n : ℝ)|) :=
    funext (fun n => s.weight_embed _ _ (hf n))
  have no : ¬ Summable (fun n => s.weight ((f n).getD s.zero)) := by rw [e]; exact Newton.not_summable p w hn
  cases s <;> exact if_neg (fun h => no h.2.1)

theorem ExactTest.sum_zero (s : ExactScalar) {f : ℕ → Option s.carrier} {p : SampledPolynomial}
    (hf : ExactTest s f p) (h : Newton.constantChecks p 0 = true)
    (z : Option s.carrier) (hz : z = some s.zero) : s.sum (some f) = z := by
  have he := Newton.constant_rows hf 0 h (some 0) (by simp)
  have entire : f = (fun _ => some s.zero) := funext (fun n => s.reflect_zero _ (congrFun he n))
  rw [entire, hz]
  cases s
  · exact Summation.zero _ (by simp)
  · exact Summation.zero norm norm_zero
  · exact Summation.zero norm norm_zero

end QSym.GeometricMoments
