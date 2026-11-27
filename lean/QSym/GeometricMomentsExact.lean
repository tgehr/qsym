import QSym.GeometricMoments

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

end QSym.GeometricMoments
