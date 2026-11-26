import QSym.DistributionAtomicShift
import QSym.GeometricMoments

/-! Compact scalar certificates for every polynomial moment of a contracting
natural-counter distribution. -/
noncomputable section
namespace QSym.Distribution.Atomic
open StepSource GeometricMoments

theorem nat_shift_polynomial (weighted left : Bool) (stride : ℕ) (hk : 0 < stride) (w q : ℚ)
    (hw : 0 ≤ w) (hq : 0 ≤ q) (converges : |q| < 1)
    {p r : Option ℝ} (hp : p = some (w : ℝ)) (hr : r = some (q : ℝ)) (a : ℕ)
    {start : Option ℕ} (ha : start = some a) {f : D ℕ → Option (D ℕ)}
    (body : ∀ d, f d = shiftBody weighted left p r start stride d)
    {test : ℕ → Option ℝ} {cs : SampledPolynomial} (source : NatTest test cs)
    (primitive : List ℚ) (z : ℚ)
    (check : checks cs primitive q (if weighted then w else 1) a stride = true)
    (answer : -primitive.headD 0 = z) {result : Option ℝ} (out : result = some (z : ℝ)) :
    massValue (weightValue (some test) (fixedValue (some f))) = result := by
  subst start p r result
  rw [(CountableObservation.mass.weight (some test)).nat_shift weighted left stride hk w q hw hq rfl rfl (some a)
    (index := fun i => some (a+i*stride)) (fun _ => rfl) body (fun _ => rfl)]
  apply GeometricMoments.evaluate cs primitive q _ z a stride converges check answer
  intro n
  simp only [shiftObservation, mass_weight_diracValue, Option.bind, source (a+n*stride)]
  cases weighted <;> simp [Functions.powRN, Function2.apply, Value.mul, polyEval, Nat.cast_add, Nat.cast_mul] <;> ring

end QSym.Distribution.Atomic
