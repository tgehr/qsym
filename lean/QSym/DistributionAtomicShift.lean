import QSym.DistributionAtomicTransport
import QSym.SummationLinearity

/-! Source certificates for an atomic fixed point that shifts each recursively
emitted natural by a positive stride. The starting point may be partial. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal Classical

def shiftEmission (weighted : Bool) (p : Option ℝ) (a : Option ℕ) : Option (D ℕ) :=
  if weighted then scaleValue p (diracValue a) else diracValue a

def shiftKernel (left : Bool) (stride i : ℕ) : Option (D ℕ) := diracValue
  (if left then Functions.addN.apply (some stride) (some i) else Functions.addN.apply (some i) (some stride))

def shiftBody (weighted left : Bool) (p r : Option ℝ) (a : Option ℕ) (stride : ℕ) (d : D ℕ) :=
  addValue (shiftEmission weighted p a) (scaleValue r (bindValue (some d) (some (shiftKernel left stride))))

def ShiftIndex (a : Option ℕ) (stride : ℕ) (index : ℕ → Option ℕ) : Prop :=
  ∀ i, index i = a.map (fun v => v+i*stride)

theorem ShiftIndex.add_mul (a : Option ℕ) (k : ℕ) : ShiftIndex a k (fun i =>
    Functions.addN.apply a (Functions.mulN.apply (some i) (some k))) := by
  intro i; cases a <;> simp [Functions.addN, Functions.mulN, Function2.apply]

theorem ShiftIndex.add (a : Option ℕ) : ShiftIndex a 1 (fun i => Functions.addN.apply a (some i)) := by
  intro i; cases a <;> simp [Functions.addN, Function2.apply]

theorem ShiftIndex.mul (k : ℕ) : ShiftIndex (some 0) k (fun i => Functions.mulN.apply (some i) (some k)) := by
  intro i; simp [Functions.mulN, Function2.apply]

theorem ShiftIndex.self : ShiftIndex (some 0) 1 some := by intro i; simp

def shiftObservation (o : Option (D ℕ) → Option ℝ) (weighted : Bool) (p r : Option ℝ) (index : ℕ → Option ℕ) (i : ℕ) :=
  Value.mul (if weighted then Value.mul p (Functions.powRN.apply r (some i)) else Functions.powRN.apply r (some i))
    (o (diracValue (index i)))

private theorem iterate_shift (k n a : ℕ) : (fun i => i+k)^[n] a = a+n*k := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih, Nat.add_mul, Nat.add_assoc]

theorem CountableObservation.nat_shift_real {o : Option (D ℕ) → Option ℝ} (ho : CountableObservation o)
    (weighted left : Bool) (stride : ℕ) (hk : 0 < stride) (w q : ℝ) (hw : 0 ≤ w) (hq : 0 ≤ q)
    {p r : Option ℝ} (hp : p = some w) (hr : r = some q) (a : Option ℕ)
    {index : ℕ → Option ℕ} (hi : ShiftIndex a stride index) {f : D ℕ → Option (D ℕ)} (body : ∀ d, f d = shiftBody weighted left p r a stride d)
    {rows : ℕ → Option ℝ} (row : ∀ i, rows i = shiftObservation o weighted p r index i) :
    o (fixedValue (some f)) = a.bind (fun _ => Summation.value norm (some rows)) := by
  subst p r
  cases a with
  | none =>
    have no : iterateBody f 1 = none := by
      change f .zero = none
      rw [body, shiftBody]
      cases weighted <;> rfl
    rw [fixed_missing no]
    exact ho.finite.missing
  | some a =>
    let b := fun i : ℕ => shiftEmission weighted (some w) (some i)
    let next := fun i : ℕ => i+stride
    let m : Kernel ℕ ℕ := fun i =>
      (fun x => (if weighted then ENNReal.ofReal w else 1) * atom i x, {i})
    have seed (i : ℕ) (_ : i ∈ (Set.univ : Set ℕ)) : ∃ d, b i = some d ∧ Presents d (m i) := by
      cases weighted with
      | false => exact ⟨_, rfl, by simpa [m] using Represents.dirac i, visited_dirac i⟩
      | true => exact ⟨_, rfl, (Represents.dirac i).scale (r := w) hw, by simp [m]⟩
    have kernel (i : ℕ) : shiftKernel left stride i = some (.dirac (next i)) := by
      cases left <;> simp [shiftKernel, next, Functions.addN, Function2.apply, diracValue, Nat.add_comm]
    have move (i : ℕ) (_ : i ∈ (Set.univ : Set ℕ)) :
        bindValue (b i) (some (shiftKernel left stride)) = b (next i) := by
      cases weighted with
      | false => exact kernel i
      | true =>
        change scaleValue (some w) (shiftKernel left stride i) = _
        rw [kernel]; rfl
    have infinite : (⋃ n : ℕ, (m (next^[n] a)).2).Infinite := by
      change (⋃ n : ℕ, {next^[n] a}).Infinite
      rw [Set.iUnion_singleton_eq_range]
      apply Set.infinite_range_of_injective
      intro i j eq
      simpa [next, iterate_shift, Nat.mul_right_cancel_iff hk] using eq
    rw [ho.forward_orbit (Transport.bind (shiftKernel left stride)) b q hq
      next m Set.univ (fun _ _ => Set.mem_univ _) seed move (Set.mem_univ a) infinite body]
    rw [orbitSeries, ho.natSum]
    change Summation.value norm (some _) = Summation.value norm (some rows)
    congr 2
    funext i
    rw [row, reachWeight_const, shiftObservation, hi]
    cases ho.finite with
    | absent absent =>
      rw [absent, absent]
      cases weighted <;> simp [Functions.powRN, Function2.apply, Value.mul]
    | linear linear =>
      have power : Functions.powRN.apply (some q) (some i) = some (q^i) := by
        simp [Functions.powRN, Function2.apply]
      rw [power]
      change _ = Value.mul _ (o (diracValue (some (a+i*stride))))
      cases weighted
      · simp only [b, next, iterate_shift, shiftEmission, Bool.false_eq_true, if_false, linear.scale]
      · simp only [b, next, iterate_shift, shiftEmission, if_true, linear.scale]
        cases o (diracValue (some (a+i*stride))) <;> simp [Value.mul, mul_comm, mul_left_comm, mul_assoc]

theorem CountableObservation.nat_shift {o : Option (D ℕ) → Option ℝ} (ho : CountableObservation o)
    (weighted left : Bool) (stride : ℕ) (hk : 0 < stride) (w q : ℚ) (hw : 0 ≤ w) (hq : 0 ≤ q)
    {p r : Option ℝ} (hp : p = some (w : ℝ)) (hr : r = some (q : ℝ)) (a : Option ℕ)
    {index : ℕ → Option ℕ} (hi : ShiftIndex a stride index) {f : D ℕ → Option (D ℕ)} (body : ∀ d, f d = shiftBody weighted left p r a stride d)
    {rows : ℕ → Option ℝ} (row : ∀ i, rows i = shiftObservation o weighted p r index i) :
    o (fixedValue (some f)) = a.bind (fun _ => Summation.value norm (some rows)) :=
  ho.nat_shift_real weighted left stride hk (w : ℝ) (q : ℝ) (by exact_mod_cast hw) (by exact_mod_cast hq)
    hp hr a hi body row

private theorem shift_first_coefficients (weighted left : Bool) (p r : Option ℝ) (a : Option ℕ) (stride : ℕ)
    {d : D ℕ} {k : Weights ℕ} (eq : shiftBody weighted left p r a stride .zero = some d) (hd : Represents d k) :
    ∃ w q : ℝ, (if weighted then p else some ((1 : ℚ) : ℝ)) = some w ∧ r = some q ∧ 0 ≤ w ∧ 0 ≤ q := by
  cases r with
  | none => cases weighted <;> cases a <;> cases p <;> cases eq
  | some q =>
    cases a with
    | none => cases weighted <;> cases p <;> cases eq
    | some a =>
      cases weighted with
      | false =>
        change some (.add (.dirac a) (.scale q .zero)) = some d at eq
        cases eq
        cases hd with | add _ tail => cases tail with | scale hq _ => exact ⟨_, q, rfl, rfl, by norm_num, hq⟩
      | true =>
        cases p with
        | none => cases eq
        | some w =>
          change some (.add (.scale w (.dirac a)) (.scale q .zero)) = some d at eq
          cases eq
          cases hd with
          | add seed tail =>
            cases seed with
            | scale hw _ => cases tail with | scale hq _ => exact ⟨w, q, rfl, rfl, hw, hq⟩

private theorem shift_coefficients_iff (p r : Option ℝ) :
    Value.and (Value.le (some ((0 : ℚ) : ℝ)) p) (Value.le (some ((0 : ℚ) : ℝ)) r) = some true ↔
    ∃ w q : ℝ, p = some w ∧ r = some q ∧ 0 ≤ w ∧ 0 ≤ q := by
  cases p with
  | none => simp [Value.le, Value.and]
  | some w =>
    by_cases hw : 0 ≤ w <;> cases r <;> simp [hw, Value.le, Value.and]

/-- Guard a symbolic shift series by exactly the coefficient checks required
at its first approximation. The initial point remains strict inside the guard. -/
theorem CountableObservation.nat_shift_parameter {o : Option (D ℕ) → Option ℝ} (ho : CountableObservation o)
    (weighted left : Bool) (stride : ℕ) (hk : 0 < stride) (p r : Option ℝ) (a : Option ℕ)
    {index : ℕ → Option ℕ} (hi : ShiftIndex a stride index) {f : D ℕ → Option (D ℕ)}
    (body : ∀ d, f d = shiftBody weighted left p r a stride d)
    {rows : ℕ → Option ℝ} (row : ∀ i, rows i = shiftObservation o weighted p r index i) :
    o (fixedValue (some f)) = Binding.guardValue
      (Value.and (Value.le (some ((0 : ℚ) : ℝ)) (if weighted then p else some ((1 : ℚ) : ℝ)))
        (Value.le (some ((0 : ℚ) : ℝ)) r)) (a.bind fun _ => Summation.value norm (some rows)) := by
  let weight : Option ℝ := if weighted then p else some ((1 : ℚ) : ℝ)
  let gate := Value.and (Value.le (some ((0 : ℚ) : ℝ)) weight) (Value.le (some ((0 : ℚ) : ℝ)) r)
  change _ = Binding.guardValue gate _
  by_cases accept : gate = some true
  · obtain ⟨w, q, hp, hr, hw, hq⟩ := (shift_coefficients_iff weight r).mp accept
    rw [accept]
    apply ho.nat_shift_real weighted left stride hk w q hw hq hp hr a hi
    · intro d; rw [body]; cases weighted <;> rfl
    · intro i; rw [row]; cases weighted <;> rfl
  · have missing : fixedValue (some f) = none := by
      apply fixed_first_unrepresented
      intro d k eq hd
      exact accept ((shift_coefficients_iff weight r).mpr
        (shift_first_coefficients weighted left p r a stride ((body _).symm.trans eq) hd))
    rw [missing, ho.finite.missing]
    simp [Binding.guardValue, accept]

/-- Extract a nonzero emission weight once, before taking the infinite sum. -/
theorem CountableObservation.nat_shift_factored {o : Option (D ℕ) → Option ℝ} (ho : CountableObservation o)
    (left : Bool) (stride : ℕ) (hk : 0 < stride) (w q : ℚ) (hw : 0 < w) (hq : 0 ≤ q)
    {p r : Option ℝ} (hp : p = some (w : ℝ)) (hr : r = some (q : ℝ)) (a : Option ℕ)
    {index : ℕ → Option ℕ} (hi : ShiftIndex a stride index) {f : D ℕ → Option (D ℕ)}
    (body : ∀ d, f d = shiftBody true left p r a stride d)
    {rows : ℕ → Option ℝ} (row : ∀ i, rows i = shiftObservation o false p r index i) :
    o (fixedValue (some f)) = a.bind (fun _ => Value.mul p (Summation.value norm (some rows))) := by
  have h := ho.nat_shift true left stride hk w q hw.le hq hp hr a hi body
    (rows := fun i => Value.mul p (rows i)) (fun i => by
      change Value.mul p (rows i) = _
      rw [row, shiftObservation, shiftObservation]
      cases p <;> cases Functions.powRN.apply r (some i) <;> cases o (diracValue (index i)) <;>
        simp [Value.mul, mul_assoc])
  subst p
  rwa [SummationLinearity.scale_nonzero _ (by exact_mod_cast hw.ne')] at h

def shiftMassTotal (w q : ℚ) : Option ℚ :=
  if w = 0 then some 0 else if q < 1 then some (w/(1-q)) else none

private theorem shift_geometric_mass (w q : ℚ) (hq : 0 ≤ q) :
    Summation.value norm (some (fun i : ℕ => Value.mul (some (w : ℝ)) (some ((q : ℝ)^i)))) =
      (shiftMassTotal w q).map (fun t => (t : ℝ)) := by
  by_cases zero : w = 0
  · subst w
    simpa [shiftMassTotal, Value.mul] using (Summation.zero (ι := ℕ) norm (norm_zero : ‖(0 : ℝ)‖ = 0))
  · rw [SummationLinearity.scale_nonzero _ (by exact_mod_cast zero), Summation.geometric, Real.norm_eq_abs,
      abs_of_nonneg (by exact_mod_cast hq)]
    by_cases lt : q < 1
    · simp [shiftMassTotal, zero, lt, show (q : ℝ) < 1 by exact_mod_cast lt, Value.mul, div_eq_mul_inv]
    · simp [shiftMassTotal, zero, lt, show ¬ (q : ℝ) < 1 by exact_mod_cast lt, Value.mul]

theorem nat_shift_mass (weighted left : Bool) (stride : ℕ) (hk : 0 < stride) (w q : ℚ) (hw : 0 ≤ w) (hq : 0 ≤ q)
    {p r : Option ℝ} (hp : p = some (w : ℝ)) (hr : r = some (q : ℝ)) (a : Option ℕ)
    {f : D ℕ → Option (D ℕ)} (body : ∀ d, f d = shiftBody weighted left p r a stride d)
    (total : Option ℚ) (check : shiftMassTotal (if weighted then w else 1) q = total)
    {result : Option ℝ} (out : result = total.map (fun t => (t : ℝ))) :
    massValue (fixedValue (some f)) = a.bind (fun _ => result) := by
  subst p r result total
  let index := fun i : ℕ => a.map (fun v => v+i*stride)
  rw [CountableObservation.mass.nat_shift weighted left stride hk w q hw hq rfl rfl a (index := index)
    (fun _ => rfl) body (fun _ => rfl)]
  cases a with
  | none => rfl
  | some a =>
    simp only [Option.bind]
    rw [← shift_geometric_mass _ _ hq]
    congr 2
    funext i
    cases weighted <;> simp [index, shiftObservation, Functions.powRN, Function2.apply,
      mass_dirac, Value.mul]

end QSym.Distribution.Atomic
