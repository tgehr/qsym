import QSym.DistributionAtomicIteration

/-! Compositional certificates for finite affine expressions in a recursive
distribution. A constant source can omit every visit to the recursive input.
The reachable inputs themselves only visit atoms of the complete seed. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal

private def sumModel (a b : Model α) : Model α := (fun x => a.1 x + b.1 x, a.2 ∪ b.2)
private def scaleModel (r : ℝ≥0∞) (a : Model α) : Model α := (fun x => r * a.1 x, a.2)

def affineModel (b : Model α) (q : ℚ) (uses : Bool) (k : Model α) : Model α :=
  (fun x => b.1 x + ENNReal.ofReal (q : ℝ) * k.1 x, b.2 ∪ (if uses then k.2 else ∅))

private theorem presents_sum {d e : D α} {a b : Model α} (hd : Presents d a) (he : Presents e b) :
    Presents (.add d e) (sumModel a b) :=
  ⟨hd.1.add he.1, (visited_add _ _).trans (congrArg₂ (· ∪ ·) hd.2 he.2)⟩

private theorem presents_scale {d : D α} {a : Model α} (hd : Presents d a) {c : ℝ} (hc : 0 ≤ c) :
    Presents (.scale c d) (scaleModel (ENNReal.ofReal c) a) :=
  ⟨hd.1.scale hc, (visited_scale _ _).trans hd.2⟩

inductive AffineBehavior (f : D α → Option (D α)) (s : Option (D α)) (q : ℚ) (uses : Bool) : Prop where
  | missing (seed : s = none) (step : ∀ d, f d = none)
  | present {b m} (seed : s = some b) (data : Presents b m)
      (step : ∀ d k, Presents d k → ∃ e, f d = some e ∧ Presents e (affineModel m q uses k))

structure Affine (f : D α → Option (D α)) (s : Option (D α)) (q : ℚ) (uses : Bool) : Prop where
  nonneg : 0 ≤ q
  behavior : AffineBehavior f s q uses

theorem Affine.constant {s : Option (D α)} (h : Admissible s) : Affine (fun _ => s) s 0 false := by
  refine ⟨le_refl 0, ?_⟩
  cases s with
  | none => exact .missing rfl (fun _ => rfl)
  | some b =>
    obtain ⟨m, hm⟩ := h b rfl
    exact .present rfl hm (fun _ _ _ => ⟨b, rfl, by simpa [affineModel] using hm⟩)

theorem Affine.self : Affine (fun d : D α => some d) zeroValue 1 true := by
  let m : Model α := (fun _ => 0, ∅)
  have hz : Presents (.zero : D α) m := ⟨Represents.zero, visited_zero⟩
  exact ⟨zero_le_one, .present rfl hz (fun d _ hd => ⟨d, rfl, by simpa [affineModel, m] using hd⟩)⟩

private theorem affine_sum (m n k : Model α) {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u v : Bool) :
    sumModel (affineModel m a u k) (affineModel n b v k) = affineModel (sumModel m n) (a+b) (u || v) k := by
  apply Prod.ext
  · funext x
    have a0 : 0 ≤ (a : ℝ) := by exact_mod_cast ha
    have b0 : 0 ≤ (b : ℝ) := by exact_mod_cast hb
    simp only [sumModel, affineModel, Rat.cast_add, ENNReal.ofReal_add a0 b0, add_mul]
    exact add_add_add_comm _ _ _ _
  · ext x
    cases u <;> cases v <;> simp [sumModel, affineModel, Set.mem_union] <;> tauto

theorem Affine.add {f g : D α → Option (D α)} {s t : Option (D α)} {a b : ℚ} {u v : Bool}
    (z : ℚ) (hz : z = a+b) (hf : Affine f s a u) (hg : Affine g t b v) :
    Affine (fun d => addValue (f d) (g d)) (addValue s t) z (u || v) := by
  subst z
  refine ⟨add_nonneg hf.nonneg hg.nonneg, ?_⟩
  cases hf.behavior with
  | missing hs fs => exact .missing (by rw [hs]; rfl) (fun d => by rw [fs]; rfl)
  | @present x m hs hx fs =>
    cases hg.behavior with
    | missing ht ft =>
      exact .missing (by rw [ht]; cases s <;> rfl) (fun d => by rw [ft]; cases f d <;> rfl)
    | @present y n ht hy ft =>
      refine .present (b := .add x y) (by rw [hs, ht]; rfl) (presents_sum hx hy) ?_
      intro d k hd
      obtain ⟨i, hi, ki⟩ := fs d k hd
      obtain ⟨j, hj, kj⟩ := ft d k hd
      exact ⟨.add i j, by rw [hi, hj]; rfl, (affine_sum m n k hf.nonneg hg.nonneg u v) ▸ presents_sum ki kj⟩

private theorem affine_scale (m k : Model α) (a : ℚ) (u : Bool) {c : ℚ} (hc : 0 ≤ c) :
    scaleModel (ENNReal.ofReal (c : ℝ)) (affineModel m a u k) =
      affineModel (scaleModel (ENNReal.ofReal (c : ℝ)) m) (c*a) u k := by
  have c0 : 0 ≤ (c : ℝ) := by exact_mod_cast hc
  exact Prod.ext (funext fun _ => by simp [scaleModel, affineModel, ENNReal.ofReal_mul c0, mul_add, mul_assoc]) rfl

theorem Affine.scale {f : D α → Option (D α)} {s : Option (D α)} {a : ℚ} {u : Bool}
    (weighted : Bool) {r : Option ℝ} (c z : ℚ) (hc : 0 ≤ c) (hz : z = c*a)
    (hr : r = some (c : ℝ)) (h : Affine f s a u) :
    Affine (fun d => scaleTerm weighted r (f d)) (scaleValue r s) z u := by
  subst r z
  have c0 : 0 ≤ (c : ℝ) := by exact_mod_cast hc
  refine ⟨mul_nonneg hc h.nonneg, ?_⟩
  cases h.behavior with
  | missing hs step => exact .missing (by rw [hs]; rfl) (fun d => by rw [step]; cases weighted <;> rfl)
  | @present b m hs hb step =>
    refine .present (b := .scale c b) (by rw [hs]; rfl) (presents_scale hb c0) ?_
    intro d k hd
    obtain ⟨y, hy, ky⟩ := step d k hd
    obtain ⟨e, he, ke, ve⟩ := tail_step weighted ky c0
    refine ⟨e, hy ▸ he, ?_⟩
    rw [← affine_scale m k a u hc]
    exact ⟨ke, ve⟩

private theorem Affine.admissible {f : D α → Option (D α)} {s q u} (h : Affine f s q u) : Admissible s := by
  intro e he
  cases h.behavior with
  | missing hs _ => simp [hs] at he
  | present hs hb _ => exact ⟨_, Option.some.inj (hs.symm.trans he) ▸ hb⟩

private theorem Affine.change_present {f : D α → Option (D α)} {s t q u} (h : Affine f s q u)
    {a b : D α} {m : Model α} (ha : s = some a) (hb : t = some b) (ma : Presents a m) (mb : Presents b m) :
    Affine f t q u := by
  cases h.behavior with
  | missing hs _ => simp [hs] at ha
  | @present x k hx hk step =>
    cases Option.some.inj (ha.symm.trans hx)
    cases (hk.eq_iff ma).mpr (fun _ => rfl)
    exact ⟨h.nonneg, .present hb mb step⟩

private theorem Affine.drop_zero {f : D α → Option (D α)} {s q u} (left : Bool) (hs : Admissible s)
    (h : Affine f (if left then addValue zeroValue s else addValue s zeroValue) q u) : Affine f s q u := by
  cases s with
  | none => cases left <;> exact h
  | some b =>
    obtain ⟨m, hm⟩ := hs b rfl
    let z : Model α := (fun _ => 0, ∅)
    have hz : Presents (.zero : D α) z := ⟨Represents.zero, visited_zero⟩
    cases left with
    | false => exact h.change_present (a := .add b .zero) rfl rfl (by simpa [sumModel, z] using presents_sum hm hz) hm
    | true => exact h.change_present (a := .add .zero b) rfl rfl (by simpa [sumModel, z] using presents_sum hz hm) hm

theorem Affine.add_left_zero {f g : D α → Option (D α)} {t : Option (D α)} {a b : ℚ} {u v : Bool}
    (z : ℚ) (hz : z = a+b) (hf : Affine f zeroValue a u) (hg : Affine g t b v) :
    Affine (fun d => addValue (f d) (g d)) t z (u || v) :=
  drop_zero true hg.admissible (add z hz hf hg)

theorem Affine.add_right_zero {f g : D α → Option (D α)} {s : Option (D α)} {a b : ℚ} {u v : Bool}
    (z : ℚ) (hz : z = a+b) (hf : Affine f s a u) (hg : Affine g zeroValue b v) :
    Affine (fun d => addValue (f d) (g d)) s z (u || v) :=
  drop_zero false hf.admissible (add z hz hf hg)

theorem Affine.scale_zero {f : D α → Option (D α)} {a : ℚ} {u : Bool}
    (weighted : Bool) {r : Option ℝ} (c z : ℚ) (hc : 0 ≤ c) (hz : z = c*a)
    (hr : r = some (c : ℝ)) (h : Affine f zeroValue a u) :
    Affine (fun d => scaleTerm weighted r (f d)) zeroValue z u := by
  subst r
  let m : Model α := (fun _ => 0, ∅)
  have hm : Presents (.zero : D α) m := ⟨Represents.zero, visited_zero⟩
  apply (scale weighted c z hc hz rfl h).change_present (a := .scale c .zero) rfl rfl _ hm
  simpa [scaleModel, m] using presents_scale hm (show 0 ≤ (c : ℝ) by exact_mod_cast hc)

theorem fixed_affine {f g : D α → Option (D α)} {s : Option (D α)} {r : Option ℝ} {u : Bool}
    (q : ℚ) (hr : r = some (q : ℝ)) (h : Affine g s q u) (body : ∀ d, f d = g d) :
    fixedValue (some f) = retryValue r s := by
  subst r
  cases h.behavior with
  | missing hs step =>
    rw [hs, retry_missing]
    exact fixed_missing (n := 1) ((body .zero).trans (step .zero))
  | @present b m hs hm step =>
    rw [hs, retry_eq_realize hm (by exact_mod_cast h.nonneg)]
    apply fixed_of_step_on _ _ (strictRetry_continuous _ _) (fun k => k.2 ⊆ m.2)
    · exact Set.empty_subset _
    · intro k hk
      exact Set.union_subset (Set.Subset.rfl) hk
    · intro d k hk hd
      obtain ⟨e, he, ke⟩ := step d k hd
      refine ⟨e, (body d).trans he, ke.1, ke.2.trans ?_⟩
      cases u <;> simp [affineModel, strictRetryStep, Set.union_eq_left.mpr hk]

end QSym.Distribution.Atomic
