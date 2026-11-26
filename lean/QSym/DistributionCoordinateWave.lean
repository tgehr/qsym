import QSym.DistributionCoordinatePeriodic

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.Grid.VariationChange
open Set MeasureTheory Real

/-- Evaluate the absolute derivative on a rising arc followed by a falling arc. -/
theorem two_arcs {h : ℝ → ℝ} {c P : ℝ} (sm : ContDiff ℝ 1 h) (hc : 0 ≤ c)
    (rise : ∀ x ∈ Icc 0 c, 0 ≤ deriv h x) (fall : ∀ x ∈ Icc c P, deriv h x ≤ 0)
    {u : ℝ} (hu : u ∈ Icc 0 P) :
    (∫ x in (0:ℝ)..u, |deriv h x|) =
      if u < c then h u - h 0 else (h c - h 0) + (h c - h u) := by
  have d := sm.differentiable le_rfl
  have cont := sm.continuous_deriv le_rfl
  have first {v : ℝ} (hv : v ∈ Icc 0 c) :
      (∫ x in (0:ℝ)..v, |deriv h x|) = h v - h 0 := by
    rw [intervalIntegral.integral_congr (g := deriv h) (fun x hx => abs_of_nonneg
      (rise x ((uIcc_of_le hv.1 ▸ hx : x ∈ Icc 0 v).imp_right (·.trans hv.2))))]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (d x).hasDerivAt) (cont.intervalIntegrable _ _)
  split_ifs with huc
  · exact first ⟨hu.1, huc.le⟩
  · have cu := le_of_not_gt huc
    rw [← intervalIntegral.integral_add_adjacent_intervals (cont.abs.intervalIntegrable 0 c) (cont.abs.intervalIntegrable c u),
      first ⟨hc, le_rfl⟩]
    congr 1
    rw [intervalIntegral.integral_congr (g := fun x => -deriv h x) (fun x hx => abs_of_nonpos
      (fall x ((uIcc_of_le cu ▸ hx : x ∈ Icc c u).imp_right (·.trans hu.2)))),
      intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (d x).hasDerivAt) (cont.intervalIntegrable _ _), neg_sub]

/-- For a sine or cosine input only the positive unit interval and symmetry of
the derivative magnitude are needed to count every turn of the composition. -/
structure WaveProfile (h : ℝ → ℝ) (op : Option ℝ → Option ℝ) : Prop where
  smooth : ContDiff ℝ 1 h
  rising : ∀ u ∈ Icc 0 1, 0 ≤ deriv h u
  reflect : ∀ u, |deriv h (-u)| = |deriv h u|
  source : ∀ u, op (some u) = some (h u)

namespace WaveProfile

private def wave (h : ℝ → ℝ) := h ∘ Real.sin
private def lengthTo (h : ℝ → ℝ) (x : ℝ) := (∫ t in (0:ℝ)..x, |deriv (wave h) t|) - (h 1 - h 0)/2

private theorem lengthDeriv {h op} (w : WaveProfile h op) (x : ℝ) :
    HasDerivAt (lengthTo h) |deriv (wave h) x| x := by
  have cont := ((w.smooth.comp Real.contDiff_sin).continuous_deriv le_rfl).abs
  exact (intervalIntegral.integral_hasDerivAt_right (cont.intervalIntegrable 0 x)
    cont.stronglyMeasurable.stronglyMeasurableAtFilter cont.continuousAt).sub_const _

private theorem lengthCell {h op} (w : WaveProfile h op) (x : ℝ) :
    lengthTo h x =
      let m : ℤ := ⌊x/π⌋
      let height := h |Real.sin x| - h 0
      let span := 2 * (h 1 - h 0)
      span * (m:ℝ) + (if x - (m:ℝ)*π < π/2 then height else span - height) - (h 1 - h 0)/2 := by
  have d (t : ℝ) : deriv (wave h) t = deriv h (Real.sin t) * Real.cos t :=
    ((w.smooth.differentiable le_rfl _).hasDerivAt.comp t (Real.hasDerivAt_sin t)).deriv
  have per : Function.Periodic (fun t : ℝ => |deriv (wave h) t|) π := fun t => by
    simp only [d, Real.sin_add_pi, Real.cos_add_pi, abs_mul, abs_neg, w.reflect]
  have nonneg {t : ℝ} (ht : t ∈ Icc 0 π) := w.rising (Real.sin t)
    ⟨Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2, Real.sin_le_one _⟩
  have half : 0 ≤ π/2 := by positivity
  have cell (u : ℝ) (hu : u ∈ Icc 0 π) : (∫ t in (0:ℝ)..u, |deriv (wave h) t|) =
      if u < π/2 then h (Real.sin u) - h 0 else 2*(h 1-h 0) - (h (Real.sin u)-h 0) := by
    rw [two_arcs (w.smooth.comp Real.contDiff_sin) half (P := π) (h := wave h) (u := u)]
    · simp only [wave, Function.comp_apply, Real.sin_zero, Real.sin_pi_div_two]
      split <;> ring
    · intro t ht
      rw [d]
      exact mul_nonneg (nonneg ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩)
        (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [ht.1]) ht.2)
    · intro t ht
      rw [d]
      exact mul_nonpos_of_nonneg_of_nonpos (nonneg ⟨half.trans ht.1, ht.2⟩)
        (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1 (by linarith [ht.2]))
    · exact hu
  let m : ℤ := ⌊x/π⌋
  have lo : (m:ℝ)*π ≤ x := (le_div_iff₀ Real.pi_pos).mp (Int.floor_le _)
  have hi : x < ((m:ℝ)+1)*π := (div_lt_iff₀ Real.pi_pos).mp (Int.lt_floor_add_one _)
  have pos := Real.sin_nonneg_of_nonneg_of_le_pi (x := x-(m:ℝ)*π) (by linarith) (by linarith)
  have parity : |(-1:ℝ)^m| = 1 := by rw [← Real.norm_eq_abs, norm_zpow]; simp
  have reflected : Real.sin (x - (m:ℝ)*π) = |Real.sin x| := by
    rw [← abs_of_nonneg pos, Real.sin_sub_int_mul_pi, abs_mul, parity, one_mul]
  rw [lengthTo, periodic_primitive Real.pi_pos per ((w.smooth.comp Real.contDiff_sin).continuous_deriv le_rfl).abs _ cell]
  simp only [show ¬π < π/2 by linarith [Real.pi_pos], if_false, Real.sin_pi, sub_self, sub_zero]
  rw [show ⌊x/π⌋ = m from rfl, reflected, mul_comm (m:ℝ)]

private theorem lengthQuarter {h op} (w : WaveProfile h op) (x : ℝ) :
    lengthTo h x =
      let q : ℤ := ⌊2*x/π⌋
      let span := h 1 - h 0
      span * (q:ℝ) + (-1:ℝ)^q * (h |Real.sin x| - h 0 - span/2) := by
  let m : ℤ := ⌊x/π⌋
  have lo : (m:ℝ)*π ≤ x := (le_div_iff₀ Real.pi_pos).mp (Int.floor_le _)
  have hi : x < ((m:ℝ)+1)*π := (div_lt_iff₀ Real.pi_pos).mp (Int.lt_floor_add_one _)
  have even : (-1:ℝ)^(2*m) = 1 := by rw [zpow_mul]; norm_num
  have odd : (-1:ℝ)^(2*m+1) = -1 := by rw [zpow_add₀ (by norm_num), even]; simp
  rw [lengthCell w x]
  change 2 * _ * (m:ℝ) + (if x-(m:ℝ)*π < π/2 then _ else _) - _ = _
  by_cases first : x-(m:ℝ)*π < π/2
  · have q : ⌊2*x/π⌋ = 2*m := Int.floor_eq_iff.mpr ⟨(le_div_iff₀ Real.pi_pos).mpr (by push_cast; linarith),
      (div_lt_iff₀ Real.pi_pos).mpr (by push_cast; linarith)⟩
    simp only [if_pos first, q, even, one_mul, Int.cast_mul, Int.cast_ofNat]
    ring
  · have q : ⌊2*x/π⌋ = 2*m+1 := Int.floor_eq_iff.mpr ⟨(le_div_iff₀ Real.pi_pos).mpr (by push_cast; linarith),
      (div_lt_iff₀ Real.pi_pos).mpr (by push_cast; linarith)⟩
    simp only [if_neg first, q, odd, neg_one_mul, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat]
    ring

private def halfPi : Option ℝ := Value.mul (some π) (Value.inv (some ((2:ℤ):ℝ)))
private def difference (u v : Option ℝ) := Value.add u (Value.mul (some ((-1:ℤ):ℝ)) v)
private def trig (sine : Bool) (v : Option ℝ) :=
  if sine then Functions.sinR.apply v else Functions.cosR.apply v

def primitive (op : Option ℝ → Option ℝ) (sine : Bool) (v : Option ℝ) : Option ℝ :=
  let phase := if sine then v else Value.add v halfPi
  let two := some ((2:ℤ):ℝ)
  let index := Functions.floorR.apply (Value.mul (Value.mul two phase) (Value.inv (some π)))
  let count := Functions.castQR.apply (Functions.castZQ.apply index)
  let parity := Functions.powRZ.apply (some ((-1:ℤ):ℝ)) index
  let base := op (some ((0:ℤ):ℝ))
  let span := difference (op (some ((1:ℤ):ℝ))) base
  let height := difference (op (Value.abs (trig sine v))) base
  let centered := difference height (Value.mul span (Value.inv two))
  Value.add (Value.mul span count) (Value.mul parity centered)

private theorem primitive_some {h op} (w : WaveProfile h op) (sine : Bool) (x : ℝ) :
    primitive op sine (some x) = some (lengthTo h (if sine then x else x + π/2)) := by
  cases sine <;>
    simp [primitive, trig, halfPi, difference, lengthQuarter w, w.source, Value.mul, Value.inv, Value.add, Value.abs,
      Value.le, Binding.conditionalValue, Functions.castQR, Functions.castZQ, Functions.floorR,
      Functions.cosR, Functions.sinR, Functions.powRZ, Function2.apply, Function1.apply, Real.pi_ne_zero, Real.sin_add_pi_div_two,
      div_eq_mul_inv, sub_eq_add_neg] <;>
    simp only [← div_eq_mul_inv π 2, Real.sin_add_pi_div_two, true_or]

/-- Count quarter turns with one signed floor and use parity to orient the endpoint height. -/
theorem variation {h op} (w : WaveProfile h op) (sine : Bool) :
    VariationChange (fun x => wave h (if sine then x else x + π/2))
      (fun x => lengthTo h (if sine then x else x + π/2)) (fun v => op (trig sine v)) (primitive op sine) := by
  have sm : ContDiff ℝ 1 (wave h) := w.smooth.comp Real.contDiff_sin
  have deriv_eq : deriv (lengthTo h) = fun x => |deriv (wave h) x| := funext fun x => (lengthDeriv w x).deriv
  have sk : ContDiff ℝ 1 (lengthTo h) := contDiff_one_iff_deriv.mpr
    ⟨fun x => (lengthDeriv w x).differentiableAt, deriv_eq ▸ (sm.continuous_deriv le_rfl).abs⟩
  have mono := monotone_of_hasDerivAt_nonneg (lengthDeriv w) (fun x => abs_nonneg _)
  cases sine
  · refine ⟨sm.comp (contDiff_id.add contDiff_const), sk.comp (contDiff_id.add contDiff_const),
      mono.comp (fun _ _ hxy => add_le_add_right hxy _), ?_, ?_, primitive_some w false⟩
    · intro x
      have e : HasDerivAt (fun t : ℝ => t + π/2) 1 x := (hasDerivAt_id x).add_const _
      have l := (lengthDeriv w (x + π/2)).comp x e
      have r := ((sm.differentiable le_rfl _).hasDerivAt.comp x e).deriv
      change deriv (lengthTo h ∘ (fun x : ℝ => x + π/2)) x = |deriv (wave h ∘ (fun x : ℝ => x + π/2)) x|
      rw [l.deriv, r, mul_one, mul_one]
    · intro x
      simp [trig, wave, Real.sin_add_pi_div_two, Functions.cosR, Function1.apply, w.source]
  · refine ⟨sm, sk, mono, fun x => (lengthDeriv w x).deriv, ?_, primitive_some w true⟩
    intro x
    simp [trig, wave, Functions.sinR, Function1.apply, w.source]

theorem power (n : ℕ) : WaveProfile (fun x : ℝ => x^n) (fun v => v.map (·^n)) := by
  refine ⟨contDiff_id.pow n, ?_, ?_, fun _ => rfl⟩
  · intro u hu
    rw [(hasDerivAt_pow n u).deriv]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu.1 _)
  · intro u
    simp [(hasDerivAt_pow n _).deriv, abs_mul, abs_pow]

end WaveProfile
end QSym.Distribution.GraphFibre.Coordinates.Grid.VariationChange
