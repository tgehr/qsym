import QSym.DistributionAtomicValue
import QSym.DistributionMixture

/-! A scalar observation can pass through an atomic fixed point whenever it
respects zero, addition, and scaling. Weighting and composition preserve this
certificate, including missing kernels and signed or partial scalar tests. -/
noncomputable section
namespace QSym.Distribution.Atomic

structure LinearObservation (o : Option (D α) → Option ℝ) : Prop where
  missing : o none = none
  zero : o zeroValue = some 0
  add (a b) : o (addValue a b) = Value.add (o a) (o b)
  scale (r d) : o (scaleValue r d) = Value.mul r (o d)

/-- Missing a weight function or kernel invalidates even an empty input. -/
inductive Observation (o : Option (D α) → Option ℝ) : Prop where
  | absent (h : ∀ d, o d = none)
  | linear (h : LinearObservation o)

theorem Observation.mass : Observation (massValue (α := α)) :=
  .linear ⟨rfl, rfl, mass_addValue, mass_scaleValue⟩

theorem Observation.missing {o : Option (D α) → Option ℝ} (h : Observation o) :
    o none = none := by
  cases h with
  | absent h => exact h none
  | linear h => exact h.missing

private theorem Observation.through {o : Option (D β) → Option ℝ} (h : Observation o)
    (g : Option (D α) → Option (D β)) (hn : g none = none) (hz : g zeroValue = zeroValue)
    (ha : ∀ a b, g (addValue a b) = addValue (g a) (g b))
    (hs : ∀ r d, g (scaleValue r d) = scaleValue r (g d)) : Observation (fun d => o (g d)) := by
  cases h with
  | absent p => exact .absent fun d => p (g d)
  | linear p =>
    exact .linear ⟨(congrArg o hn).trans p.missing, (congrArg o hz).trans p.zero,
      fun a b => (congrArg o (ha a b)).trans (p.add _ _),
      fun r d => (congrArg o (hs r d)).trans (p.scale _ _)⟩

theorem Observation.weight {o : Option (D α) → Option ℝ} (h : Observation o) (f : Option (α → Option ℝ)) :
    Observation (fun d => o (weightValue f d)) := by
  cases f with
  | none => exact .absent fun _ => h.missing
  | some f => exact h.through _ rfl rfl (weight_addValue _) (weight_scaleValue _)

theorem Observation.bind {o : Option (D β) → Option ℝ} (h : Observation o) (k : Option (α → Option (D β))) :
    Observation (fun d => o (bindValue d k)) := by
  cases k with
  | none => exact .absent fun d => by cases d <;> exact h.missing
  | some k => exact h.through _ rfl rfl (fun _ _ => bind_addValue _ _ _) (fun _ _ => bind_scaleValue _ _ _)

theorem Observation.realBind {o : Option (D ℝ) → Option ℝ} (h : Observation o) (k : Option (α → Option (D ℝ))) :
    Observation (fun d => o (GraphFibre.realBindValue d k)) := by
  cases k with
  | none => exact .absent fun d => by cases d <;> exact h.missing
  | some k =>
    exact h.through (fun d => GraphFibre.realBindValue d (some k)) rfl rfl
      (fun _ _ => GraphFibre.realBind_addValue _ _ _) (fun _ _ => GraphFibre.realBind_scaleValue _ _ _)

theorem LinearObservation.atoms {o : Option (D α) → Option ℝ} (h : LinearObservation o)
    {d : D α} {k : Weights α} (hd : Represents d k) :
    o (some d) = integrate d (fun a => o (some (.dirac a))) := by
  induction hd with
  | zero => exact h.zero
  | dirac => rfl
  | add _ _ ih jh => exact (h.add _ _).trans (congrArg₂ Value.add ih jh)
  | @scale r _ _ _ _ ih => exact (h.scale (some r) _).trans (congrArg (Value.mul (some r)) ih)

theorem Observation.retry {o : Option (D α) → Option ℝ} (h : Observation o)
    {r g : Option ℝ} (q c : ℚ) (h0 : 0 ≤ q) (h1 : q < 1) (hc : c = (1-q)⁻¹)
    (hr : r = some (q : ℝ)) (hg : g = some (c : ℝ)) {s : Option (D α)} (hs : Admissible s) :
    o (retryValue r s) = o (scaleValue g s) := by
  have strict (v : Option (D α)) : o v = v.bind (fun d => o (some d)) := by
    cases v with
    | none => exact h.missing
    | some => rfl
  rw [strict (retryValue r s), strict (scaleValue g s)]
  apply observe_retry _ _ q c h0 h1 hc hr hg hs
  intro d e m hd he
  cases h with
  | absent p => exact (p _).trans (p _).symm
  | linear p => exact (p.atoms hd.1).trans (((hd.eq_iff he).mp rfl _).trans (p.atoms he.1).symm)

end QSym.Distribution.Atomic
