import QSym.DistributionCoordinatePiecewise

noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates
open Classical Set Filter Topology

private def piece (a b x : ℝ) : ℝ → ℝ :=
  if x < a then (· ^ 2) else if b < x then id else fun _ => 0

private def jumpFn (a b x : ℝ) := piece a b x x

private theorem germ {a b x : ℝ} (ha : x ≠ a) (hb : x ≠ b) :
    jumpFn a b =ᶠ[𝓝 x] piece a b x := by
  rcases lt_or_gt_of_ne ha with l | l
  · filter_upwards [gt_mem_nhds l] with y hy
    simp [jumpFn, piece, l, hy]
  · rcases lt_or_gt_of_ne hb with r | r
    · filter_upwards [lt_mem_nhds l, gt_mem_nhds r] with y hl hr
      simp [jumpFn, piece, l.not_lt, hl.not_lt, r.not_lt, hr.not_lt]
    · filter_upwards [lt_mem_nhds l, lt_mem_nhds r] with y hl hr
      simp [jumpFn, piece, l.not_lt, hl.not_lt, r, hr]

private theorem traces {a b : ℝ} (hab : a < b) :
    Tendsto (jumpFn a b) (𝓝[<] a) (𝓝 (a^2)) ∧ Tendsto (jumpFn a b) (𝓝[>] a) (𝓝 0) ∧
    Tendsto (jumpFn a b) (𝓝[<] b) (𝓝 0) ∧ Tendsto (jumpFn a b) (𝓝[>] b) (𝓝 b) := by
  refine ⟨((continuousAt_id.pow 2).continuousWithinAt : ContinuousWithinAt _ (Iio a) a).tendsto.congr' ?_,
    tendsto_const_nhds.congr' ?_, tendsto_const_nhds.congr' ?_,
    (continuousAt_id.continuousWithinAt : ContinuousWithinAt id (Ioi b) b).tendsto.congr' ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : x < a)
    simp [jumpFn, piece, hx]
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hab)] with x (l : a < x) (r : x < b)
    simp [jumpFn, piece, l.not_lt, r.not_lt]
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hab)] with x (r : x < b) (l : a < x)
    simp [jumpFn, piece, l.not_lt, r.not_lt]
  · filter_upwards [self_mem_nhdsWithin] with x (r : b < x)
    simp [jumpFn, piece, (hab.trans r).not_lt, r]

private theorem nondiff_jump {g : ℝ → ℝ} {a l r : ℝ} (hl : Tendsto g (𝓝[<] a) (𝓝 l))
    (hr : Tendsto g (𝓝[>] a) (𝓝 r)) (hne : l ≠ r) : ¬ DifferentiableAt ℝ g a := by
  intro h
  exact hne ((tendsto_nhds_unique hl h.continuousAt.continuousWithinAt).trans
    (tendsto_nhds_unique hr h.continuousAt.continuousWithinAt).symm)

private def jumpChart {a b : ℝ} (ha : a < 0) (hb : 0 < b) : VariationChart := by
  have ab := ha.trans hb
  have tr := traces ab
  have al := tr.1
  have ar := tr.2.1
  have bl := tr.2.2.1
  have br := tr.2.2.2
  have an := nondiff_jump al ar (pow_ne_zero 2 ha.ne)
  have bn := nondiff_jump bl br hb.ne
  have reg (x : ℝ) (l : x ≠ a) (r : x ≠ b) : ContDiffAt ℝ 1 (jumpFn a b) x := by
    apply ContDiffAt.congr_of_eventuallyEq _ (germ l r)
    unfold piece
    split
    · fun_prop
    · split <;> fun_prop
  refine ⟨jumpFn a b, [a,b], by simp [ab], ?_, ?_, ?_⟩
  · intro x
    by_cases l : x = a
    · simp [l, an]
    by_cases r : x = b
    · simp [r, bn]
    simp [l, r, (reg x l r).differentiableAt le_rfl]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    exact reg x hx.1 hx.2
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, _, al, ar, Or.inr (by simp [jumpFn, piece, ab.not_lt])⟩
    · exact ⟨_, _, bl, br, Or.inl (by simp [jumpFn, piece, ab.not_lt])⟩

private theorem weight_eq {a b : ℝ} (ha : a < 0) (hb : 0 < b) (x : ℝ) :
    |deriv (jumpFn a b) x| = (if x < a then -2*x else 0) + (if b < x then 1 else 0) := by
  have ab := ha.trans hb
  obtain ⟨al, ar, bl, br⟩ := traces ab
  by_cases l : x = a
  · subst x
    simp [deriv_zero_of_not_differentiableAt (nondiff_jump al ar (pow_ne_zero 2 ha.ne)), ab.not_lt]
  by_cases r : x = b
  · subst x
    simp [deriv_zero_of_not_differentiableAt (nondiff_jump bl br hb.ne), ab.not_lt]
  rw [(germ l r).deriv_eq]
  by_cases hl : x < a
  · simp [piece, hl, (hl.trans ab).not_lt, abs_of_neg (show 2*x < 0 by linarith)]
  · by_cases hr : b < x <;> simp [piece, hl, hr]

/-- A disjoint left quadratic ray and right linear ray. The jump heights
and open-piece weights are computed from their real one-sided germs. -/
theorem twoRayJumps (a b : ℚ) (ha : a < 0) (hb : 0 < b) {va vb : Option ℝ}
    (hva : va = some (a:ℝ)) (hvb : vb = some (b:ℝ)) (swap : Bool) :
    value (Tensor.consValue (some fun x => ordered swap Value.add
      (Value.mask (Value.lt (some x) va) ((some x).map (· ^ 2)))
      (Value.mask (Value.lt vb (some x)) (some x))) Tensor.nilValue) =
    addValue (if a^2 = 1 then diracValue va else scaleValue (va.map (· ^ 2)) (diracValue va))
      (addValue (if b = 1 then diracValue vb else scaleValue vb (diracValue vb))
        (weightValue (some fun x => Value.add
          (Value.mask (Value.lt (some x) va) (Value.mul (some ((-2:ℤ):ℝ)) (some x)))
          (Value.mask (Value.lt vb (some x)) (some ((1:ℤ):ℝ)))) lebesgueValue)) := by
  subst va; subst vb
  have al : (a:ℝ) < 0 := by exact_mod_cast ha
  have br : 0 < (b:ℝ) := by exact_mod_cast hb
  have ab := al.trans br
  rw [singleton_pieces (jumpChart al br) (by
    intro x
    change _ = some (jumpFn (a:ℝ) b x)
    by_cases l : x < (a:ℝ)
    · cases swap <;> simp [ordered, Value.add, Value.mask, Value.lt, jumpFn, piece, l, (l.trans ab).not_lt]
    · by_cases r : (b:ℝ) < x <;> cases swap <;> simp [ordered, Value.add, Value.mask, Value.lt, jumpFn, piece, l, r])]
  obtain ⟨la,ra,lb,rb⟩ := traces ab
  change addValue (VariationChart.atCut (jumpFn (a:ℝ) b) a none)
    (addValue (VariationChart.atCut (jumpFn (a:ℝ) b) b none) _) = _
  have aUnit : ((a:ℝ)^2 = 1) ↔ a^2 = 1 := by norm_cast
  have bUnit : ((b:ℝ) = 1) ↔ b = 1 := by norm_cast
  simp only [VariationChart.atCut_of_limits la ra, VariationChart.atCut_of_limits lb rb, pow_ne_zero 2 al.ne, br.ne,
    ↓reduceIte, Option.elim, VariationChart.atom, zero_sub, abs_neg, abs_of_nonneg (sq_nonneg (a:ℝ)),
    sub_zero, abs_of_pos br, Option.some.injEq, aUnit, bUnit, Option.map_some]
  apply congrArg (fun w : ℝ → Option ℝ => addValue _ (addValue _ (weightValue (some w) lebesgueValue)))
  funext x
  change some |deriv (jumpFn (a:ℝ) b) x| = _
  rw [weight_eq al br]
  by_cases l : x < (a:ℝ) <;> by_cases r : (b:ℝ) < x <;> simp [Value.add, Value.lt, Value.mask, Value.mul, l, r]

end QSym.Distribution.GraphFibre.Coordinates
