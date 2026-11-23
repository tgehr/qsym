import QSym.DistributionGraphBridge
import QSym.AxiomCheck

noncomputable section
namespace QSym.Distribution.BranchTests
open GraphFibre MeasureTheory Set

theorem pullback_pair_rule {s : Set ℝ} {f d : ℝ → ℝ} (hs : MeasurableSet s) (hi : InjOn f s)
    (hd : ∀ x ∈ s, HasDerivWithinAt f (d x) s x) (g : ℝ → Option (ℝ × ℝ)) :
    branchIntegral (f '' s) g = branchIntegral s (fun x => (g (f x)).map (|d x| • ·)) := by qsym_rule

theorem regular_root_rule {s : Set ℝ} {f : ℝ → ℝ} (hi : InjOn f s) {x d : ℝ}
    (hx : x ∈ s) (hd : HasStrictDerivAt f d x) (hn : d ≠ 0) :
    fibreOn s f (f x) = some [(x, |d|⁻¹)] := by qsym_rule

/-- The source supplies an injectivity and derivative certificate, with no
hypotheses about the probe, its sign, or an inverse expression. -/
theorem branch_rule {s : Set ℝ} {f d : ℝ → ℝ} (hs : MeasurableSet s) (hi : InjOn f s)
    (hd : ∀ x ∈ s, HasStrictDerivAt f (d x) x) (hn : ∀ x ∈ s, d x ≠ 0)
    (h : ℝ → ℝ → Option ℝ) :
    branchIntegral s (fun x => h x (f x)) = partialIntegral volume (fun y =>
      (fibreOn s f y).bind (fun atoms => observe atoms (fun x => h x y))) := by qsym_rule

open Classical in
theorem masked_branch_rule {s : Set ℝ} {f d : ℝ → ℝ} (hs : MeasurableSet s) (hi : InjOn f s)
    (hd : ∀ x ∈ s, HasStrictDerivAt f (d x) x) (hn : ∀ x ∈ s, d x ≠ 0)
    (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => Value.mul (some (sourceWeight s x)) (h x (f x))) =
      if ∀ x ∉ s, Value.Defined (h x (f x)) then
        partialIntegral volume (fun y => (fibreOn s f y).bind (fun atoms => observe atoms (fun x => h x y)))
      else none := by qsym_rule

theorem pullback_cover_rule {s : Set ℝ} {f g i d : ℝ → ℝ} {y : ℝ} {xs zs : List ℝ}
    (outer : RootCover s g y xs) (inner : GlobalInverseBranch f i d)
    (order : zs.Sorted (· < ·)) (roots : ∀ x, x ∈ zs ↔ x ∈ xs.map i) :
    RootCover (f ⁻¹' s) (fun x => g (f x)) y zs := by qsym_rule

theorem restrict_cover_rule {s : Set ℝ} {f : ℝ → ℝ} {y : ℝ} {xs : List ℝ}
    (cover : RootCover s f y xs) (r : Set ℝ) [DecidablePred (· ∈ r)] :
    RootCover (s ∩ r) f y (xs.filter fun x => decide (x ∈ r)) := by qsym_rule

theorem finite_density_rule {f d : ℝ → ℝ} {y : ℝ} {xs : List ℝ}
    (cover : RootCover univ f y xs) (p : ℝ → Option Bool) (hm : Measurable f)
    (hd : ∀ x ∈ xs, p x ≠ some false → HasStrictDerivAt f (d x) x) :
    densityAtValue (realPushforwardOnValue (some p) (some fun x => some (f x))) (some y) =
      xs.foldr (fun x acc => Value.add (Value.mask (p x) (Value.inv (some |d x|))) acc) (some 0) := by qsym_rule

/-- The only inverse point is a cusp and is explicitly excluded. -/
theorem excluded_cusp : densityAtValue (realPushforwardOnValue (some fun _ => some false)
    (some fun x => some |x|)) (some 0) = some 0 := by
  have cover : RootCover univ (fun x : ℝ => |x|) 0 [0] :=
    ⟨by simp [List.Sorted], fun x => by simp⟩
  simpa [Value.mask, Value.add] using cover.density (fun _ => some false) continuous_abs.measurable
    (fun _ => 0) (fun _ _ h => (h rfl).elim)

theorem compose_branch_rule {f g i j d e : ℝ → ℝ} (a : GlobalInverseBranch f i d)
    (b : GlobalInverseBranch g j e) :
    GlobalInverseBranch (fun x => g (f x)) (fun y => i (j y)) (fun x => e (f x) * d x) := by qsym_rule

theorem total_density_rule {f root slope : ℝ → ℝ} (branch : GlobalInverseBranch f root slope)
    (p : ℝ → Option Bool) :
    (∀ y, Value.Defined (densityAtValue (realPushforwardOnValue (some p) (some fun x => some (f x))) (some y))) ↔
      (∀ x, Value.Defined (p x)) ∧ (∀ x, slope x = 0 → p x = some false) := by qsym_rule

theorem change_coordinates_rule {f root slope : ℝ → ℝ} (branch : GlobalInverseBranch f root slope)
    (p : ℝ → Option Bool) (hp : ∀ x, Value.Defined (p x)) (hc : ∀ x, slope x = 0 → p x = some false) :
    realPushforwardOnValue (some p) (some fun x => some (f x)) =
      densityValue (some fun y => Value.mask (p (root y)) (Value.inv (some |slope (root y)|))) := by qsym_rule

private def cube (x : ℝ) := x ^ 3
private abbrev regular : Set ℝ := ({0} : Set ℝ)ᶜ

private theorem cube_deriv (x : ℝ) : HasStrictDerivAt cube (3 * x^2) x := by
  simpa [cube] using hasStrictDerivAt_pow 3 x

private theorem cube_inj : Function.Injective cube :=
  (show Odd 3 from ⟨1, rfl⟩).pow_injective

theorem cube_fibres :
    fibre cube 8 = some [(2, 1/12)] ∧ fibre cube 0 = none ∧ fibreOn regular cube 0 = some [] := by
  constructor
  · have eq := fibreOn_of_injOn (s := univ) cube_inj.injOn (mem_univ 2) (cube_deriv 2) (by norm_num)
    norm_num [cube, one_div] at eq ⊢
    exact eq
  constructor
  · rw [← fibreOn_univ]
    apply fibreOn_of_critical (x := 0) (mem_univ _) (by norm_num [cube])
    rw [(cube_deriv 0).hasDerivAt.deriv]
    norm_num
  · apply fibreOn_of_notMem_image
    rintro ⟨x, hx, he⟩
    exact hx (cube_inj (he.trans (by norm_num [cube] : (0 : ℝ) = cube 0)))

private def cubeTest (h : ℝ → ℝ → Option ℝ) := fun y =>
  (fibreOn regular cube y).bind (fun atoms => observe atoms (fun x => h x y))

open Classical in
theorem cube_reconstruction (h : ℝ → ℝ → Option ℝ) :
    partialIntegral volume (fun x => h x (cube x)) =
      if Value.Defined (h 0 0) then partialIntegral volume (cubeTest h) else none := by
  have hae : (univ : Set ℝ) =ᵐ[volume] regular := by
    filter_upwards [(countable_singleton (0 : ℝ)).ae_not_mem volume] with x hx
    exact propext ⟨fun _ => hx, fun _ => mem_univ x⟩
  have hn : ∀ x ∈ regular, 3*x^2 ≠ 0 := fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero _ hx)
  simpa [branchIntegral_univ, regular, cubeTest, cube] using
    injectiveBranch_disintegrates_ae (subset_univ regular) hae (measurableSet_singleton _).compl
      cube_inj.injOn (fun x _ => cube_deriv x) hn h

/-- Both source half-lines map onto the same positive target. The rule sums
their separately integrated signed observations. -/
theorem square_branches (h : ℝ → ℝ → Option ℝ) :
    branchIntegral (Iio 0 ∪ Ioi 0) (fun x => h x (square x)) =
      Value.add (partialIntegral volume (fun y => (fibreOn (Iio 0) square y).bind
        (fun atoms => observe atoms (fun x => h x y))))
        (partialIntegral volume (fun y => (fibreOn (Ioi 0) square y).bind
          (fun atoms => observe atoms (fun x => h x y)))) := by
  have hi {s : Set ℝ} (side : s ⊆ Iio 0 ∨ s ⊆ Ioi 0) : InjOn square s := by
    intro x hx z hz he
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
    · exact he
    · rcases side with hn | hp
      · linarith [show x < 0 from hn hx, show z < 0 from hn hz]
      · linarith [show 0 < x from hp hx, show 0 < z from hp hz]
  have hd (x : ℝ) : HasStrictDerivAt square (2*x) x := by simpa [square] using hasStrictDerivAt_pow 2 x
  have dis : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
    apply Set.disjoint_left.mpr
    intro x hx hz
    exact (not_lt_of_ge (le_of_lt (show x < 0 from hx))) (show 0 < x from hz)
  rw [branchIntegral_union dis.aedisjoint measurableSet_Ioi.nullMeasurableSet,
    branch_rule measurableSet_Iio (hi (Or.inl Subset.rfl)) (fun x _ => hd x)
      (fun x hx => mul_ne_zero (by norm_num) (ne_of_lt hx)),
    branch_rule measurableSet_Ioi (hi (Or.inr Subset.rfl)) (fun x _ => hd x)
      (fun x hx => mul_ne_zero (by norm_num) (ne_of_gt hx))]

/-- The missing critical probe matters even though every regular observation
of this probe is defined and zero. -/
theorem missing_critical : partialIntegral volume (fun x : ℝ => if x = 0 then none else some (0 : ℝ)) =
    none ∧ partialIntegral volume (cubeTest (fun x _ => if x = 0 then none else some 0)) = some 0 := by
  constructor
  · rw [cube_reconstruction (fun x _ => if x = 0 then none else some 0)]
    simp [Value.Defined]
  · unfold cubeTest
    rw [← branch_rule (measurableSet_singleton (0 : ℝ)).compl (f := cube) cube_inj.injOn
      (fun x _ => cube_deriv x) (fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero _ hx))
      (fun x _ => if x = 0 then none else some 0)]
    have eq : EqOn (fun x : ℝ => if x = 0 then none else some (0 : ℝ)) (fun _ => some 0) regular := by
      intro x hx
      simp [show x ≠ 0 from hx]
    rw [branchIntegral_congr (measurableSet_singleton _).compl eq]
    simp [branchIntegral, Value.Defined]

theorem smooth_coordinate_rule {ι : Type} {sheets : ι → ℝ → Option ℝ} {g : ℝ → ℝ}
    (hg : Coordinates.Describes sheets g) :
    Coordinates.value (some sheets) = weightValue (some fun x => some |deriv g x|) lebesgueValue := by
  qsym_rule

theorem smooth_coordinate_restriction_rule {ι : Type} {sheets : ι → ℝ → Option ℝ} {g : ℝ → ℝ}
    (hg : Coordinates.Describes sheets g) (p : ℝ → Option Bool) :
    Coordinates.restricted (some p) (some sheets) =
      weightValue (some fun x => Value.mask (p (g x)) (some |deriv g x|)) lebesgueValue := by
  qsym_rule

#qsym_check_axioms smooth_coordinate_rule
#qsym_check_axioms smooth_coordinate_restriction_rule
#qsym_check_axioms Coordinates.branch_image
#qsym_check_axioms Coordinates.square
theorem joined_coordinate_rule {l r : ℝ → ℝ} {a : ℝ} (hl : ContDiff ℝ 1 l) (hr : ContDiff ℝ 1 r)
    (hv : l a = r a) (hd : deriv l a = deriv r a) :
    Coordinates.value (Tensor.consValue (some fun x => some (if x < a then l x else r x)) Tensor.nilValue) =
      weightValue (some fun x => some |if x < a then deriv l x else deriv r x|) lebesgueValue := by qsym_rule

open Classical in
/-- The nonconstant pieces of [x < -1]x² + [1 < x]x both visit
(1,∞). Separate tests allow those visits to be observed independently. -/
theorem jumping_coordinate_pieces (u v : ℝ → Option ℝ) :
    branchIntegral (Iio (-1) ∪ Ioi 1) (fun x : ℝ =>
      if x ∈ Iio (-1) then (u (x^2)).map (|2*x| • ·) else (v x).map (|(1:ℝ)| • ·)) =
    Value.add (branchIntegral ((fun x : ℝ => x^2) '' Iio (-1)) u) (branchIntegral (id '' Ioi 1) v) := by
  apply Coordinates.branch_pair_image (dl := fun x => 2*x) (dr := fun _ => 1)
    measurableSet_Iio measurableSet_Ioi
  · exact Set.disjoint_left.mpr fun x (hl : x < -1) (hr : 1 < x) => by linarith
  · intro x (hx : x < -1) y (hy : y < -1) (h : x^2 = y^2)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · exact h
    · linarith
  · exact Set.injOn_id _
  · intro x _
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  · exact fun x _ => (hasDerivAt_id x).hasDerivWithinAt

theorem variation_coordinate_rule {ι : Type} {gs : ι → ℝ → Option ℝ} {c : Coordinates.VariationChart}
    (hc : Coordinates.Displays gs c) :
    Coordinates.value (some gs) = c.present none := by qsym_rule

#qsym_check_axioms variation_coordinate_rule
#qsym_check_axioms Coordinates.VariationChart.atCut_of_limits
#qsym_check_axioms jumping_coordinate_pieces
#qsym_check_axioms joined_coordinate_rule
#qsym_check_axioms Coordinates.contDiff_join
#qsym_check_axioms Coordinates.pieces_eq
#qsym_check_axioms Coordinates.restricted_pieces_eq
#qsym_check_axioms Coordinates.rayLinear
#qsym_check_axioms Coordinates.corner_density
#qsym_check_axioms Coordinates.corner_integral
#qsym_check_axioms Coordinates.corner_pairing
#qsym_check_axioms Coordinates.twoRayJumps
#qsym_check_axioms Coordinates.rayPower
#qsym_check_axioms square_joint_inverse_split
#qsym_check_axioms InverseSheet.reciprocal
#qsym_check_axioms inverseCover_joint_split
#qsym_check_axioms inversePart_pairing_split
#qsym_check_axioms inversePart_density_roots
#qsym_check_axioms square_positiveSource_disintegrates
#qsym_check_axioms branchIntegral_image
#qsym_check_axioms injectiveBranch_disintegrates_ae
#qsym_check_axioms pullback_pair_rule
#qsym_check_axioms pullback_cover_rule
#qsym_check_axioms restrict_cover_rule
#qsym_check_axioms RootCover.observe_weighted
#qsym_check_axioms finite_density_rule
#qsym_check_axioms excluded_cusp
#qsym_check_axioms compose_branch_rule
#qsym_check_axioms total_density_rule
#qsym_check_axioms change_coordinates_rule
#qsym_check_axioms regular_root_rule
#qsym_check_axioms branch_rule
#qsym_check_axioms masked_branch_rule
#qsym_check_axioms square_branches
#qsym_check_axioms cube_fibres
#qsym_check_axioms cube_reconstruction
#qsym_check_axioms missing_critical
end QSym.Distribution.BranchTests
