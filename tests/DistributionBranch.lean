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

#qsym_check_axioms square_positiveSource_disintegrates
#qsym_check_axioms branchIntegral_image
#qsym_check_axioms injectiveBranch_disintegrates_ae
#qsym_check_axioms pullback_pair_rule
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
