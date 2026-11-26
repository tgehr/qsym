import QSym.DistributionCoordinateVariation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Smooth changes of the displayed value of a piecewise coordinate. A left
inverse on the values actually visited recovers differentiability of the inner
coordinate. The two traces are checked separately because one can be omitted
from the image at a jump. -/
noncomputable section
namespace QSym.Distribution.GraphFibre.Coordinates.VariationChart
open Filter Set Topology

structure ChangeOn (s : Set ℝ) (h : ℝ → ℝ) where
  inverse : ℝ → ℝ
  leftInv : Set.LeftInvOn inverse h s
  smooth : ∀ u ∈ s, ContDiffAt ℝ 1 h u
  inverseDiff : ∀ u ∈ s, DifferentiableAt ℝ inverse (h u)

/-- At a jump the branch predicate ranges over the interval between the new
traces. Its endpoints, as well as all the actual values, must admit the change. -/
structure RangeIn (c : VariationChart) (s : Set ℝ) : Prop where
  value : ∀ x, c.coord x ∈ s
  traces : ∀ a ∈ c.cuts, Function.leftLim c.coord a ∈ s ∧ Function.rightLim c.coord a ∈ s

theorem RangeIn.univ (c : VariationChart) : RangeIn c Set.univ :=
  ⟨fun _ => trivial, fun _ _ => ⟨trivial, trivial⟩⟩

/-- For a continuous join, checking the actual value checks both traces. -/
theorem RangeIn.of_continuousAt {c : VariationChart} {s : Set ℝ}
    (values : ∀ x, c.coord x ∈ s) (cuts : ∀ a ∈ c.cuts, ContinuousAt c.coord a) :
    RangeIn c s := by
  refine ⟨values, fun a ha => ?_⟩
  have t := cuts a ha
  rw [leftLim_eq_of_tendsto (NeBot.ne inferInstance) (t.continuousWithinAt (s := Iio a)),
    rightLim_eq_of_tendsto (NeBot.ne inferInstance) (t.continuousWithinAt (s := Ioi a))]
  exact ⟨values a, values a⟩

theorem atCut_of_continuousAt {g : ℝ → ℝ} {a : ℝ} (t : ContinuousAt g a)
    (p : Option (ℝ → Option Bool)) :
    atCut g a p = corner a (p.elim (some true) (fun q => q (g a))) := by
  rw [atCut_of_limits (t.continuousWithinAt (s := Iio a)) (t.continuousWithinAt (s := Ioi a)),
    if_pos rfl]

namespace ChangeOn

/-- The inverse function theorem supplies the inverse derivative on an open
range of input values. The coordinate change need only be injective on that set. -/
def ofInjOn {s : Set ℝ} {f : ℝ → ℝ} (hs : IsOpen s) (inj : InjOn f s)
    (sm : ∀ u ∈ s, ContDiffAt ℝ 1 f u) (hn : ∀ u ∈ s, deriv f u ≠ 0) : ChangeOn s f := by
  refine ⟨_, inj.leftInvOn_invFunOn, sm, ?_⟩
  intro u hu
  have left : ∀ᶠ x in 𝓝 u, Function.invFunOn f s (f x) = x := by
    filter_upwards [hs.mem_nhds hu] with x hx using inj.leftInvOn_invFunOn hx
  exact ((sm u hu).hasStrictDerivAt le_rfl |>.to_local_left_inverse (hn u hu) left).hasDerivAt.differentiableAt
variable {s : Set ℝ} {h g : ℝ → ℝ}

theorem differentiable_iff (e : ChangeOn s h) (values : ∀ x, g x ∈ s) (x : ℝ) :
    DifferentiableAt ℝ (h ∘ g) x ↔ DifferentiableAt ℝ g x := by
  constructor
  · intro d
    have eq : e.inverse ∘ (h ∘ g) = g := funext fun y => e.leftInv (values y)
    exact eq ▸ (e.inverseDiff _ (values x)).comp x d
  · exact fun d => ((e.smooth _ (values x)).differentiableAt le_rfl).comp x d

/-- Lean's total derivative is zero at a cut. The point observation there is
separately carried by the chart event. -/
theorem deriv_comp (e : ChangeOn s h) (values : ∀ x, g x ∈ s) (x : ℝ) :
    deriv (h ∘ g) x = deriv h (g x) * deriv g x := by
  by_cases d : DifferentiableAt ℝ g x
  · exact _root_.deriv_comp x ((e.smooth _ (values x)).differentiableAt le_rfl) d
  · rw [deriv_zero_of_not_differentiableAt (d ∘ (e.differentiable_iff values x).mp),
      deriv_zero_of_not_differentiableAt d, mul_zero]

def exp : ChangeOn univ Real.exp :=
  ⟨Real.log, fun _ _ => Real.log_exp _, fun _ _ => Real.contDiff_exp.contDiffAt,
    fun _ _ => Real.differentiableAt_log (Real.exp_pos _).ne'⟩

def sinh : ChangeOn univ Real.sinh :=
  ⟨Real.arsinh, fun _ _ => Real.arsinh_sinh _, fun _ _ => Real.contDiff_sinh.contDiffAt,
    fun _ _ => Real.differentiable_arsinh _⟩

theorem tanh_deriv (x : ℝ) : deriv Real.tanh x = ((Real.cosh x)^2)⁻¹ := by
  have eq : Real.tanh = fun v => Real.sinh v / Real.cosh v := funext Real.tanh_eq_sinh_div_cosh
  rw [eq, ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne').deriv]
  rw [← sq, ← sq, Real.cosh_sq_sub_sinh_sq, one_div]

theorem tanh_mono : StrictMono Real.tanh :=
  strictMono_of_deriv_pos fun x => (tanh_deriv x).symm ▸ inv_pos.mpr (sq_pos_of_pos (Real.cosh_pos x))

def tanh : ChangeOn univ Real.tanh := by
  apply ofInjOn isOpen_univ tanh_mono.injective.injOn
  · intro u _
    have eq : Real.tanh = fun v => Real.sinh v / Real.cosh v := funext Real.tanh_eq_sinh_div_cosh
    rw [eq]
    exact (Real.contDiff_sinh.div Real.contDiff_cosh (fun x => (Real.cosh_pos x).ne')).contDiffAt
  · intro u _
    rw [tanh_deriv]
    positivity

def arctan : ChangeOn univ Real.arctan :=
  ⟨Real.tan, fun _ _ => Real.tan_arctan _, fun _ _ => Real.contDiff_arctan.contDiffAt,
    fun u _ => Real.differentiableAt_tan.mpr (Real.cos_arctan_pos u).ne'⟩

def arsinh : ChangeOn univ Real.arsinh :=
  ⟨Real.sinh, fun _ _ => Real.sinh_arsinh _, fun _ _ => Real.contDiff_arsinh.contDiffAt,
    fun _ _ => Real.differentiable_sinh _⟩

def log : ChangeOn (Ioi 0) Real.log :=
  ⟨Real.exp, fun _ hu => Real.exp_log hu, fun _ hu => Real.contDiffAt_log.mpr (ne_of_gt hu),
    fun _ _ => Real.differentiable_exp _⟩

def sqrt : ChangeOn (Ioi 0) Real.sqrt :=
  ⟨fun x => x^2, fun _ hu => Real.sq_sqrt (le_of_lt hu),
    fun _ hu => Real.contDiffAt_sqrt (ne_of_gt hu), fun _ _ => differentiableAt_id.pow 2⟩

def reciprocal : ChangeOn {u : ℝ | u ≠ 0} (fun u => u⁻¹) :=
  ⟨fun x => x⁻¹, fun _ _ => inv_inv _, fun _ hu => contDiffAt_id.inv hu,
    fun _ hu => differentiableAt_id.inv (inv_ne_zero hu)⟩

/-- Equal old traces retain the pointwise corner. At a jump its weight and
every restriction use the transformed endpoints, including for a decreasing
change or for two traces in different components of the range. -/
theorem atCut {a l r : ℝ} (e : ChangeOn s h) (hl : Tendsto g (𝓝[<] a) (𝓝 l))
    (hr : Tendsto g (𝓝[>] a) (𝓝 r)) (ls : l ∈ s) (rs : r ∈ s)
    (p : Option (ℝ → Option Bool)) :
    VariationChart.atCut (h ∘ g) a p = if l = r then
      corner a (p.elim (some true) (fun q => q (h (g a))))
    else atom a (p.elim (some |h r - h l|) (fun q => branchIntegral (uIcc (h l) (h r))
      (fun z => Value.mask (q z) (some 1)))) := by
  rw [atCut_of_limits (((e.smooth _ ls).continuousAt.tendsto).comp hl)
    (((e.smooth _ rs).continuousAt.tendsto).comp hr)]
  simp only [e.leftInv.injOn.eq_iff ls rs, Function.comp_apply]

end ChangeOn

/-- Postcomposition retains exactly the intrinsic cuts. It also preserves the
endpoint condition for a genuine jump, even if the original traces were reversed. -/
def postcompose (c : VariationChart) {s h} (e : ChangeOn s h) (range : RangeIn c s) :
    VariationChart where
  coord := h ∘ c.coord
  cuts := c.cuts
  sorted := c.sorted
  exceptional x := (c.exceptional x).trans (not_congr (e.differentiable_iff range.value x).symm)
  regular x hx := (e.smooth _ (range.value x)).comp x (c.regular x hx)
  limits a ha := by
    obtain ⟨l, r, hl, hr, side⟩ := c.limits a ha
    obtain ⟨ls, rs⟩ := range.traces a ha
    rw [leftLim_eq_of_tendsto (NeBot.ne inferInstance) hl] at ls
    rw [rightLim_eq_of_tendsto (NeBot.ne inferInstance) hr] at rs
    exact ⟨h l, h r, ((e.smooth _ ls).continuousAt.tendsto).comp hl,
      ((e.smooth _ rs).continuousAt.tendsto).comp hr, side.imp (congrArg h) (congrArg h)⟩

/-- The regular part changes by the ordinary Jacobian. Exceptional parts are
recomputed in the new value coordinate before taking their sum. -/
theorem present_postcompose (c : VariationChart) {s h} (e : ChangeOn s h)
    (range : RangeIn c s) (p : Option (ℝ → Option Bool)) :
    (c.postcompose e range).present p =
      c.cuts.foldr (fun a d => addValue (atCut (h ∘ c.coord) a p) d)
        (weightValue (some fun x =>
          let w := some (|deriv h (c.coord x)| * |deriv c.coord x|)
          p.elim w (fun q => Value.mask (q (h (c.coord x))) w)) lebesgueValue) := by
  unfold present
  simp only [postcompose, e.deriv_comp range.value, abs_mul, Function.comp_apply]

end QSym.Distribution.GraphFibre.Coordinates.VariationChart
