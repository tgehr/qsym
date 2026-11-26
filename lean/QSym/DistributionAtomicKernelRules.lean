import QSym.DistributionAtomicAffine
import QSym.DistributionAtomicKernel

/-! Compositional continuity and realization certificates for branching atomic
kernels. Each recursive call can read a different state. A guard can certify
its arms on smaller regions than the set of possible recursive calls. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal
open OmegaCompletePartialOrder

abbrev KernelMap (ι α : Type) := Kernel ι α →o Kernel ι α

namespace KernelMap

def call (next : ι → ι) : KernelMap ι α :=
  ⟨fun k x => k (next x), fun _ _ h x => h (next x)⟩

def add (f g : KernelMap ι α) : KernelMap ι α :=
  ⟨fun k x => sumModel (f k x) (g k x), fun _ _ h x =>
    ⟨fun y => add_le_add ((f.monotone h x).1 y) ((g.monotone h x).1 y),
      Set.union_subset_union (f.monotone h x).2 (g.monotone h x).2⟩⟩

def scale (r : ι → ℝ≥0∞) (f : KernelMap ι α) : KernelMap ι α :=
  ⟨fun k x => scaleModel (r x) (f k x), fun _ _ h x =>
    ⟨fun y => mul_le_mul_left' ((f.monotone h x).1 y) _, (f.monotone h x).2⟩⟩

def branch (p : ι → Bool) (f g : KernelMap ι α) : KernelMap ι α :=
  ⟨fun k x => if p x then f k x else g k x, fun k m h x => by
    cases hp : p x <;> simp [hp, f.monotone h x, g.monotone h x]⟩

theorem add_continuous {f g : KernelMap ι α} (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous (add f g) := by
  apply ωScottContinuous_iff_map_ωSup_of_orderHom.mpr
  intro c
  change (fun x => sumModel (f (ωSup c) x) (g (ωSup c) x)) = _
  rw [hf.map_ωSup_of_orderHom c, hg.map_ωSup_of_orderHom c]
  funext x
  apply Prod.ext
  · funext y
    exact ENNReal.iSup_add_iSup_of_monotone (fun i j hij => (f.monotone (c.monotone hij) x).1 y)
      (fun i j hij => (g.monotone (c.monotone hij) x).1 y)
  · ext y
    change y ∈ (⋃ n, (f (c n) x).2) ∪ (⋃ n, (g (c n) x).2) ↔ y ∈ ⋃ n, (f (c n) x).2 ∪ (g (c n) x).2
    simp only [Set.mem_union, Set.mem_iUnion]
    exact exists_or.symm

theorem scale_continuous (r : ι → ℝ≥0∞) {f : KernelMap ι α} (hf : ωScottContinuous f) :
    ωScottContinuous (scale r f) := by
  apply ωScottContinuous_iff_map_ωSup_of_orderHom.mpr
  intro c
  change (fun x => scaleModel (r x) (f (ωSup c) x)) = _
  rw [hf.map_ωSup_of_orderHom c]
  funext x
  exact Prod.ext (funext fun _ => ENNReal.mul_iSup _ _) rfl

theorem branch_continuous (p : ι → Bool) {f g : KernelMap ι α}
    (hf : ωScottContinuous f) (hg : ωScottContinuous g) : ωScottContinuous (branch p f g) := by
  apply ωScottContinuous_iff_map_ωSup_of_orderHom.mpr
  intro c
  change (fun x => if p x then f (ωSup c) x else g (ωSup c) x) = _
  rw [hf.map_ωSup_of_orderHom c, hg.map_ωSup_of_orderHom c]
  funext x
  have at_state (u : KernelMap ι α) : ωSup (c.map u) x = ⨆ n, u (c n) x := by
    apply Prod.ext
    · funext y
      simp only [Prod.fst_iSup, iSup_apply]
      rfl
    · simp only [Prod.snd_iSup]
      rfl
  simp only [at_state]
  cases hp : p x <;> simp [KernelMap.branch, hp]


end KernelMap

/-- Recursive arguments must present the model on `read`. The body only has
to present its output on `run`, which may be narrowed by a state guard. -/
structure KernelRule (read run : Set ι) (body : (ι → Option (D α)) → ι → Option (D α))
    (step : KernelMap ι α) : Prop where
  continuous : ωScottContinuous step
  lift : ∀ k m, (∀ a ∈ read, ∃ d, k a = some d ∧ Presents d (m a)) →
    ∀ x ∈ run, ∃ e, body k x = some e ∧ Presents e (step m x)

namespace KernelRule

theorem congr {read run F G} {f : KernelMap ι α} (h : KernelRule read run F f)
    (same : ∀ k x, x ∈ run → G k x = F k x) : KernelRule read run G f :=
  ⟨h.continuous, fun k m hm x hx => (same k x hx) ▸ h.lift k m hm x hx⟩

theorem seed {read run : Set ι} {b : ι → Option (D α)} {m : Kernel ι α}
    (source : ∀ x ∈ run, ∃ e, b x = some e ∧ Presents e (m x)) :
    KernelRule read run (fun _ => b) (OrderHom.const _ m) :=
  ⟨ωScottContinuous.const, fun _ _ _ => source⟩

theorem call {read run : Set ι} (next : ι → ι) (safe : Set.MapsTo next run read) :
    KernelRule (α := α) read run (fun k x => k (next x)) (KernelMap.call next) :=
  ⟨ωScottContinuous_iff_map_ωSup_of_orderHom.mpr (fun _ => rfl),
    fun _ _ represented x hx => represented (next x) (safe hx)⟩

theorem applyAt {read run : Set ι} {arg : ι → Option ι} (next : ι → ι)
    (safe : Set.MapsTo next run read) (defined : ∀ x ∈ run, arg x = some (next x)) :
    KernelRule (α := α) read run (fun k x => (arg x).bind k) (KernelMap.call next) :=
  (call next safe).congr fun _ x hx => by rw [defined x hx]; rfl

theorem add {f g : KernelMap ι α} {read run F G} (h : KernelRule read run F f) (j : KernelRule read run G g) :
    KernelRule read run (fun k x => addValue (F k x) (G k x)) (f.add g) := by
  refine ⟨KernelMap.add_continuous h.continuous j.continuous, ?_⟩
  intro k m hm x hx
  obtain ⟨a, ha, pa⟩ := h.lift k m hm x hx
  obtain ⟨b, hb, pb⟩ := j.lift k m hm x hx
  exact ⟨.add a b, by rw [ha, hb]; rfl, presents_sum pa pb⟩

theorem scale {f : KernelMap ι α} {read run F} (h : KernelRule read run F f) (r : ι → ℝ)
    {weight : ι → Option ℝ} (ok : ∀ x ∈ run, weight x = some (r x) ∧ 0 ≤ r x) :
    KernelRule read run (fun k x => scaleValue (weight x) (F k x)) (KernelMap.scale (fun x => ENNReal.ofReal (r x)) f) := by
  refine ⟨KernelMap.scale_continuous _ h.continuous, ?_⟩
  intro k m hm x hx
  obtain ⟨d, hd, pd⟩ := h.lift k m hm x hx
  obtain ⟨hw, hr⟩ := ok x hx
  exact ⟨.scale (r x) d, by rw [hw, hd]; rfl, presents_scale pd hr⟩

theorem branch {read run : Set ι} (p : ι → Bool) {guard : ι → Option Bool}
    (ok : ∀ x ∈ run, guard x = some (p x)) {f g : KernelMap ι α} {F G}
    (h : KernelRule read {x | x ∈ run ∧ p x = true} F f)
    (j : KernelRule read {x | x ∈ run ∧ p x = false} G g) :
    KernelRule read run (fun k x => (guard x).bind (fun b => if b then F k x else G k x)) (KernelMap.branch p f g) := by
  refine ⟨KernelMap.branch_continuous p h.continuous j.continuous, ?_⟩
  intro k m hm x hx
  rw [ok x hx, Option.some_bind]
  cases hb : p x with
  | false => simpa [KernelMap.branch, hb] using j.lift k m hm x ⟨hx, hb⟩
  | true => simpa [KernelMap.branch, hb] using h.lift k m hm x ⟨hx, hb⟩

theorem lfp {states body} {g : KernelMap ι α} (h : KernelRule states states body g) {x : ι} (hx : x ∈ states) :
    kernelModelAt body x = some (g.lfp x) := kernelModelAt_of_step_on _ _ h.continuous _ h.lift hx

end KernelRule
end QSym.Distribution.Atomic
