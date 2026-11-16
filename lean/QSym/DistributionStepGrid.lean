import QSym.DistributionStepSource
import QSym.Binding

noncomputable section
namespace QSym.Distribution.StepSource

def ZeroOrUndefined {α : Type} [Zero α] (v : Option α) : Prop := v = none ∨ v = some 0

theorem ZeroOrUndefined.value {α : Type} [Zero α] {v : Option α}
    (h : ZeroOrUndefined v) (hd : Value.Defined v) : v = some 0 := by
  rcases h with h | h
  · obtain ⟨x, hx⟩ := hd; rw [h] at hx; cases hx
  · exact h

theorem zero_value {α : Type} [Zero α] : ZeroOrUndefined (some (0 : α)) := Or.inr rfl

theorem zero_numericN (ρ : Env) (t : Expr .natural) (h : Numeric.calculate t = some 0) :
    ZeroOrUndefined (t.eval ρ) := Or.inr (Numeric.calculate_sound ρ t 0 h)

theorem zero_numericZ (ρ : Env) (t : Expr .integer) (h : Numeric.calculate t = some 0) :
    ZeroOrUndefined (t.eval ρ) := Or.inr (Numeric.calculate_sound ρ t 0 h)

theorem zero_numericQ (ρ : Env) (t : Expr .rational) (h : Numeric.calculate t = some 0) :
    ZeroOrUndefined (t.eval ρ) := Or.inr (Numeric.calculate_sound ρ t 0 h)

theorem zero_numericR (ρ : Env) (t : Expr .real) (h : Numeric.calculate t = some 0) :
    ZeroOrUndefined (t.eval ρ) := by
  apply Or.inr
  simpa [Numeric.denote] using Numeric.calculate_sound ρ t 0 h

theorem zero_add {α : Type} [AddZeroClass α] {a b : Option α}
    (ha : ZeroOrUndefined a) (hb : ZeroOrUndefined b) : ZeroOrUndefined (Value.add a b) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [Value.add, ha, hb, ZeroOrUndefined]

theorem zero_mul_left {α : Type} [MulZeroClass α] {a b : Option α}
    (ha : ZeroOrUndefined a) : ZeroOrUndefined (Value.mul a b) := by
  rcases ha with ha | ha <;> cases b <;> simp [Value.mul, ha, ZeroOrUndefined]

theorem zero_mul_right {α : Type} [MulZeroClass α] {a b : Option α}
    (hb : ZeroOrUndefined b) : ZeroOrUndefined (Value.mul a b) := by
  rcases hb with hb | hb <;> cases a <;> simp [Value.mul, hb, ZeroOrUndefined]

theorem zero_mask {α : Type} [Zero α] (p : Option Bool) {v : Option α}
    (hv : ZeroOrUndefined v) : ZeroOrUndefined (Value.mask p v) := by
  cases p with
  | none => exact Or.inl rfl
  | some p => cases p <;> simp_all [Value.mask, ZeroOrUndefined]

theorem zero_mask_false {α : Type} [Zero α] {p : Option Bool} (v : Option α)
    (hp : p = some false) : ZeroOrUndefined (Value.mask p v) := by
  rw [hp]; exact zero_value

theorem zero_unary {α β : Type} [Zero α] [Zero β] (op : Function1 α β)
    (h : op.value 0 = 0) {v : Option α} (hv : ZeroOrUndefined v) :
    ZeroOrUndefined (op.apply v) := by
  rcases hv with hv | hv <;> rw [hv]
  · exact Or.inl rfl
  · by_cases hd : op.domain 0 <;> simp [Function1.apply, hd, h, ZeroOrUndefined]

theorem zero_castNZ {v : Option ℕ} (h : ZeroOrUndefined v) : ZeroOrUndefined (Functions.castNZ.apply v) :=
  zero_unary Functions.castNZ rfl h

theorem zero_castZQ {v : Option ℤ} (h : ZeroOrUndefined v) : ZeroOrUndefined (Functions.castZQ.apply v) := by
  apply zero_unary Functions.castZQ _ h
  simp [Functions.castZQ]

theorem zero_castQR {v : Option ℚ} (h : ZeroOrUndefined v) : ZeroOrUndefined (Functions.castQR.apply v) := by
  apply zero_unary Functions.castQR _ h
  simp [Functions.castQR]

theorem zero_binary {α β γ : Type} [Zero α] [Zero β] [Zero γ] (op : Function2 α β γ)
    (h : op.value 0 0 = 0) {a : Option α} {b : Option β}
    (ha : ZeroOrUndefined a) (hb : ZeroOrUndefined b) : ZeroOrUndefined (op.apply a b) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · by_cases hd : op.domain 0 0 <;> simp [Function2.apply, hd, h, ZeroOrUndefined]

theorem zero_binary_left {α β γ : Type} [Zero α] [Zero γ] (op : Function2 α β γ)
    (h : ∀ b, op.value 0 b = 0) {a : Option α} (b : Option β)
    (ha : ZeroOrUndefined a) : ZeroOrUndefined (op.apply a b) := by
  rcases ha with ha | ha <;> rw [ha]
  · exact Or.inl rfl
  · cases b with
    | none => exact Or.inl rfl
    | some b => by_cases hd : op.domain 0 b <;> simp [Function2.apply, hd, h, ZeroOrUndefined]

theorem zero_binary_right {α β γ : Type} [Zero β] [Zero γ] (op : Function2 α β γ)
    (h : ∀ a, op.value a 0 = 0) (a : Option α) {b : Option β}
    (hb : ZeroOrUndefined b) : ZeroOrUndefined (op.apply a b) := by
  rcases hb with hb | hb <;> rw [hb] <;> cases a with
  | none => exact Or.inl rfl
  | some a =>
    first | exact Or.inl rfl
          | by_cases hd : op.domain a 0 <;> simp [Function2.apply, hd, h, ZeroOrUndefined]

def gridCells (a : ℚ) : List ℚ → List StepCell
  | [] => []
  | b :: bs => ⟨a, b, ((a+b)/2 : ℚ)⟩ :: gridCells b bs

def gridProbes (a : ℚ) : List ℚ → List ℝ
  | [] => [a, (a+1 : ℚ)]
  | b :: bs => (a : ℝ) :: (((a+b)/2 : ℚ) : ℝ) :: gridProbes b bs

def lastProbe (a : ℚ) : List ℚ → ℚ
  | [] => a+1
  | b :: bs => lastProbe b bs

inductive Tail (f : ℝ → Option ℝ) : ℚ → List ℚ → Prop
  | nil (a : ℚ) (h : Uniform (.after a) f) : Tail f a []
  | cons {a b : ℚ} {bs : List ℚ} (ordered : a < b)
      (h : Uniform (.between a b) f) (tail : Tail f b bs) : Tail f a (b :: bs)

theorem Tail.ordered {f a bs} (h : Tail f a bs) :
    ∀ c ∈ gridCells a bs, c.lower ≤ c.upper := by
  induction h with
  | nil => simp [gridCells]
  | @cons a b bs hab h ht ih =>
    intro c hc
    rcases List.mem_cons.mp hc with hc | hc
    · subst c; exact le_of_lt (Rat.cast_lt.mpr hab)
    · exact ih c hc

theorem Tail.zero_left {f a bs} (h : Tail f a bs) {x : ℝ} (hx : x < a) :
    stepValue f (gridCells a bs) x = 0 := by
  induction h with
  | nil => rfl
  | @cons a b bs hab h ht ih =>
    have hab' : (a : ℝ) < b := Rat.cast_lt.mpr hab
    have hxb : x < b := hx.trans hab'
    have hn : ¬ ((a : ℝ) ≤ x ∧ x ≤ b) := by intro ha; linarith [ha.1]
    simp only [gridCells, stepValue, if_neg hn, ih hxb, _root_.zero_add]

theorem Tail.total {f a bs} (h : Tail f a bs)
    (hd : ∀ x ∈ gridProbes a bs, Value.Defined (f x)) :
    ∀ x : ℝ, (a : ℝ) ≤ x → Value.Defined (f x) := by
  induction h with
  | nil a h =>
    intro x hx
    by_cases he : x = a
    · subst x; exact hd _ (by simp [gridProbes])
    · have hx' : (a : ℝ) < x := lt_of_le_of_ne hx (Ne.symm he)
      rw [h x hx']
      exact hd _ (by simp [Region.sample, gridProbes])
  | @cons a b bs hab h ht ih =>
    intro x hx
    by_cases he : x = a
    · subst x; exact hd _ (by simp [gridProbes])
    · by_cases hxb : x < b
      · rw [h x ⟨lt_of_le_of_ne hx (Ne.symm he), hxb⟩]
        exact hd _ (by simp [Region.sample, gridProbes])
      · exact ih (fun y hy => hd y (by simp [gridProbes, hy])) x (le_of_not_gt hxb)

theorem Tail.away {f a bs} (h : Tail f a bs)
    (hd : ∀ x ∈ gridProbes a bs, Value.Defined (f x))
    (hz : ZeroOrUndefined (f (lastProbe a bs : ℝ))) :
    ∀ x : ℝ, (a : ℝ) < x → (∀ p ∈ a :: bs, x ≠ (p : ℝ)) →
      f x = some (stepValue f (gridCells a bs) x) := by
  induction h with
  | nil a h =>
    intro x hx _
    rw [h x hx]
    exact hz.value (hd _ (by simp [lastProbe, gridProbes]))
  | @cons a b bs hab h ht ih =>
    intro x hx hp
    by_cases hxb : x < b
    · obtain ⟨v, hv⟩ := hd (((a+b)/2 : ℚ) : ℝ) (by simp [gridProbes])
      rw [h x ⟨hx, hxb⟩]
      have hi : (a : ℝ) ≤ x ∧ x ≤ b := ⟨le_of_lt hx, le_of_lt hxb⟩
      simp only [Region.sample, hv, gridCells, stepValue,
        if_pos hi, ht.zero_left hxb, Option.getD_some, _root_.add_zero]
    · have hne := hp b (by simp)
      have hbx : (b : ℝ) < x := lt_of_le_of_ne (le_of_not_gt hxb) (Ne.symm hne)
      have hi := ih (fun y hy => hd y (by simp [gridProbes, hy])) hz x hbx
        (fun p hp' => hp p (by simp [hp']))
      have hn : ¬ ((a : ℝ) ≤ x ∧ x ≤ b) := by intro ha; linarith [ha.2]
      simpa only [gridCells, stepValue, if_neg hn, _root_.zero_add] using hi

theorem grid_certificate {f a bs} (hl : Uniform (.before a) f) (ht : Tail f a bs)
    (zl : ZeroOrUndefined (f ((a-1 : ℚ) : ℝ)))
    (zr : ZeroOrUndefined (f (lastProbe a bs : ℝ))) :
    StepCertificate f (gridCells a bs) (((a-1 : ℚ) : ℝ) :: gridProbes a bs)
      ((a :: bs).map (fun q : ℚ => (q : ℝ))) := by
  refine ⟨ht.ordered, ?_, ?_⟩
  · intro hd x
    by_cases hx : x < a
    · rw [hl x hx]; exact hd _ (by simp [Region.sample])
    · exact ht.total (fun y hy => hd y (by simp [hy])) x (le_of_not_gt hx)
  · intro hd x hp
    by_cases hx : x < a
    · rw [hl x hx, ht.zero_left hx]
      exact zl.value (hd _ (by simp [Region.sample]))
    · have hne : x ≠ (a : ℝ) := hp _ (by simp)
      exact ht.away (fun y hy => hd y (by simp [hy])) zr x
        (lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hne))
        (fun p hp' => hp (p : ℝ) (List.mem_map_of_mem (f := fun q : ℚ => (q : ℝ)) hp'))

-- Keep sampling and environment substitution out of definitional equality
-- comparisons of whole exported integrals.
theorem eval_sample {Γ : List Binding.Ty} (b : Binding.Expr (.scalar .real :: Γ) (.scalar .real))
    (t : Binding.Expr Γ (.scalar .real)) (ξ : Env) (ρ : Binding.Env Γ) (q : ℚ)
    (h : t.eval ξ ρ = some (q : ℝ)) :
    (Binding.Expr.app (.lam b) t).eval ξ ρ = b.eval ξ (ρ.cons (some (q : ℝ))) := by
  simp only [Binding.Expr.eval, Option.some_bind, h]

theorem rat_argument {α : Type} (f : ℝ → α) (a b : ℚ) (h : a = b) :
    f (a : ℝ) = f (b : ℝ) := congrArg (fun q : ℚ => f (q : ℝ)) h

theorem seq_congr {α β : Type} {a a' : Option α} {b b' : Option β}
    (ha : a = a') (hb : b = b') : a.bind (fun _ => b) = a'.bind (fun _ => b') :=
  congrArg₂ (fun x y => x.bind (fun _ => y)) ha hb

theorem numeric_one (x : ℝ) : DensityProgram.lebesgue.density x =
    some (Numeric.denote (s := .real) (1 : ℚ)) := by
  norm_num [DensityProgram.density, Numeric.denote]

theorem numeric_mul {a b : Option ℝ} (x y : ℚ)
    (ha : a = some (Numeric.denote (s := .real) x))
    (hb : b = some (Numeric.denote (s := .real) y)) :
    Value.mul a b = some (Numeric.denote (s := .real) (x*y)) := by
  rw [ha, hb]; simp [Value.mul, Numeric.denote, Rat.cast_mul]

/-- Explicit finite evidence, assembled with constructors by the exporter. -/
inductive ProbeFacts (P : ℝ → Prop) : List ℝ → Prop
  | nil : ProbeFacts P []
  | cons {x xs} : P x → ProbeFacts P xs → ProbeFacts P (x :: xs)

theorem ProbeFacts.all {P xs} (h : ProbeFacts P xs) : ∀ x ∈ xs, P x := by
  induction h with
  | nil => simp
  | cons hx ht ih =>
    intro x h
    rcases List.mem_cons.mp h with rfl | h
    · exact hx
    · exact ih x h

theorem grid_total {f a bs} (hl : Uniform (.before a) f) (ht : Tail f a bs)
    (hd : ProbeFacts (fun x => Value.Defined (f x)) (((a-1 : ℚ) : ℝ) :: gridProbes a bs)) :
    ∀ x, Value.Defined (f x) := by
  intro x
  by_cases hx : x < a
  · rw [hl x hx]; exact hd.all _ (by simp [Region.sample])
  · exact ht.total (fun y hy => hd.all y (by simp [hy])) x (le_of_not_gt hx)

inductive SameSamples (f g : ℝ → Option ℝ) : ℚ → List ℚ → Prop
  | nil (a : ℚ) (h : f ((a+1 : ℚ) : ℝ) = g ((a+1 : ℚ) : ℝ)) : SameSamples f g a []
  | cons {a b bs} (h : f (((a+b)/2 : ℚ) : ℝ) = g (((a+b)/2 : ℚ) : ℝ))
      (tail : SameSamples f g b bs) : SameSamples f g a (b :: bs)

theorem Tail.equal_away {f g a bs} (hf : Tail f a bs) (hg : Tail g a bs)
    (he : SameSamples f g a bs) :
    ∀ x : ℝ, (a : ℝ) < x → (∀ p ∈ a :: bs, x ≠ (p : ℝ)) → f x = g x := by
  induction hf with
  | nil a hf =>
    cases hg with | nil _ hg =>
      cases he with | nil _ he =>
        intro x hx _
        exact (hf x hx).trans (he.trans (hg x hx).symm)
  | @cons a b bs hab hf ht ih =>
    cases hg with | cons _ hg hgt =>
      cases he with | cons he het =>
        intro x hx hp
        by_cases hxb : x < b
        · exact (hf x ⟨hx, hxb⟩).trans (he.trans (hg x ⟨hx, hxb⟩).symm)
        · have hne := hp b (by simp)
          exact ih hgt het x (lt_of_le_of_ne (le_of_not_gt hxb) (Ne.symm hne))
            (fun p hp' => hp p (by simp [hp']))

theorem grid_null_edit {f g a bs}
    (fl : Uniform (.before a) f) (ft : Tail f a bs)
    (gl : Uniform (.before a) g) (gt : Tail g a bs)
    (fd : ProbeFacts (fun x => Value.Defined (f x)) (((a-1 : ℚ) : ℝ) :: gridProbes a bs))
    (gd : ProbeFacts (fun x => Value.Defined (g x)) (((a-1 : ℚ) : ℝ) :: gridProbes a bs))
    (el : f ((a-1 : ℚ) : ℝ) = g ((a-1 : ℚ) : ℝ)) (et : SameSamples f g a bs) :
    NullEditCertificate f g ((a :: bs).map (fun q : ℚ => (q : ℝ))) := by
  refine ⟨grid_total fl ft fd, grid_total gl gt gd, ?_⟩
  intro x hp
  by_cases hx : x < a
  · exact (fl x hx).trans (el.trans (gl x hx).symm)
  · have hne : x ≠ (a : ℝ) := hp _ (by simp)
    exact ft.equal_away gt et x (lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hne))
      (fun p hp' => hp (p : ℝ) (List.mem_map_of_mem (f := fun q : ℚ => (q : ℝ)) hp'))

-- This spelling matches the frontend's rational interval widths, avoiding
-- arithmetic normalization in each exported proof.
def gridMass (f : ℝ → Option ℝ) (a : ℚ) : List ℚ → Option ℝ
  | [] => some 0
  | b :: bs => Value.add (Value.mul (f (((a+b)/2 : ℚ) : ℝ)) (some ((b-a : ℚ) : ℝ)))
      (gridMass f b bs)

theorem gridMass_eq (f : ℝ → Option ℝ) (a : ℚ) (bs : List ℚ) :
    stepMass f (gridCells a bs) = gridMass f a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => simp only [gridCells, stepMass, gridMass, Rat.cast_sub, ih]

/-- A closed numeric grid avoids exporting a second simplification trace for
all sampled source expressions. -/
inductive KnownMass (f : ℝ → Option ℝ) : ℚ → List ℚ → ℚ → Prop
  | nil (a : ℚ) : KnownMass f a [] 0
  | cons {a b v w : ℚ} {bs : List ℚ} (sample : f (((a+b)/2 : ℚ) : ℝ) = some (v : ℝ))
      (tail : KnownMass f b bs w) : KnownMass f a (b :: bs) (v*(b-a)+w)

theorem KnownMass.value {f a bs v} (h : KnownMass f a bs v) :
    gridMass f a bs = some (Numeric.denote (s := .real) v) := by
  induction h with
  | nil => simp [gridMass, Numeric.denote]
  | cons hs ht ih =>
    simp only [gridMass, hs, ih, Numeric.denote, Value.add, Value.mul,
      Option.some_bind, Rat.cast_add, Rat.cast_mul, Rat.cast_sub]


end QSym.Distribution.StepSource

namespace QSym.Distribution.DensityProgram

def runProbe (p : DensityProgram) (x : ℝ) (result : Option ℝ) : Option ℝ :=
  match p with
  | .lebesgue => result
  | .weight w p => runProbe p x ((w x).bind (fun _ => result))

def runProbes (p : DensityProgram) : List ℝ → Option ℝ → Option ℝ
  | [], result => result
  | x :: xs, result => p.runProbe x (p.runProbes xs result)

theorem runProbe_eq (p : DensityProgram) (x : ℝ) (result : Option ℝ) :
    (p.density x).bind (fun _ => result) = p.runProbe x result := by
  induction p generalizing result with
  | lebesgue => rfl
  | weight w p ih =>
    simp only [density, runProbe, Value.mul_bind_const, ih]

theorem runProbes_eq (p : DensityProgram) (probes : List ℝ) (result : Option ℝ) :
    (zeroOnProbes p.density probes).bind (fun _ => result) = p.runProbes probes result := by
  induction probes with
  | nil => rfl
  | cons x xs ih =>
    rw [runProbes, ← runProbe_eq]
    cases h : p.density x <;> simp only [zeroOnProbes, h, Option.some_bind, Option.none_bind, ih]

theorem mass_grid (p : DensityProgram) {a : ℚ} {bs : List ℚ}
    (hl : StepSource.Uniform (.before a) p.density) (ht : StepSource.Tail p.density a bs)
    (zl : StepSource.ZeroOrUndefined (p.density ((a-1 : ℚ) : ℝ)))
    (zr : StepSource.ZeroOrUndefined (p.density (StepSource.lastProbe a bs : ℝ))) :
    p.mass = p.runProbes (((a-1 : ℚ) : ℝ) :: StepSource.gridProbes a bs)
      (StepSource.gridMass p.density a bs) := by
  rw [p.mass_step (StepSource.grid_certificate hl ht zl zr), StepSource.gridMass_eq, runProbes_eq]

theorem presentation_mass_grid (p : DensityProgram) {a : ℚ} {bs : List ℚ}
    (hl : StepSource.Uniform (.before a) p.density) (ht : StepSource.Tail p.density a bs)
    (zl : StepSource.ZeroOrUndefined (p.density ((a-1 : ℚ) : ℝ)))
    (zr : StepSource.ZeroOrUndefined (p.density (StepSource.lastProbe a bs : ℝ))) :
    massValue p.presentation = p.runProbes (((a-1 : ℚ) : ℝ) :: StepSource.gridProbes a bs)
      (StepSource.gridMass p.density a bs) :=
  (mass_bridge p).trans (mass_grid p hl ht zl zr)

theorem presentation_mass_grid_known (p : DensityProgram) {a : ℚ} {bs : List ℚ} {v : ℚ}
    (hl : StepSource.Uniform (.before a) p.density) (ht : StepSource.Tail p.density a bs)
    (zl : StepSource.ZeroOrUndefined (p.density ((a-1 : ℚ) : ℝ)))
    (zr : StepSource.ZeroOrUndefined (p.density (StepSource.lastProbe a bs : ℝ)))
    (hd : StepSource.ProbeFacts (fun x => Value.Defined (p.density x))
      (((a-1 : ℚ) : ℝ) :: StepSource.gridProbes a bs))
    (hv : StepSource.KnownMass p.density a bs v) :
    massValue p.presentation = some (Numeric.denote (s := .real) v) := by
  rw [presentation_mass_grid p hl ht zl zr, ← runProbes_eq, zeroOnProbes_eq,
    if_pos hd.all, Option.some_bind, hv.value]


theorem presentation_mass_grid_null_edit (p q : DensityProgram) {a : ℚ} {bs : List ℚ}
    (fl : StepSource.Uniform (.before a) p.density) (ft : StepSource.Tail p.density a bs)
    (gl : StepSource.Uniform (.before a) q.density) (gt : StepSource.Tail q.density a bs)
    (fd : StepSource.ProbeFacts (fun x => Value.Defined (p.density x))
      (((a-1 : ℚ) : ℝ) :: StepSource.gridProbes a bs))
    (gd : StepSource.ProbeFacts (fun x => Value.Defined (q.density x))
      (((a-1 : ℚ) : ℝ) :: StepSource.gridProbes a bs))
    (el : p.density ((a-1 : ℚ) : ℝ) = q.density ((a-1 : ℚ) : ℝ))
    (et : StepSource.SameSamples p.density q.density a bs) :
    massValue p.presentation = massValue q.presentation :=
  (mass_bridge p).trans ((p.mass_null_edit q (StepSource.grid_null_edit fl ft gl gt fd gd el et)).trans
    (mass_bridge q).symm)

end QSym.Distribution.DensityProgram
