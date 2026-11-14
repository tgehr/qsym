import QSym.SummationTails

noncomputable section
namespace QSym.SummationMasks
open Summation
set_option linter.unusedSectionVars false
variable {α : Type} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]

theorem deltaN_zero (weight : α → ℝ) (hw : weight 0 = 0) (f : ℕ → Option α) :
    value weight (some (fun i => Value.mask (Value.not
      (Functions.nonzeroZ.apply (Functions.castNZ.apply (some i)))) (f i))) = f 0 := by
  have he : (fun i => Value.mask (Value.not
      (Functions.nonzeroZ.apply (Functions.castNZ.apply (some i)))) (f i)) =
      (fun i => if i = 0 then f i else some 0) := by
    funext i; by_cases h : i = 0 <;>
      simp [Function1.apply,Functions.castNZ,Functions.nonzeroZ,Value.not,Value.mask,h]
  rw [he]; exact delta_select weight hw 0 f

theorem deltaN_nonzeroN (weight : α → ℝ) (hw : weight 0=0) (f : ℕ → Option α) :
    value weight (some (fun i => Value.mask (Value.not (Functions.nonzeroN.apply (some i))) (f i))) = f 0 := by
  have he : (fun i => Value.mask (Value.not (Functions.nonzeroN.apply (some i))) (f i)) =
      (fun i => if i=0 then f i else some 0) := by
    funext i; by_cases h : i=0 <;> simp [Function1.apply,Functions.nonzeroN,Value.not,Value.mask,h]
  rw [he]; exact delta_select weight hw 0 f

theorem deltaZ_zero (weight : α → ℝ) (hw : weight 0 = 0) (f : ℤ → Option α) :
    value weight (some (fun i => Value.mask (Value.not
      (Functions.nonzeroZ.apply (some i))) (f i))) = f 0 := by
  have he : (fun i => Value.mask (Value.not
      (Functions.nonzeroZ.apply (some i))) (f i)) =
      (fun i => if i = 0 then f i else some 0) := by
    funext i; by_cases h : i = 0 <;>
      simp [Function1.apply,Functions.nonzeroZ,Value.not,Value.mask,h]
  rw [he]; exact delta_select weight hw 0 f

def upper (n : Option ℕ) (inclusive : Bool) : Option ℕ :=
  if inclusive then Functions.addN.apply n (some 1) else n

def below (i n : Option ℕ) (inclusive : Bool) : Option Bool :=
  (if inclusive then Functions.leN else Functions.ltN).apply i n

theorem below_upper (i n : Option ℕ) (inclusive : Bool) :
    below i n inclusive = Functions.ltN.apply i (upper n inclusive) := by
  cases inclusive <;> cases i <;> cases n <;>
    simp [below,upper,Function2.apply,Functions.leN,Functions.ltN,Functions.addN,Nat.lt_succ_iff]

theorem finite_below (f : ℕ → Option α) (n k : ℕ) :
    finite (Finset.range n) (fun i => Value.mask (Functions.ltN.apply (some i) (some k)) (f i)) =
      finite (Finset.range (min n k)) f := by
  classical
  have he (i : ℕ) : Value.mask (Functions.ltN.apply (some i) (some k)) (f i) = if i < k then f i else some 0 := by
    by_cases h : i < k <;> simp [Function2.apply,Functions.ltN,Value.mask,h]
  simp only [he]
  rw [SummationAlgebra.finite_filter]
  congr 1
  ext i; simp [lt_min_iff]

theorem bounded_add_lt (weight : α → ℝ) (hw : weight 0 = 0)
    (f g : ℕ → Option α) (n m : Option ℕ) :
    value weight (some (fun i => Value.add
      (Value.mask (Functions.ltN.apply (some i) n) (f i))
      (Value.mask (Functions.ltN.apply (some i) m) (g i)))) =
    Value.add (rangeValue (some f) n) (rangeValue (some g) m) := by
  classical
  cases n with
  | none =>
    rw [undefined_term weight _ 0 (by simp [Function2.apply,Functions.ltN,Value.mask,Value.add])]
    rfl
  | some n =>
    cases m with
    | none =>
      rw [undefined_term weight _ 0 (by simp [Function2.apply,Functions.ltN,Value.mask,Value.add])]
      cases rangeValue (some f) (some n) <;> rfl
    | some m =>
      rw [finite_support weight hw (Finset.range (max n m)) _ (by
        intro i hi
        have hn : ¬ i < n := by simp only [Finset.mem_range,not_lt] at hi; omega
        have hm : ¬ i < m := by simp only [Finset.mem_range,not_lt] at hi; omega
        simp [Function2.apply,Functions.ltN,Value.mask,Value.add,hn,hm])]
      rw [SummationAlgebra.finite_add,finite_below,finite_below]
      simp [rangeValue,min_eq_right (le_max_left n m),min_eq_right (le_max_right n m)]

theorem bounded_add (weight : α → ℝ) (hw : weight 0 = 0)
    (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b)))
    (f g : ℕ → Option α) (n m : Option ℕ) (ni mi : Bool) :
    value weight (some (fun i => op
      (Value.mask (below (some i) n ni) (f i))
      (Value.mask (below (some i) m mi) (g i)))) =
    op (rangeValue (some f) (upper n ni)) (rangeValue (some g) (upper m mi)) := by
  have he : op = Value.add := by funext a b; rw [hop,Summation.add]
  rw [he]; simp only [below_upper]; exact bounded_add_lt weight hw f g _ _

theorem castNZ_mask (p : Option Bool) (x : Option ℕ) :
    Functions.castNZ.apply (Value.mask p x) = Value.mask p (Functions.castNZ.apply x) := by
  cases p with
  | none => rfl
  | some p => cases p <;> simp [Value.mask,Function1.apply,Functions.castNZ]

theorem castNZ_add (x y : Option ℕ) :
    Functions.castNZ.apply (Functions.addN.apply x y) = Functions.addZ.apply (Functions.castNZ.apply x) (Functions.castNZ.apply y) := by
  cases x <;> cases y <;>
    simp [Function1.apply,Function2.apply,Functions.castNZ,Functions.addN,Functions.addZ,Functions.addQ,Value.add]

theorem castZQ_mask (p : Option Bool) (x : Option ℤ) :
    Functions.castZQ.apply (Value.mask p x) = Value.mask p (Functions.castZQ.apply x) := by
  cases p with
  | none => rfl
  | some p => cases p <;> simp [Value.mask,Function1.apply,Functions.castZQ]

theorem castZQ_add (x y : Option ℤ) :
    Functions.castZQ.apply (Functions.addZ.apply x y) = Functions.addQ.apply (Functions.castZQ.apply x) (Functions.castZQ.apply y) := by
  cases x <;> cases y <;>
    simp [Function1.apply,Function2.apply,Functions.castZQ,Functions.addN,Functions.addZ,Functions.addQ,Value.add]

theorem castQR_mask (p : Option Bool) (x : Option ℚ) :
    Functions.castQR.apply (Value.mask p x) = Value.mask p (Functions.castQR.apply x) := by
  cases p with
  | none => rfl
  | some p => cases p <;> simp [Value.mask,Function1.apply,Functions.castQR]

theorem castQR_add (x y : Option ℚ) :
    Functions.castQR.apply (Functions.addQ.apply x y) = Value.add (Functions.castQR.apply x) (Functions.castQR.apply y) := by
  cases x <;> cases y <;>
    simp [Function1.apply,Function2.apply,Functions.castQR,Functions.addN,Functions.addZ,Functions.addQ,Value.add]

theorem castRC_mask (p : Option Bool) (x : Option ℝ) :
    Functions.castRC.apply (Value.mask p x) = Value.mask p (Functions.castRC.apply x) := by
  cases p with
  | none => rfl
  | some p => cases p <;> simp [Value.mask,Function1.apply,Functions.castRC]

theorem castRC_add (x y : Option ℝ) :
    Functions.castRC.apply (Value.add x y) = Value.add (Functions.castRC.apply x) (Functions.castRC.apply y) := by
  cases x <;> cases y <;>
    simp [Function1.apply,Function2.apply,Functions.castRC,Functions.addN,Functions.addZ,Functions.addQ,Value.add]

theorem add_none_left (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b))) (x : Option α) :
    op none x = none := by rw [hop]; rfl

theorem add_none_right (op : Option α → Option α → Option α)
    (hop : ∀ a b, op a b = a.bind (fun a => b.map (fun b => a+b))) (x : Option α) :
    op x none = none := by rw [hop]; cases x <;> rfl

theorem exclude_zero (weight : α → ℝ) (hw : weight 0=0) (f : Option ℕ → Option α) :
    value weight (some (fun i => Value.mask
      (Functions.nonzeroZ.apply (Functions.castNZ.apply (some i))) (f (some i)))) =
    value weight (some (fun i => f (Functions.addN.apply (some i) (some 1)))) := by
  have hp (i : ℕ) : Value.mask (Functions.nonzeroZ.apply (Functions.castNZ.apply (some i))) (f (some i)) =
      Value.mask (Functions.ltN.apply (some 0) (some i)) (f (some i)) := by
    by_cases h : i=0 <;> simp [Function1.apply,Function2.apply,Functions.castNZ,Functions.nonzeroZ,Functions.ltN,Value.mask,h,Nat.pos_iff_ne_zero]
  simp only [hp]
  simpa [Function2.apply,Functions.addN] using tailN_strict weight hw (fun i => f (some i)) (some 0)

end QSym.SummationMasks
