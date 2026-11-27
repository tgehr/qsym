import QSym.DistributionGraph
import QSym.DistributionPartialModel

noncomputable section
namespace QSym.Distribution.FiniteFibre
open MeasureTheory WeightedParameter.Fibre

abbrev Model (α : Type) := PartialHom PUnit.{1} PUnit.{1} α

/-- A finite weighted fibre uses one latent point for each row, including a
row with weight zero. The empty fibre uses an empty latent space. -/
def ofRows {α : Type} : List (α × ℝ) → Model α
  | [] => PartialHom.ofFamily (PrimitiveProgram.zeroFamily α)
  | (x,w) :: xs => PartialHom.add
      (PartialHom.reweight (fun _ _ _ => some w) (PartialHom.pure (fun _ _ => some x))) (ofRows xs)

def pairing {α : Type} (m : Model α) (test : α → Option ℝ) : Option ℝ :=
  m.observe PUnit.unit PUnit.unit test

theorem pairing_rows {α : Type} (xs : List (α × ℝ)) (test : α → Option ℝ) :
    pairing (ofRows xs) test =
      xs.foldr (fun row acc => Value.add (Value.mul (some row.2) (test row.1)) acc) (some 0) := by
  induction xs with
  | nil =>
    change partialIntegral (0 : Measure Empty) _ = some 0
    rw [partialIntegral_valid _ _ (fun x => isEmptyElim x) Integrable.of_isEmpty, integral_of_isEmpty]
  | cons a xs ih =>
    obtain ⟨x,w⟩ := a
    simpa only [pairing, ofRows, PartialHom.observe_add, PartialHom.observe_reweight, PartialHom.observe_pure,
      Option.some_bind, List.foldr_cons] using congrArg (Value.add (Value.mul (some w) (test x))) ih

/-- A finite atomic fibre has zero regular part. Its signed charge at a
query is the observation of that singleton in the weighted model. -/
def density (m : Model ℝ) (q : ℝ) : Option ℝ := do
  let charge ← pairing m (fun x => some (if q = x then 1 else 0))
  if charge = 0 then some 0 else none

private def charge (q : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | (x,w) :: xs => w*(if q = x then 1 else 0) + charge q xs

private theorem singleton_charge (rows : List (ℝ × ℝ)) (q : ℝ) :
    pairing (ofRows rows) (fun x => some (if q = x then 1 else 0)) = some (charge q rows) := by
  rw [pairing_rows]
  induction rows with
  | nil => rfl
  | cons row xs ih =>
    obtain ⟨x,w⟩ := row
    rw [List.foldr_cons, ih]
    rfl

private theorem presentation_fibre (rows : List (ℝ × ℝ)) (q : ℝ) :
    realFibre (GraphFibre.presentation rows) q = ⟨charge q rows, some 0⟩ := by
  induction rows with
  | nil => rfl
  | cons row xs ih =>
    obtain ⟨x,w⟩ := row
    cases xs with
    | nil => simp [GraphFibre.presentation, realFibre, RealDensityFibre.scale, charge, Value.mul]
    | cons b bs =>
      change (realFibre (.scale w (.dirac x)) q).add (realFibre (GraphFibre.presentation (b :: bs)) q) = _
      rw [ih]
      simp [realFibre, RealDensityFibre.scale, RealDensityFibre.add, charge, Value.mul, Value.add]

theorem density_rows (rows : List (ℝ × ℝ)) (q : ℝ) :
    densityAt (GraphFibre.presentation rows) q = density (ofRows rows) q := by
  rw [densityAt, presentation_fibre, density, singleton_charge]
  rfl

theorem observe_optional (rows : Option (List (ℝ × ℝ))) (test : ℝ → Option ℝ) :
    (rows.map ofRows).bind (fun m => pairing m test) = rows.bind (fun xs => GraphFibre.observe xs test) := by
  cases rows with
  | none => rfl
  | some xs => exact pairing_rows xs test

/-- One latent-space model supplies both observations of a possibly missing real fibre. -/
structure Represents (d : Option (D ℝ)) (m : Option (Model ℝ)) : Prop where
  integral (test : ℝ → Option ℝ) : d.bind (fun a => integrate a test) = m.bind (fun p => pairing p test)
  densityAt (q : ℝ) : densityAtValue d (some q) = m.bind (fun p => density p q)

theorem represents_rows (rows : Option (List (ℝ × ℝ))) :
    Represents (rows.map GraphFibre.presentation) (rows.map ofRows) := by
  constructor
  · intro test; rw [observe_optional]
    cases rows with
    | none => rfl
    | some xs => exact GraphFibre.integrate_presentation xs test
  · intro q
    cases rows with
    | none => rfl
    | some xs => exact density_rows xs q

end QSym.Distribution.FiniteFibre
