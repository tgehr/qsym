import QSym.Functions

namespace QSym
inductive Ty where
  | real | complex | bool | density | measure | natural | integer | rational
  deriving DecidableEq

abbrev Ty.denote : Ty → Type
  | .natural => ℕ
  | .integer => ℤ
  | .rational => ℚ
  | .real => ℝ
  | .complex => ℂ
  | .bool => Bool
  | .density => Density
  | .measure => MeasureTheory.Measure ℝ

structure Env where
  natural : Nat → ℕ
  integer : Nat → ℤ
  rational : Nat → ℚ
  real : Nat → ℝ
  complex : Nat → ℂ
  bool : Nat → Bool

inductive Expr : Ty → Type where
  | nat (n : Nat) : Expr .natural
  | int (n : Int) : Expr .integer
  | rat (q : ℚ) : Expr .rational
  | varN (i : Nat) : Expr .natural
  | varZ (i : Nat) : Expr .integer
  | varQ (i : Nat) : Expr .rational
  | real (n : Int) : Expr .real
  | complex (re im : Int) : Expr .complex
  | ratR (q : ℚ) : Expr .real
  | ratC (re im : ℚ) : Expr .complex
  | bool (b : Bool) : Expr .bool
  | varR (i : Nat) : Expr .real
  | varC (i : Nat) : Expr .complex
  | varB (i : Nat) : Expr .bool
  | addR : Expr .real → Expr .real → Expr .real
  | addC : Expr .complex → Expr .complex → Expr .complex
  | mulR : Expr .real → Expr .real → Expr .real
  | mulC : Expr .complex → Expr .complex → Expr .complex
  | invR : Expr .real → Expr .real
  | invC : Expr .complex → Expr .complex
  | powR : Expr .real → Nat → Expr .real
  | powC : Expr .complex → Nat → Expr .complex
  | absR : Expr .real → Expr .real
  | nonzeroR : Expr .real → Expr .bool
  | nonzeroC : Expr .complex → Expr .bool
  | not : Expr .bool → Expr .bool
  | and : Expr .bool → Expr .bool → Expr .bool
  | or : Expr .bool → Expr .bool → Expr .bool
  | ltR : Expr .real → Expr .real → Expr .bool
  | leR : Expr .real → Expr .real → Expr .bool
  | maskR : Expr .bool → Expr .real → Expr .real
  | maskC : Expr .bool → Expr .complex → Expr .complex
  | conj : Expr .complex → Expr .complex
  | lebesgue : Expr .density
  | puncture : Expr .density → Expr .density
  | densityAt : Expr .density → Expr .real → Expr .real
  | forget : Expr .density → Expr .measure
  | powN : Expr .natural → Nat → Expr .natural
  | maskN : Expr .bool → Expr .natural → Expr .natural
  | powZ : Expr .integer → Nat → Expr .integer
  | maskZ : Expr .bool → Expr .integer → Expr .integer
  | powQ : Expr .rational → Nat → Expr .rational
  | maskQ : Expr .bool → Expr .rational → Expr .rational
  | castNZ : Expr .natural → Expr .integer
  | castZQ : Expr .integer → Expr .rational
  | castQR : Expr .rational → Expr .real
  | castRC : Expr .real → Expr .complex
  | addN : Expr .natural → Expr .natural → Expr .natural
  | mulN : Expr .natural → Expr .natural → Expr .natural
  | ltN : Expr .natural → Expr .natural → Expr .bool
  | leN : Expr .natural → Expr .natural → Expr .bool
  | nonzeroN : Expr .natural → Expr .bool
  | addZ : Expr .integer → Expr .integer → Expr .integer
  | mulZ : Expr .integer → Expr .integer → Expr .integer
  | ltZ : Expr .integer → Expr .integer → Expr .bool
  | leZ : Expr .integer → Expr .integer → Expr .bool
  | nonzeroZ : Expr .integer → Expr .bool
  | addQ : Expr .rational → Expr .rational → Expr .rational
  | mulQ : Expr .rational → Expr .rational → Expr .rational
  | ltQ : Expr .rational → Expr .rational → Expr .bool
  | leQ : Expr .rational → Expr .rational → Expr .bool
  | nonzeroQ : Expr .rational → Expr .bool
  | invQ : Expr .rational → Expr .rational
  | eqB : Expr .bool → Expr .bool → Expr .bool
  | powNN : Expr .natural → Expr .natural → Expr .natural
  | powZN : Expr .integer → Expr .natural → Expr .integer
  | powQN : Expr .rational → Expr .natural → Expr .rational
  | powRN : Expr .real → Expr .natural → Expr .real
  | powCN : Expr .complex → Expr .natural → Expr .complex
  | powQZ : Expr .rational → Expr .integer → Expr .rational
  | powRZ : Expr .real → Expr .integer → Expr .real
  | powCZ : Expr .complex → Expr .integer → Expr .complex
  | powerR : Expr .real → Expr .real → Expr .real
  | powerC : Expr .complex → Expr .complex → Expr .complex
  | sqrtR : Expr .real → Expr .real
  | sqrtC : Expr .complex → Expr .complex
  | cbrtR : Expr .real → Expr .real
  | expR : Expr .real → Expr .real
  | expC : Expr .complex → Expr .complex
  | sinR : Expr .real → Expr .real
  | sinC : Expr .complex → Expr .complex
  | cosR : Expr .real → Expr .real
  | cosC : Expr .complex → Expr .complex
  | sinhR : Expr .real → Expr .real
  | sinhC : Expr .complex → Expr .complex
  | coshR : Expr .real → Expr .real
  | coshC : Expr .complex → Expr .complex
  | tanhR : Expr .real → Expr .real
  | tanhC : Expr .complex → Expr .complex
  | logR : Expr .real → Expr .real
  | logC : Expr .complex → Expr .complex
  | tanR : Expr .real → Expr .real
  | tanC : Expr .complex → Expr .complex
  | asinR : Expr .real → Expr .real
  | acosR : Expr .real → Expr .real
  | atanR : Expr .real → Expr .real
  | asinC : Expr .complex → Expr .complex
  | acosC : Expr .complex → Expr .complex
  | atanC : Expr .complex → Expr .complex
  | asinhR : Expr .real → Expr .real
  | acoshR : Expr .real → Expr .real
  | atanhR : Expr .real → Expr .real
  | asinhC : Expr .complex → Expr .complex
  | acoshC : Expr .complex → Expr .complex
  | atanhC : Expr .complex → Expr .complex
  | exp2R : Expr .real → Expr .real
  | log2R : Expr .real → Expr .real
  | log10R : Expr .real → Expr .real
  | makeC : Expr .real → Expr .real → Expr .complex
  | reC : Expr .complex → Expr .real
  | imC : Expr .complex → Expr .real
  | absC : Expr .complex → Expr .real
  | argC : Expr .complex → Expr .real
  | cisR : Expr .real → Expr .complex
  | expiC : Expr .complex → Expr .complex
  | polarC : Expr .real → Expr .real → Expr .complex
  | atan2R : Expr .real → Expr .real → Expr .real
  | floorR : Expr .real → Expr .integer
  | ceilR : Expr .real → Expr .integer
  | roundR : Expr .real → Expr .integer
  | signR : Expr .real → Expr .integer
  | isIntR : Expr .real → Expr .bool
  | minR : Expr .real → Expr .real → Expr .real
  | maxR : Expr .real → Expr .real → Expr .real
  | hypotR : Expr .real → Expr .real → Expr .real
  | gcdZ : Expr .integer → Expr .integer → Expr .natural
  | makeQ : Expr .integer → Expr .integer → Expr .rational
  | numQ : Expr .rational → Expr .integer
  | denQ : Expr .rational → Expr .natural
  | erfR : Expr .real → Expr .real
  | erfcR : Expr .real → Expr .real
  | gammaR : Expr .real → Expr .real
  | lgammaR : Expr .real → Expr .real
  | gammaC : Expr .complex → Expr .complex
  | pi : Expr .real
  | e : Expr .real

namespace Expr
noncomputable def eval (ρ : Env) : {s : Ty} → Expr s → Option s.denote
  | _, .nat n => some n
  | _, .int n => some n
  | _, .rat q => some q
  | _, .varN i => some (ρ.natural i)
  | _, .varZ i => some (ρ.integer i)
  | _, .varQ i => some (ρ.rational i)
  | _, .powN a n => (eval ρ a).map (· ^ n)
  | _, .maskN p a => Value.mask (eval ρ p) (eval ρ a)
  | _, .powZ a n => (eval ρ a).map (· ^ n)
  | _, .maskZ p a => Value.mask (eval ρ p) (eval ρ a)
  | _, .powQ a n => (eval ρ a).map (· ^ n)
  | _, .maskQ p a => Value.mask (eval ρ p) (eval ρ a)
  | _, .castNZ a => Functions.castNZ.apply (eval ρ a)
  | _, .castZQ a => Functions.castZQ.apply (eval ρ a)
  | _, .castQR a => Functions.castQR.apply (eval ρ a)
  | _, .castRC a => Functions.castRC.apply (eval ρ a)
  | _, .addN a b => Functions.addN.apply (eval ρ a) (eval ρ b)
  | _, .mulN a b => Functions.mulN.apply (eval ρ a) (eval ρ b)
  | _, .ltN a b => Functions.ltN.apply (eval ρ a) (eval ρ b)
  | _, .leN a b => Functions.leN.apply (eval ρ a) (eval ρ b)
  | _, .nonzeroN a => Functions.nonzeroN.apply (eval ρ a)
  | _, .addZ a b => Functions.addZ.apply (eval ρ a) (eval ρ b)
  | _, .mulZ a b => Functions.mulZ.apply (eval ρ a) (eval ρ b)
  | _, .ltZ a b => Functions.ltZ.apply (eval ρ a) (eval ρ b)
  | _, .leZ a b => Functions.leZ.apply (eval ρ a) (eval ρ b)
  | _, .nonzeroZ a => Functions.nonzeroZ.apply (eval ρ a)
  | _, .addQ a b => Functions.addQ.apply (eval ρ a) (eval ρ b)
  | _, .mulQ a b => Functions.mulQ.apply (eval ρ a) (eval ρ b)
  | _, .ltQ a b => Functions.ltQ.apply (eval ρ a) (eval ρ b)
  | _, .leQ a b => Functions.leQ.apply (eval ρ a) (eval ρ b)
  | _, .nonzeroQ a => Functions.nonzeroQ.apply (eval ρ a)
  | _, .invQ a => Functions.invQ.apply (eval ρ a)
  | _, .eqB a b => Functions.eqB.apply (eval ρ a) (eval ρ b)
  | _, .powNN a b => Functions.powNN.apply (eval ρ a) (eval ρ b)
  | _, .powZN a b => Functions.powZN.apply (eval ρ a) (eval ρ b)
  | _, .powQN a b => Functions.powQN.apply (eval ρ a) (eval ρ b)
  | _, .powRN a b => Functions.powRN.apply (eval ρ a) (eval ρ b)
  | _, .powCN a b => Functions.powCN.apply (eval ρ a) (eval ρ b)
  | _, .powQZ a b => Functions.powQZ.apply (eval ρ a) (eval ρ b)
  | _, .powRZ a b => Functions.powRZ.apply (eval ρ a) (eval ρ b)
  | _, .powCZ a b => Functions.powCZ.apply (eval ρ a) (eval ρ b)
  | _, .powerR a b => Functions.powerR.apply (eval ρ a) (eval ρ b)
  | _, .powerC a b => Functions.powerC.apply (eval ρ a) (eval ρ b)
  | _, .sqrtR a => Functions.sqrtR.apply (eval ρ a)
  | _, .sqrtC a => Functions.sqrtC.apply (eval ρ a)
  | _, .cbrtR a => Functions.cbrtR.apply (eval ρ a)
  | _, .expR a => Functions.expR.apply (eval ρ a)
  | _, .expC a => Functions.expC.apply (eval ρ a)
  | _, .sinR a => Functions.sinR.apply (eval ρ a)
  | _, .sinC a => Functions.sinC.apply (eval ρ a)
  | _, .cosR a => Functions.cosR.apply (eval ρ a)
  | _, .cosC a => Functions.cosC.apply (eval ρ a)
  | _, .sinhR a => Functions.sinhR.apply (eval ρ a)
  | _, .sinhC a => Functions.sinhC.apply (eval ρ a)
  | _, .coshR a => Functions.coshR.apply (eval ρ a)
  | _, .coshC a => Functions.coshC.apply (eval ρ a)
  | _, .tanhR a => Functions.tanhR.apply (eval ρ a)
  | _, .tanhC a => Functions.tanhC.apply (eval ρ a)
  | _, .logR a => Functions.logR.apply (eval ρ a)
  | _, .logC a => Functions.logC.apply (eval ρ a)
  | _, .tanR a => Functions.tanR.apply (eval ρ a)
  | _, .tanC a => Functions.tanC.apply (eval ρ a)
  | _, .asinR a => Functions.asinR.apply (eval ρ a)
  | _, .acosR a => Functions.acosR.apply (eval ρ a)
  | _, .atanR a => Functions.atanR.apply (eval ρ a)
  | _, .asinC a => Functions.asinC.apply (eval ρ a)
  | _, .acosC a => Functions.acosC.apply (eval ρ a)
  | _, .atanC a => Functions.atanC.apply (eval ρ a)
  | _, .asinhR a => Functions.asinhR.apply (eval ρ a)
  | _, .acoshR a => Functions.acoshR.apply (eval ρ a)
  | _, .atanhR a => Functions.atanhR.apply (eval ρ a)
  | _, .asinhC a => Functions.asinhC.apply (eval ρ a)
  | _, .acoshC a => Functions.acoshC.apply (eval ρ a)
  | _, .atanhC a => Functions.atanhC.apply (eval ρ a)
  | _, .exp2R a => Functions.exp2R.apply (eval ρ a)
  | _, .log2R a => Functions.log2R.apply (eval ρ a)
  | _, .log10R a => Functions.log10R.apply (eval ρ a)
  | _, .makeC a b => Functions.makeC.apply (eval ρ a) (eval ρ b)
  | _, .reC a => Functions.reC.apply (eval ρ a)
  | _, .imC a => Functions.imC.apply (eval ρ a)
  | _, .absC a => Functions.absC.apply (eval ρ a)
  | _, .argC a => Functions.argC.apply (eval ρ a)
  | _, .cisR a => Functions.cisR.apply (eval ρ a)
  | _, .expiC a => Functions.expiC.apply (eval ρ a)
  | _, .polarC a b => Functions.polarC.apply (eval ρ a) (eval ρ b)
  | _, .atan2R a b => Functions.atan2R.apply (eval ρ a) (eval ρ b)
  | _, .floorR a => Functions.floorR.apply (eval ρ a)
  | _, .ceilR a => Functions.ceilR.apply (eval ρ a)
  | _, .roundR a => Functions.roundR.apply (eval ρ a)
  | _, .signR a => Functions.signR.apply (eval ρ a)
  | _, .isIntR a => Functions.isIntR.apply (eval ρ a)
  | _, .minR a b => Functions.minR.apply (eval ρ a) (eval ρ b)
  | _, .maxR a b => Functions.maxR.apply (eval ρ a) (eval ρ b)
  | _, .hypotR a b => Functions.hypotR.apply (eval ρ a) (eval ρ b)
  | _, .gcdZ a b => Functions.gcdZ.apply (eval ρ a) (eval ρ b)
  | _, .makeQ a b => Functions.makeQ.apply (eval ρ a) (eval ρ b)
  | _, .numQ a => Functions.numQ.apply (eval ρ a)
  | _, .denQ a => Functions.denQ.apply (eval ρ a)
  | _, .erfR a => Functions.erfR.apply (eval ρ a)
  | _, .erfcR a => Functions.erfcR.apply (eval ρ a)
  | _, .gammaR a => Functions.gammaR.apply (eval ρ a)
  | _, .lgammaR a => Functions.lgammaR.apply (eval ρ a)
  | _, .gammaC a => Functions.gammaC.apply (eval ρ a)
  | _, .pi => some Functions.pi
  | _, .e => some Functions.e
  | _, .real n => some (n : ℝ)
  | _, .complex r i => some ((r : ℂ) + (i : ℂ) * Complex.I)
  | _, .ratR q => some (q : ℝ)
  | _, .ratC r i => some ((r : ℂ) + (i : ℂ) * Complex.I)
  | _, .bool b => some b
  | _, .varR i => some (ρ.real i)
  | _, .varC i => some (ρ.complex i)
  | _, .varB i => some (ρ.bool i)
  | _, .addR a b => Value.add (eval ρ a) (eval ρ b)
  | _, .addC a b => Value.add (eval ρ a) (eval ρ b)
  | _, .mulR a b => Value.mul (eval ρ a) (eval ρ b)
  | _, .mulC a b => Value.mul (eval ρ a) (eval ρ b)
  | _, .invR a => Value.inv (eval ρ a)
  | _, .invC a => Value.inv (eval ρ a)
  | _, .powR a n => (eval ρ a).map (· ^ n)
  | _, .powC a n => (eval ρ a).map (· ^ n)
  | _, .absR a => Value.abs (eval ρ a)
  | _, .nonzeroR a => Value.nonzero (eval ρ a)
  | _, .nonzeroC a => Value.nonzero (eval ρ a)
  | _, .not p => Value.not (eval ρ p)
  | _, .and p q => Value.and (eval ρ p) (eval ρ q)
  | _, .or p q => Value.or (eval ρ p) (eval ρ q)
  | _, .ltR a b => Value.lt (eval ρ a) (eval ρ b)
  | _, .leR a b => Value.le (eval ρ a) (eval ρ b)
  | _, .maskR p a => Value.mask (eval ρ p) (eval ρ a)
  | _, .maskC p a => Value.mask (eval ρ p) (eval ρ a)
  | _, .conj a => Value.conj (eval ρ a)
  | _, .lebesgue => some Density.lebesgue
  | _, .puncture a => (eval ρ a).map Density.puncture
  | _, .densityAt d x => Value.densityAt (eval ρ d) (eval ρ x)
  | _, .forget d => (eval ρ d).map Density.forget

def Defined {s : Ty} (ρ : Env) (term : Expr s) : Prop := Value.Defined (eval ρ term)

theorem density_total_measurable (ρ : Env) :
    (d : Expr .density) → ∃ f, eval ρ d = some f ∧ Measurable f
  | .lebesgue => ⟨Density.lebesgue, rfl, measurable_const⟩
  | .puncture d => by
      obtain ⟨f, h, hf⟩ := density_total_measurable ρ d
      exact ⟨Density.puncture f, by simp [eval, h], Density.measurable_puncture f hf⟩

theorem forget_puncture (ρ : Env) (d : Expr .density) :
    eval ρ (.forget (.puncture d)) = eval ρ (.forget d) := by
  simp only [eval, Option.map_map, Function.comp_def, Density.forget_puncture]

-- Partial-value equality preserves both values and definedness.
theorem defined_congr {s : Ty} {ρ : Env} {a b : Expr s}
    (h : eval ρ a = eval ρ b) : Defined ρ a ↔ Defined ρ b := by
  unfold Defined
  rw [h]
end Expr
end QSym
