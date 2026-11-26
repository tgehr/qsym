import QSym.DistributionAtomicKernelRules
import QSym.AxiomCheck

noncomputable section
namespace BranchingKernelTest
open QSym.Distribution QSym.Distribution.Atomic
open scoped ENNReal

/- A state-indexed program with two distinct recursive calls. -/
private def body (k : Bool → Option (D Unit)) (stop : Bool) : Option (D Unit) :=
  (some stop).bind fun done => if done then diracValue (some ()) else
    addValue (scaleValue (some (1/2)) (k false)) (scaleValue (some (1/4)) (k true))

private def atomAtStop : Kernel Bool Unit := fun _ => (atom (), {()})

private def step : KernelMap Bool Unit := KernelMap.branch id (OrderHom.const _ atomAtStop)
  ((KernelMap.scale (fun _ => ENNReal.ofReal (1/2 : ℝ)) (KernelMap.call fun _ => false)).add
   (KernelMap.scale (fun _ => ENNReal.ofReal (1/4 : ℝ)) (KernelMap.call fun _ => true)))

theorem source : KernelRule Set.univ Set.univ body step := by
  refine KernelRule.branch id (fun _ _ => rfl) ?_ ?_
  · exact KernelRule.seed fun x _ => ⟨_, rfl, Represents.dirac (), visited_dirac ()⟩
  · apply KernelRule.add
    · exact (KernelRule.call (fun _ => false) (fun _ _ => Set.mem_univ _)).scale (fun _ => 1/2)
        (fun _ _ => ⟨rfl, by norm_num⟩)
    · exact (KernelRule.call (fun _ => true) (fun _ _ => Set.mem_univ _)).scale (fun _ => 1/4)
        (fun _ _ => ⟨rfl, by norm_num⟩)

theorem semantics (stop : Bool) : kernelModelAt body stop = some (step.lfp stop) :=
  source.lfp (Set.mem_univ stop)

private def solution (stop : Bool) : Model Unit :=
  (fun _ => if stop then 1 else 1/2, Set.univ)

private theorem step_solution : step solution = solution := by
  funext x
  apply Prod.ext
  · funext y
    cases y
    cases x <;> norm_num [step, solution, KernelMap.branch, KernelMap.add, KernelMap.scale,
      KernelMap.call, sumModel, scaleModel, atomAtStop, atom, ENNReal.ofReal_div_of_pos]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]
  · ext y
    cases y
    cases x <;> simp [step, solution, KernelMap.branch, KernelMap.add, KernelMap.scale,
      KernelMap.call, sumModel, scaleModel, atomAtStop]

/-- The call at false retries with charge 1/2 and enters the stopping state
with charge 1/4. Its limiting emitted mass is exactly 1/2. -/
theorem false_mass : (step.lfp false).1 () = 1/2 := by
  have hs : (step.lfp true).1 () = 1 := calc
    _ = (step step.lfp true).1 () := congrArg (fun k : Kernel Bool Unit => (k true).1 ()) step.map_lfp.symm
    _ = 1 := by change atom () () = 1; simp [atom]
  have eqn : (step.lfp false).1 () = (1/2) * (step.lfp false).1 () + 1/4 := calc
    _ = (step step.lfp false).1 () := congrArg (fun k : Kernel Bool Unit => (k false).1 ()) step.map_lfp.symm
    _ = _ := by
      change ENNReal.ofReal (1/2 : ℝ) * (step.lfp false).1 () + ENNReal.ofReal (1/4 : ℝ) * (step.lfp true).1 () = _
      rw [hs, mul_one, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num
  have bounded : step.lfp ≤ solution := step.lfp_le_fixed step_solution
  have hfin : (step.lfp false).1 () ≠ ⊤ := ne_top_of_le_ne_top (by norm_num [solution]) ((bounded false).1 ())
  apply (ENNReal.toReal_eq_toReal_iff' hfin (by norm_num)).mp
  have e := congrArg ENNReal.toReal eqn
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by norm_num) hfin) (by norm_num)] at e
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div] at e ⊢
  linarith

-- A missing argument at the unreachable state does not prevent a call.
theorem partial_argument : KernelRule (α := Unit) {true} {true}
    (fun k x => (if x then some true else none).bind k) (KernelMap.call id) :=
  KernelRule.applyAt id (fun _ hx => hx) (fun x hx => by cases x <;> simp_all)

#qsym_check_axioms partial_argument
#qsym_check_axioms QSym.Distribution.Atomic.KernelRule.lfp
#qsym_check_axioms source
#qsym_check_axioms semantics
#qsym_check_axioms false_mass
end BranchingKernelTest
