import QSym.DistributionAtomicDivergence
import QSym.DistributionAtomicOrbit

/-! Transport the recursive distribution before adding this round's emission.
For example, mapping every emitted natural number to its successor produces
a geometric distribution over the counter. -/
noncomputable section
namespace QSym.Distribution.Atomic
open scoped ENNReal Classical
variable {ι α : Type}

/-- A distribution transformer preserves the operations appearing in the
finite source unfoldings. Its action on increments does not assume continuity. -/
structure Transport (push : Option (D α) → Option (D α)) : Prop where
  missing : push none = none
  zero : push zeroValue = zeroValue
  add (a b) : push (addValue a b) = addValue (push a) (push b)
  scale (r : ℝ) (a) : push (scaleValue (some r) a) = scaleValue (some r) (push a)

theorem Transport.bind (k : α → Option (D α)) : Transport (fun d => bindValue d (some k)) :=
  ⟨rfl, rfl, fun _ _ => bind_addValue _ _ _, fun _ _ => bind_scaleValue _ _ _⟩

theorem Transport.realBind (k : ℝ → Option (D ℝ)) : Transport (fun d => GraphFibre.realBindValue d (some k)) :=
  ⟨rfl, rfl, fun _ _ => GraphFibre.realBind_addValue _ _ _, fun _ _ => GraphFibre.realBind_scaleValue _ _ _⟩

private theorem Transport.orbit_stages {push : Option (D α) → Option (D α)} (hp : Transport push)
    (b : ι → Option (D α)) (r : ℝ) (next : ι → ι) (states : Set ι) (closed : Set.MapsTo next states states)
    (move : ∀ a ∈ states, push (b a) = b (next a)) (n : ℕ) {x : ι} (hx : x ∈ states) :
    push (iterateKernel (orbitBody b (fun _ => r) next) n x) =
      iterateKernel (orbitBody b (fun _ => r) next) n (next x) := by
  induction n generalizing x with
  | zero => exact hp.zero
  | succ n ih => simp only [iterateKernel, orbitBody, hp.add, hp.scale, move x hx, ih (closed hx)]

theorem Transport.fixed_stages {push : Option (D α) → Option (D α)} (hp : Transport push)
    (b : ι → Option (D α)) (r : ℝ) (next : ι → ι) (states : Set ι) (closed : Set.MapsTo next states states)
    (move : ∀ a ∈ states, push (b a) = b (next a)) {x : ι} (hx : x ∈ states)
    {f : D α → Option (D α)} (body : ∀ d, f d = addValue (b x) (scaleValue (some r) (push (some d)))) (n : ℕ) :
    iterateBody f n = iterateKernel (orbitBody b (fun _ => r) next) n x := by
  have lift (v : Option (D α)) : v.bind f = addValue (b x) (scaleValue (some r) (push v)) := by
    cases v with
    | none => rw [hp.missing]; cases b x <;> rfl
    | some d => exact body d
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateBody, ih, lift, hp.orbit_stages b r next states closed move n hx]; rfl

theorem Represents.finite_visits {d : D α} {w : Weights α} (p : Represents d w) : (visited d).Finite := by
  induction p with
  | zero => simp
  | dirac => simp
  | add _ _ ih jh => simpa only [visited_add] using ih.union jh
  | scale _ _ ih => simpa only [visited_scale] using ih

theorem realize_of_infinite_visits {m : Model α} (h : m.2.Infinite) : realize m = none := by
  rcases realize_cases m with ⟨_, _, hd⟩ | ⟨_, rfl, _⟩ | e
  · exact False.elim (h (hd.2 ▸ hd.1.finite_visits))
  · exact False.elim (h (Set.finite_singleton _))
  · exact e

/-- Moving the recursive value along an orbit gives the explicit countable sum
under every supported scalar observer. Infinite visits rule out the finite and
single-atom representations, even when the total mass is finite. -/
theorem CountableObservation.forward_orbit {o : Option (D α) → Option ℝ} (h : CountableObservation o)
    {push : Option (D α) → Option (D α)} (hp : Transport push) (b : ι → Option (D α)) (r : ℝ)
    (hr : 0 ≤ r) (next : ι → ι) (m : Kernel ι α) (states : Set ι) (closed : Set.MapsTo next states states)
    (seed : ∀ a ∈ states, ∃ d, b a = some d ∧ Presents d (m a)) (move : ∀ a ∈ states, push (b a) = b (next a))
    {x : ι} (hx : x ∈ states) (infinite : (⋃ n : ℕ, (m (next^[n] x)).2).Infinite)
    {f : D α → Option (D α)} (body : ∀ d, f d = addValue (b x) (scaleValue (some r) (push (some d)))) :
    o (fixedValue (some f)) = o (orbitSeries b (fun _ => r) next x) := by
  let g := kernelStep m (fun _ => ENNReal.ofReal r) next
  have lim := orbit_limit_on b (fun _ => r) next m states closed seed (fun _ _ => hr) hx
  obtain ⟨s, hs, hm⟩ := limitModel_eq_some_iff.mp lim
  have actual := funext (hp.fixed_stages b r next states closed move hx body)
  have track : Tracks f s := by rw [Tracks, actual]; exact hs
  have visits : (g.lfp x).2 = ⋃ n : ℕ, (m (next^[n] x)).2 := by
    ext y
    exact (kernel_lfp_visits m _ next x y).trans Set.mem_iUnion.symm
  have unrepresented : realize (⨆ n, s n) = none := realize_of_infinite_visits (by rw [hm]; exact visits ▸ infinite)
  cases h.finite with
  | absent absent => rw [absent, absent]
  | linear p =>
    let t := fun a => o (some (.dirac a))
    rw [fixed_chain track, h.at_chain p _ hs, probe_realizeChain unrepresented hs, probe_orbit_increments]
    rw [orbitSeries, probe_nat_sum, h.natSum]
    congr 1
    congr 1
    funext n
    obtain ⟨d, hd, pres⟩ := seed (next^[n] x) (closed.iterate n hx)
    rw [probe_scale, p.scale, hd]
    exact congrArg (QSym.Value.mul _) (p.atoms pres.1).symm

end QSym.Distribution.Atomic
