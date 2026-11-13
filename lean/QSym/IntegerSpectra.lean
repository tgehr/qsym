import QSym.Spectral

namespace QSym.IntegerSpectra

def run {R : Type} (add mul : Option R → Option R → Option R) (zero one : R) (d : ℕ)
    (a : Option (Matrix (Fin d) (Fin d) R)) (v : Option (Fin d → R)) (n : Option ℕ) :
    Option (Fin d → R) :=
  Tensor.matvecValue add mul zero d d (Tensor.matrixPowerValue add mul zero one d a n) v

def restore {R S : Type} (project : Option S → Option R) (d : ℕ) (v : Option (Fin d → S)) :
    Option (Fin d → R) :=
  Tensor.tabulateValue d (fun i => project (Tensor.getValue v (some i.val)))

theorem restore_map {R S : Type} (f : R → S) (project : Option S → Option R)
    (hn : project none=none) (hs : ∀ x, project (some (f x))=some x)
    (d : ℕ) (v : Option (Fin (d+1) → R)) :
    restore project (d+1) (v.map (fun v i => f (v i)))=v := by
  cases v with
  | none => simp [restore, Tensor.tabulateValue, Tensor.getValue, Tensor.consValue, hn]
  | some v =>
    simp only [restore, Option.map, Tensor.getValue, Option.some_bind,
      Fin.isLt, ↓reduceDIte, Fin.eta]
    simp_rw [hs]
    exact Tensor.tabulateValue_some (d+1) v

theorem map_run {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) (d : ℕ)
    (a : Option (Matrix (Fin d) (Fin d) R)) (v : Option (Fin d → R)) (n : Option ℕ) :
    run Value.add Value.mul 0 1 d (a.map (fun a i j => f (a i j)))
      (v.map (fun v i => f (v i))) n =
      (run Value.add Value.mul 0 1 d a v n).map (fun v i => f (v i)) := by
  unfold run
  cases a with
  | none => rfl
  | some a =>
    cases n with
    | none => rfl
    | some n =>
      simp only [Option.map]
      rw [AffineRecurrence.power_some, AffineRecurrence.power_some]
      cases v with
      | none => rfl
      | some v =>
        simp only [Option.map]
        rw [Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl),
          Tensor.matvecValue_some Value.add Value.mul (fun _ _ => rfl) (fun _ _ => rfl)]
        apply congrArg some
        funext i
        change (((a.map f)^n).mulVec (f ∘ v)) i = f (((a^n).mulVec v) i)
        rw [← show (a^n).map f=(a.map f)^n from map_pow f.mapMatrix a n]
        exact (f.map_mulVec (a^n) v i).symm

theorem lift_value {R S : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (project : Option S → Option R) (hn : project none=none)
    (hs : ∀ x, project (some (f x))=some x) (d : ℕ)
    (zero one : S) (hz : zero=0) (ho : one=1)
    (a : Option (Matrix (Fin (d+1)) (Fin (d+1)) R)) (v : Option (Fin (d+1) → R)) (n : Option ℕ)
    (b : Option (Matrix (Fin (d+1)) (Fin (d+1)) S)) (w : Option (Fin (d+1) → S))
    (hb : b=a.map (fun a i j => f (a i j))) (hw : w=v.map (fun v i => f (v i))) :
    run Value.add Value.mul 0 1 (d+1) a v n =
      restore project (d+1) (run Value.add Value.mul zero one (d+1) b w n) := by
  subst zero; subst one
  rw [hb, hw, map_run, restore_map f project hn hs]

theorem map_nil {R S : Type} (f : R → S) :
    Tensor.nilValue=(Tensor.nilValue : Option (Fin 0 → R)).map (fun v i => f (v i)) := by
  apply congrArg some
  funext i
  exact Fin.elim0 i

theorem map_cons {R S : Type} {d : ℕ} (f : R → S)
    (x : Option R) (xs : Option (Fin d → R)) (y : Option S) (ys : Option (Fin d → S))
    (hy : y=x.map f) (hys : ys=xs.map (fun v i => f (v i))) :
    Tensor.consValue y ys=(Tensor.consValue x xs).map (fun v i => f (v i)) := by
  rw [hy, hys]
  cases x <;> cases xs <;> simp only [Tensor.consValue, Option.map,
    Option.none_bind, Option.some_bind]
  apply congrArg some
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem castNR (x : Option ℕ) :
    Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply x))=
      x.map (Nat.castRingHom ℝ) := by
  cases x <;> simp [Function1.apply, Functions.castNZ, Functions.castZQ, Functions.castQR]

theorem castZR (x : Option ℤ) :
    Functions.castQR.apply (Functions.castZQ.apply x)=x.map (Int.castRingHom ℝ) := by
  cases x <;> simp [Function1.apply, Functions.castZQ, Functions.castQR]

theorem castNC (x : Option ℕ) :
    Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply (Functions.castNZ.apply x)))=
      x.map (Nat.castRingHom ℂ) := by
  cases x <;> simp [Function1.apply, Functions.castNZ, Functions.castZQ, Functions.castQR, Functions.castRC]

theorem castZC (x : Option ℤ) :
    Functions.castRC.apply (Functions.castQR.apply (Functions.castZQ.apply x))=
      x.map (Int.castRingHom ℂ) := by
  cases x <;> simp [Function1.apply, Functions.castZQ, Functions.castQR, Functions.castRC]

theorem liftNR (d : ℕ) (zero one : ℝ) (hz : zero=0) (ho : one=1)
    (a : Option (Matrix (Fin (d+1)) (Fin (d+1)) ℕ)) (v : Option (Fin (d+1) → ℕ)) (n : Option ℕ)
    (b : Option (Matrix (Fin (d+1)) (Fin (d+1)) ℝ)) (w : Option (Fin (d+1) → ℝ))
    (hb : b=a.map (fun a i j => (a i j : ℝ))) (hw : w=v.map (fun v i => (v i : ℝ))) :
    run Functions.addN.apply Functions.mulN.apply 0 1 (d+1) a v n =
      restore Functions.floorN.apply (d+1) (run Value.add Value.mul zero one (d+1) b w n) := by
  rw [AffineRecurrence.addN, AffineRecurrence.mulN]
  exact lift_value (Nat.castRingHom ℝ) Functions.floorN.apply rfl
    (by intro x; simp [Function1.apply, Functions.floorN]) d zero one hz ho a v n b w hb hw

theorem liftZR (d : ℕ) (zero one : ℝ) (hz : zero=0) (ho : one=1)
    (a : Option (Matrix (Fin (d+1)) (Fin (d+1)) ℤ)) (v : Option (Fin (d+1) → ℤ)) (n : Option ℕ)
    (b : Option (Matrix (Fin (d+1)) (Fin (d+1)) ℝ)) (w : Option (Fin (d+1) → ℝ))
    (hb : b=a.map (fun a i j => (a i j : ℝ))) (hw : w=v.map (fun v i => (v i : ℝ))) :
    run Functions.addZ.apply Functions.mulZ.apply 0 1 (d+1) a v n =
      restore Functions.floorR.apply (d+1) (run Value.add Value.mul zero one (d+1) b w n) := by
  rw [AffineRecurrence.addZ, AffineRecurrence.mulZ]
  exact lift_value (Int.castRingHom ℝ) Functions.floorR.apply rfl
    (by intro x; simp [Function1.apply, Functions.floorR]) d zero one hz ho a v n b w hb hw

theorem liftNC (d : ℕ) (zero one : ℂ) (hz : zero=0) (ho : one=1)
    (a : Option (Matrix (Fin (d+1)) (Fin (d+1)) ℕ)) (v : Option (Fin (d+1) → ℕ)) (n : Option ℕ)
    (b : Option (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) (w : Option (Fin (d+1) → ℂ))
    (hb : b=a.map (fun a i j => (a i j : ℂ))) (hw : w=v.map (fun v i => (v i : ℂ))) :
    run Functions.addN.apply Functions.mulN.apply 0 1 (d+1) a v n =
      restore (fun x => Functions.floorN.apply (Functions.reC.apply x)) (d+1)
        (run Value.add Value.mul zero one (d+1) b w n) := by
  rw [AffineRecurrence.addN, AffineRecurrence.mulN]
  exact lift_value (Nat.castRingHom ℂ) (fun x => Functions.floorN.apply (Functions.reC.apply x)) rfl
    (by intro x; simp [Function1.apply, Functions.floorN, Functions.reC]) d zero one hz ho a v n b w hb hw

theorem liftZC (d : ℕ) (zero one : ℂ) (hz : zero=0) (ho : one=1)
    (a : Option (Matrix (Fin (d+1)) (Fin (d+1)) ℤ)) (v : Option (Fin (d+1) → ℤ)) (n : Option ℕ)
    (b : Option (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) (w : Option (Fin (d+1) → ℂ))
    (hb : b=a.map (fun a i j => (a i j : ℂ))) (hw : w=v.map (fun v i => (v i : ℂ))) :
    run Functions.addZ.apply Functions.mulZ.apply 0 1 (d+1) a v n =
      restore (fun x => Functions.floorR.apply (Functions.reC.apply x)) (d+1)
        (run Value.add Value.mul zero one (d+1) b w n) := by
  rw [AffineRecurrence.addZ, AffineRecurrence.mulZ]
  exact lift_value (Int.castRingHom ℂ) (fun x => Functions.floorR.apply (Functions.reC.apply x)) rfl
    (by intro x; simp [Function1.apply, Functions.floorR, Functions.reC]) d zero one hz ho a v n b w hb hw

end QSym.IntegerSpectra
