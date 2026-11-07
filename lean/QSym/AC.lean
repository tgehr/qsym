import Mathlib.Data.Multiset.OrderedMonoid

namespace QSym.Replay

structure AC (α : Type) where
  op : α → α → α
  unit : α
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  comm : ∀ x y, op x y = op y x
  right_id : ∀ x, op x unit = x

inductive Tree where
  | leaf (index : Nat)
  | unit
  | node (left right : Tree)
  deriving DecidableEq

def Tree.leaves : Tree → List Nat
  | .leaf i => [i]
  | .unit => []
  | .node l r => l.leaves ++ r.leaves

def AC.eval {α : Type} (a : AC α) (ρ : Nat → α) : Tree → α
  | .leaf i => ρ i
  | .unit => a.unit
  | .node l r => a.op (a.eval ρ l) (a.eval ρ r)

def AC.fold {α : Type} (a : AC α) (ρ : Nat → α) : List Nat → α
  | [] => a.unit
  | i :: is => a.op (ρ i) (a.fold ρ is)

theorem AC.left_id {α : Type} (a : AC α) (x : α) : a.op a.unit x = x := by
  rw [a.comm, a.right_id]

def AC.repeat {α : Type} (a : AC α) (x : α) : Nat → α
  | 0 => a.unit
  | n+1 => a.op x (a.repeat x n)

theorem AC.repeat_add {α : Type} (a : AC α) (x : α) (n m : Nat) :
    a.repeat x (n+m) = a.op (a.repeat x n) (a.repeat x m) := by
  induction n with
  | zero => simp [AC.repeat, a.left_id]
  | succ n ih => simpa [AC.repeat, Nat.succ_add, ih] using (a.assoc x (a.repeat x n) (a.repeat x m)).symm

theorem AC.fold_append {α : Type} (a : AC α) (ρ : Nat → α) (xs ys : List Nat) :
    a.fold ρ (xs ++ ys) = a.op (a.fold ρ xs) (a.fold ρ ys) := by
  induction xs with
  | nil => simp [fold, a.left_id]
  | cons x xs ih => simp [fold, ih, a.assoc]

theorem AC.eval_fold {α : Type} (a : AC α) (ρ : Nat → α) (t : Tree) :
    a.eval ρ t = a.fold ρ t.leaves := by
  induction t with
  | leaf i => simp [eval, Tree.leaves, fold, a.right_id]
  | unit => rfl
  | node l r hl hr => simp [eval, Tree.leaves, hl, hr, a.fold_append]

theorem AC.fold_perm {α : Type} (a : AC α) (ρ : Nat → α) {xs ys : List Nat}
    (h : xs.Perm ys) : a.fold ρ xs = a.fold ρ ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [fold, ih]
  | swap x y xs =>
    simp only [fold]
    rw [← a.assoc, ← a.assoc, a.comm (ρ x) (ρ y)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem AC.sound {α : Type} (a : AC α) (ρ : Nat → α) (x y : Tree)
    (h : x.leaves.Perm y.leaves) : a.eval ρ x = a.eval ρ y := by
  rw [a.eval_fold, a.eval_fold]
  exact a.fold_perm ρ h

abbrev Counts := List (Nat × Nat)

def Counts.mergeFuel : Nat → Counts → Counts → Counts
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, (i, n) :: xs, (j, m) :: ys =>
    if i < j then (i, n) :: mergeFuel fuel xs ((j, m) :: ys)
    else if i = j then (i, n + m) :: mergeFuel fuel xs ys
    else (j, m) :: mergeFuel fuel ((i, n) :: xs) ys

def Counts.merge (xs ys : Counts) : Counts := mergeFuel (xs.length + ys.length) xs ys

def Counts.denote : Counts → Multiset Nat
  | [] => 0
  | (i, n) :: xs => n • ({i} : Multiset Nat) + denote xs

theorem Counts.denote_append (xs ys : Counts) : denote (xs ++ ys) = denote xs + denote ys := by
  induction xs with
  | nil => simp [denote]
  | cons x xs ih => obtain ⟨i, n⟩ := x; simp [denote, ih, add_assoc]

theorem Counts.denote_mergeFuel (fuel : Nat) (xs ys : Counts) :
    denote (mergeFuel fuel xs ys) = denote xs + denote ys := by
  induction fuel generalizing xs ys with
  | zero => exact denote_append xs ys
  | succ fuel ih =>
    cases xs with
    | nil => simp [mergeFuel, denote]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel, denote]
      | cons y ys =>
        obtain ⟨i, n⟩ := x
        obtain ⟨j, m⟩ := y
        simp only [mergeFuel]
        split
        · simp [denote, ih, add_assoc]
        · split
          · next h => subst j; simp only [denote, ih, add_nsmul]; ac_rfl
          · simp only [denote, ih]; ac_rfl

theorem Counts.denote_merge (xs ys : Counts) :
    denote (Counts.merge xs ys) = denote xs + denote ys := denote_mergeFuel _ xs ys

def Tree.counts : Tree → Counts
  | .leaf i => [(i, 1)]
  | .unit => []
  | .node l r => Counts.merge l.counts r.counts

theorem Tree.counts_node (l r : Tree) {ls rs result : Counts}
    (hl : l.counts = ls) (hr : r.counts = rs) (h : Counts.merge ls rs = result) :
    (Tree.node l r).counts = result := (congrArg₂ Counts.merge hl hr).trans h

theorem Tree.denote_counts (t : Tree) : Counts.denote t.counts = (t.leaves : Multiset Nat) := by
  induction t with
  | leaf i => simp [counts, Counts.denote, leaves]
  | unit => rfl
  | node l r hl hr => simp [counts, Counts.denote_merge, leaves, hl, hr, Multiset.coe_add]

theorem AC.sound_counts {α : Type} (a : AC α) (ρ : Nat → α) (x y : Tree)
    (h : x.counts = y.counts) : a.eval ρ x = a.eval ρ y := by
  apply a.sound ρ x y
  apply Multiset.coe_eq_coe.mp
  rw [← x.denote_counts, ← y.denote_counts, h]

end QSym.Replay
