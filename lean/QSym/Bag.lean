import QSym.AC

namespace QSym.Replay

inductive Bag : Nat → Type where
  | zero {h : Nat} : Bag h
  | leaf (count : Nat) : Bag 0
  | node {h : Nat} (left right : Bag h) : Bag (h+1)

def Bag.merge {h : Nat} : Bag h → Bag h → Bag h
  | .zero, y => y
  | x, .zero => x
  | .leaf n, .leaf m => .leaf (n+m)
  | .node l r, .node s t => .node (l.merge s) (r.merge t)
termination_by structural h

def Bag.eval {α : Type} (a : AC α) (ρ : Nat → α) {h : Nat} : Bag h → α
  | .zero => a.unit
  | .leaf n => a.repeat (ρ 0) n
  | .node l r => a.op (l.eval a (fun i => ρ (2*i))) (r.eval a (fun i => ρ (2*i+1)))
termination_by structural h

theorem Bag.eval_merge {α : Type} (a : AC α) (ρ : Nat → α) {h : Nat} (x y : Bag h) :
    (x.merge y).eval a ρ = a.op (x.eval a ρ) (y.eval a ρ) := by
  induction x generalizing ρ with
  | zero => simp [merge, eval, a.left_id]
  | leaf n => cases y <;> simp [merge, eval, a.right_id, a.repeat_add]
  | node l r hl hr =>
    cases y with
    | zero => simp [merge, eval, a.right_id]
    | node s t =>
      simp only [merge, eval, hl, hr]
      simp only [a.assoc]
      congr 1
      rw [← a.assoc, a.comm (s.eval a _) (r.eval a _), a.assoc]

def Bag.single : (h : Nat) → Nat → Bag h
  | 0, _ => .leaf 1
  | h+1, i => if i%2=0 then .node (single h (i/2)) .zero else .node .zero (single h (i/2))

theorem Bag.eval_single {α : Type} (a : AC α) (ρ : Nat → α) (h i : Nat) (hi : i<2^h) :
    (single h i).eval a ρ = ρ i := by
  induction h generalizing i ρ with
  | zero =>
    have : i=0 := by simpa using hi
    subst i
    simp [single, eval, AC.repeat, a.right_id]
  | succ h ih =>
    have hd : i/2<2^h := by rw [pow_succ] at hi; omega
    simp only [single]
    split
    · next he =>
      simp only [eval, ih _ _ hd, a.right_id]
      congr 1; omega
    · next he =>
      simp only [eval, ih _ _ hd, a.left_id]
      congr 1; omega

theorem Bag.atom_sound {α : Type} (a : AC α) (ρ : Nat → α) (h i : Nat) (x : α) (b : Bag h)
    (hi : i<2^h) (hb : single h i=b) (hx : ρ i=x) : x=b.eval a ρ :=
  hx.symm.trans ((eval_single a ρ h i hi).symm.trans (congrArg (eval a ρ) hb))

theorem Bag.node_sound {α : Type} (a : AC α) (ρ : Nat → α) {h : Nat}
    (x y : α) (l r b : Bag h) (hl : x=l.eval a ρ) (hr : y=r.eval a ρ) (hb : l.merge r=b) :
    a.op x y=b.eval a ρ :=
  (congrArg₂ a.op hl hr).trans ((eval_merge a ρ l r).symm.trans (congrArg (eval a ρ) hb))

end QSym.Replay
