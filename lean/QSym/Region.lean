import QSym.Expr
import QSym.Replay
import Mathlib.Data.Multiset.Fold

namespace QSym

inductive Positive where
  | one
  | twice (half : Positive)
  | twicePlusOne (half : Positive)
  deriving DecidableEq

def Positive.toNat : Positive → Nat
  | .one => 1
  | .twice n => n.toNat+n.toNat
  | .twicePlusOne n => n.toNat+n.toNat+1

def Positive.repeat {α : Type} (op : α → α → α) (x : α) : Positive → α
  | .one => x
  | .twice n => let y := n.repeat op x; op y y
  | .twicePlusOne n => let y := n.repeat op x; op (op y y) x

theorem Positive.repeat_hom {α β : Type} (op : α → α → α) (op' : β → β → β)
    (f : α → β) (h : ∀ x y, f (op x y)=op' (f x) (f y)) (x : α) (n : Positive) :
    f (n.repeat op x)=n.repeat op' (f x) := by
  induction n <;> simp [Positive.repeat, h, *]

theorem Positive.repeat_eq {α : Type} (a : Replay.AC α) (x : α) (n : Positive) :
    n.repeat a.op x=a.repeat x n.toNat := by
  induction n <;> simp [Positive.repeat, toNat, Replay.AC.repeat_add, Replay.AC.repeat, a.right_id, a.comm, *]

inductive Region (α : Type) where
  | unit
  | item (value : α) (count : Positive)
  | join (left right : Region α)
  deriving DecidableEq

def Region.fold {α β : Type} (op : β → β → β) (unit : β) (f : α → β) : Region α → β
  | .unit => unit
  | .item x n => n.repeat op (f x)
  | .join l r => op (l.fold op unit f) (r.fold op unit f)

def Region.contents {α : Type} : Region α → Multiset α
  | .unit => 0
  | .item x n => n.toNat • {x}
  | .join l r => l.contents+r.contents

theorem Region.fold_hom {α β γ : Type} (op : β → β → β) (unit : β)
    (op' : γ → γ → γ) (unit' : γ) (f : β → γ) (g : α → β)
    (hu : f unit=unit') (ho : ∀ x y, f (op x y)=op' (f x) (f y)) (r : Region α) :
    f (r.fold op unit g)=r.fold op' unit' (fun x => f (g x)) := by
  induction r <;> simp [fold, hu, ho, Positive.repeat_hom, *]

private def foldMultiset {α β : Type} (a : Replay.AC β) (f : α → β) (s : Multiset α) : β :=
  letI : Std.Commutative a.op := ⟨a.comm⟩
  letI : Std.Associative a.op := ⟨a.assoc⟩
  Multiset.fold a.op a.unit (s.map f)

private theorem foldMultiset_add {α β : Type} (a : Replay.AC β) (f : α → β) (s t : Multiset α) :
    foldMultiset a f (s+t)=a.op (foldMultiset a f s) (foldMultiset a f t) := by
  letI : Std.Commutative a.op := ⟨a.comm⟩
  letI : Std.Associative a.op := ⟨a.assoc⟩
  unfold foldMultiset
  rw [Multiset.map_add]
  simpa only [a.right_id] using Multiset.fold_add a.op a.unit a.unit (s.map f) (t.map f)

private theorem foldMultiset_repeat {α β : Type} (a : Replay.AC β) (f : α → β) (x : α) (n : Nat) :
    foldMultiset a f (n • ({x} : Multiset α))=a.repeat (f x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [succ_nsmul, foldMultiset_add, ih]
    simp [foldMultiset, Multiset.fold_singleton, a.right_id, Replay.AC.repeat, a.comm]

theorem Region.fold_contents {α β : Type} (a : Replay.AC β) (f : α → β) (r : Region α) :
    r.fold a.op a.unit f=foldMultiset a f r.contents := by
  induction r with
  | unit => rfl
  | item x n => exact (n.repeat_eq a (f x)).trans (foldMultiset_repeat a f x n.toNat).symm
  | join l r hl hr => simp [fold, contents, foldMultiset_add, hl, hr]

theorem Region.fold_congr {α β : Type} (a : Replay.AC β) (f : α → β) (r s : Region α)
    (h : r.contents=s.contents) : r.fold a.op a.unit f=s.fold a.op a.unit f :=
  (r.fold_contents a f).trans ((congrArg (foldMultiset a f) h).trans (s.fold_contents a f).symm)

namespace Expr

def sumR (r : Region (Expr .real)) : Expr .real := r.fold addR (.real 0) id
def sumC (r : Region (Expr .complex)) : Expr .complex := r.fold addC (.complex 0 0) id
def productR (r : Region (Expr .real)) : Expr .real := r.fold mulR (.real 1) id
def productC (r : Region (Expr .complex)) : Expr .complex := r.fold mulC (.complex 1 0) id

theorem eval_sumR (ρ : Env) (r : Region (Expr .real)) :
    eval ρ (sumR r)=r.fold Value.add (some 0) (eval ρ) :=
  r.fold_hom addR (.real 0) Value.add (some 0) (eval ρ) id (by simp [eval]) (fun _ _ => rfl)

theorem eval_sumC (ρ : Env) (r : Region (Expr .complex)) :
    eval ρ (sumC r)=r.fold Value.add (some 0) (eval ρ) := by
  exact r.fold_hom addC (.complex 0 0) Value.add (some 0) (eval ρ) id (by simp [eval]) (fun _ _ => rfl)

theorem eval_productR (ρ : Env) (r : Region (Expr .real)) :
    eval ρ (productR r)=r.fold Value.mul (some 1) (eval ρ) :=
  r.fold_hom mulR (.real 1) Value.mul (some 1) (eval ρ) id (by simp [eval]) (fun _ _ => rfl)

theorem eval_productC (ρ : Env) (r : Region (Expr .complex)) :
    eval ρ (productC r)=r.fold Value.mul (some 1) (eval ρ) := by
  exact r.fold_hom mulC (.complex 1 0) Value.mul (some 1) (eval ρ) id (by simp [eval]) (fun _ _ => rfl)

end Expr
end QSym
