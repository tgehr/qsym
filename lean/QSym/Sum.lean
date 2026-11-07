import QSym.Replay

namespace QSym.Replay

def AC.evalCounts {α : Type} (a : AC α) (ρ : Nat → α) : Counts → α
  | [] => a.unit
  | (i,n)::xs => a.op (a.repeat (ρ i) n) (a.evalCounts ρ xs)

def Counts.insert (i n : Nat) : Counts → Counts
  | [] => [(i,n)]
  | (j,m)::xs =>
    if i<j then (i,n)::(j,m)::xs
    else if i=j then (i,n+m)::xs
    else (j,m)::Counts.insert i n xs

theorem AC.evalCounts_insert {α : Type} (a : AC α) (ρ : Nat → α) (i n : Nat) (xs : Counts) :
    a.evalCounts ρ (Counts.insert i n xs) = a.op (a.repeat (ρ i) n) (a.evalCounts ρ xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨j,m⟩ := x
    simp only [Counts.insert]
    split
    · rfl
    · split
      · next h => subst j; simp [evalCounts, a.repeat_add, a.assoc]
      · simp only [evalCounts, ih]
        rw [← a.assoc, a.comm (a.repeat (ρ j) m), a.assoc]

end QSym.Replay

namespace QSym.Sum
open Replay

inductive Atom (κ : Type) where
  | literal (value : κ)
  | term (index : Nat)
  deriving DecidableEq

abbrev Expr (κ : Type) := List (Atom κ × Nat)

structure Normal (κ : Type) where
  constant : κ
  terms : Counts
  deriving DecidableEq

structure Model (κ α : Type) where
  ac : AC α
  zero : κ
  add : κ → κ → κ
  scale : Nat → κ → κ
  literal : κ → α
  zero_sound : literal zero = ac.unit
  add_sound : ∀ x y, literal (add x y) = ac.op (literal x) (literal y)
  scale_sound : ∀ n x, literal (scale n x) = ac.repeat (literal x) n

def eval {κ α : Type} (m : Model κ α) (ρ : Nat → α) : Expr κ → α
  | [] => m.ac.unit
  | (a,n)::xs => m.ac.op (m.ac.repeat (match a with | .literal x => m.literal x | .term i => ρ i) n) (eval m ρ xs)

def normalize {κ α : Type} (m : Model κ α) : Expr κ → Normal κ
  | [] => ⟨m.zero,[]⟩
  | (.literal x,n)::xs => let r := normalize m xs; ⟨m.add (m.scale n x) r.constant,r.terms⟩
  | (.term i,n)::xs => let r := normalize m xs; ⟨r.constant,Counts.insert i n r.terms⟩

def evalNormal {κ α : Type} (m : Model κ α) (ρ : Nat → α) (r : Normal κ) : α :=
  m.ac.op (m.literal r.constant) (m.ac.evalCounts ρ r.terms)

theorem normalize_sound {κ α : Type} (m : Model κ α) (ρ : Nat → α) (xs : Expr κ) :
    eval m ρ xs = evalNormal m ρ (normalize m xs) := by
  induction xs with
  | nil => simp [eval, normalize, evalNormal, AC.evalCounts, m.zero_sound, m.ac.right_id]
  | cons x xs ih =>
    obtain ⟨a,n⟩ := x
    cases a with
    | literal x => simp [eval, normalize, evalNormal, ih, m.add_sound, m.scale_sound, m.ac.assoc]
    | term i =>
      simp only [eval, normalize, ih, evalNormal, m.ac.evalCounts_insert]
      rw [← m.ac.assoc, m.ac.comm (m.ac.repeat (ρ i) n), m.ac.assoc]

def check {κ α : Type} [DecidableEq κ] (m : Model κ α) (xs ys : Expr κ) : Bool :=
  decide (normalize m xs = normalize m ys)

theorem sound {κ α : Type} [DecidableEq κ] (m : Model κ α) (ρ : Nat → α) (xs ys : Expr κ)
    (h : check m xs ys = true) : eval m ρ xs = eval m ρ ys :=
  (normalize_sound m ρ xs).trans ((congrArg (evalNormal m ρ) (of_decide_eq_true h)).trans (normalize_sound m ρ ys).symm)

private theorem scale_real (n : Nat) (q : ℚ) :
    some (((n : ℚ)*q : ℚ) : ℝ) = addR.repeat (some (q : ℝ)) n := by
  induction n with
  | zero => simp [AC.repeat, addR]
  | succ n ih =>
    rw [AC.repeat, ← ih]
    simp [addR, Value.add, Nat.cast_add, Nat.cast_one, add_mul, add_comm]

noncomputable def real : Model ℚ (Option ℝ) where
  ac := addR
  zero := 0
  add := (·+·)
  scale := fun n q => (n : ℚ)*q
  literal := fun q => some (q : ℝ)
  zero_sound := by simp [addR]
  add_sound := by intros; simp [addR, Value.add]
  scale_sound := scale_real

private noncomputable def castComplex (q : ℚ × ℚ) : Option ℂ :=
  some ((q.1 : ℂ)+(q.2 : ℂ)*Complex.I)

private theorem scale_complex (n : Nat) (q : ℚ × ℚ) :
    castComplex ((n : ℚ)*q.1,(n : ℚ)*q.2) = addC.repeat (castComplex q) n := by
  induction n with
  | zero => simp [castComplex, AC.repeat, addC]
  | succ n ih =>
    rw [AC.repeat, ← ih]
    simp [castComplex, addC, Value.add, Nat.cast_add, Nat.cast_one, add_mul]
    ring

noncomputable def complex : Model (ℚ × ℚ) (Option ℂ) where
  ac := addC
  zero := (0,0)
  add := fun x y => (x.1+y.1,x.2+y.2)
  scale := fun n q => ((n : ℚ)*q.1,(n : ℚ)*q.2)
  literal := castComplex
  zero_sound := by simp [castComplex, addC]
  add_sound := by intros; simp [castComplex, addC, Value.add]; ring
  scale_sound := scale_complex

end QSym.Sum
