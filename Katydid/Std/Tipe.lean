-- Tipe is a collection of standard types and functions associated with Type,
-- that we would expect to be in the Lean standard library at some point in future.
-- The file is named Tipe, since it is Afrikaans for Type and common way to avoid using the keyword Type, since it has the same pronounciation as type.

-- required for `attribute [refl]`
import Mathlib.Init.Algebra.Classes

/--
The equality relation. We use this instead of Lean's `Eq` because
we need it to be defined on Type instead of Prop.
-/
inductive TEq.{u} {α : Type u} : α -> α -> Type u where
  | refl (x : α) : TEq x x

#check TEq.casesOn

-- the abbreviation ≡ is typed with `slash = =`
infixl:65 " ≡ " => TEq

example : 1 ≡ 1 := TEq.refl 1

-- attribute [refl] allows us to use the rfl tactic on TEq, see the example below.
-- Discussion where we got the tips for this library: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/is.20there.20a.20refl.20for.20Type
attribute [refl] TEq.refl

example : 1 ≡ 1 := by rfl

example {α : Type u} {a b : α} (p q : a = b) : p = q := by
  cases p
  cases q
  rfl

example {α : Type u} {a b : α} (p q : a ≡ b) : p ≡ q := by
  cases p
  cases q
  rfl

-- rfl for Type instead of Prop
@[match_pattern] def trifle {α : Type u} {a : α} : TEq a a := @TEq.refl α a
attribute [simp] trifle

example : 1 ≡ 1 := trifle

def eq_of_teq {α : Type u} {a a' : α} (h : TEq a a') : Eq a a' :=
  have : (α β : Type u) → (a b: α) → TEq a b → (h : Eq α β) → Eq a b :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ => rfl)
  this α α a a' h rfl

-- TODO: Find out if this is legal
def teq_of_eq {α : Type u} {a a' : α} (h : Eq a a') : TEq a a' :=
  have : (α β : Type u) → (a b: α) → Eq a b → (h : TEq α β) → TEq a b :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ => trifle)
  this α α a a' h trifle

/-- Non-dependent recursor for the Tequality type. -/
@[simp] abbrev TEq.ndrec.{u1, u2} {α : Type u2} {a : α} {motive : α → Type u1} (m : motive a) {b : α} (h : TEq a b) : motive b := by
  have h' := eq_of_teq h
  apply (Eq.ndrec m h')

theorem TEq.subst {α : Type u} {motive : α → Type} {a b : α} (h₁ : TEq a b) (h₂ : motive a) : motive b :=
  TEq.ndrec h₂ h₁

noncomputable example (α : Type) (a b : α) (p : α → Type)
        (h1 : a ≡ b) (h2 : p a) : p b :=
  TEq.subst h1 h2

theorem congrTArg {α : Type u} {β : Type v} {a₁ a₂ : α} (f : α → β) (h : TEq a₁ a₂) : TEq (f a₁) (f a₂) :=
  teq_of_eq (congrArg f (eq_of_teq h))

example : ¬ 1 = 2 :=
  fun h => Eq.subst (motive := fun | 1 => True | _ => False) h trivial

example : ¬ 1 = 2 := by
  intro
  contradiction

example : 1 ≡ 2 -> False :=
  let motive | 1 => True | _ => False;
  fun h => TEq.rec (motive := fun n _ => motive n) trivial h

theorem Eq.all_tequal (p q : Eq x y) : Eq p q := by
  cases p
  cases q
  apply refl

theorem TEq.all_tequal (p q : TEq x y) : TEq p q := by
  cases p
  cases q
  apply refl

theorem TEq.all_equal (p q : TEq x y) : p = q := by
  cases p
  cases q
  rfl

-- Only the Prop version is available in mathlib https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Defs.html#List.Forall
-- so we have to create our own version for Type
inductive All {α: Type u} (P : α -> Type u) : (List α -> Type u)  where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

infixr:29 " ∷ " => All.cons
-- TODO: Find a better notation
notation (priority:=low) " ∀[] " => All.nil

-- Also note that the following doesn't work, once you start trying to prove things like that are required to be in Type and not in Prop.
-- def All {α: Type u} (P : α -> Type u) (xs: List α): Type u :=
--   ∀ x ∈ xs, P x

-- TNot is the Type version to replace the Prop version of Not
def TNot (a : Type u) : Type u := a → Empty

-- TIff is the Type version to replace the Prop version of Iff
structure TIff (a b : Type) : Type where
  /-- If `a → b` and `b → a` then `a` and `b` are equivalent. -/
  intro ::
  /-- Modus ponens for if and only if. If `a ↔ b` and `a`, then `b`. -/
  mp : a → b
  /-- Modus ponens for if and only if, reversed. If `a ↔ b` and `b`, then `a`. -/
  mpr : b → a

infix:19 " <-> " => TIff

structure Tiso (a b : Type) : Type where
  intro ::
  f : a → b
  f' : b → a
  ff' : ∀ x, f (f' x) ≡ x
  f'f : ∀ x, f' (f x) ≡ x

infix:19 " ↔ " => Tiso -- slash <->

def Teso {w : α} (P : α -> Type) (Q : α -> Type) := Tiso (P w) (Q w)

infix:19 " ⟷ " => Teso -- slash <-->

theorem t : 1 ≡ 2 -> False := by
  intro x
  contradiction

theorem t'' : 1 = 2 -> False := by
  intro
  contradiction

theorem t''' : 1 = 2 → False :=
fun a => absurd a (of_decide_eq_false (Eq.refl (decide (1 = 2))))

theorem t' : 1 ≡ 2 → False :=
fun a =>
  (TEq.casesOn (motive := fun a_1 x => 2 = a_1 → HEq a x → False) a
      (fun h => Nat.noConfusion h fun n_eq => Nat.noConfusion n_eq) (Eq.refl 2) (HEq.refl a)).elim
