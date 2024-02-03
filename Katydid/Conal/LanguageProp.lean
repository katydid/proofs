-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Language.lagda

import Mathlib.Init.Algebra.Classes

example {α : Type u} {a b : α} (p q : a = b) : p = q := by
  cases p
  cases q
  rfl

open List

inductive TEq.{tu} {α: Type tu} (a b: α) : Type tu where
  | mk : a = b -> TEq a b

-- attribute [refl] TEq.mk

-- example : 1 ≡ 1 := by rfl

@[match_pattern] def trifle {α : Type u} {a : α} : TEq a a := TEq.mk rfl
attribute [simp] trifle

-- the abbreviation ≡ is typed with `slash = =`
infixl:65 " ≡ " => TEq

-- TODO: Do we have to redefine Equiv for TEq?
-- TODO: How can we make rewrite easier, without needing to destruct first?
--   TODO: if all else fails, write a tactic
-- TODO: Try to use Σ' and ×' instead of TEq

-- module Language {ℓ} (A : Set ℓ) where
universe u
variable (α : Type u)

-- Lang : Set (suc ℓ)
-- Lang = A ✶ → Set ℓ
def Lang : Type (u + 1) :=
  List α -> Type u

-- Sort 0 = Prop
-- Sort 1 = Type 0
-- Sort 2 = Type 1



-- inductive climb (p: Prop) : Type u where
--   | up (x: p): climb p

-- def Lang: Type (u + 1) :=
--   List α -> Type u

-- namespace Lang is required to avoid ambiguities with or, and, concat and star.
namespace Lang

-- variable α should be implicit to make sure examples do not need to also provide the parameter of α when constructing char, or, concat, since it usually can be inferred to be Char.
variable {α : Type u}

-- ∅ : Lang
-- ∅ w = ⊥
def emptySet : Lang α :=
  -- PEmpty is Empty, but allows specifying the universe
  -- PEmpty is a Sort, which works for both Prop and Type
  fun _ => PEmpty

-- 𝒰 : Lang
-- 𝒰 w = ⊤
def universal : Lang α :=
  -- PUnit is Empty, but allows specifying the universe
  -- PUnit is a Sort, which works for both Prop and Type
  fun _ => PUnit

-- 𝟏 : Lang
-- 𝟏 w = w ≡ []
def emptyStr : Lang α :=
  fun w => w ≡ []

-- ` : A → Lang
-- ` c w = w ≡ [ c ]
def char (a : α): Lang α :=
  fun w => w ≡ [a]

-- infixl 7 _·_
-- _·_ : Set ℓ → Op₁ Lang
-- (s · P) w = s × P w
def scalar (s : Type u) (P : Lang α) : Lang α :=
  fun w => s × P w

-- infixr 6 _∪_
-- _∪_ : Op₂ Lang
-- (P ∪ Q) w = P w ⊎ Q w
def or (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w ⊕ Q w

-- infixr 6 _∩_
-- _∩_ : Op₂ Lang
-- (P ∩ Q) w = P w × Q w
def and (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w × Q w

-- infixl 7 _⋆_
-- _⋆_ : Op₂ Lang
-- (P ⋆ Q) w = ∃⇃ λ (u ,  v) → (w ≡ u ⊙ v) × P u × Q v
def concat (P : Lang α) (Q : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ' (x : List α) (y : List α), w ≡ (x ++ y) × P x × Q y

inductive All {α: Type u} (P : α -> Type u) : (List α -> Type u)  where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

-- infixl 10 _☆
-- _☆ : Op₁ Lang
-- (P ☆) w = ∃ λ ws → (w ≡ concat ws) × All P ws
def star (P : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ' (ws : List (List α)), w ≡ (List.join ws) × All P ws

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptySet emptyStr char scalar or and concat star

end Lang

theorem rewrite_test:
  ∀ (_: a ≡ b) (_: b ≡ c),
    a ≡ c := by
  intro ab bc
  cases ab with
  | mk ab =>
    rw [ab]
    cases bc with
    | mk bc =>
      rw [bc]
      constructor
      rfl

theorem rewrite_test':
  ∀ (_: a ≡ b) (_: b ≡ c),
    a ≡ c := by
  intro ab bc
  cases ab with
  | mk ab =>
    rw [ab]
    cases bc with
    | mk bc =>
      rw [bc]
      exact trifle

def rewrite_test'' (ab: a ≡ b) (bc: b ≡ c): a ≡ c :=
  match (ab, bc) with
  | ⟨ ⟨ ab' ⟩ , ⟨ bc' ⟩ ⟩ => by sorry

theorem rewrite_test''':
  ∀ (_: a ≡ b) (_: b ≡ c),
    a ≡ c := by
  intro ab bc



  cases ab with
  | mk ab =>
    rw [ab]
    cases bc with
    | mk bc =>
      rw [bc]
      exact trifle
