-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Language.lagda

import GroundZero.Types.Id

open List

-- module Language {ℓ} (A : Set ℓ) where
universe u
variable (α : Type u)

-- Lang : Set (suc ℓ)
-- Lang = A ✶ → Set ℓ
def Lang: Type (u + 1) :=
  List α -> Type u

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
  fun w => w = []

-- ` : A → Lang
-- ` c w = w ≡ [ c ]
def char (a : α): Lang α :=
  fun w => w = [a]

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
    Σ (x : List α) (y : List α), (w = (x ++ y)) × P x × Q y

-- Only the Prop version is available in mathlib https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Defs.html#List.Forall
-- so we have to create our own version for Type
inductive All {α: Type u} (P : α -> Type u) : (List α -> Type u)  where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

-- infixl 10 _☆
-- _☆ : Op₁ Lang
-- (P ☆) w = ∃ λ ws → (w ≡ concat ws) × All P ws
def star (P : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ (ws : List (List α)), (w = (List.join ws)) × All P ws

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptySet emptyStr char scalar or and concat star

end Lang
