-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Language.lagda

import Katydid.Std.Tipe

namespace Language

-- module Language {ℓ} (A : Set ℓ) where
universe u

-- Lang : Set (suc ℓ)
-- Lang = A ✶ → Set ℓ
def Lang (α : Type u) : Type (u + 1) :=
  List α -> Type u

-- variable α should be implicit to make sure examples do not need to also provide the parameter of α when constructing char, or, concat, since it usually can be inferred to be Char.
variable {α : Type u}

-- ∅ : Lang
-- ∅ w = ⊥
def emptyset : Lang α :=
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
def emptystr : Lang α :=
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
    Σ' (x : List α) (y : List α), (_px: P x) ×' (_qy: Q y) ×' w = (x ++ y)

inductive All {α: Type u} (P : α -> Type u) : (List α -> Type u) where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

-- infixl 10 _☆
-- _☆ : Op₁ Lang
-- (P ☆) w = ∃ λ ws → (w ≡ concat ws) × All P ws
def star (P : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ' (ws : List (List α)), (_pws: All P ws) ×' w = (List.join ws)

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptyset emptystr char scalar or and concat star

example: Lang α := universal
example: Lang α := emptystr
example: Lang α := (or emptystr universal)
example: Lang α := (and emptystr universal)
example: Lang α := emptyset
example: Lang α := (star emptyset)
example: Lang Char := char 'a'
example: Lang Char := char 'b'
example: Lang Char := (or (char 'a') emptyset)
example: Lang Char := (and (char 'a') (char 'b'))
example: Lang Nat := (and (char 1) (char 2))
example: Lang Nat := (scalar PUnit (char 2))
example: Lang Nat := (concat (char 1) (char 2))

-- 𝜈 :(A✶ → B) → B -- “nullable”
-- 𝜈 f = f []
-- nullable
-- ν = backslash nu
def null (f: List α -> β): β :=
  f []

-- 𝒟: (A✶ → B) → A✶ → (A✶ → B) -- “derivative”
-- 𝒟 f u = 𝜆 v → f (u + v)
-- 𝒟 = backslash McD
def derives (f: List α -> β) (u: List α): (List α -> β) :=
  fun v => f (u ++ v)

-- 𝛿 : (A✶ → B) → A → (A✶ → B)
-- 𝛿 f a = 𝒟 f [a]
-- δ = backslash delta or backslash Gd
def derive (f: List α -> β) (a: α): (List α -> β) :=
  derives f [a]

end Language
