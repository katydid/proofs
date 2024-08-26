-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Language.lagda

import Katydid.Std.Tipe

-- module Language {ℓ} (A : Set ℓ) where
universe u

-- Lang : Set (suc ℓ)
-- Lang = A ✶ → Set ℓ
def dLang (α : Type u) : Type (u + 1) :=
  List α -> Type u

-- namespace Lang is required to avoid ambiguities with or, and, concat and star.
namespace dLang

-- variable α should be implicit to make sure examples do not need to also provide the parameter of α when constructing char, or, concat, since it usually can be inferred to be Char.
variable {α : Type u}

-- ∅ : Lang
-- ∅ w = ⊥
def emptyset : dLang α :=
  -- PEmpty is Empty, but allows specifying the universe
  -- PEmpty is a Sort, which works for both Prop and Type
  fun _ => PEmpty

-- 𝒰 : Lang
-- 𝒰 w = ⊤
def universal : dLang α :=
  -- PUnit is Empty, but allows specifying the universe
  -- PUnit is a Sort, which works for both Prop and Type
  fun _ => PUnit

-- 𝟏 : Lang
-- 𝟏 w = w ≡ []
def emptystr : dLang α :=
  fun w => w ≡ []

-- ` : A → Lang
-- ` c w = w ≡ [ c ]
def char (a : α): dLang α :=
  fun w => w ≡ [a]

-- infixl 7 _·_
-- _·_ : Set ℓ → Op₁ Lang
-- (s · P) w = s × P w
def scalar (s : Type u) (P : dLang α) : dLang α :=
  fun w => s × P w

-- infixr 6 _∪_
-- _∪_ : Op₂ Lang
-- (P ∪ Q) w = P w ⊎ Q w
def or (P : dLang α) (Q : dLang α) : dLang α :=
  fun w => P w ⊕ Q w

-- infixr 6 _∩_
-- _∩_ : Op₂ Lang
-- (P ∩ Q) w = P w × Q w
def and (P : dLang α) (Q : dLang α) : dLang α :=
  fun w => P w × Q w

-- infixl 7 _⋆_
-- _⋆_ : Op₂ Lang
-- (P ⋆ Q) w = ∃⇃ λ (u ,  v) → (w ≡ u ⊙ v) × P u × Q v
def concat (P : dLang α) (Q : dLang α) : dLang α :=
  fun (w : List α) =>
    Σ' (x : List α) (y : List α), (_px: P x) ×' (_qy: Q y) ×' w = (x ++ y)

inductive All {α: Type u} (P : α -> Type u) : (List α -> Type u) where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

-- infixl 10 _☆
-- _☆ : Op₁ Lang
-- (P ☆) w = ∃ λ ws → (w ≡ concat ws) × All P ws
def star (P : dLang α) : dLang α :=
  fun (w : List α) =>
    Σ' (ws : List (List α)), (_pws: All P ws) ×' w = (List.join ws)

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptyset emptystr char scalar or and concat star

example: dLang α := universal
example: dLang α := emptystr
example: dLang α := (or emptystr universal)
example: dLang α := (and emptystr universal)
example: dLang α := emptyset
example: dLang α := (star emptyset)
example: dLang Char := char 'a'
example: dLang Char := char 'b'
example: dLang Char := (or (char 'a') emptyset)
example: dLang Char := (and (char 'a') (char 'b'))
example: dLang Nat := (and (char 1) (char 2))
example: dLang Nat := (scalar PUnit (char 2))
example: dLang Nat := (concat (char 1) (char 2))

-- 𝜈 :(A✶ → B) → B -- “nullable”
-- 𝜈 f = f []
-- nullable
-- ν = backslash nu
def ν (f: List α -> β): β :=
  f []

-- 𝒟: (A✶ → B) → A✶ → (A✶ → B) -- “derivative”
-- 𝒟 f u = 𝜆 v → f (u + v)
-- 𝒟 = backslash McD
def 𝒟 (f: dLang α) (u: List α): (dLang α) :=
  fun v => f (u ++ v)

-- 𝛿 : (A✶ → B) → A → (A✶ → B)
-- 𝛿 f a = 𝒟 f [a]
-- δ = backslash delta or backslash Gd
def δ (f: dLang α) (a: α): (dLang α) :=
  𝒟 f [a]

end dLang
