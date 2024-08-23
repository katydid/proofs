-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Language.lagda
import Katydid.Std.Tipe2

open List

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

-- TODO: Why are these definitions open, instead of in an inductive family, like
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Proof.20relevance/near/419702213
-- One reason is that with not operator, which run into the strictly positive limitation, but we don't have the not operator in the Agda paper.
-- TODO: Ask Conal if there is another reason.

-- ∅ : Lang
-- ∅ w = ⊥
def emptySet : dLang α :=
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
def emptyStr : dLang α :=
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

-- TODO: What does proof relevance even mean for the `not` operator?
def not (P: dLang α) : dLang α :=
  fun (w: List α) =>
    P w -> Empty

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptySet emptyStr char scalar or and concat star

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

-- data Dec (A: Set l):Set l where
--   yes: A → Dec A
--   no :¬A → Dec A
inductive Dec (α: Type u): Type u where
  | yes: α -> Dec α
  | no: (α -> PEmpty.{u}) -> Dec α

-- ⊥? : Dec ⊥
-- ⊥? =no(𝜆())
def empty? : Dec PEmpty :=
  Dec.no (by intro; contradiction)

def unit? : Dec PUnit :=
  Dec.yes PUnit.unit

def sum? (a: Dec α) (b: Dec β): Dec (α ⊕ β) :=
  match (a, b) with
  | (Dec.no a, Dec.no b) =>
    Dec.no (fun ab =>
      match ab with
      | Sum.inl sa => a sa
      | Sum.inr sb => b sb
    )
  | (Dec.yes a, Dec.no _) =>
    Dec.yes (Sum.inl a)
  | (_, Dec.yes b) =>
    Dec.yes (Sum.inr b)

def prod? (a: Dec α) (b: Dec β): Dec (α × β) :=
  match (a, b) with
  | (Dec.yes a, Dec.yes b) => Dec.yes (Prod.mk a b)
  | (Dec.no a, Dec.yes _) => Dec.no (fun ⟨a', _⟩ => a a')
  | (_, Dec.no b) => Dec.no (fun ⟨_, b'⟩ => b b')

def list?: Dec α -> Dec (List α) := fun _ => Dec.yes []



inductive Lang : (List α -> Type u) -> Type (u + 1) where
  -- | emptySet : Lang dLang.emptySet
  | universal : Lang (fun _ => PUnit)
  -- | emptyStr : Lang dLang.emptyStr
  -- | char {a: Type u}: (a: α) -> Lang (dLang.char a)
  -- | or : Lang P -> Lang Q -> Lang (dLang.or P Q)
  -- | and : Lang P -> Lang Q -> Lang (dLang.and P Q)
  -- | scalar {s: Type u}: (Dec s) -> Lang P -> Lang (dLang.scalar s P)
  -- | concat : Lang P -> Lang Q -> Lang (dLang.concat P Q)
  -- | star : Lang P -> Lang (dLang.star P)

-- TODO: 𝜈 : Lang P → Dec (⋄.𝜈 P)
-- theorem ν {α: Type u} {P: dLang α} (f: Lang P): Dec (dLang.ν P) := by
--   induction f with
--   | universal => exact unit?

-- TODO: rewrite ν using casesOn
-- def ν' {α: Type u} {P: dLang α} (f: Lang P): Dec (dLang.ν P) := by
--   refine (Lang.casesOn ?a ?b ?c ?d ?e)
--   match f with
--   | universal => unit?

-- def ν'' {α: Type u} {P: dLang α} (f: Lang P): Dec (dLang.ν P) := by
--   induction f with
--   | universal => exact unit?

-- #print ν''













  -- | lang_emptyset (str : List α):
  --   False ->
  --   Lang Regex.emptyset str
