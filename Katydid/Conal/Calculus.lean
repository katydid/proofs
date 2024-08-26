-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Calculus.lagda

import Katydid.Conal.Function
import Katydid.Conal.Language
import Mathlib.Logic.Equiv.Defs -- ≃
import Katydid.Std.Tipe

namespace Calculus

open dLang
open List
open Char
open String

-- Print Parse
-- set_option pp.all true
open List

def example_of_proof_relevant_parse : (char 'a' ⋃ char 'b') (toList "a") -> Nat := by
  intro x
  cases x with
  | inl xa =>
    cases xa with
    | mk eq =>
      cases eq with
      | refl =>
        exact 0
  | inr xb =>
    cases xb with
    | mk eq =>
      contradiction

def example_of_proof_relevant_parse2 : (concat (char 'a') (char 'b' ⋃ char 'c')) (toList "ab") -> Nat := by
  intro x1
  simp at x1
  cases x1 with
  | mk x1 x2 =>
    cases x2 with
    | mk x2 x3 =>
      cases x3 with
      | mk x3 x4 =>
        cases x3 with
        | mk x3 =>
          cases x4 with
          | mk x4 x5 =>
            cases x4 with
            | inl x4 =>
                cases x4 with
                | mk x4 =>
                  subst_vars
                  exact 0
            | inr x4 =>
              cases x4 with
              | mk x4 =>
                subst_vars
                contradiction

-- ν⇃ : Lang → Set ℓ      -- “nullable”
-- ν⇃ P = P []
def null' (P : dLang α) : Type u := -- backslash nu
  P []

-- δ⇃ : Lang → A → Lang   -- “derivative”
-- δ⇃ P a w = P (a ∷ w)
def derive' (P : dLang α) (a : α) : dLang α := -- backslash delta
  fun (w : List α) => P (a :: w)

-- ν : (A ✶ → B) → B                -- “nullable”
-- ν f = f []
def null (f: List α -> β): β :=
  f []

-- 𝒟 : (A ✶ → B) → A ✶ → (A ✶ → B)  -- “derivative”
-- 𝒟 f u = λ v → f (u ⊙ v)
def derives (f: List α -> β) (u: List α): (List α -> β) :=
  λ v => f (u ++ v)

-- δ : (A ✶ → B) → A → (A ✶ → B)
-- δ f a = 𝒟 f [ a ]
def derive (f: List α -> β) (a: α): (List α -> β) :=
  derives f [a]

attribute [simp] null' derive'

-- ν∅  : ν ∅ ≡ ⊥
-- ν∅ = refl
def nullable_emptySet:
  ∀ (α: Type),
    @null' α ∅ ≡ PEmpty := by
  intro α
  constructor
  rfl

-- ν𝒰  : ν 𝒰 ≡ ⊤
-- ν𝒰 = refl
def nullable_universal:
  ∀ (α: Type),
    @null' α 𝒰 ≡ PUnit := by
  intro α
  constructor
  rfl

-- ν𝟏  : ν 𝟏 ↔ ⊤
-- ν𝟏 = mk↔′
--   (λ { refl → tt })
--   (λ { tt → refl })
--   (λ { tt → refl })
--   (λ { refl → refl })
def nullable_emptystr:
  ∀ (α: Type),
    @null' α ε ≃ PUnit := by
  intro α
  refine Equiv.mk ?a ?b ?c ?d
  intro _
  exact PUnit.unit
  intro _
  constructor
  rfl
  intro c
  simp
  constructor
  intro _
  simp

def nullable_emptyStr':
  ∀ (α: Type),
    @null' α ε ≃ PUnit :=
    fun _ => Equiv.mk
      (fun _ => PUnit.unit)
      (fun _ => by constructor; rfl)
      (sorry)
      (sorry)

-- ν`  : ν (` c) ↔ ⊥
-- ν` = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
def nullable_char:
  ∀ (c: α),
    null' (char c) ≃ PEmpty := by
  intro α
  simp
  apply Equiv.mk
  intro x
  cases x with
  | mk x =>
    contradiction
  intro
  contradiction
  sorry
  sorry

def nullable_char':
  ∀ (c: α),
    null' (char c) -> PEmpty := by
  intro
  refine (fun x => ?c)
  simp at x
  cases x with
  | mk x =>
    contradiction

-- set_option pp.all true
-- #print nullable_char'

-- ν∪  : ν (P ∪ Q) ≡ (ν P ⊎ ν Q)
-- ν∪ = refl
def nullable_or:
  ∀ (P Q: dLang α),
    null' (P ⋃ Q) ≡ (Sum (null' P) (null' Q)) := by
  intro P Q
  constructor
  rfl

-- ν∩  : ν (P ∩ Q) ≡ (ν P × ν Q)
-- ν∩ = refl
def nullable_and:
  ∀ (P Q: dLang α),
    null' (P ⋂ Q) ≡ (Prod (null' P) (null' Q)) := by
  intro P Q
  constructor
  rfl

-- ν·  : ν (s · P) ≡ (s × ν P)
-- ν· = refl
def nullable_scalar:
  ∀ (s: Type) (P: dLang α),
    null' (dLang.scalar s P) ≡ (Prod s (null' P)) := by
  intro P Q
  constructor
  rfl

-- ν⋆  : ν (P ⋆ Q) ↔ (ν P × ν Q)
-- ν⋆ = mk↔′
--   (λ { (([] , []) , refl , νP , νQ) → νP , νQ })
--   (λ { (νP , νQ) → ([] , []) , refl , νP , νQ })
--   (λ { (νP , νQ) → refl } )
--   (λ { (([] , []) , refl , νP , νQ) → refl})
def nullable_concat:
  ∀ (P Q: dLang α),
    null' (concat P Q) ≃ (Prod (null' Q) (null' P)) := by
  -- TODO
  sorry

-- ν✪  : ν (P ✪) ↔ (ν P) ✶
-- ν✪ {P = P} = mk↔′ k k⁻¹ invˡ invʳ
--  where
--    k : ν (P ✪) → (ν P) ✶
--    k zero✪ = []
--    k (suc✪ (([] , []) , refl , (νP , νP✪))) = νP ∷ k νP✪

--    k⁻¹ : (ν P) ✶ → ν (P ✪)
--    k⁻¹ [] = zero✪
--    k⁻¹ (νP ∷ νP✶) = suc✪ (([] , []) , refl , (νP , k⁻¹ νP✶))

--    invˡ : ∀ (νP✶ : (ν P) ✶) → k (k⁻¹ νP✶) ≡ νP✶
--    invˡ [] = refl
--    invˡ (νP ∷ νP✶) rewrite invˡ νP✶ = refl

--    invʳ : ∀ (νP✪ : ν (P ✪)) → k⁻¹ (k νP✪) ≡ νP✪
--    invʳ zero✪ = refl
--    invʳ (suc✪ (([] , []) , refl , (νP , νP✪))) rewrite invʳ νP✪ = refl

-- ν☆  : ν (P ☆) ↔ (ν P) ✶
-- ν☆ {P = P} =
--   begin
--     ν (P ☆)
--   ≈˘⟨ ✪↔☆ ⟩
--     ν (P ✪)
--   ≈⟨ ν✪ ⟩
--     (ν P) ✶
--   ∎ where open ↔R
def nullable_star:
  ∀ (P: dLang α),
    null' (P *) ≃ List (null' P) := by
  -- TODO
  sorry

-- δ∅  : δ ∅ a ≡ ∅
-- δ∅ = refl
def derivative_emptySet:
  ∀ (a: α),
    (derive' ∅ a) ≡ ∅ := by
  intro a
  constructor
  rfl

-- δ𝒰  : δ 𝒰 a ≡ 𝒰
-- δ𝒰 = refl
def derivative_universal:
  ∀ (a: α),
    (derive' 𝒰 a) ≡ 𝒰 := by
  intro a
  constructor
  rfl

-- δ𝟏  : δ 𝟏 a ⟷ ∅
-- δ𝟏 = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
def derivative_emptyStr: ∀ (w: List α), (derive' ε a) w <=> ∅ w := by
  intro w
  constructor
  · intro D
    simp at D
    cases D
    next D =>
    contradiction
  · intro E
    contradiction

-- δ`  : δ (` c) a ⟷ (a ≡ c) · 𝟏
-- δ` = mk↔′
--   (λ { refl → refl , refl })
--   (λ { (refl , refl) → refl })
--   (λ { (refl , refl) → refl })
--   (λ { refl → refl })
-- TODO: Redo this definition to do extensional isomorphism: `⟷` properly
def derivative_char:
  ∀ (a: α) (c: α),
    (derive' (char c) a) ≡ dLang.scalar (a ≡ c) ε := by
    intros a c
    unfold derive'
    unfold char
    unfold emptystr
    unfold scalar
    sorry

-- δ∪  : δ (P ∪ Q) a ≡ δ P a ∪ δ Q a
-- δ∪ = refl
def derivative_or:
  ∀ (a: α) (P Q: dLang α),
    (derive' (P ⋃ Q) a) ≡ ((derive' P a) ⋃ (derive' Q a)) := by
  intro a P Q
  constructor
  rfl

-- δ∩  : δ (P ∩ Q) a ≡ δ P a ∩ δ Q a
-- δ∩ = refl
def derivative_and:
  ∀ (a: α) (P Q: dLang α),
    (derive' (P ⋂ Q) a) ≡ ((derive' P a) ⋂ (derive' Q a)) := by
  intro a P Q
  constructor
  rfl

-- δ·  : δ (s · P) a ≡ s · δ P a
-- δ· = refl
def derivative_scalar:
  ∀ (a: α) (s: Type) (P: dLang α),
    (δ (dLang.scalar s P) a) ≡ (dLang.scalar s (derive' P a)) := by
  intro a s P
  constructor
  rfl

-- δ⋆  : δ (P ⋆ Q) a ⟷ ν P · δ Q a ∪ δ P a ⋆ Q
-- δ⋆ {a = a} {w = w} = mk↔′
--   (λ { (([] , .(a ∷ w)) , refl , νP , Qaw) → inj₁ (νP , Qaw)
--      ; ((.a ∷ u , v) , refl , Pu , Qv) → inj₂ ((u , v) , refl , Pu , Qv) })
--   (λ { (inj₁ (νP , Qaw)) → ([] , a ∷ w) , refl , νP , Qaw
--      ; (inj₂ ((u , v) , refl , Pu , Qv)) → ((a ∷ u , v) , refl , Pu , Qv) })
--   (λ { (inj₁ (νP , Qaw)) → refl
--      ; (inj₂ ((u , v) , refl , Pu , Qv)) → refl })
--   (λ { (([] , .(a ∷ w)) , refl , νP , Qaw) → refl
--      ; ((.a ∷ u , v) , refl , Pu , Qv) → refl })
-- TODO: Redo this definition to do extensional isomorphism: `⟷` properly
def derivative_concat:
  ∀ (a: α) (P Q: dLang α),
  -- TODO: Redo this definition to do extensional isomorphism: `⟷` properly
    (derive' (concat P Q) a) ≡ dLang.scalar (null' P) ((derive' Q a) ⋃ (concat (derive' P a) Q)) := by
  -- TODO
  sorry

-- δ✪  : δ (P ✪) a ⟷ (ν P) ✶ · (δ P a ⋆ P ✪)
-- δ✪ {P}{a} {w} = mk↔′ k k⁻¹ invˡ invʳ
--  where
--    k : δ (P ✪) a w → ((ν P) ✶ · (δ P a ⋆ P ✪)) w
--    k (suc✪ (([] , .(a ∷ w)) , refl , (νP , P✪a∷w))) with k P✪a∷w
--    ... |            νP✶  , etc
--        = νP ∷ νP✶ , etc
--    k (suc✪ ((.a ∷ u , v) , refl , (Pa∷u , P✪v))) = [] , (u , v) , refl , (Pa∷u , P✪v)

--    k⁻¹ : ((ν P) ✶ · (δ P a ⋆ P ✪)) w → δ (P ✪) a w
--    k⁻¹ ([] , (u , v) , refl , (Pa∷u , P✪v)) = (suc✪ ((a ∷ u , v) , refl , (Pa∷u , P✪v)))
--    k⁻¹ (νP ∷ νP✶ , etc) = (suc✪ (([] , a ∷ w) , refl , (νP , k⁻¹ (νP✶ , etc))))

--    invˡ : (s : ((ν P) ✶ · (δ P a ⋆ P ✪)) w) → k (k⁻¹ s) ≡ s
--    invˡ ([] , (u , v) , refl , (Pa∷u , P✪v)) = refl
--    invˡ (νP ∷ νP✶ , etc) rewrite invˡ (νP✶ , etc) = refl

--    invʳ : (s : δ (P ✪) a w) → k⁻¹ (k s) ≡ s
--    invʳ (suc✪ (([] , .(a ∷ w)) , refl , (νP , P✪a∷w))) rewrite invʳ P✪a∷w = refl
--    invʳ (suc✪ ((.a ∷ u , v) , refl , (Pa∷u , P✪v))) = refl

-- δ☆  : δ (P ☆) a ⟷ (ν P) ✶ · (δ P a ⋆ P ☆)
-- δ☆ {P = P}{a} {w} =
--   begin
--     δ (P ☆) a w
--   ≈˘⟨ ✪↔☆ ⟩
--     δ (P ✪) a w
--   ≈⟨ δ✪ ⟩
--     ((ν P) ✶ · (δ P a ⋆ P ✪)) w
--   ≈⟨ ×-congˡ (⋆-congˡ ✪↔☆) ⟩
--     ((ν P) ✶ · (δ P a ⋆ P ☆)) w
--   ∎ where open ↔R
-- TODO: Redo this definition to do extensional isomorphism: `⟷` properly
def derivative_star:
  ∀ (a: α) (P: dLang α),
  -- TODO: Redo this definition to do extensional isomorphism: `⟷` properly
    (derive' (P *) a) ≡ dLang.scalar (List (null' P)) (concat (derive' P a) (P *)) := by
  -- TODO
  sorry

end Calculus
