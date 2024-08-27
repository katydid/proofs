-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Calculus.lagda

import Katydid.Std.Tipe
import Katydid.Conal.Function
import Katydid.Conal.Language

namespace Calculus

open Language
open List
open Char
open String

-- Print Parse
-- set_option pp.all true
open List

def example_of_proof_relevant_parse : (or (char 'a') (char 'b')) (toList "a") -> Nat := by
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

def example_of_proof_relevant_parse2 : (concat (char 'a') (or (char 'b') (char 'c'))) (toList "ab") -> Nat := by
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
def null' (P : Lang α) : Type u := -- backslash nu
  P []

-- δ⇃ : Lang → A → Lang   -- “derivative”
-- δ⇃ P a w = P (a ∷ w)
def derive' (P : Lang α) (a : α) : Lang α := -- backslash delta
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
def derive (f: Lang α) (a: α): (Lang α) :=
  derives f [a]

attribute [simp] null' derive'

-- ν∅  : ν ∅ ≡ ⊥
-- ν∅ = refl
def null_emptyset:
  ∀ {α: Type},
    @null α _ emptyset ≡ PEmpty := by
  intro α
  constructor
  rfl

-- ν𝒰  : ν 𝒰 ≡ ⊤
-- ν𝒰 = refl
def null_universal:
  ∀ {α: Type},
    @null α _ universal ≡ PUnit := by
  intro α
  constructor
  rfl

-- ν𝟏  : ν 𝟏 ↔ ⊤
-- ν𝟏 = mk↔′
--   (λ { refl → tt })
--   (λ { tt → refl })
--   (λ { tt → refl })
--   (λ { refl → refl })
def null_emptystr:
  ∀ {α: Type},
    @null α _ emptystr <=> PUnit := by
  intro α
  refine TEquiv.mk ?a ?b ?c ?d
  · intro _
    exact PUnit.unit
  · intro _
    constructor
    rfl
  · intro c
    simp
    constructor
    constructor
  · intro _
    constructor
    simp

-- An alternative "proof" of null_emptystr not using tactics
def null_emptystr':
  ∀ {α: Type},
    @null α _ emptystr <=> PUnit :=
    TEquiv.mk
      (fun _ => PUnit.unit)
      (fun _ => by constructor; rfl)
      (sorry)
      (sorry)

-- ν`  : ν (` c) ↔ ⊥
-- ν` = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
def null_char:
  ∀ {c: α},
    null (char c) <=> PEmpty := by
  intro c
  apply TEquiv.mk
  intro x
  cases x with
  | mk x =>
    contradiction
  intro
  contradiction
  sorry
  sorry

-- ν∪  : ν (P ∪ Q) ≡ (ν P ⊎ ν Q)
-- ν∪ = refl
def null_or:
  ∀ {P Q: Lang α},
    null (or P Q) ≡ (Sum (null P) (null Q)) := by
  intro P Q
  constructor
  rfl

-- ν∩  : ν (P ∩ Q) ≡ (ν P × ν Q)
-- ν∩ = refl
def null_and:
  ∀ {P Q: Lang α},
    null (and P Q) ≡ (Prod (null P) (null Q)) := by
  intro P Q
  constructor
  rfl

-- ν·  : ν (s · P) ≡ (s × ν P)
-- ν· = refl
def null_scalar:
  ∀ {s: Type} {P: Lang α},
    null (scalar s P) ≡ (Prod s (null P)) := by
  intro P Q
  constructor
  rfl

-- ν⋆  : ν (P ⋆ Q) ↔ (ν P × ν Q)
-- ν⋆ = mk↔′
--   (λ { (([] , []) , refl , νP , νQ) → νP , νQ })
--   (λ { (νP , νQ) → ([] , []) , refl , νP , νQ })
--   (λ { (νP , νQ) → refl } )
--   (λ { (([] , []) , refl , νP , νQ) → refl})
def null_concat:
  ∀ {P Q: Lang α},
    null (concat P Q) <=> (Prod (null P) (null Q)) := by
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
def null_star:
  ∀ {P: Lang α},
    null (star P) <=> List (null P) := by
  -- TODO
  sorry

-- δ∅  : δ ∅ a ≡ ∅
-- δ∅ = refl
def derive_emptyset:
  ∀ {a: α},
    (derive emptyset a) ≡ emptyset := by
  intro a
  constructor
  rfl

-- δ𝒰  : δ 𝒰 a ≡ 𝒰
-- δ𝒰 = refl
def derive_universal:
  ∀ {a: α},
    (derive universal a) ≡ universal := by
  intro a
  constructor
  rfl

-- δ𝟏  : δ 𝟏 a ⟷ ∅
-- δ𝟏 = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
def derive_emptystr:
  ∀ {w: List α},
    (derive emptystr a) w <=> emptyset w := by
  intro w
  constructor
  · intro D
    cases D
    next D =>
    contradiction
  · intro E
    contradiction
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
def derive_char:
  ∀ {w: List α} {a: α} {c: α},
    (derive (char c) a) w <=> (scalar (a ≡ c) emptystr) w := by
    intros a c
    unfold derive
    unfold char
    unfold emptystr
    unfold scalar
    sorry

-- δ∪  : δ (P ∪ Q) a ≡ δ P a ∪ δ Q a
-- δ∪ = refl
def derive_or:
  ∀ {a: α} {P Q: Lang α},
    (derive (or P Q) a) ≡ (or (derive P a) (derive Q a)) := by
  intro a P Q
  constructor
  rfl

-- δ∩  : δ (P ∩ Q) a ≡ δ P a ∩ δ Q a
-- δ∩ = refl
def derive_and:
  ∀ {a: α} {P Q: Lang α},
    (derive (and P Q) a) ≡ (and (derive P a) (derive Q a)) := by
  intro a P Q
  constructor
  rfl

-- δ·  : δ (s · P) a ≡ s · δ P a
-- δ· = refl
def derive_scalar:
  ∀ {a: α} {s: Type} {P: Lang α},
    (derive (scalar s P) a) ≡ (scalar s (derive P a)) := by
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
def derive_concat:
  ∀ {w: List α} {a: α} {P Q: Lang α},
    (derive (concat P Q) a) w <=> (scalar (null P) (or (derive Q a) (concat (derive P a) Q))) w := by
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
def derive_star:
  ∀ {w: List α} {a: α} {P: Lang α},
    (derive (star P) a) w <=> (scalar (List (null P)) (concat (derive P a) (star P))) w := by
  -- TODO
  sorry

end Calculus
