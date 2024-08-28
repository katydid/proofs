-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Calculus.lagda

import Katydid.Conal.Tipe
import Katydid.Conal.Function
import Katydid.Conal.Language

namespace Calculus

open Language
open List
open Char
open String

-- ν : (A ✶ → B) → B
-- ν f = f []
def null {α: Type u} {β: Type v} (f: List α -> β): β :=
  f []

-- 𝒟 : (A ✶ → B) → A ✶ → (A ✶ → B)
-- 𝒟 f u = λ v → f (u ⊙ v)
def derives {α: Type u} {β: Type v} (f: List α -> β) (u: List α): (List α -> β) :=
  λ v => f (u ++ v)

-- δ : (A ✶ → B) → A → (A ✶ → B)
-- δ f a = 𝒟 f [ a ]
def derive {α: Type u} {β: Type v} (f: List α -> β) (a: α): (List α -> β) :=
  derives f [a]

attribute [simp] null derive derives

-- ν∅  : ν ∅ ≡ ⊥
-- ν∅ = refl
def null_emptyset {α: Type u}:
  @null α _ emptyset ≡ PEmpty :=
  trfl

-- ν𝒰  : ν 𝒰 ≡ ⊤
-- ν𝒰 = refl
def null_universal {α: Type u}:
  @null α _ universal ≡ PUnit :=
  trfl

-- ν𝟏  : ν 𝟏 ↔ ⊤
-- ν𝟏 = mk↔′
--   (λ { refl → tt })
--   (λ { tt → refl })
--   (λ { tt → refl })
--   (λ { refl → refl })
def null_emptystr {α: Type u}:
  @null α _ emptystr <=> PUnit := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
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

-- ν`  : ν (` c) ↔ ⊥
-- ν` = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
def null_char {α: Type u} {c: α}:
  null (char c) <=> PEmpty := by
  constructor <;> (intro x; cases x) <;> contradiction

-- ν∪  : ν (P ∪ Q) ≡ (ν P ⊎ ν Q)
-- ν∪ = refl
def null_or {α: Type u} {P Q: Lang α}:
  null (or P Q) ≡ (Sum (null P) (null Q)) :=
  trfl

-- ν∩  : ν (P ∩ Q) ≡ (ν P × ν Q)
-- ν∩ = refl
def null_and {α: Type u} {P Q: Lang α}:
  null (and P Q) ≡ (Prod (null P) (null Q)) :=
  trfl

-- ν·  : ν (s · P) ≡ (s × ν P)
-- ν· = refl
def null_scalar {α: Type u} {s: Type u} {P: Lang α}:
  null (scalar s P) ≡ (Prod s (null P)) :=
  trfl

-- ν⋆  : ν (P ⋆ Q) ↔ (ν P × ν Q)
-- ν⋆ = mk↔′
--   (λ { (([] , []) , refl , νP , νQ) → νP , νQ })
--   (λ { (νP , νQ) → ([] , []) , refl , νP , νQ })
--   (λ { (νP , νQ) → refl } )
--   (λ { (([] , []) , refl , νP , νQ) → refl})
def null_concat {α: Type u} {P Q: Lang α}:
  null (concat P Q) <=> (Prod (null P) (null Q)) := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    -- TODO
    sorry
  case invFun =>
    -- TODO
    sorry
  case leftInv =>
    -- TODO
    sorry
  case rightInv =>
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
def null_star {α: Type u} {P: Lang α}:
  null (star P) <=> List (null P) := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    -- TODO
    sorry
  case invFun =>
    -- TODO
    sorry
  case leftInv =>
    -- TODO
    sorry
  case rightInv =>
    -- TODO
    sorry

-- δ∅  : δ ∅ a ≡ ∅
-- δ∅ = refl
def derive_emptyset {α: Type u} {a: α}:
  (derive emptyset a) ≡ emptyset :=
  trfl

-- δ𝒰  : δ 𝒰 a ≡ 𝒰
-- δ𝒰 = refl
def derive_universal {α: Type u} {a: α}:
  (derive universal a) ≡ universal :=
  trfl

-- δ𝟏  : δ 𝟏 a ⟷ ∅
-- δ𝟏 = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
def derive_emptystr {α: Type u} {a: α} {w: List α}:
  (derive emptystr a) w <=> emptyset w := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    intro D
    cases D
    next D =>
    contradiction
  case invFun =>
    intro E
    contradiction
  case leftInv =>
    intro D
    simp at D
    cases D
    next D =>
    contradiction
  case rightInv =>
    intro E
    contradiction

-- δ`  : δ (` c) a ⟷ (a ≡ c) · 𝟏
-- δ` = mk↔′
--   (λ { refl → refl , refl })
--   (λ { (refl , refl) → refl })
--   (λ { (refl , refl) → refl })
--   (λ { refl → refl })
def derive_char {α: Type u} {a: α} {c: α} {w: List α}:
  (derive (char c) a) w <=> (scalar (a ≡ c) emptystr) w := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    -- TODO
    sorry
  case invFun =>
    -- TODO
    sorry
  case leftInv =>
    -- TODO
    sorry
  case rightInv =>
    -- TODO
    sorry

-- δ∪  : δ (P ∪ Q) a ≡ δ P a ∪ δ Q a
-- δ∪ = refl
def derive_or {α: Type u} {a: α} {P Q: Lang α}:
  (derive (or P Q) a) ≡ (or (derive P a) (derive Q a)) :=
  trfl

-- δ∩  : δ (P ∩ Q) a ≡ δ P a ∩ δ Q a
-- δ∩ = refl
def derive_and {α: Type u} {a: α} {P Q: Lang α}:
  (derive (and P Q) a) ≡ (and (derive P a) (derive Q a)) :=
  trfl

-- δ·  : δ (s · P) a ≡ s · δ P a
-- δ· = refl
def derive_scalar {α: Type u} {a: α} {s: Type u} {P: Lang α}:
  (derive (scalar s P) a) ≡ (scalar s (derive P a)) :=
  trfl

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
def derive_concat {α: Type u} {a: α} {P Q: Lang α} {w: List α}:
  (derive (concat P Q) a) w <=> (scalar (null P) (or (derive Q a) (concat (derive P a) Q))) w := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    -- TODO
    sorry
  case invFun =>
    -- TODO
    sorry
  case leftInv =>
    -- TODO
    sorry
  case rightInv =>
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
def derive_star {α: Type u} {a: α} {P: Lang α} {w: List α}:
  (derive (star P) a) w <=> (scalar (List (null P)) (concat (derive P a) (star P))) w := by
  refine TEquiv.mk ?toFun ?invFun ?leftInv ?rightInv
  case toFun =>
    -- TODO
    sorry
  case invFun =>
    -- TODO
    sorry
  case leftInv =>
    -- TODO
    sorry
  case rightInv =>
    -- TODO
    sorry

end Calculus
