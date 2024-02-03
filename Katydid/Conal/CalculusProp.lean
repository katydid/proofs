-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Calculus.lagda

import Katydid.Conal.LanguageNotationProp
open Lang

-- Print Parse
set_option pp.all true
open List
def a_or_b := ({'a'} ⋃ {'b'})
#print a_or_b
def a_or_b_parse_a := a_or_b ['a']
-- #eval a_or_b_parse_a

def p : a_or_b ['a'] -> Nat := by
  intro x
  cases x with
  | inl xa =>
    cases xa with
    | refl => exact 0
  | inr xb =>
    contradiction

-- ν⇃ : Lang → Set ℓ      -- “nullable”
-- ν⇃ P = P []
def ν (P : Lang α) : Type u := -- backslash nu
  P []

-- δ⇃ : Lang → A → Lang   -- “derivative”
-- δ⇃ P a w = P (a ∷ w)
def δ (P : Lang α) (a : α) : Lang α := -- backslash delta
  fun (w : List α) => P (a :: w)

attribute [simp] ν δ

-- ν∅  : ν ∅ ≡ ⊥
-- ν∅ = refl
theorem nullable_emptySet:
  ∀ (α: Type),
    @ν α ∅ ≡ PEmpty := by
  intro α
  constructor
  rfl

-- ν𝒰  : ν 𝒰 ≡ ⊤
-- ν𝒰 = refl
theorem nullable_universal:
  ∀ (α: Type),
    @ν α 𝒰 ≡ PUnit := by
  intro α
  constructor
  rfl

-- ν𝟏  : ν 𝟏 ↔ ⊤
-- ν𝟏 = mk↔′
--   (λ { refl → tt })
--   (λ { tt → refl })
--   (λ { tt → refl })
--   (λ { refl → refl })
theorem nullable_emptyStr:
  ∀ (α: Type),
    @ν α ε ↔ PUnit := by
  intro α
  refine Tiso.intro ?a ?b ?c ?d
  intro
  exact PUnit.unit
  intro
  exact trifle
  intro
  exact trifle
  simp
  intro x
  cases x with
  | _ => exact trifle

theorem nullable_emptyStr':
  ∀ (α: Type),
    @ν α ε ↔ PUnit :=
    fun _ => Tiso.intro
      (fun _ => PUnit.unit)
      (fun _ => trifle)
      (sorry)
      (sorry)

-- ν`  : ν (` c) ↔ ⊥
-- ν` = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
theorem nullable_char:
  ∀ (c: α),
    ν (char c) ↔ PEmpty := by
  intro α
  simp
  apply Tiso.intro
  intro
  contradiction
  intro
  contradiction
  sorry
  sorry

theorem nullable_char':
  ∀ (c: α),
    ν (char c) -> PEmpty := by
  intro
  refine (fun x => ?c)
  simp at x
  contradiction

-- set_option pp.all true
-- #print nullable_char'

theorem t : 1 ≡ 2 -> False := by
  intro
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

theorem nullable_char'''.{u_2, u_1} : {α : Type u_1} → (c : α) → ν.{u_1} (Lang.char.{u_1} c) → PEmpty.{u_2} :=
fun {α : Type u_1} (c : α) (x : ν.{u_1} (Lang.char.{u_1} c)) =>
  False.elim.{u_2}
    (False.elim.{0}
      (TEq.casesOn.{0, u_1} (motive := fun (a : List.{u_1} α) (x_1 : TEq.{u_1} List.nil.{u_1} a) =>
        Eq.{u_1 + 1} (List.cons.{u_1} c List.nil.{u_1}) a → HEq.{u_1 + 1} x x_1 → False) x
        (fun (h : Eq.{u_1 + 1} (List.cons.{u_1} c List.nil.{u_1}) List.nil.{u_1}) => List.noConfusion.{0, u_1} h)
        (Eq.refl.{u_1 + 1} (List.cons.{u_1} c List.nil.{u_1})) (HEq.refl.{u_1 + 1} x)))

-- ν∪  : ν (P ∪ Q) ≡ (ν P ⊎ ν Q)
-- ν∪ = refl
theorem nullable_or:
  ∀ (P Q: Lang α),
    ν (P ⋃ Q) ≡ (Sum (ν P) (ν Q)) := by
  intro P Q
  rfl

-- ν∩  : ν (P ∩ Q) ≡ (ν P × ν Q)
-- ν∩ = refl
theorem nullable_and:
  ∀ (P Q: Lang α),
    ν (P ⋂ Q) ≡ (Prod (ν P) (ν Q)) := by
  intro P Q
  rfl

-- ν·  : ν (s · P) ≡ (s × ν P)
-- ν· = refl
theorem nullable_scalar:
  ∀ (s: Type) (P: Lang α),
    ν (Lang.scalar s P) ≡ (Prod s (ν P)) := by
  intro P Q
  rfl

-- ν⋆  : ν (P ⋆ Q) ↔ (ν P × ν Q)
-- ν⋆ = mk↔′
--   (λ { (([] , []) , refl , νP , νQ) → νP , νQ })
--   (λ { (νP , νQ) → ([] , []) , refl , νP , νQ })
--   (λ { (νP , νQ) → refl } )
--   (λ { (([] , []) , refl , νP , νQ) → refl})
theorem nullable_concat:
  ∀ (P Q: Lang α),
    ν (P, Q) ↔ (Prod (ν Q) (ν P)) := by
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
theorem nullable_star:
  ∀ (P: Lang α),
    ν (P *) ↔ List (ν P) := by
  -- TODO
  sorry

-- δ∅  : δ ∅ a ≡ ∅
-- δ∅ = refl
theorem derivative_emptySet:
  ∀ (a: α),
    (δ ∅ a) ≡ ∅ := by
  intro a
  rfl

-- δ𝒰  : δ 𝒰 a ≡ 𝒰
-- δ𝒰 = refl
theorem derivative_universal:
  ∀ (a: α),
    (δ 𝒰 a) ≡ 𝒰 := by
  intro a
  rfl

-- δ𝟏  : δ 𝟏 a ⟷ ∅
-- δ𝟏 = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
-- TODO: Redo this definition to do extensional isomorphism: `⟷` properly
theorem derivative_emptyStr:
  ∀ (a: α),
    (δ ε a) ≡ ∅ := by
  -- TODO
  sorry

-- δ`  : δ (` c) a ⟷ (a ≡ c) · 𝟏
-- δ` = mk↔′
--   (λ { refl → refl , refl })
--   (λ { (refl , refl) → refl })
--   (λ { (refl , refl) → refl })
--   (λ { refl → refl })
-- TODO: Redo this definition to do extensional isomorphism: `⟷` properly
theorem derivative_char:
  ∀ (a: α) (c: α),
    (δ (char c) a) ≡ Lang.scalar (a ≡ c) ε := by
    intros a c
    unfold δ
    unfold char
    unfold emptyStr
    unfold scalar
    sorry

-- δ∪  : δ (P ∪ Q) a ≡ δ P a ∪ δ Q a
-- δ∪ = refl
theorem derivative_or:
  ∀ (a: α) (P Q: Lang α),
    (δ (P ⋃ Q) a) ≡ ((δ P a) ⋃ (δ Q a)) := by
  intro a P Q
  rfl

-- δ∩  : δ (P ∩ Q) a ≡ δ P a ∩ δ Q a
-- δ∩ = refl
theorem derivative_and:
  ∀ (a: α) (P Q: Lang α),
    (δ (P ⋂ Q) a) ≡ ((δ P a) ⋂ (δ Q a)) := by
  intro a P Q
  rfl

-- δ·  : δ (s · P) a ≡ s · δ P a
-- δ· = refl
theorem derivative_scalar:
  ∀ (a: α) (s: Type) (P: Lang α),
    (δ (Lang.scalar s P) a) ≡ (Lang.scalar s (δ P a)) := by
  intro a s P
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
theorem derivative_concat:
  ∀ (a: α) (P Q: Lang α),
  -- TODO: Redo this definition to do extensional isomorphism: `⟷` properly
    (δ (P , Q) a) ≡ Lang.scalar (ν P) ((δ Q a) ⋃ ((δ P a), Q)) := by
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
theorem derivative_star:
  ∀ (a: α) (P: Lang α),
  -- TODO: Redo this definition to do extensional isomorphism: `⟷` properly
    (δ (P *) a) ≡ Lang.scalar (List (ν P)) (δ P a, P *) := by
  -- TODO
  sorry
