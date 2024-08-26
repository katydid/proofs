-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Symbolic.lagda

import Katydid.Conal.Decidability
import Katydid.Conal.Function
import Katydid.Conal.Language
import Katydid.Conal.Calculus

namespace Symbolic

-- data Lang : ◇.Lang → Set (suc ℓ) where
inductive Lang: Language.Lang.{u} α -> Type (u + 1) where
  -- ∅ : Lang ◇.∅
  | emptyset : Lang Language.emptyset
  -- 𝒰 : Lang ◇.𝒰
  | universal : Lang Language.universal
  -- 𝟏 : Lang ◇.𝟏
  | emptystr : Lang Language.emptystr
  -- ` : (a : A) → Lang (◇.` a)
  | char {a: Type u}: (a: α) -> Lang (Language.char a)
  -- _∪_ : Lang P → Lang Q → Lang (P ◇.∪ Q)
  | or : Lang P -> Lang Q -> Lang (Language.or P Q)
  -- _∩_ : Lang P → Lang Q → Lang (P ◇.∩ Q)
  | and : Lang P -> Lang Q -> Lang (Language.and P Q)
  -- _·_ : Dec s → Lang P → Lang (s ◇.· P)
  | scalar {s: Type u}: (Decidability.Dec s) -> Lang P -> Lang (Language.scalar s P)
  -- _⋆_ : Lang  P → Lang Q → Lang (P ◇.⋆ Q)
  | concat : Lang P -> Lang Q -> Lang (Language.concat P Q)
  -- _☆  : Lang P → Lang (P ◇.☆)
  | star : Lang P -> Lang (Language.star P)
  -- TODO: complete definition of Lang by adding the last operator:
  -- _◂_  : (Q ⟷ P) → Lang P → Lang Q
  -- We tried this definition in Lean:
  -- | iso {P Q: Language.Lang α}: (Q ⟷ P) -> Lang P -> Lang Q
  -- But we got the following error:
  -- "(kernel) declaration has free variables 'Symbolic.Lang.iso'"
  -- The paper says: "The reason _◀_ must be part of the inductive representation is the same as the other constructors, namely so that the core lemmas (Figure 3) translate into an implementation in terms of that representation."

-- ν  : Lang P → Dec (◇.ν P)
def null (l: Lang R): Decidability.Dec (Calculus.null R) :=
  match l with
  -- ν ∅ = ⊥‽
  | Lang.emptyset => Decidability.empty?
  -- ν 𝒰 = ⊤‽
  | Lang.universal => Decidability.unit?
  -- ν 𝟏 = ν𝟏 ◃ ⊤‽
  | Lang.emptystr => Decidability.apply' Calculus.nullable_emptystr Decidability.unit?
  -- ν (p ∪ q) = ν p ⊎‽ ν q
  | Lang.or p q => Decidability.sum? (null p) (null q)
  -- ν (p ∩ q) = ν p ×‽ ν q
  | Lang.and p q => Decidability.prod? (null p) (null q)
  -- ν (s · p) = s ×‽ ν p
  | Lang.scalar s p => Decidability.prod? s (null p)
  -- ν (p ⋆ q) = ν⋆ ◃ (ν p ×‽ ν q)
  | Lang.concat p q => Decidability.apply' Calculus.nullable_concat (Decidability.prod? (null p) (null q))
  -- ν (p ☆) = ν☆ ◃ (ν p ✶‽)
  | Lang.star p => Decidability.apply' Calculus.nullable_star (Decidability.list? (null p))
  -- ν (` a) = ν` ◃ ⊥‽
  | Lang.char a => Decidability.apply' Calculus.nullable_char Decidability.empty?
  -- ν (f ◂ p) = f ◃ ν p
  -- | Lang.iso f p => Decidability.apply' f (null p)

end Symbolic
