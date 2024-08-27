import Katydid.Conal.Decidability
import Katydid.Conal.Function
import Katydid.Conal.Language
import Katydid.Conal.Calculus

namespace Automatic

-- record Lang (P : ◇.Lang) : Set (suc ℓ) where
--   coinductive
--   field
--     ν : Dec (◇.ν P)
--     δ : (a : A) → Lang (◇.δ P a)

unsafe
-- we need "unsafe" otherwise we get the following error:
-- "(kernel) arg #4 of 'Automatic.Lang.mk' contains a non valid occurrence of the datatypes being declared"
inductive Lang {α: Type u} (R: Language.Lang α): Type (u) where
  | mk
   (null: Decidability.Dec (Calculus.null R))
   (derive: (a: α) -> Lang (Calculus.derive R a))
   : Lang R

unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def null (l: Lang R): Decidability.Dec (Calculus.null R) :=
  match l with
  | Lang.mk n _ => n

unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def derive {α: Type u} {R: Language.Lang α} (l: Lang R) (a: α): Lang (Calculus.derive R a) :=
  match l with
  | Lang.mk _ d => d a

-- ∅ : Lang ◇.∅
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def emptyset {α: Type u}: Lang (@Language.emptyset.{u} α) := Lang.mk
  -- ν ∅ = ⊥‽
  (null := Decidability.empty?)
  -- δ ∅ a = ∅
  (derive := fun _ => emptyset)

-- 𝒰    : Lang  ◇.𝒰
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def universal {α: Type u}: Lang (@Language.universal.{u} α) := Lang.mk
  -- ν 𝒰 = ⊤‽
  (null := Decidability.unit?)
  -- δ 𝒰 a = 𝒰
  (derive := fun _ => universal)

-- _∪_  : Lang  P  → Lang Q  → Lang (P  ◇.∪  Q)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def or {α: Type u} {P Q: Language.Lang α} (p: Lang P) (q: Lang Q): Lang (Language.or P Q) := Lang.mk
  -- ν (p ∪ q) = ν p ⊎‽ ν q
  (null := Decidability.sum? (null p) (null q))
  -- δ (p ∪ q) a = δ p a ∪ δ q a
  (derive := fun (a: α) => or (derive p a) (derive q a))

-- _∩_  : Lang  P  → Lang Q  → Lang (P  ◇.∩  Q)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def and {α: Type u} {P Q: Language.Lang α} (p: Lang P) (q: Lang Q): Lang (Language.and P Q) := Lang.mk
  -- ν (p ∩ q) = ν p ×‽ ν q
  (null := Decidability.prod? (null p) (null q))
  -- δ (p ∩ q) a = δ p a ∩ δ q a
  (derive := fun (a: α) => and (derive p a) (derive q a))

-- _·_  : Dec   s  → Lang P  → Lang (s  ◇.·  P)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def scalar {α: Type u} {P: Language.Lang α} (s: Decidability.Dec S) (p: Lang P): Lang (Language.scalar S P) := Lang.mk
  -- ν (s · p) = s ×‽ ν p
  (null := Decidability.prod? s (null p))
  -- δ (s · p) a = s · δ p a
  (derive := fun (a: α) => scalar s (derive p a))

-- _◂_  : (Q ⟷ P) → Lang P → Lang Q
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def iso {α: Type u} {P Q: Language.Lang α} (f: ∀ {w: List α}, Q w <=> P w) (p: Lang P): Lang Q := Lang.mk
  -- ν (f ◂ p) = f ◃ ν p
  (null := Decidability.apply' f (null p))
  -- δ (f ◂ p) a = f ◂ δ p a
  (derive := fun (a: α) => iso f (derive p a))

-- 𝟏    : Lang ◇.𝟏
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def emptystr {α: Type u}: Lang (@Language.emptystr α) := Lang.mk
  -- ν 𝟏 = ν𝟏 ◃ ⊤‽
  (null := Decidability.apply' Calculus.null_emptystr Decidability.unit?)
  -- δ 𝟏 a = δ𝟏 ◂ ∅
  (derive := fun _ => iso Calculus.derive_emptystr emptyset)

-- _⋆_  : Lang  P  → Lang Q  → Lang (P  ◇.⋆  Q)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def concat {α: Type u} {P Q: Language.Lang α} (p: Lang P) (q: Lang Q): Lang (Language.concat P Q) := Lang.mk
  -- ν (p ⋆ q) = ν⋆ ◃ (ν p ×‽ ν q)
  (null := Decidability.apply' Calculus.null_concat (Decidability.prod? (null p) (null q)))
  -- δ (p ⋆ q) a = δ⋆ ◂ (ν p · δ q a ∪ δ p a ⋆ q)
  (derive := fun (a: α) =>
    (iso Calculus.derive_concat
      (scalar (null p)
        (or
          (derive q a)
          (concat (derive p a) q)
        )
      )
    )
  )

-- _☆   : Lang  P → Lang (P ◇.☆)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def star {α: Type u} {P: Language.Lang α} (p: Lang P): Lang (Language.star P) := Lang.mk
  -- ν (p ☆) = ν☆ ◃ (ν p ✶‽)
  (null := Decidability.apply' Calculus.null_star (Decidability.list? (null p)))
  -- δ (p ☆) a = δ☆ ◂ (ν p ✶‽ · (δ p a ⋆ p ☆))
  (derive := fun (a: α) =>
    (iso Calculus.derive_star
      (scalar
        (Decidability.list? (null p))
        (concat (derive p a) (star p))
      )
    )
  )

-- `    : (a : A) → Lang (◇.` a)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def char {α: Type u} [Decidability.DecEq α] (c: α): Lang (Language.char c) := Lang.mk
  -- ν (` a) = ν` ◃ ⊥‽
  (null := Decidability.apply' Calculus.null_char Decidability.empty?)
  -- δ (` c) a = δ` ◂ ((a ≟ c) · 𝟏)
  (derive := fun (a: α) =>
     let cmp: Decidability.Dec (a ≡ c) := Decidability.decEq a c
    (iso Calculus.derive_char
      (scalar cmp emptystr)
    )
  )

end Automatic
