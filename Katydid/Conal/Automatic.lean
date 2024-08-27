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

-- we need "unsafe" otherwise we get the following error: (kernel) arg #4 of 'Automatic.Lang.mk' contains a non valid occurrence of the datatypes being declaredLean 4
unsafe
inductive Lang {α: Type u} (R: List α -> Type u): Type u where
  | mk
   (null: Decidability.Dec (Language.null R))
   (derive: (a: α) -> Lang (Language.derive R a))
   : Lang R

-- ∅ : Lang ◇.∅
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def emptyset {α: Type u}: Lang (@Language.emptyset.{u} α) := Lang.mk
  -- ν ∅ = ⊥‽
  (null := Decidability.empty?)
  -- δ ∅ a = ∅
  (derive := fun _ => emptyset)

-- 𝒰    : Lang  ◇.𝒰
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def universal {a: Type u}: Lang (@Language.universal.{u} α) := Lang.mk
  -- ν 𝒰 = ⊤‽
  (null := by sorry)
  -- δ 𝒰 a = 𝒰
  (derive := by sorry)

-- _∪_  : Lang  P  → Lang Q  → Lang (P  ◇.∪  Q)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def or {a: Type u} (p: @Lang α P) (q: @Lang α Q): Lang (@Language.or.{u} α P Q) := Lang.mk
  -- ν (p ∪ q) = ν p ⊎‽ ν q
  (null := sorry)
  -- δ (p ∪ q) a = δ p a ∪ δ q a
  (derive := sorry)

-- _∩_  : Lang  P  → Lang Q  → Lang (P  ◇.∩  Q)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def and {a: Type u} (p: @Lang α P) (q: @Lang α Q): Lang (@Language.and.{u} α P Q) := Lang.mk
  -- ν (p ∩ q) = ν p ×‽ ν q
  (null := sorry)
  -- δ (p ∩ q) a = δ p a ∩ δ q a
  (derive := sorry)

-- _·_  : Dec   s  → Lang P  → Lang (s  ◇.·  P)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def scalar {a: Type u} (_: Decidability.Dec s) (p: @Lang α P): Lang (@Language.scalar.{u} α s Q) := Lang.mk
  -- ν (s · p) = s ×‽ ν p
  (null := sorry)
  -- δ (s · p) a = s · δ p a
  (derive := sorry)

-- 𝟏    : Lang ◇.𝟏
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def emptystr {α: Type u}: Lang (@Language.emptystr.{u} α) := Lang.mk
  -- ν 𝟏 = ν𝟏 ◃ ⊤‽
  (null := sorry)
  -- δ 𝟏 a = δ𝟏 ◂ ∅
  (derive := sorry)

-- _⋆_  : Lang  P  → Lang Q  → Lang (P  ◇.⋆  Q)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def concat {a: Type u} (p: @Lang α P) (q: @Lang α Q): Lang (@Language.concat.{u} α P Q) := Lang.mk
  -- ν (p ⋆ q) = ν⋆ ◃ (ν p ×‽ ν q)
  (null := sorry)
  -- δ (p ⋆ q) a = δ⋆ ◂ (ν p · δ q a ∪ δ p a ⋆ q)
  (derive := sorry)

-- _☆   : Lang  P → Lang (P ◇.☆)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def star {a: Type u} (p: @Lang α P): Lang (@Language.star.{u} α P) := Lang.mk
  -- ν (p ☆) = ν☆ ◃ (ν p ✶‽)
  (null := sorry)
  -- δ (p ☆) a = δ☆ ◂ (ν p ✶‽ · (δ p a ⋆ p ☆))
  (derive := sorry)

-- `    : (a : A) → Lang (◇.` a)
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def char {a: Type u} (a: α): Lang (Language.char a) := Lang.mk
  -- ν (` a) = ν` ◃ ⊥‽
  (null := sorry)
  -- δ (` c) a = δ` ◂ ((a ≟ c) · 𝟏)
  (derive := sorry)

-- _◂_  : (Q ⟷ P) → Lang P → Lang Q
unsafe -- we need unsafe, since Automatic.Lang requires unsafe
def iso {a: Type u} (f: ∀ w: List α, Q w <=> P w) (p: @Lang α P): Lang Q := Lang.mk
  -- ν (f ◂ p) = f ◃ ν p
  (null := sorry)
  -- δ (f ◂ p) a = f ◂ δ p a
  (derive := sorry)


end Automatic
