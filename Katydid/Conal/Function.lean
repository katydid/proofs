-- An approximation of the Function module in the Agda standard library.

import Katydid.Std.Tipe

-- A ↔ B = Inverse A B

-- mk↔′ : ∀ (f : A → B) (f⁻¹ : B → A) → Inverseˡ f f⁻¹ → Inverseʳ f f⁻¹ → A ↔ B

-- record Inverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
--   field
--     to        : A → B
--     from      : B → A
--     to-cong   : Congruent _≈₁_ _≈₂_ to
--     from-cong : Congruent _≈₂_ _≈₁_ from
--     inverse   : Inverseᵇ _≈₁_ _≈₂_ to from

-- Congruent : (A → B) → Set _
-- Congruent f = ∀ {x y} → x ≈₁ y → f x ≈₂ f y

-- Inverseᵇ : (A → B) → (B → A) → Set _
-- Inverseᵇ f g = Inverseˡ f g × Inverseʳ f g

-- Inverseˡ : (A → B) → (B → A) → Set _
-- Inverseˡ f g = ∀ {x y} → y ≈₁ g x → f y ≈₂ x

-- Inverseʳ : (A → B) → (B → A) → Set _
-- Inverseʳ f g = ∀ {x y} → y ≈₂ f x → g y ≈₁ x

-- (_≈₁_ : Rel A ℓ₁) -- Equality over the domain
-- (_≈₂_ : Rel B ℓ₂) -- Equality over the codomain

-- Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
-- Rel A ℓ = REL A A ℓ

-- REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
-- REL A B ℓ = A → B → Set ℓ

def Congruent (f: A -> B): Type :=
  ∀ {x y}, x ≡ y -> f x ≡ f y

def Inverse (f: A -> B) (g: B -> A): Type :=
  ∀ {x y}, y ≡ g x -> f y ≡ x

inductive Inverses (f: A -> B) (g: B -> A): Type (u + 1) where
  | mk
    (congF : Congruent f)
    (congG : Congruent g)
    (inverseL : Inverse f g)
    (inverseR : Inverse g f): Inverses f g

-- Lean has Bi-implication
-- If and only if, or logical bi-implication. `a ↔ b` means that `a` implies `b` and vice versa. By `propext`, this implies that `a` and `b` are equal and hence any expression involving `a` is equivalent to the corresponding expression with `b` instead.
-- structure Iff (a b : Prop) : Prop where
  -- If `a → b` and `b → a` then `a` and `b` are equivalent. -/
  -- intro ::
  -- Modus ponens for if and only if. If `a ↔ b` and `a`, then `b`. -/
  -- mp : a → b
  -- Modus ponens for if and only if, reversed. If `a ↔ b` and `b`, then `a`. -/
  -- mpr : b → a

-- We use this weaker form of Inverses, but redefine it work Type

structure TIff (a b: Type u): Type (u + 1) where
  intro ::
    mp : a → b
    mpr : b → a

infixr:100 " <=> " => TIff

-- Extensional (or “pointwise”) isomorphism relates predicates isomorphic on every argument: P ←→ Q = ∀ {w} → P w ↔ Q w

def EIff {w: List α} (a b: List α -> Type u) := (a w) <=> (b w)

-- blackslash <-->
infixr:100 " ⟷ " => EIff

-- Note: We see that proofs that need ⟷ are typically proven using mk↔′
-- δ𝟏  : δ 𝟏 a ⟷ ∅
-- δ𝟏 = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())

-- Lean struggles to synthesize w sometimes, for example
--   (δ' ε a) ⟷ ∅
-- results in the error: "don't know how to synthesize implicit argument 'w'"
-- Then we need to explicitly provide 'w', as such
--   ∀ (w: List α), (δ' ε a) w <=> ∅ w
