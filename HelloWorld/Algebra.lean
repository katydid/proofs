class Magma (α : Type u) where
  op : α → α → α

infixl:65 " ∘ " => Magma.op

class Semigroup (G : Type u) extends Magma G where
  is_assoc : ∀ a b c : G, op (op a b) c = op a (op b c)
  -- is_assoc a b c : op (op a b) c = op a (op b c)
  -- is_assoc (a b c: α) : op (op a b) c = op a (op b c)
  -- is_assoc : op (op a b) c = op a (op b c)

class Monoid (M : Type u) extends Semigroup M where
  identity: M
  left_identity: ∀ (a: M), op identity a = a
  right_identity: ∀ (a: M), op a identity = a

namespace algebra_using_structure'

  structure Magma'Struct where
    carrier : Type
    op : carrier → carrier → carrier

  structure Semigroup'Struct extends Magma'Struct where
    is_assoc : ∀ a b c, op (op a b) c = op a (op b c)

  structure Monoid'Struct extends Semigroup'Struct where
    e : carrier -- alternative names: identity or unit or ε
    left_identity: ∀ x, op e x = x
    right_identity: ∀ x, op x e = x

end algebra_using_structure'







