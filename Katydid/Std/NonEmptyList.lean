structure NonEmptyList (α: Type) where
  head : α
  tail : List α

namespace NonEmptyList

def cons (x: α) (xs: NonEmptyList α): NonEmptyList α :=
  NonEmptyList.mk x (xs.head :: xs.tail)
