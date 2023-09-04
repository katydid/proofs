import Katydid.Std.Algebra
import Mathlib.Data.Tree

-- # Examples of Monoids

-- ## Addition is a Monoid

instance : Magma Nat where
  op a b := a + b

instance : Semigroup Nat where
  is_assoc := Nat.add_assoc

theorem add_left_identity (a: Nat):
  0 + a = a := by
  simp

theorem add_right_identity (a: Nat):
  a + 0 = a := by
  simp

instance AddMonoid : Monoid Nat where
  id := 0
  left_identity := add_left_identity
  right_identity := add_right_identity

-- ## Or is a Monoid

instance : Magma Bool where
  op a b := a || b

theorem bool_or_assoc: ∀ (a b c : Bool), (a || b || c) = (a || (b || c)) := by
  intro a b c
  cases a with
  | false =>
    simp
  | true =>
    simp

instance : Semigroup Bool where
  is_assoc := bool_or_assoc

instance AnyMonoid : Monoid Bool where
  id := false
  left_identity := by simp
  right_identity := by simp

-- We can write common functions that can be applied to any of these monoids

-- A simple function mconcat, which takes a list of monoid elements and combines them into a single element. Summing a list of integers is now the same as overlaying a list of images.
def mconcat (m: Monoid α) (xs: List α): α := Id.run <| do
  let mut res: α := m.id
  for x in xs do
    res := res ∘ x
  return res

def sum (xs: List Nat): Nat :=
  mconcat AddMonoid xs

def any (xs: List Bool): Bool :=
  mconcat AnyMonoid xs

#eval sum [0,1,2]

-- A more complex function foldMap can recursively walk over a tree and either: return whether any element is true, find if there is any element is larger than 5, or transform the foldable structure into a set, all depending on the type of monoid we use.
def foldMap (m: Monoid β) (f: α -> β): Tree α -> β
  | Tree.nil => Monoid.id
  | Tree.node a left right =>
    let b := f a
    let lb := foldMap m f left
    let rb := foldMap m f right
    b ∘ (lb ∘ rb)

def anyTree (t: Tree Bool): Bool :=
  foldMap AnyMonoid id t

#eval anyTree (Tree.node false Tree.nil Tree.nil)
#eval anyTree (Tree.node false Tree.nil (Tree.node false (Tree.node true Tree.nil Tree.nil) Tree.nil))

def anyLargerThan (t: Tree Nat) (max: Nat): Bool :=
  foldMap AnyMonoid (fun x => x > max) t

#eval anyLargerThan (Tree.node 6 Tree.nil Tree.nil) 5
#eval anyLargerThan (Tree.node 3 Tree.nil (Tree.node 7 (Tree.node 1 Tree.nil Tree.nil) Tree.nil)) 4
#eval anyLargerThan (Tree.node 3 Tree.nil (Tree.node 7 (Tree.node 1 Tree.nil Tree.nil) Tree.nil)) 8
