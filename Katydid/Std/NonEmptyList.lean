import Katydid.Std.Ordering
import Katydid.Std.Lists

structure NonEmptyList (α: Type) where
  head : α
  tail : List α

namespace NonEmptyList

def compare [o: Ord α] (xs ys: NonEmptyList α): Ordering :=
  match xs with
  | NonEmptyList.mk x' xs' =>
  match ys with
  | NonEmptyList.mk y' ys' =>
    Ordering.lex (Ord.compare x' y') (Ord.compare xs' ys')

instance [Ord α] : Ord (NonEmptyList α) where
  compare := compare

def cons (x: α) (xs: NonEmptyList α): NonEmptyList α :=
  NonEmptyList.mk x (xs.head :: xs.tail)

def toList (xs: NonEmptyList α): List α :=
  match xs with
  | NonEmptyList.mk head tail =>
    head :: tail

instance [Ord α] : LE (NonEmptyList α) where
  le (x: NonEmptyList α) (y: NonEmptyList α) :=
    LE.le x.toList y.toList

def merge' [Ord α] (xs: NonEmptyList α) (ys: NonEmptyList α): List α :=
  List.merge (xs.toList) (ys.toList) (fun x y => (Ord.compare x y).isLE)

def merge [Ord α] (xs: NonEmptyList α) (ys: NonEmptyList α): NonEmptyList α :=
  match xs with
  | NonEmptyList.mk x' xs' =>
  match ys with
  | NonEmptyList.mk y' ys' =>
  match Ord.compare x' y' with
  | Ordering.eq =>
    NonEmptyList.mk x' (Lists.merge xs' ys')
  | Ordering.lt =>
    NonEmptyList.mk x' (Lists.merge xs' (y'::ys'))
  | Ordering.gt =>
    NonEmptyList.mk y' (Lists.merge (x'::xs') ys')

def eraseReps [BEq α] (xs: NonEmptyList α): NonEmptyList α :=
  match xs with
  | NonEmptyList.mk x' xs' =>
    match xs' with
    | [] => xs
    | (x''::xs'') =>
      if x' == x''
      then NonEmptyList.eraseReps (NonEmptyList.mk x'' xs'')
      else NonEmptyList.mk x' (List.eraseReps xs')

def mergeRep [BEq α] [Ord α] (x: α) (ys zs : List α): NonEmptyList α :=
  match ys, zs with
  | [], [] =>
    NonEmptyList.mk x []
  | (y::ys), [] =>
    match Ord.compare x y with
    | Ordering.eq =>
        NonEmptyList.eraseReps (NonEmptyList.mk y ys)
    | Ordering.lt =>
        NonEmptyList.cons x (NonEmptyList.eraseReps (NonEmptyList.mk y ys))
    | Ordering.gt =>
        NonEmptyList.cons y (NonEmptyList.eraseReps (NonEmptyList.mk x ys))
  | [], (y::ys) =>
    match Ord.compare x y with
    | Ordering.eq => eraseReps (NonEmptyList.mk y ys)
    | Ordering.lt => NonEmptyList.cons x (eraseReps (NonEmptyList.mk y ys))
    | Ordering.gt => NonEmptyList.cons y (eraseReps (NonEmptyList.mk x ys))
  | (y::ys'), (z::zs') =>
    sorry

def mergeReps [BEq α] [Ord α] (xs ys : NonEmptyList α): NonEmptyList α :=
  match xs, ys with
  | NonEmptyList.mk x [], NonEmptyList.mk y ys' =>
    match Ord.compare x y with
    | Ordering.eq => NonEmptyList.eraseReps ys
    | Ordering.lt => NonEmptyList.cons x (NonEmptyList.eraseReps ys)
    | Ordering.gt => NonEmptyList.cons y (NonEmptyList.eraseReps (NonEmptyList.mk x ys'))
  | NonEmptyList.mk x xs', NonEmptyList.mk y ys' =>
   sorry
