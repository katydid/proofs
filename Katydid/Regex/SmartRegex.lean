import Katydid.Std.NonEmptyList

import Katydid.Regex.Language

open List

namespace SmartRegex

def mkCharPredFunc (c: Char): Char -> Prop :=
  (· = c)

instance : DecidablePred (mkCharPredFunc c) := by
  intro c'
  unfold mkCharPredFunc
  by_cases (c' = c)
  · case pos h =>
    exact Decidable.isTrue h
  · case neg h =>
    exact Decidable.isFalse h

def mkAnyPredFunc: α -> Prop :=
  fun _ => True

instance : @DecidablePred α mkAnyPredFunc := by
  intro a
  unfold mkAnyPredFunc
  exact Decidable.isTrue True.intro

inductive Predicate (α: Type) where
  | mk
    (desc: String)
    (func: α -> Prop)
  : [DecidablePred func] -> [Ord α] -> Predicate α

def Predicate.desc {α: Type} (p: Predicate α): String :=
  match p with
  | Predicate.mk desc _ => desc

def Predicate.compare (x: Predicate α) (y: Predicate α): Ordering :=
  let xd: String := x.desc
  let yd: String := y.desc
  Ord.compare xd yd

instance : Ord (Predicate α) where
  compare: Predicate α → Predicate α → Ordering := Predicate.compare

def Predicate.mkChar (c: Char): Predicate Char :=
  Predicate.mk (String.mk [c]) (mkCharPredFunc c)

def Predicate.mkAny [o: Ord α]: Predicate α :=
  Predicate.mk "any" mkAnyPredFunc

def Predicate.func (p: Predicate α): α -> Prop :=
  match p with
  | Predicate.mk _ func => func

def Predicate.decfunc (p: Predicate α): DecidablePred p.func := by
  cases p with
  | mk desc f =>
    rename_i dec _
    intro a
    unfold DecidablePred at dec
    unfold Predicate.func
    simp only
    apply dec

def evalPredicate (p: Predicate α) (a: α): Bool := by
  cases p.decfunc a with
  | isFalse => exact Bool.false
  | isTrue => exact Bool.true

inductive Regex (α: Type): Type where
  | emptyset : Regex α
  | emptystr : Regex α
  | pred : (p: Predicate α) → Regex α
  | or : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α

def Regex.compare (x y: Regex α): Ordering :=
  match x with
  | Regex.emptyset =>
    match y with
    | Regex.emptyset =>
      Ordering.eq
    | _ =>
      Ordering.lt
  | Regex.emptystr =>
    match y with
    | Regex.emptyset =>
      Ordering.gt
    | Regex.emptystr =>
      Ordering.eq
    | _ =>
      Ordering.lt
  | Regex.pred p1 =>
    match y with
    | Regex.emptyset =>
      Ordering.gt
    | Regex.emptystr =>
      Ordering.gt
    | Regex.pred p2 =>
      Ord.compare p1 p2
    | _ =>
      Ordering.lt
  | Regex.or x1 x2 =>
    match y with
    | Regex.emptyset =>
      Ordering.gt
    | Regex.emptystr =>
      Ordering.gt
    | Regex.pred _ =>
      Ordering.gt
    | Regex.or y1 y2 =>
      match Regex.compare x1 y1 with
      | Ordering.eq =>
        Regex.compare x2 y2
      | o => o
    | _ =>
      Ordering.lt
  | Regex.concat x1 x2 =>
    match y with
    | Regex.emptyset =>
      Ordering.gt
    | Regex.emptystr =>
      Ordering.gt
    | Regex.pred _ =>
      Ordering.gt
    | Regex.or _ _ =>
      Ordering.gt
    | Regex.concat y1 y2 =>
      match Regex.compare x1 y1 with
      | Ordering.eq =>
        Regex.compare x2 y2
      | o => o
    | _ =>
      Ordering.lt
  | Regex.star x1 =>
    match y with
    | Regex.star y1 =>
      Regex.compare x1 y1
    | _ =>
      Ordering.lt

instance : Ord (Regex α) where
  compare (x y: Regex α): Ordering := Regex.compare x y

instance : LE (Regex α) where
  le x y := (Ord.compare x y).isLE

instance : BEq (Regex α) where
  beq x y := Ord.compare x y == Ordering.eq

def Regex.le (x y: Regex α): Bool :=
  x <= y

def onlyif (cond: Prop) [dcond: Decidable cond] (r: Regex α): Regex α :=
  if cond then r else Regex.emptyset

def onlyif' {cond: Prop} (dcond: Decidable cond) (r: Regex α): Regex α :=
  if cond then r else Regex.emptyset

def denote {α: Type} (r: Regex α): Language.Lang α :=
  match r with
  | Regex.emptyset => Language.emptyset
  | Regex.emptystr => Language.emptystr
  | Regex.pred p => Language.pred p.func
  | Regex.or x y => Language.or (denote x) (denote y)
  | Regex.concat x y => Language.concat (denote x) (denote y)
  | Regex.star x => Language.star (denote x)

def null (r: Regex α): Bool :=
  match r with
  | Regex.emptyset => false
  | Regex.emptystr => true
  | Regex.pred _ => false
  | Regex.or x y => null x || null y
  | Regex.concat x y => null x && null y
  | Regex.star _ => true

-- copy of SimpleRegex.null_commutes
theorem null_commutes {α: Type} (r: Regex α):
  ((null r) = true) = Language.null (denote r) := by
  induction r with
  | emptyset =>
    unfold denote
    rw [Language.null_emptyset]
    unfold null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    rw [Language.null_emptystr]
    unfold null
    simp only
  | pred p =>
    unfold denote
    rw [Language.null_pred]
    unfold null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    rw [Language.null_or]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    rw [Language.null_concat]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    unfold denote
    rw [Language.null_star]
    unfold null
    simp only

-- smartStar is a smart constructor for Regex.star which incorporates the following simplification rules:
-- 1. star (star x) = star x (Language.simp_star_star_is_star)
-- 2. star emptystr = emptystr (Language.simp_star_emptystr_is_emptystr)
-- 3. star emptyset = emptystr (Language.simp_star_emptyset_is_emptystr)
def smartStar (x: Regex α): Regex α :=
  match x with
  | Regex.emptyset => Regex.emptystr
  | Regex.emptystr => Regex.emptystr
  | Regex.star _ => x
  | _ => Regex.star x

theorem smartStar_is_star (x: Regex α):
  denote (Regex.star x) = denote (smartStar x) := by
  cases x with
  | emptyset =>
    simp only [smartStar]
    simp only [denote]
    rw [Language.simp_star_emptyset_is_emptystr]
  | emptystr =>
    simp only [smartStar]
    simp only [denote]
    rw [Language.simp_star_emptystr_is_emptystr]
  | pred p =>
    simp only [smartStar]
  | concat x1 x2 =>
    simp only [smartStar]
  | or x1 x2 =>
    simp only [smartStar]
  | star x' =>
    simp only [smartStar]
    simp only [denote]
    rw [Language.simp_star_star_is_star]

-- smartConcat is a smart constructor for Regex.concat that includes the following simplification rules:
-- 1. If x or y is emptyset then return emptyset (Language.simp_concat_emptyset_l_is_emptyset and Language.simp_concat_emptyset_r_is_emptyset)
-- 2. If x or y is emptystr return the other (Language.simp_concat_emptystr_r_is_l and Language.simp_concat_emptystr_l_is_r)
-- 3. If x is a concat then `((concat x1 x2) y) = concat x1 (concat x2 y)` use associativity (Language.simp_concat_assoc).
def smartConcat (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => y
  | Regex.concat x1 x2 =>
      -- smartConcat needs to be called again on the rigth hand side, since x2 might also be a Regex.concat.
      -- x1 is gauranteed to not be a Regex.concat if it has been constructed with smartConcat, so we do not called smartConcat again on the left hand side.
      Regex.concat x1 (smartConcat x2 y)
  | _otherwise =>
      match y with
      | Regex.emptyset => Regex.emptyset
      | Regex.emptystr => x
      | _otherwise => Regex.concat x y

theorem smartConcat_is_concat {α: Type} (x y: Regex α):
  denote (Regex.concat x y) = denote (smartConcat x y) := by
  cases x with
  | emptyset =>
    unfold smartConcat
    simp only [denote]
    exact Language.simp_concat_emptyset_l_is_emptyset (denote y)
  | emptystr =>
    unfold smartConcat
    simp only [denote]
    exact Language.simp_concat_emptystr_l_is_r (denote y)
  | pred p =>
    cases y <;> simp only [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | or x1 x2 =>
    cases y <;> simp only [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | concat x1 x2 =>
    unfold smartConcat
    simp only [denote]
    rw [<- smartConcat_is_concat x2 y]
    simp only [denote]
    rw [Language.simp_concat_assoc]
  | star x1 =>
    cases y <;> simp only [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l

def orToList (x: Regex α): NonEmptyList (Regex α) :=
  match x with
  | Regex.or x1 x2 =>
    -- smartOr guarantees that left hand side will not be an Regex.or so a recursive call is only required on the right hand side.
    NonEmptyList.cons x1 (orToList x2)
  | _ =>
    NonEmptyList.mk x []

def orFromList (xs: NonEmptyList (Regex α)): Regex α :=
  match xs with
  | NonEmptyList.mk x1 [] =>
    x1
  | NonEmptyList.mk x1 (x2::xs) =>
    Regex.or x1 (orFromList (NonEmptyList.mk x2 xs))

theorem orToList_is_orFromList (x: Regex α):
  orFromList (orToList x) = x := by
  induction x <;> (try simp only [orToList, orFromList])
  · case or x1 x2 ih1 ih2 =>
    -- TODO
    sorry

-- 1. If x or y is emptyset then return the other (Language.simp_or_emptyset_r_is_l and Language.simp_or_emptyset_l_is_r)
-- 2. If x or y is star (any) then return star (any) (Language.simp_or_universal_r_is_universal and Language.simp_or_universal_l_is_universal)
-- 3. Get the lists of ors using orToList (Language.simp_or_assoc)
-- 4. Merge sort the sorrted lists (Language.simp_or_comm and Language.simp_or_assoc)
-- 5. Remove duplicates from the list (or create a set) (Language.simp_or_idemp)
-- 6. If at any following step the set is size one, simply return
-- TODO: 7. If any of the set is nullable, remove emptystr from the set (Language.simp_or_emptystr_null_r_is_r and Language.simp_or_null_l_emptystr_is_l)
-- 8. Reconstruct Regex.or from the list using orFromList (Language.simp_or_assoc)
def smartOr (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => y
  | Regex.star (Regex.pred (Predicate.mk "any" _)) => x
  | _ =>
  match y with
  | Regex.emptyset => x
  | Regex.star (Regex.pred (Predicate.mk "any" _)) => y
  | _ =>
    -- it is implied that xs is sorted, given it was created using smartOr
    let xs := orToList x
    let ys := orToList y
    -- merge the sorted lists and remove duplicates,
    -- resulting in a sorted list of unique items.
    let ors := NonEmptyList.mergeReps xs ys
    orFromList ors

theorem smartOr_is_or (x y: Regex α):
  denote (Regex.or x y) = denote (smartOr x y) := by
  -- TODO
  sorry

def derive (r: Regex α) (a: α): Regex α :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.pred p => onlyif' (p.decfunc a) Regex.emptystr
  | Regex.or x y =>
      SmartRegex.smartOr (derive x a) (derive y a)
  | Regex.concat x y =>
      SmartRegex.smartOr
        (SmartRegex.smartConcat (derive x a) y)
        (onlyif (null x) (derive y a))
  | Regex.star x =>
      SmartRegex.smartConcat (derive x a) (Regex.star x)

theorem derive_commutes {α: Type} (r: Regex α) (x: α):
  denote (derive r x) = Language.derive (denote r) x := by
  -- TODO
  sorry

def derives (r: Regex α) (xs: List α): Regex α :=
  (List.foldl derive r) xs

-- copy of SimpleRegex.derives_commutes
theorem derives_commutes {α: Type} (r: Regex α) (xs: List α):
  denote (derives r xs) = Language.derives (denote r) xs := by
  unfold derives
  rw [Language.derives_foldl]
  revert r
  induction xs with
  | nil =>
    simp only [foldl_nil]
    intro h
    exact True.intro
  | cons x xs ih =>
    simp only [foldl_cons]
    intro r
    have h := derive_commutes r x
    have ih' := ih (derive r x)
    rw [h] at ih'
    exact ih'

def validate (r: Regex α) (xs: List α): Bool :=
  null (derives r xs)

-- copy of SimpleRegex.validate_commutes
theorem validate_commutes {α: Type} (r: Regex α) (xs: List α):
  (validate r xs = true) = (denote r) xs := by
  rw [<- Language.validate (denote r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

-- decidableDenote shows that the derivative algorithm is decidable
-- copy of SimpleRegex.decidableDenote
def decidableDenote (r: Regex α): DecidablePred (denote r) := by
  unfold DecidablePred
  intro xs
  rw [<- validate_commutes]
  cases (validate r xs)
  · simp only [Bool.false_eq_true]
    apply Decidable.isFalse
    simp only [not_false_eq_true]
  · simp only
    apply Decidable.isTrue
    exact True.intro
