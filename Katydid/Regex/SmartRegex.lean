import Katydid.Regex.Language

open List

namespace SmartRegex

inductive Predicate (α: Type) where
  | mk
    (desc: String)
    (func: α -> Prop)
    (dec: DecidablePred func)
  : Predicate α

def Predicate.desc (p: Predicate α): String :=
  match p with
  | ⟨ desc, _, _ ⟩ => desc

def Predicate.func (p: Predicate α): α -> Prop :=
  match p with
  | ⟨ _, f, _ ⟩ => f

def Predicate.decfunc (p: Predicate α): DecidablePred p.func := by
  cases p with
  | mk desc f dec =>
    intro a
    unfold DecidablePred at dec
    unfold Predicate.func
    simp
    apply dec

def evalPredicate (p: Predicate α) (a: α): Bool := by
  cases p.decfunc a with
  | isFalse => exact Bool.false
  | isTrue => exact Bool.true

def Predicate.compare (x: Predicate α) (y: Predicate α): Ordering :=
  let xd: String := x.desc
  let yd: String := y.desc
  Ord.compare xd yd

instance : Ord (Predicate α) where
  compare: Predicate α → Predicate α → Ordering := Predicate.compare

inductive Regex (α: Type): Type where
  | emptyset : Regex α
  | emptystr : Regex α
  | pred : (p: Predicate α) → Regex α
  | or : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α

def null (r: Regex α): Bool :=
  match r with
  | Regex.emptyset => false
  | Regex.emptystr => true
  | Regex.pred _ => false
  | Regex.or x y => null x || null y
  | Regex.concat x y => null x && null y
  | Regex.star _ => true

def onlyif (cond: Prop) [dcond: Decidable cond] (r: Regex α): Regex α :=
  if cond then r else Regex.emptyset

def onlyif' {cond: Prop} (dcond: Decidable cond) (r: Regex α): Regex α :=
  if cond then r else Regex.emptyset

def derive (r: Regex α) (a: α): Regex α :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.pred p => onlyif' (p.decfunc a) Regex.emptystr
  | Regex.or x y =>
      -- TODO: use smartOr
      Regex.or (derive x a) (derive y a)
  | Regex.concat x y =>
      -- TODO: use smartOr and smartConcat
      Regex.or
        (Regex.concat (derive x a) y)
        (onlyif (null x) (derive y a))
  | Regex.star x =>
      -- TODO: use smartStar
      Regex.concat (derive x a) (Regex.star x)

def denote {α: Type} (r: Regex α): Language.Lang α :=
  match r with
  | Regex.emptyset => Language.emptyset
  | Regex.emptystr => Language.emptystr
  | Regex.pred p => Language.pred p.func
  | Regex.or x y => Language.or (denote x) (denote y)
  | Regex.concat x y => Language.concat (denote x) (denote y)
  | Regex.star x => Language.star (denote x)

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
    simp [smartStar]
    simp [denote]
    rw [Language.simp_star_emptyset_is_emptystr]
  | emptystr =>
    simp [smartStar]
    simp [denote]
    rw [Language.simp_star_emptystr_is_emptystr]
  | pred p =>
    simp [smartStar]
  | concat x1 x2 =>
    simp [smartStar]
  | or x1 x2 =>
    simp [smartStar]
  | star x' =>
    simp [smartStar]
    simp [denote]
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
    simp [denote]
    exact Language.simp_concat_emptyset_l_is_emptyset (denote y)
  | emptystr =>
    unfold smartConcat
    simp [denote]
    exact Language.simp_concat_emptystr_l_is_r (denote y)
  | pred p =>
    cases y <;> simp [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | or x1 x2 =>
    cases y <;> simp [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l
  | concat x1 x2 =>
    unfold smartConcat
    simp [denote]
    rw [<- smartConcat_is_concat x2 y]
    simp [denote]
    rw [Language.simp_concat_assoc]
  | star x1 =>
    cases y <;> simp [denote]
    · case emptyset =>
      apply Language.simp_concat_emptyset_r_is_emptyset
    · case emptystr =>
      apply Language.simp_concat_emptystr_r_is_l

-- TODO: incorporate more simplification rules into the smart constructor
-- 1. Get the list of ors (Language.simp_or_assoc)
-- 2. Remove duplicates from the list (create a set) (Language.simp_or_comm and Language.simp_or_idemp and Language.simp_or_assoc)
-- 3. If at any following step the set is size one, simply return
-- 4. If the set contains star (any) then return star (any) (Language.simp_or_universal_r_is_universal and Language.simp_or_universal_l_is_universal)
-- 5. Delete emptyset from the set (Language.simp_or_emptyset_r_is_l and Language.simp_or_emptyset_l_is_r)
-- 6. If any of the set is nullable, remove emptystr from the set (Language.simp_or_emptystr_null_r_is_r and Language.simp_or_null_l_emptystr_is_l)
-- 7. create a sorted list from the set (Language.simp_or_assoc and Language.simp_or_comm)
def smartOr (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => y
  | _ =>
    match y with
    | Regex.emptyset => x
    | _ => Regex.or x y

private theorem smartOr_is_or_righthand (x y: Regex α) (hx_emptyset: x ≠ Regex.emptyset):
  denote (Regex.or x y) = denote (smartOr x y) := by
  cases y <;> (try simp [smartOr])
  · case emptyset =>
    simp [denote]
    exact (Language.simp_or_emptyset_r_is_l (denote x))

theorem smartOr_is_or (x y: Regex α):
  denote (Regex.or x y) = denote (smartOr x y) := by
  have hy := smartOr_is_or_righthand x y
  match x with
  | Regex.emptyset =>
    unfold smartOr
    simp [denote]
    exact (Language.simp_or_emptyset_l_is_r (denote y))
  | Regex.emptystr =>
    exact hy (by simp)
  | Regex.pred p =>
    exact hy (by simp)
  | Regex.or x1 x2 =>
    exact hy (by simp)
  | Regex.concat x1 x2 =>
    exact hy (by simp)
  | Regex.star x1 =>
    exact hy (by simp)
