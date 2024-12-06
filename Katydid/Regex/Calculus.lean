import Katydid.Regex.Language

namespace Calculus

open Language
open List
open Char
open String

def null' (P: Lang α): Prop :=
  P []

def derive' (P: Lang α) (a: α): Lang α :=
  fun (w: List α) => P (a :: w)

def null {α: Type} (f: List α -> Prop): Prop :=
  f []

def derives {α: Type} (f: List α -> Prop) (u: List α): (List α -> Prop) :=
  λ v => f (u ++ v)

def derive {α: Type} (f: List α -> Prop) (a: α): (List α -> Prop) :=
  derives f [a]

attribute [simp] null derive derives

def derives_emptylist : derives f [] = f :=
  rfl

def derives_strings (f: List α -> Prop) (u v: List α): derives f (u ++ v) = derives (derives f u) v :=
  match u with
  | [] => rfl
  | (a :: u') => derives_strings (derive f a) u' v

def null_derives (f: List α -> Prop) (u: List α): (null ∘ derives f) u = f u := by
  simp

def derives_foldl (f: List α -> Prop) (u: List α): (derives f) u = (List.foldl derive f) u :=
  match u with
  | [] => rfl
  | (a :: as) => by sorry

def null_emptyset {α: Type}:
  @null α emptyset = False :=
  rfl

def null_universal {α: Type}:
  @null α universal = True :=
  rfl

def null_emptystr {α: Type}:
  @null α emptystr <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => rfl)

def null_char {α: Type} {c: α}:
  null (char c) <-> False :=
  Iff.intro nofun nofun

def null_or {α: Type} {P Q: Lang α}:
  null (or P Q) = ((null P) \/ (null Q)) := by
  rfl

def null_and {α: Type} {P Q: Lang α}:
  null (and P Q) = ((null P) /\ (null Q)) :=
  rfl

def null_concat {α: Type} {P Q: Lang α}:
  null (concat P Q) <-> ((null P) /\ (null Q)) := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro ⟨x, y, hx, hy, hxy⟩
    simp at hxy
    simp [hxy] at hx hy
    exact ⟨hx, hy⟩
  case invFun =>
    exact fun ⟨x, y⟩ => ⟨[], [], x, y, rfl⟩

-- def null_star {α: Type} {P: Lang α}:
--   null (star P) <-> (List (null P)) := by
--   refine Iff.intro ?toFun ?invFun
--   case toFun =>
--     sorry
--   case invFun =>
--     sorry

def derive_emptyset {α: Type} {a: α}:
  (derive emptyset a) = emptyset :=
  rfl

def derive_universal {α: Type} {a: α}:
  (derive universal a) = universal :=
  rfl

def derive_emptystr {α: Type} {a: α} {w: List α}:
  (derive emptystr a) w <-> emptyset w :=
  Iff.intro nofun nofun

def derive_char {α: Type} {a: α} {c: α} {w: List α}:
  (derive (char c) a) w <-> (scalar (a = c) emptystr) w := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro D
    cases D with | refl =>
    exact ⟨ rfl, rfl ⟩
  case invFun =>
    intro ⟨ H1 , H2  ⟩
    cases H1 with | refl =>
    cases H2 with | refl =>
    exact rfl

def derive_or {α: Type} {a: α} {P Q: Lang α}:
  (derive (or P Q) a) = (or (derive P a) (derive Q a)) :=
  rfl

def derive_and {α: Type} {a: α} {P Q: Lang α}:
  (derive (and P Q) a) = (and (derive P a) (derive Q a)) :=
  rfl

def derive_scalar {α: Type} {a: α} {s: Prop} {P: Lang α}:
  (derive (scalar s P) a) = (scalar s (derive P a)) :=
  rfl

def derive_concat {α: Type} {a: α} {P Q: Lang α} {w: List α}:
  (derive (concat P Q) a) w <-> (scalar (null P) (or (derive Q a) (concat (derive P a) Q))) w := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    sorry
  case invFun =>
    sorry

-- def derive_star {α: Type} {a: α} {P: Lang α} {w: List α}:
--   (derive (star P) a) w <-> (scalar (List (null P)) (concat (derive P a) (star P))) w := by
--   refine Iff.intro ?toFun ?invFun
--   case toFun =>
--     sorry
--   case invFun =>
--     sorry
