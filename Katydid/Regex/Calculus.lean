-- Originally based on https://github.com/conal/paper-2021-language-derivatives/blob/main/Calculus.lagda

import Katydid.Regex.Language
import Katydid.Std.Balistic

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

def derives_foldl (f: List α -> Prop) (u: List α): (derives f) u = (List.foldl derive f) u := by
  induction u with
  | nil =>
    simp
    unfold derives
    simp
  | cons x xs ih =>
    sorry

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

def null_star' {α: Type} {P: Lang α}:
  null (star P) := by
  simp
  exists []
  apply And.intro
  · exact All.nil
  · intro l hl
    cases hl

def null_star {α: Type} {P: Lang α}:
  null (star P) <-> True := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    exact (fun _ => True.intro)
  case invFun =>
    intro t
    exact null_star'

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

def derive_concat {α: Type} {x: α} {P Q: Lang α} {xs: List α}:
  (derive (concat P Q) x) xs <->
    (or (concat (derive P x) Q) (scalar (null P) (derive Q x))) xs := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro d
    guard_hyp d: derive (Language.concat P Q) x xs
    simp at d
    cases d with
    | intro xs' d =>
    cases d with
    | intro hp d =>
    cases d with
    | intro ys' d =>
    cases d with
    | intro hq hxs =>
    guard_hyp hp: P xs'
    guard_hyp hq: Q ys'
    guard_hyp hxs: x :: xs = xs' ++ ys'
    unfold scalar
    simp
    balistic
    · guard_hyp hp: P []
      guard_hyp hq: Q (x :: xs)
      right
      guard_target = P [] ∧ Q (x :: xs)
      apply And.intro <;> assumption
    · left
      exists e
      apply And.intro
      exact hp
      exists ys'
  case invFun =>
    intro e
    guard_target = derive (Language.concat P Q) x xs
    cases e with
    | inl e =>
      guard_hyp e: Language.concat (derive P x) Q xs
      simp at e
      cases e with
      | intro xs' e =>
        cases e with
        | intro hp e =>
          cases e with
          | intro ys' hq =>
            cases hq with
            | intro hq hxs =>
              simp
              guard_hyp hp: P (x :: xs')
              guard_hyp hq: Q ys'
              guard_hyp hxs: xs = xs' ++ ys'
              exists (x :: xs')
              apply And.intro
              · exact hp
              · exists ys'
                apply And.intro
                · exact hq
                · congr
    | inr e =>
      unfold scalar at e
      guard_hyp e: null P ∧ derive Q x xs
      cases e with
      | intro hp hq =>
        simp
        exists []
        apply And.intro
        · exact hp
        · exists (x :: xs)

def derive_star {α: Type} {a: α} {P: Lang α} {w: List α}:
  (derive (star P) a) w <-> (concat (derive P a) (star P)) w := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    sorry
  case invFun =>
    sorry
