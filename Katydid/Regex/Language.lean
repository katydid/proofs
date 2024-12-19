import Katydid.Std.Lists

namespace Language

open List

def Lang (α: Type): Type := List α -> Prop

def emptyset : Lang α :=
  fun _ => False

def universal {α: Type} : Lang α :=
  fun _ => True

def emptystr {α: Type} : Lang α :=
  fun xs => xs = []

def char {α: Type} (x : α): Lang α :=
  fun xs => xs = [x]

def pred {α: Type} (p : α -> Prop): Lang α :=
  fun xs => ∃ x, xs = [x] /\ p x

-- onlyif is used as an and to make derive char not require an if statement
-- (derive (char c) a) w <-> (onlyif (a = c) emptystr)
def onlyif {α: Type} (cond : Prop) (R : Lang α) : Lang α :=
  fun xs => cond /\ R xs

def or {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun xs => P xs \/ Q xs

def and {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun xs => P xs /\ Q xs

def concat {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun (xs : List α) =>
    ∃ (xs1 : List α) (xs2 : List α), P xs1 /\ Q xs2 /\ xs = (xs1 ++ xs2)

inductive star {α: Type} (R: Lang α): Lang α where
  | zero: star R []
  | more: ∀ (x: α) (xs1 xs2 xs: List α),
    xs = (x::xs1) ++ xs2
    -> R (x::xs1)
    -> star R xs2
    -> star R xs

def not {α: Type} (R: Lang α): Lang α :=
  fun xs => (Not (R xs))

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptyset emptystr char onlyif or and concat

example: Lang α := universal
example: Lang α := emptystr
example: Lang α := (or emptystr universal)
example: Lang α := (and emptystr universal)
example: Lang α := emptyset
example: Lang α := (star emptyset)
example: Lang Char := char 'a'
example: Lang Char := char 'b'
example: Lang Char := (or (char 'a') emptyset)
example: Lang Char := (and (char 'a') (char 'b'))
example: Lang Nat := (and (char 1) (char 2))
example: Lang Nat := (onlyif True (char 2))
example: Lang Nat := (concat (char 1) (char 2))

def null {α: Type} (R: Lang α): Prop :=
  R []

def derives {α: Type} (R: Lang α) (xs: List α): Lang α :=
  λ ys => R (xs ++ ys)

def derive {α: Type} (R: Lang α) (x: α): Lang α :=
  derives R [x]

def derive' {α: Type} (R: Lang α) (x: α): Lang α :=
  fun (xs: List α) => R (x :: xs)

attribute [simp] null derive derives derive'

theorem derive_is_derive' {α: Type} (R: Lang α) (x: α):
  derive R x = derive' R x :=
  rfl

def derives_empty_list {α: Type} (R: Lang α):
  derives R [] = R :=
  rfl

theorem derives_strings {α: Type} (R: Lang α) (xs ys: List α):
  derives R (xs ++ ys) = derives (derives R xs) ys :=
  match xs with
  | [] => rfl
  | (x :: xs) => derives_strings (derive R x) xs ys

theorem derives_step {α: Type} (R: Lang α) (x: α) (xs: List α):
  derives R (x :: xs) = derives (derive R x) xs := by
  simp
  rw [<- derives_strings]
  congr

theorem null_derives {α: Type} (R: Lang α) (xs: List α):
  (null ∘ derives R) xs = R xs := by
  unfold derives
  unfold null
  simp

def derives_foldl (R: Lang α) (xs: List α):
  (derives R) xs = (List.foldl derive R) xs := by
  revert R
  induction xs with
  | nil =>
    unfold derives
    simp
  | cons x xs ih =>
    simp
    intro R
    rw [derives_step]
    rw [ih (derive R x)]
    simp

def null_emptyset {α: Type}:
  @null α emptyset = False :=
  rfl

def null_iff_emptyset {α: Type}:
  @null α emptyset <-> False := by
  rw [null_emptyset]

def not_null_if_emptyset {α: Type}:
  @null α emptyset -> False :=
  null_iff_emptyset.mp

def null_universal {α: Type}:
  @null α universal = True :=
  rfl

def null_iff_emptystr {α: Type}:
  @null α emptystr <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => rfl)

def null_if_emptystr {α: Type}:
  @null α emptystr :=
  rfl

def null_emptystr {α: Type}:
  @null α emptystr = True := by
  rw [null_iff_emptystr]

def null_iff_char {α: Type} {c: α}:
  null (char c) <-> False :=
  Iff.intro nofun nofun

def not_null_if_char {α: Type} {c: α}:
  null (char c) -> False :=
  nofun

def null_char {α: Type} {c: α}:
  null (char c) = False := by
  rw [null_iff_char]

def null_iff_pred {α: Type} {p: α -> Prop}:
  null (pred p) <-> False :=
  Iff.intro nofun nofun

def not_null_if_pred {α: Type} {p: α -> Prop}:
  null (pred p) -> False :=
  nofun

def null_pred {α: Type} {p: α -> Prop}:
  null (pred p) = False := by
  rw [null_iff_pred]

def null_or {α: Type} {P Q: Lang α}:
  null (or P Q) = ((null P) \/ (null Q)) :=
  rfl

def null_iff_or {α: Type} {P Q: Lang α}:
  null (or P Q) <-> ((null P) \/ (null Q)) := by
  rw [null_or]

def null_and {α: Type} {P Q: Lang α}:
  null (and P Q) = ((null P) /\ (null Q)) :=
  rfl

def null_iff_concat {α: Type} {P Q: Lang α}:
  null (concat P Q) <-> ((null P) /\ (null Q)) := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro ⟨x, y, hx, hy, hxy⟩
    simp at hxy
    simp [hxy] at hx hy
    exact ⟨hx, hy⟩
  case invFun =>
    exact fun ⟨x, y⟩ => ⟨[], [], x, y, rfl⟩

def null_concat {α: Type} {P Q: Lang α}:
  null (concat P Q) = ((null P) /\ (null Q)) := by
  rw [null_iff_concat]

def null_if_star {α: Type} {R: Lang α}:
  null (star R) :=
  star.zero

def null_iff_star {α: Type} {R: Lang α}:
  null (star R) <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => star.zero)

def null_star {α: Type} {R: Lang α}:
  null (star R) = True := by
  rw [null_iff_star]

def null_not {α: Type} {R: Lang α}:
  null (not R) = null (Not ∘ R) :=
  rfl

def null_iff_not {α: Type} {R: Lang α}:
  null (not R) <-> null (Not ∘ R) := by
  rw [null_not]

def derive_emptyset {α: Type} {a: α}:
  (derive emptyset a) = emptyset :=
  rfl

def derive_universal {α: Type} {a: α}:
  (derive universal a) = universal :=
  rfl

def derive_iff_emptystr {α: Type} {a: α} {w: List α}:
  (derive emptystr a) w <-> emptyset w :=
  Iff.intro nofun nofun

def derive_emptystr {α: Type} {a: α}:
  (derive emptystr a) = emptyset := by
  funext
  rw [derive_iff_emptystr]

def derive_iff_char {α: Type} [DecidableEq α] {a: α} {c: α} {w: List α}:
  (derive (char c) a) w <-> (onlyif (a = c) emptystr) w := by
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

def derive_char {α: Type} [DecidableEq α] {a: α} {c: α}:
  (derive (char c) a) = (onlyif (a = c) emptystr) := by
  funext
  rw [derive_iff_char]

def derive_iff_pred {α: Type} {p: α -> Prop} [dp: DecidablePred p] {x: α} {xs: List α}:
  (derive (pred p) x) xs <-> (onlyif (p x) emptystr) xs := by
  simp only [derive, derives, singleton_append]
  simp only [onlyif, emptystr]
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro D
    match D with
    | Exists.intro x' D =>
    simp only [cons.injEq] at D
    match D with
    | And.intro (And.intro hxx' hxs) hpx =>
    rw [<- hxx'] at hpx
    exact And.intro hpx hxs
  case invFun =>
    intro ⟨ hpx , hxs  ⟩
    unfold pred
    exists x
    simp only [cons.injEq, true_and]
    exact And.intro hxs hpx

def derive_pred {α: Type} {p: α -> Prop} [DecidablePred p] {x: α}:
  (derive (pred p) x) = (onlyif (p x) emptystr) := by
  funext
  rw [derive_iff_pred]

def derive_or {α: Type} {a: α} {P Q: Lang α}:
  (derive (or P Q) a) = (or (derive P a) (derive Q a)) :=
  rfl

def derive_and {α: Type} {a: α} {P Q: Lang α}:
  (derive (and P Q) a) = (and (derive P a) (derive Q a)) :=
  rfl

def derive_onlyif {α: Type} {a: α} {s: Prop} {P: Lang α}:
  (derive (onlyif s P) a) = (onlyif s (derive P a)) :=
  rfl

def derive_iff_concat {α: Type} {x: α} {P Q: Lang α} {xs: List α}:
  (derive (concat P Q) x) xs <->
    (or (concat (derive P x) Q) (onlyif (null P) (derive Q x))) xs := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    simp only [Language.or, Language.concat, derive, derives, null, onlyif]
    intro d
    guard_hyp d: ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ xs = x_1 ++ y
    guard_target = (∃ x_1 y, P ([x] ++ x_1) ∧ Q y ∧ xs = x_1 ++ y) ∨ P [] ∧ Q ([x] ++ xs)
    match d with
    | Exists.intro ps (Exists.intro qs (And.intro hp (And.intro hq hs))) =>
    guard_hyp hp : P ps
    guard_hyp hq : Q qs
    guard_hyp hs : [x] ++ xs = ps ++ qs
    match ps with
    | nil =>
      guard_hyp hp : P []
      guard_hyp hq : Q qs
      refine Or.inr ?r
      guard_target = P [] ∧ Q ([x] ++ xs)
      rw [nil_append] at hs
      rw [hs]
      exact And.intro hp hq
    | cons p ps =>
      guard_hyp hp : P (p :: ps)
      guard_hyp hq : Q qs
      guard_hyp hs : [x] ++ xs = p :: ps ++ qs
      refine Or.inl ?l
      guard_target = ∃ x_1 y, P ([x] ++ x_1) ∧ Q y ∧ xs = x_1 ++ y
      simp only [cons_append, cons.injEq] at hs
      match hs with
      | And.intro hpx hs =>
        rw [hpx]
        rw [nil_append] at hs
        rw [hs]
        guard_hyp hs : xs = ps ++ qs
        guard_target = ∃ x y, P ([p] ++ x) ∧ Q y ∧ ps ++ qs = x ++ y
        exact Exists.intro ps (Exists.intro qs (And.intro hp (And.intro hq rfl)))
  case invFun =>
    simp only [Language.or, Language.concat, derive, derives, null, onlyif]
    intro e
    guard_hyp e : (∃ x_1 y, P ([x] ++ x_1) ∧ Q y ∧ xs = x_1 ++ y) ∨ P [] ∧ Q ([x] ++ xs)
    guard_target = ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ xs = x_1 ++ y
    match e with
    | Or.inl e =>
      guard_hyp e: ∃ x_1 y, P ([x] ++ x_1) ∧ Q y ∧ xs = x_1 ++ y
      guard_target = ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ xs = x_1 ++ y
      match e with
      | Exists.intro ps (Exists.intro qs (And.intro hp (And.intro hq hs))) =>
        guard_hyp hp: P ([x] ++ ps)
        guard_hyp hq: Q qs
        guard_hyp hs: xs = ps ++ qs
        rw [hs]
        guard_target = ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ (ps ++ qs) = x_1 ++ y
        exact Exists.intro ([x] ++ ps) (Exists.intro qs (And.intro hp (And.intro hq rfl)))
    | Or.inr e =>
      guard_hyp e : P [] ∧ Q ([x] ++ xs)
      guard_target = ∃ x_1 y, P x_1 ∧ Q y ∧ [x] ++ xs = x_1 ++ y
      match e with
      | And.intro hp hq =>
        exact Exists.intro [] (Exists.intro (x :: xs) (And.intro hp (And.intro hq rfl)))

def derive_concat {α: Type} {x: α} {P Q: Lang α}:
  (derive (concat P Q) x) =
    (or (concat (derive P x) Q) (onlyif (null P) (derive Q x))) := by
  funext
  rw [derive_iff_concat]

def derive_iff_star {α: Type} {x: α} {R: Lang α} {xs: List α}:
  (derive (star R) x) xs <-> (concat (derive R x) (star R)) xs := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    sorry
  case invFun =>
    sorry

def derive_star {α: Type} {x: α} {R: Lang α}:
  (derive (star R) x) = (concat (derive R x) (star R)) := by
  funext
  rw [derive_iff_star]

def derive_not {α: Type} {x: α} {R: Lang α}:
  (derive (not R) x) = Not ∘ (derive R x) :=
  rfl

def derive_iff_not {α: Type} {x: α} {R: Lang α} {xs: List α}:
  (derive (not R) x) xs <-> Not ((derive R x) xs) := by
  rw [derive_not]
  rfl
