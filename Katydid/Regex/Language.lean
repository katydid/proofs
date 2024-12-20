import Katydid.Std.Lists

namespace Language

open List

-- Definitions

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

theorem derives_empty_list {α: Type} (R: Lang α):
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

theorem validate {α: Type} (R: Lang α) (xs: List α):
  null (derives R xs) = R xs := by
  unfold derives
  unfold null
  simp

theorem derives_foldl (R: Lang α) (xs: List α):
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

-- Theorems: null

theorem null_emptyset {α: Type}:
  @null α emptyset = False :=
  rfl

theorem null_iff_emptyset {α: Type}:
  @null α emptyset <-> False := by
  rw [null_emptyset]

theorem not_null_if_emptyset {α: Type}:
  @null α emptyset -> False :=
  null_iff_emptyset.mp

theorem null_universal {α: Type}:
  @null α universal = True :=
  rfl

theorem null_iff_emptystr {α: Type}:
  @null α emptystr <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => rfl)

theorem null_if_emptystr {α: Type}:
  @null α emptystr :=
  rfl

theorem null_emptystr {α: Type}:
  @null α emptystr = True := by
  rw [null_iff_emptystr]

theorem null_iff_char {α: Type} {c: α}:
  null (char c) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_char {α: Type} {c: α}:
  null (char c) -> False :=
  nofun

theorem null_char {α: Type} {c: α}:
  null (char c) = False := by
  rw [null_iff_char]

theorem null_iff_pred {α: Type} {p: α -> Prop}:
  null (pred p) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_pred {α: Type} {p: α -> Prop}:
  null (pred p) -> False :=
  nofun

theorem null_pred {α: Type} {p: α -> Prop}:
  null (pred p) = False := by
  rw [null_iff_pred]

theorem null_or {α: Type} {P Q: Lang α}:
  null (or P Q) = ((null P) \/ (null Q)) :=
  rfl

theorem null_iff_or {α: Type} {P Q: Lang α}:
  null (or P Q) <-> ((null P) \/ (null Q)) := by
  rw [null_or]

theorem null_and {α: Type} {P Q: Lang α}:
  null (and P Q) = ((null P) /\ (null Q)) :=
  rfl

theorem null_iff_concat {α: Type} {P Q: Lang α}:
  null (concat P Q) <-> ((null P) /\ (null Q)) := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro ⟨x, y, hx, hy, hxy⟩
    simp at hxy
    simp [hxy] at hx hy
    exact ⟨hx, hy⟩
  case invFun =>
    exact fun ⟨x, y⟩ => ⟨[], [], x, y, rfl⟩

theorem null_concat {α: Type} {P Q: Lang α}:
  null (concat P Q) = ((null P) /\ (null Q)) := by
  rw [null_iff_concat]

theorem null_if_star {α: Type} {R: Lang α}:
  null (star R) :=
  star.zero

theorem null_iff_star {α: Type} {R: Lang α}:
  null (star R) <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => star.zero)

theorem null_star {α: Type} {R: Lang α}:
  null (star R) = True := by
  rw [null_iff_star]

theorem null_not {α: Type} {R: Lang α}:
  null (not R) = null (Not ∘ R) :=
  rfl

theorem null_iff_not {α: Type} {R: Lang α}:
  null (not R) <-> null (Not ∘ R) := by
  rw [null_not]

-- Theorems: derive

theorem derive_emptyset {α: Type} {a: α}:
  (derive emptyset a) = emptyset :=
  rfl

theorem derive_universal {α: Type} {a: α}:
  (derive universal a) = universal :=
  rfl

theorem derive_iff_emptystr {α: Type} {a: α} {w: List α}:
  (derive emptystr a) w <-> emptyset w :=
  Iff.intro nofun nofun

theorem derive_emptystr {α: Type} {a: α}:
  (derive emptystr a) = emptyset := by
  funext
  rw [derive_iff_emptystr]

theorem derive_iff_char {α: Type} [DecidableEq α] {a: α} {c: α} {w: List α}:
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

theorem derive_char {α: Type} [DecidableEq α] {a: α} {c: α}:
  (derive (char c) a) = (onlyif (a = c) emptystr) := by
  funext
  rw [derive_iff_char]

theorem derive_iff_pred {α: Type} {p: α -> Prop} {x: α} {xs: List α}:
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

theorem derive_pred {α: Type} {p: α -> Prop} [DecidablePred p] {x: α}:
  (derive (pred p) x) = (onlyif (p x) emptystr) := by
  funext
  rw [derive_iff_pred]

theorem derive_or {α: Type} {a: α} {P Q: Lang α}:
  (derive (or P Q) a) = (or (derive P a) (derive Q a)) :=
  rfl

theorem derive_and {α: Type} {a: α} {P Q: Lang α}:
  (derive (and P Q) a) = (and (derive P a) (derive Q a)) :=
  rfl

theorem derive_onlyif {α: Type} {a: α} {s: Prop} {P: Lang α}:
  (derive (onlyif s P) a) = (onlyif s (derive P a)) :=
  rfl

theorem derive_iff_concat {α: Type} {x: α} {P Q: Lang α} {xs: List α}:
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

theorem derive_concat {α: Type} {x: α} {P Q: Lang α}:
  (derive (concat P Q) x) =
    (or (concat (derive P x) Q) (onlyif (null P) (derive Q x))) := by
  funext
  rw [derive_iff_concat]

theorem derive_iff_star {α: Type} {x: α} {R: Lang α} {xs: List α}:
  (derive (star R) x) xs <-> (concat (derive R x) (star R)) xs := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro deriveStar
    unfold derive at deriveStar
    unfold derives at deriveStar
    cases deriveStar with
    | more x' xs1 xs2 _ hxs Rxxs1 starRxs2 =>
      unfold concat
      exists xs1
      exists xs2
      simp at hxs
      cases hxs with
      | intro hxs1 hxs2 =>
      rw [hxs1]
      split_ands
      · exact Rxxs1
      · exact starRxs2
      · exact hxs2
  case invFun =>
    intro concatDerive
    unfold concat at concatDerive
    cases concatDerive with
    | intro xs1 concatDerive =>
    cases concatDerive with
    | intro xs2 concatDerive =>
    cases concatDerive with
    | intro deriveRxxs1 concatDerive =>
    cases concatDerive with
    | intro starRxs2 hxs =>
    unfold derive
    unfold derives
    refine star.more x xs1 xs2 ?hxs ?e ?f ?g
    · rw [hxs]
      simp
    · apply deriveRxxs1
    · exact starRxs2

theorem derive_star {α: Type} {x: α} {R: Lang α}:
  (derive (star R) x) = (concat (derive R x) (star R)) := by
  funext
  rw [derive_iff_star]

theorem derive_not {α: Type} {x: α} {R: Lang α}:
  (derive (not R) x) = Not ∘ (derive R x) :=
  rfl

theorem derive_iff_not {α: Type} {x: α} {R: Lang α} {xs: List α}:
  (derive (not R) x) xs <-> Not ((derive R x) xs) := by
  rw [derive_not]
  rfl

-- Theorems: simplification rules

theorem simp_concat_emptyset_l_is_emptyset (r: Lang α):
  concat emptyset r = emptyset := by
  unfold concat
  simp only [emptyset, false_and, exists_const]
  rfl

theorem simp_concat_emptyset_r_is_emptyset (r: Lang α):
  concat r emptyset = emptyset := by
  unfold concat
  simp only [emptyset, false_and, and_false, exists_const]
  rfl

theorem simp_concat_emptystr_l_is_r (r: Lang α):
  concat emptystr r = r := by
  unfold concat
  simp only [emptystr, exists_and_left, exists_eq_left, nil_append, exists_eq_right']

theorem simp_concat_emptystr_r_is_l (r: Lang α):
  concat r emptystr = r := by
  unfold concat
  simp only [emptystr, exists_and_left, exists_eq_left, append_nil, exists_eq_right']

theorem simp_concat_assoc (r s t: Lang α):
  concat r (concat s t) = concat (concat r s) t := by
  unfold concat
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | Exists.intro xs1
        (Exists.intro xs2
          (And.intro rxs1
            (And.intro
              (Exists.intro xs3
                (Exists.intro xs4
                  (And.intro sxs3
                    (And.intro txs4 xs2split)
                )))
              xssplit))) =>
    clear h
    exists (xs1 ++ xs3)
    exists xs4
    split_ands
    · exists xs1
      exists xs3
    · exact txs4
    · rw [xs2split] at xssplit
      simp only [append_assoc]
      exact xssplit
  case mpr =>
    intro h
    match h with
    | Exists.intro xs1
        (Exists.intro xs2
          (And.intro
            (Exists.intro xs3
              (Exists.intro xs4
                (And.intro rxs3
                  (And.intro sxs4 xs1split))))
            (And.intro txs2 xssplit))) =>
    clear h
    exists xs3
    exists (xs4 ++ xs2)
    split_ands
    · exact rxs3
    · exists xs4
      exists xs2
    · rw [xs1split] at xssplit
      simp only [append_assoc] at xssplit
      exact xssplit

theorem simp_or_emptyset_l_is_r (r: Lang α):
  or emptyset r = r := by
  unfold or
  simp only [emptyset, false_or]

theorem simp_or_emptyset_r_is_l (r: Lang α):
  or r emptyset = r := by
  unfold or
  simp only [emptyset, or_false]

theorem simp_or_universal_l_is_universal (r: Lang α):
  or universal r = universal := by
  unfold or
  simp only [universal, true_or]
  rfl

theorem simp_or_universal_r_is_universal (r: Lang α):
  or r universal = universal := by
  unfold or
  simp only [universal, or_true]
  rfl

theorem simp_or_null_l_emptystr_is_l
  (r: Lang α)
  (nullr: null r):
  or r emptystr = r := by
  unfold or
  simp
  unfold null at nullr
  funext xs
  simp
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_or_emptystr_null_r_is_r
  (r: Lang α)
  (nullr: null r):
  or emptystr r = r := by
  unfold or
  simp
  unfold null at nullr
  funext xs
  simp
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_or_idemp (r: Lang α):
  or r r = r := by
  unfold or
  simp

theorem simp_or_comm (r s: Lang α):
  or r s = or s r := by
  unfold or
  funext xs
  simp
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | Or.inl h =>
      exact Or.inr h
    | Or.inr h =>
      exact Or.inl h
  case mpr =>
    intro h
    match h with
    | Or.inl h =>
      exact Or.inr h
    | Or.inr h =>
      exact Or.inl h

theorem simp_or_assoc (r s t: Lang α):
  or r (or s t) = or (or r s) t := by
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro h
    cases h with
    | inl h =>
      left
      left
      exact h
    | inr h =>
      cases h with
      | inl h =>
        left
        right
        exact h
      | inr h =>
        right
        exact h
  · case mpr =>
    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        left
        exact h
      | inr h =>
        right
        left
        exact h
    | inr h =>
      right
      right
      exact h

theorem simp_and_emptyset_l_is_emptyset (r: Lang α):
  and emptyset r = emptyset := by
  unfold and
  simp
  rfl

theorem simp_and_emptyset_r_is_emptyset (r: Lang α):
  and r emptyset = emptyset := by
  unfold and
  simp
  rfl

theorem simp_and_universal_l_is_r (r: Lang α):
  and universal r = r := by
  unfold and
  simp

theorem simp_and_universal_r_is_l (r: Lang α):
  and r universal = r := by
  unfold and
  simp

theorem simp_and_null_l_emptystr_is_l
  (r: Lang α)
  (nullr: null r):
  and r emptystr = r := by
  funext xs
  simp only [and, emptystr, eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | And.intro hr hxs =>
    exact hr
  case mpr =>
    sorry

theorem simp_and_emptystr_null_r_is_r
  (r: Lang α)
  (nullr: null r):
  and emptystr r = r := by
  sorry

theorem simp_and_not_null_l_emptystr_is_emptyset
  (r: Lang α)
  (notnullr: Not (null r)):
  and r emptystr = emptyset := by
  sorry

theorem simp_and_emptystr_not_null_r_is_emptyset
  (r: Lang α)
  (notnullr: Not (null r)):
  and emptystr r = emptyset := by
  sorry

theorem simp_and_idemp (r: Lang α):
  and r r = r := by
  unfold and
  simp

theorem simp_and_comm (r s: Lang α):
  and r s = and s r := by
  unfold and
  funext xs
  simp
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | intro hr hs =>
      exact And.intro hs hr
  case mpr =>
    intro h
    cases h with
    | intro hs hr =>
      exact And.intro hr hs

theorem simp_and_assoc (r s t: Lang α):
  and r (and s t) = and (and r s) t := by
  unfold and
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | And.intro h1 (And.intro h2 h3) =>
    exact And.intro (And.intro h1 h2) h3
  case mpr =>
    intro h
    match h with
    | And.intro (And.intro h1 h2) h3 =>
    exact And.intro h1 (And.intro h2 h3)

theorem simp_not_not_is_double_negation (r: Lang α):
  not (not r) = r := by
  unfold not
  simp

theorem simp_not_and_demorgen (r s: Lang α):
  not (and r s) = or (not r) (not s) := by
  unfold not
  unfold and
  unfold or
  unfold Not
  funext xs
  simp only [not_and, eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    contrapose h
    simp only [imp_false, not_or, not_not] at h
    unfold Not
    intro h'
    apply h'
    exact h
  case mpr =>
    intro h
    intro hrs
    cases hrs with
    | intro hr hs =>
    simp at h
    cases h with
    | inl h =>
      contradiction
    | inr h =>
      contradiction

theorem simp_not_or_demorgen (r s: Lang α):
  not (or r s) = and (not r) (not s) := by
  unfold not
  unfold or
  unfold and
  simp only [not_or]

theorem simp_and_not_emptystr_l_not_null_r_is_r
  (r: Lang α)
  (notnullr: Not (null r)):
  and (not emptystr) r = r := by
  sorry

theorem simp_and_not_null_l_not_emptystr_r_is_l
  (r: Lang α)
  (notnullr: Not (null r)):
  and r (not emptystr) = r := by
  sorry

theorem simp_star_star_is_star (r: Lang α):
  star (star r) = star r := by
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    sorry
  case mpr =>
    sorry

theorem simp_star_emptystr_is_emptystr {α: Type}:
  star (@emptystr α) = (@emptystr α) := by
  funext xs
  simp
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case zero =>
      rfl
    case more x xs1 xs2 hemptystr hstar hsplit =>
      cases hemptystr
  case mpr =>
    intro h
    rw [h]
    exact star.zero

theorem simp_star_emptyset_is_emptystr {α: Type}:
  star (@emptyset α) = (@emptystr α) := by
  funext xs
  simp
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case zero =>
      rfl
    case more x xs1 xs2 hemptystr hstar hsplit =>
      cases hemptystr
  case mpr =>
    intro h
    rw [h]
    exact star.zero
