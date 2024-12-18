import Katydid.Std.Lists

namespace Language

open List

def Lang (α: Type): Type := List α -> Prop

def emptyset : Lang α :=
  fun _ => False

def universal {α: Type} : Lang α :=
  fun _ => True

def emptystr {α: Type} : Lang α :=
  fun w => w = []

def char {α: Type} (a : α): Lang α :=
  fun w => w = [a]

-- onlyif is used as an and to make derive char not require an if statement
-- (derive (char c) a) w <-> (onlyif (a = c) emptystr)
def onlyif {α: Type} (cond : Prop) (P : Lang α) : Lang α :=
  fun w => cond /\ P w

def or {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w \/ Q w

def and {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w /\ Q w

def concat {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun (xs : List α) =>
    ∃ (ys : List α) (zs : List α), P ys /\ Q zs /\ xs = (ys ++ zs)

inductive All {α: Type} (P : α -> Prop) : (List α -> Prop) where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

def star {α: Type} (R : Lang α) : Lang α :=
  fun (xs : List α) =>
    ∃ (xss : List (List α)), All R xss /\ xs = (List.flatten xss)

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptyset emptystr char onlyif or and concat star

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

def null_star {α: Type} {P: Lang α}:
  null (star P) = True := by
  simp
  exists []
  apply And.intro
  · exact All.nil
  · intro l hl
    cases hl

def null_iff_star {α: Type} {P: Lang α}:
  null (star P) <-> True := by
  rw [null_star]

def null_if_star {α: Type} {P: Lang α}:
  null (star P) :=
  null_iff_star.mpr True.intro

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

inductive starplus {α: Type} (R: Lang α): Lang α where
  | zero: starplus R []
  | more: ∀ (ps qs w: List α),
    w = ps ++ qs
    -> R ps
    -> starplus R qs
    -> starplus R w

theorem star_is_starplus: ∀ {α: Type} (R: Lang α) (xs: List α),
  star R xs -> starplus R xs := by
  intro α R xs
  unfold star
  intro s
  match s with
  | Exists.intro ws (And.intro sl sr) =>
    clear s
    rw [sr]
    clear sr
    clear xs
    induction ws with
    | nil =>
      simp
      exact starplus.zero
    | cons w' ws' ih =>
      cases sl with
      | cons rw allrw =>
        have hr := ih allrw
        refine starplus.more ?ps ?qs ?w ?psqs ?rps ?rqs
        · exact w'
        · exact ws'.flatten
        · simp
        · assumption
        · assumption

theorem starplus_is_star: ∀ {α: Type} (R: Lang α) (xs: List α),
  starplus R xs -> star R xs := by
  intro α R xs
  intro hs
  induction xs with
  | nil =>
    simp
    exists []
    apply And.intro ?_ (by simp)
    apply All.nil
  | cons x' xs' ih =>
    cases hs with
    | more ps qs _ xxspsqs Rps sRqs =>
      unfold star
      have hxs := list_split_cons (x' :: xs')
      cases hxs with
      | inl h =>
        contradiction
      | inr h =>
        cases h with
        | intro x h =>
        cases h with
        | intro xs h =>
        cases h with
        | intro ys h =>
        rw [h]
        have hys := list_split_flatten ys
        cases hys with
        | intro yss hyss =>
        sorry

inductive starcons {α: Type} (R: Lang α): Lang α where
  | zero: starcons R []
  | more: ∀ (p: α) (ps qs w: List α),
    w = (p::ps) ++ qs
    -> R (p::ps)
    -> starcons R qs
    -> starcons R w

def stara {α: Type} (R : Lang α) (ws : List (List α)) (allr: All R ws): star R ws.flatten := by
  unfold star
  exists ws

theorem star_is_starcons: ∀ {α: Type} (R: Lang α) (xs: List α),
  star R xs <-> starcons R xs := by
  intro α R xs
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro s
    match s with
    | Exists.intro ws (And.intro sl sr) =>
      cases sl with
      | nil =>
        rw [sr]
        exact starcons.zero
      | cons rx1 rx2 =>
        rename_i xs1 xs2
        cases xs with
        | nil =>
          exact starcons.zero
        | cons x' xs' =>
          cases xs1 with
          | nil =>
            sorry
          | cons xs1' xss1' =>
            refine starcons.more x' ?ps ?qs ?ws' ?hw ?hr ?hsr
            · exact xss1'
            · exact xs2.flatten
            · sorry
            · sorry
            · sorry
  case invFun =>
    intro hs
    induction hs with
    | zero =>
      unfold star
      exists []
      simp
      exact All.nil
    | more x' ys' zs' xs hsplit hr hrs ih =>
      have hxs := list_split_cons xs
      cases hxs with
      | inl h =>
        rw [h]
        simp
        exists []
        simp
        apply All.nil
      | inr h =>
        cases h with
        | intro x h =>
        cases h with
        | intro ys h =>
        cases h with
        | intro zs h =>
        rw [hsplit] at h
        rw [hsplit]
        unfold star
        exists [x' :: ys', zs']
        refine And.intro ?_ (by simp)
        refine All.cons hr ?_
        cases ih with
        | intro ws h2 =>
        cases h2 with
        | intro h2l h2r =>
        sorry

def derive_iff_star {α: Type} {x: α} {R: Lang α} {xs: List α}:
  (derive (star R) x) xs <-> (concat (derive R x) (star R)) xs := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    sorry
  case invFun =>
    sorry

def derive_star {α: Type} {a: α} {P: Lang α}:
  (derive (star P) a) = (concat (derive P a) (star P)) := by
  funext
  rw [derive_iff_star]
