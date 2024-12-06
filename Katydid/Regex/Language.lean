namespace Language

def Lang (α: Type): Type := List α -> Prop

def emptyset : Lang α :=
  fun _ => False

def universal {α: Type} : Lang α :=
  fun _ => True

def emptystr {α: Type} : Lang α :=
  fun w => w = []

def char {α: Type} (a : α): Lang α :=
  fun w => w = [a]

def or {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w \/ Q w

def and {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun w => P w /\ Q w

def concat {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun (w : List α) =>
    ∃ (x : List α) (y : List α), P x /\ Q y /\ w = (x ++ y)

inductive All {α: Type} (P : α -> Prop) : (List α -> Prop) where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

def star {α: Type} (P : Lang α) : Lang α :=
  fun (w : List α) =>
    ∃ (ws : List (List α)), All P ws /\ w = (List.join ws)

-- attribute [simp] allows these definitions to be unfolded when using the simp tactic.
attribute [simp] universal emptyset emptystr char or and concat star

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
example: Lang Nat := (concat (char 1) (char 2))

end Language
