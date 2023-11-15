open List

/--
The equality relation. We use this instead of Lean's `Eq` because
we need it to be defined on Type instead of Prop.
-/
inductive REq {α : Type u} (x : α) : α -> Type u where
  | rrefl : REq x x

inductive All {α: Type u} (P : α -> Type u) : (List α -> Type u)  where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

def Lang (α : Type u) : Type (u + 1) :=  List α -> Type u

def emptySet : Lang α := fun _ => Empty

def universal : Lang α := fun _ => Unit

def emptyStr : Lang α := fun w => REq w []

def char (a : α) := fun w => REq w [a]

def scalar (s : Type u) (P : Lang α) : Lang α  := fun w => s × P w

def or_ (P : Lang α) (Q : Lang α) : Lang α := fun w => P w ⊕ Q w

def and_ (P : Lang α) (Q : Lang α) : Lang α := fun w => P w × Q w

def concat (P : Lang α) (Q : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ (x : List α) (y : List α), (REq w (x ++ y)) × P x × Q y

def star (P : Lang α) : Lang α :=
  fun (w : List α) =>
    Σ (ws : List (List α)), (REq w (List.join ws)) × All P ws

def ν (P : Lang α) : Type u := P []

def δ (P : Lang α) (a : α) : Lang α := fun (w : List α) => P (a :: w)

example : (or_ (char 'a') (char 'b')) ['a'] :=
  Sum.inl REq.rrefl

example : (or_ (char 'a') (char 'b')) ['a'] := by
  apply Sum.inl
  constructor
