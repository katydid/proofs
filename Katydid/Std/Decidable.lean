namespace Decidable

def or {α β: Prop} (a: Decidable α) (b: Decidable β): Decidable (α \/ β) :=
  match (a, b) with
  | (Decidable.isFalse a, Decidable.isFalse b) =>
    Decidable.isFalse (fun ab =>
      match ab with
      | Or.inl sa => a sa
      | Or.inr sb => b sb
    )
  | (Decidable.isTrue a, Decidable.isFalse _) =>
    Decidable.isTrue (Or.inl a)
  | (_, Decidable.isTrue b) =>
    Decidable.isTrue (Or.inr b)

def and {α β: Prop} (a : Decidable α) (b : Decidable β) : Decidable (α /\ β) :=
  match a with
  | isTrue ha =>
    match b with
    | isTrue hb  => isTrue ⟨ha, hb⟩
    | isFalse hb => isFalse (fun h => hb (And.right h))
  | isFalse ha =>
    isFalse (fun h => ha (And.left h))

def map' {α β: Prop} (ab: α -> β) (ba: β -> α) (a: Decidable α): Decidable β :=
  match a with
  | Decidable.isTrue a =>
    Decidable.isTrue (ab a)
  | Decidable.isFalse nota =>
    Decidable.isFalse (nota ∘ ba)

def map {α β: Prop} (ab: α <-> β) (a: Decidable α): Decidable β :=
  map' ab.mp ab.mpr a
