Require Import CoqStock.Hashable.

Definition nat_hash (n: nat): nat :=
    n.

Instance hashable_nat : hashable nat :=
  {
    hash := nat_hash
  }.