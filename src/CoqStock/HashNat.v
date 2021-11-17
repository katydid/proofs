Require Import CoqStock.Hash.

Definition nat_hash (n: nat): nat :=
  n.

Instance HashNat : Hash nat :=
  {
    hash := nat_hash
  }.