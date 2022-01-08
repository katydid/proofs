(*
compare_nat contains comparable_nat,
which is a instance of comparable for nat.
*)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Coq.Lists.List.

Require Import CoqStock.Cmp.

Definition nat_compare := Nat.compare.

Lemma nat_proof_compare_eq_implies_equal:
  forall (x y: nat)
         (p: nat_compare x y = Eq),
    x = y.
Proof.
induction x, y.
- compute. trivial.
- compute. intros. discriminate.
- compute. intros. discriminate.
- simpl.
  intros.
  remember (IHx y p).
  rewrite e.
  reflexivity.
Qed.

Lemma nat_proof_compare_eq_implies_equal' x y:
  nat_compare x y = Eq ->
  x = y.
Proof.
(* Because of how the lemma is stated, `x' and `y' are already introduced into
   the context, causing our inductive hypothesis to become too weak to solve the
   goal. `generalize dependent y' returns `y' to the goal and makes sure any
   dependent terms are updated. *)
generalize dependent y.
induction x, y.
- compute. trivial.
- compute. intros. discriminate.
- compute. intros. discriminate.
- simpl.
  intros.
  remember (IHx y H).
  rewrite e.
  reflexivity.
Qed.

Lemma nat_proof_compare_eq_reflex
  : forall (x: nat)
  , nat_compare x x = Eq.
Proof.
induction x.
- reflexivity.
- cbn. assumption.
Qed.

Lemma nat_proof_compare_eq_trans
  : forall (x y z: nat)
           (p: nat_compare x y = Eq)
           (q: nat_compare y z = Eq)
  , nat_compare x z = Eq.
Proof.
unfold nat_compare.
intros.
rewrite PeanoNat.Nat.compare_eq_iff in *.
subst.
reflexivity.
Qed.

Lemma nat_proof_compare_lt_trans
  : forall (x y z: nat)
           (p: nat_compare x y = Lt)
           (q: nat_compare y z = Lt)
  , nat_compare x z = Lt.
Proof.
unfold nat_compare.
intros.
rewrite PeanoNat.Nat.compare_lt_iff in *.
exact (PeanoNat.Nat.lt_trans x y z  p q).
Qed.

Lemma nat_proof_compare_gt_trans
  : forall (x y z: nat)
           (p: nat_compare x y = Gt)
           (q: nat_compare y z = Gt)
  , nat_compare x z = Gt.
Proof.
unfold nat_compare.
intros.
rewrite PeanoNat.Nat.compare_gt_iff in *.
exact (PeanoNat.Nat.lt_trans z y x q p).
Qed.

#[export]
Instance CmpNat : Cmp nat :=
  { compare := nat_compare
  ; proof_compare_eq_implies_equal := nat_proof_compare_eq_implies_equal
  ; proof_compare_eq_reflex := nat_proof_compare_eq_reflex
  ; proof_compare_eq_trans := nat_proof_compare_eq_trans
  ; proof_compare_lt_trans := nat_proof_compare_lt_trans
  ; proof_compare_gt_trans := nat_proof_compare_gt_trans
  }.

Theorem nat_compare_is_compare:
  forall
    {x y: nat}
    {c: comparison},
  Nat.compare x y = c <-> compare x y = c.
Proof.
split; intros; assumption.
Qed.

Ltac rewrite_nat_compare_to_compare :=
  repeat match goal with
  | [ |- context [Nat.compare _ _]] =>
    rewrite nat_compare_is_compare
  | [ H: context [Nat.compare _ _]|- _ ] =>
    rewrite nat_compare_is_compare in H
  end.

Example example_nat_compare_to_compare:
  forall
    {x y: nat}
    (H: Nat.compare x y = Gt),
  Nat.compare y x = Lt.
Proof.
intros.
rewrite_nat_compare_to_compare.
apply compare_gt_lt_symm.
assumption.
Qed.