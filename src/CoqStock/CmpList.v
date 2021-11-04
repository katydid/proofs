Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Coq.Lists.List.

Require Import CoqStock.Cmp.
Require Import CoqStock.CmpNat.
Require Import CoqStock.Listerine.
Require Import CoqStock.List.

Fixpoint list_compare {A: Type} {c: Cmp A} (xs: list A) (ys: list A) : comparison :=
  match xs with
  | nil => match ys with
      | nil => Eq
      | _ => Lt
      end
  | x :: xs => match ys with
      | nil => Gt
      | y :: ys => match compare x y with
          | Eq => list_compare xs ys
          | Lt => Lt
          | Gt => Gt
          end
      end
  end.

(* test_compare_list_nat simply tests whether nat can be used
   with a function that expects a comparable instance.
*)
Definition test_compare_list_nat : Prop :=
  list_compare (1 :: 2 :: nil) (1 :: 3 :: nil) = Lt.

Theorem list_proof_compare_eq_is_equal
  : forall
    {A: Type}
    {c: Cmp A}
    (xs ys: list A)
    (p: list_compare xs ys = Eq)
  , xs = ys.
Proof.
induction xs, ys.
- reflexivity.
- cbn. intros. discriminate.
- cbn. intros. discriminate.
- specialize IHxs with ys.
  autorewrite with list.
  cbn.
  induction_on_compare; intros; try discriminate.
  constructor.
  + reflexivity.
  + apply IHxs.
    exact H.
Qed.

Theorem list_proof_compare_eq_reflex
  : forall
    {A: Type}
    {c: Cmp A}
    (xs: list A)
  , list_compare xs xs = Eq.
Proof.
induction xs.
- cbn. reflexivity.
- cbn. induction_on_compare.
  + exact IHxs.
  + specialize proof_compare_eq_reflex with (x := a) as Heqc1.
    rewrite Heqc1 in Heqc0.
    discriminate.
  + specialize proof_compare_eq_reflex with (x := a) as Heqc1.
    rewrite Heqc1 in Heqc0.
    discriminate.
Qed.

Theorem list_proof_compare_eq_trans
  : forall
    {A: Type}
    {c: Cmp A}
    (xs ys zs: list A)
    (xy: list_compare xs ys = Eq)
    (yz: list_compare ys zs = Eq)
  , list_compare xs zs = Eq.
Proof.
induction xs, ys, zs; intros; try assumption.
- cbn. reflexivity.
- cbn in xy. discriminate.
- generalize dependent yz.
  generalize dependent xy.
  cbn.
  induction_on_compare; induction_on_compare; (try (intros; discriminate)).
  + intros.
    specialize IHxs with (ys := ys) (zs := zs).
    apply IHxs.
    exact xy.
    exact yz.
Qed.

Theorem list_proof_compare_lt_trans
  : forall
    {A: Type}
    {c: Cmp A}
    (xs ys zs: list A)
    (xy: list_compare xs ys = Lt)
    (yz: list_compare ys zs = Lt)
  , list_compare xs zs = Lt.
Proof.
induction xs, ys, zs; intros; try assumption.
- cbn in xy. discriminate.
- cbn in xy. discriminate.
- generalize dependent yz.
  generalize dependent xy.
  cbn.
  specialize IHxs with (ys := ys) (zs := zs).
  rename a into x; rename a0 into y; rename a1 into z.
  induction_on_compare; induction_on_compare; try discriminate.
  + exact IHxs.
  + reflexivity.
  + rewrite <- Heq.
    intros.
    induction_on_compare; try discriminate; assumption.
  + specialize proof_compare_lt_trans with x y z as T.
    symmetry in Heqc0, Heqc1.
    remember (T Heqc0 Heqc1).
    rewrite e.
    reflexivity.
Qed.

Theorem list_proof_compare_gt_trans
  : forall
    {A: Type}
    {c: Cmp A}
    (xs ys zs: list A)
    (xy: list_compare xs ys = Gt)
    (yz: list_compare ys zs = Gt)
  , list_compare xs zs = Gt.
Proof.
induction xs, ys, zs; intros; try assumption.
- cbn in xy. discriminate.
- cbn in xy. discriminate.
- generalize dependent yz.
  generalize dependent xy.
  cbn.
  specialize IHxs with (ys := ys) (zs := zs).
  rename a into x; rename a0 into y; rename a1 into z.
  induction_on_compare; induction_on_compare; try discriminate.
  + exact IHxs.
  + reflexivity.
  + rewrite <- Heq.
    intros.
    induction_on_compare; try discriminate; assumption.
  + specialize proof_compare_gt_trans with x y z as T.
    symmetry in Heqc0, Heqc1.
    remember (T Heqc0 Heqc1).
    rewrite e.
    reflexivity.
Qed.

Instance CmpList {A: Type} {c: Cmp A}: Cmp (list A) :=
  { compare := list_compare
  ; proof_compare_eq_is_equal := list_proof_compare_eq_is_equal
  ; proof_compare_eq_reflex := list_proof_compare_eq_reflex
  ; proof_compare_eq_trans := list_proof_compare_eq_trans
  ; proof_compare_lt_trans := list_proof_compare_lt_trans
  ; proof_compare_gt_trans := list_proof_compare_gt_trans
  }.
