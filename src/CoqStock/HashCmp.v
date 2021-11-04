(*
hash_compare is a faster alternative comparison function.
It compares the hashes of two elements and only does a deep compare
if the hashes are equal.
*)

Require Import CoqStock.Cmp.
Require Import CoqStock.CmpNat.
Require Import CoqStock.Hash.

Definition hash_compare {A: Type} {c: Cmp A} {h: Hash A} (x y: A) : comparison :=
  match compare (hash x) (hash y) with
  | Eq => compare x y
  | Lt => Lt
  | Gt => Gt
  end.

Theorem hash_compare_proof_compare_eq_is_equal
  : forall
    {A: Type}
    {c: Cmp A}
    {h: Hash A}
    (x y: A)
    (p: hash_compare x y = Eq)
  , x = y.
Proof.
unfold hash_compare.
intros A c h x y.
induction_on_compare.
- intros.
  apply proof_compare_eq_is_equal.
  assumption.
- discriminate.
- discriminate.
Qed.

Theorem hash_compare_proof_compare_eq_reflex
  : forall
    {A: Type}
    {c: Cmp A}
    {h: Hash A}
    (x: A)
  , hash_compare x x = Eq.
Proof.
intros.
unfold hash_compare.
remember (@hash A _ x) as hash_x.
specialize (@proof_compare_eq_reflex nat CmpNat) with (x := hash_x).
intros.
rewrite H.
apply proof_compare_eq_reflex.
Qed.

Theorem hash_compare_proof_compare_eq_trans
  : forall
    {A: Type}
    {c: Cmp A}
    {h: Hash A}
    (x y z: A)
    (xy: hash_compare x y = Eq)
    (yz: hash_compare y z = Eq)
  , hash_compare x z = Eq.
Proof.
unfold hash_compare.
intros A c h x y z.
induction_on_compare; induction_on_compare; try discriminate.
intros.
assumption.
Qed.

Theorem hash_compare_proof_compare_lt_trans
  : forall
    {A: Type}
    {c: Cmp A}
    {h: Hash A}
    (x y z: A)
    (xy: hash_compare x y = Lt)
    (yz: hash_compare y z = Lt)
  , hash_compare x z = Lt.
Proof.
unfold hash_compare.
intros A c h x y z.
induction_on_compare; induction_on_compare; try discriminate.
- intros; induction_on_compare; try discriminate; try reflexivity.
  specialize proof_compare_lt_trans with (x := x) (y := y) (z := z) as T.
  symmetry in Heqc1.
  exact (T Heqc1 yz).
- rewrite <- Heq.
  rewrite <- Heqc0.
  reflexivity.
- remember (@hash A _ x) as hash_x.
  remember (@hash A _ y) as hash_y.
  remember (@hash A _ z) as hash_z.
  specialize (@proof_compare_lt_trans nat CmpNat) with (x := hash_x) (y := hash_y) (z := hash_z) as HT.
  intros.
  symmetry in Heqc0.
  symmetry in Heqc1.
  remember (HT Heqc0 Heqc1).
  rewrite e.
  reflexivity.
Qed.

Theorem hash_compare_proof_compare_gt_trans
  : forall
    {A: Type}
    {c: Cmp A}
    {h: Hash A}
    (x y z: A)
    (xy: hash_compare x y = Gt)
    (yz: hash_compare y z = Gt)
  , hash_compare x z = Gt.
Proof.
unfold hash_compare.
intros A c h x y z.
induction_on_compare; induction_on_compare; try discriminate.
- intros; induction_on_compare; try discriminate; try reflexivity.
  specialize proof_compare_gt_trans with (x := x) (y := y) (z := z) as T.
  symmetry in Heqc1.
  exact (T Heqc1 yz).
- rewrite <- Heq.
  rewrite <- Heqc0.
  reflexivity.
- remember (@hash A _ x) as hash_x.
  remember (@hash A _ y) as hash_y.
  remember (@hash A _ z) as hash_z.
  specialize (@proof_compare_gt_trans nat CmpNat) with (x := hash_x) (y := hash_y) (z := hash_z) as HT.
  intros.
  symmetry in Heqc0.
  symmetry in Heqc1.
  remember (HT Heqc0 Heqc1).
  rewrite e.
  reflexivity.
Qed.

Instance CmpHash {A: Type} {c: Cmp A} {h: Hash A}: Cmp A :=
  { compare := hash_compare
  ; proof_compare_eq_is_equal := hash_compare_proof_compare_eq_is_equal
  ; proof_compare_eq_reflex := hash_compare_proof_compare_eq_reflex
  ; proof_compare_eq_trans := hash_compare_proof_compare_eq_trans
  ; proof_compare_lt_trans := hash_compare_proof_compare_lt_trans
  ; proof_compare_gt_trans := hash_compare_proof_compare_gt_trans
  }.
