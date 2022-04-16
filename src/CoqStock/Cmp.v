Require Import Coq.Setoids.Setoid.

Class Cmp (A : Type) :=
  { compare : A -> A -> comparison (* Eq | Lt | Gt *)

  ; proof_compare_eq_implies_equal
    : forall (x y: A)
             (p: compare x y = Eq)
    , x = y
  ; proof_compare_eq_reflex
    : forall (x: A)
    , compare x x = Eq
  ; proof_compare_eq_trans
    : forall (x y z: A)
             (xy: compare x y = Eq)
             (yz: compare y z = Eq)
    , compare x z = Eq
  ; proof_compare_lt_trans
    : forall (x y z: A)
             (xy: compare x y = Lt)
             (yz: compare y z = Lt)
    , compare x z = Lt
  ; proof_compare_gt_trans
    : forall (x y z: A)
             (xy: compare x y = Gt)
             (yz: compare y z = Gt)
    , compare x z = Gt
  }.

Definition compare_leq {A: Type} {cmp: Cmp A} (x y: A) : Prop :=
  (compare x y = Eq) \/ (compare x y = Lt).

Theorem compare_eq_is_equal
  : forall {A: Type} {c: Cmp A} (x y: A)
  , compare x y = Eq <-> x = y.
Proof.
intros; split.
- apply proof_compare_eq_implies_equal.
- intros. rewrite H.
  remember (compare y y) as iH.
  symmetry in HeqiH.
  induction iH.
  + reflexivity.
  + set (proof_compare_eq_reflex y).
    rewrite e in HeqiH.
    discriminate.
  + set (proof_compare_eq_reflex y).
    rewrite e in HeqiH.
    discriminate.
Qed.

Theorem compare_eq_is_equal_r
  : forall {A: Type} {c: Cmp A} (x y: A)
  , Eq = compare x y <-> x = y.
Proof.
intros; split; intros.
- symmetry in H. apply compare_eq_is_equal in H. assumption.
- symmetry. apply compare_eq_is_equal. assumption.
Qed.

Ltac comparison_symmetry :=
  match goal with
  | [ H_Eq_Compare : Eq = Eq |- _ ] =>
    clear H_Eq_Compare
  | [ H_Eq_Compare : Eq = Lt |- _ ] =>
    discriminate
  | [ H_Eq_Compare : Eq = Gt |- _ ] =>
    discriminate
  | [ H_Eq_Compare : Lt = Eq |- _ ] =>
    discriminate
  | [ H_Eq_Compare : Lt = Lt |- _ ] =>
    clear H_Eq_Compare
  | [ H_Eq_Compare : Lt = Gt |- _ ] =>
    discriminate
  | [ H_Eq_Compare : Gt = Eq |- _ ] =>
    discriminate
  | [ H_Eq_Compare : Gt = Lt |- _ ] =>
    discriminate
  | [ H_Eq_Compare : Gt = Gt |- _ ] =>
    clear H_Eq_Compare
  | [ H_Eq_Compare : Eq = ?Compare |- _ ] =>
    symmetry in H_Eq_Compare
  | [ H_Eq_Compare : Lt = ?Compare |- _ ] =>
    symmetry in H_Eq_Compare
  | [ H_Eq_Compare : Gt = ?Compare |- _ ] =>
    symmetry in H_Eq_Compare
  | [ |- Eq = Eq ] =>
    reflexivity
  | [ |- Lt = Lt ] =>
    reflexivity
  | [ |- Gt = Gt ] =>
    reflexivity
  end.

Ltac compare_symmetry :=
  comparison_symmetry
  || match goal with
  | [ |- context [compare ?X ?X] ] =>
    rewrite proof_compare_eq_reflex
  end.

Theorem gt_reflex_discriminate:
  forall
    {A: Type}
    {c: Cmp A}
    {x: A}
    (H: compare x x = Gt),
  False.
Proof.
intros.
specialize (proof_compare_eq_reflex x) as H0.
rewrite H in H0.
discriminate.
Qed.

Theorem lt_reflex_discriminate:
  forall
    {A: Type}
    {c: Cmp A}
    {x: A}
    (H: compare x x = Lt),
  False.
Proof.
intros.
specialize (proof_compare_eq_reflex x) as H0.
rewrite H in H0.
discriminate.
Qed.

Theorem gt_contradiction:
  forall
    {A: Type}
    {c: Cmp A}
    {x y: A}
    (H1: compare x y = Gt)
    (H2: compare y x = Gt),
  False.
Proof.
intros.
specialize (gt_reflex_discriminate (proof_compare_gt_trans _ _ _ H1 H2)).
easy.
Qed.

Theorem lt_contradiction:
  forall
    {A: Type}
    {c: Cmp A}
    {x y: A}
    (H1: compare x y = Lt)
    (H2: compare y x = Lt),
  False.
Proof.
intros.
specialize (lt_reflex_discriminate (proof_compare_lt_trans _ _ _ H1 H2)).
easy.
Qed.


(* If there is a pair of hypotheses
          compare ?x0 ?x1 = Gt   and   compare ?x0 ?x1 = Lt (or = Eq)
       then this tactic derives a contradiction.
 *)
Ltac compare_contradiction :=
  repeat compare_symmetry;
  match goal with
  | [ H1: compare ?x0 ?x1 = Gt , H2: compare ?x0 ?x1 = Lt |- _ ]
    => exfalso; assert (Gt = Lt); try (rewrite <- H1; rewrite <- H2; reflexivity); discriminate
  | [ H1: compare ?x0 ?x1 = Gt , H2: compare ?x0 ?x1 = Eq |- _ ]
    => exfalso; assert (Gt = Eq); try (rewrite <- H1; rewrite <- H2; reflexivity); discriminate
  | [ H1: compare ?x0 ?x1 = Eq , H2: compare ?x0 ?x1 = Lt |- _ ]
    => exfalso; assert (Eq = Lt); try (rewrite <- H1; rewrite <- H2; reflexivity); discriminate

    | [ H1: compare ?x0 ?x0 = Gt |- _ ]
    => exfalso; specialize (gt_reflex_discriminate H1); easy
  | [ H1: compare ?x0 ?x0 = Lt |- _ ]
    => exfalso; specialize (lt_reflex_discriminate H1); easy
  | [ H1: compare ?x0 ?x1 = Gt , H2: compare ?x1 ?x0 = Gt |- _ ]
    => exfalso; specialize (gt_contradiction H1 H2); easy
  | [ H1: compare ?x0 ?x1 = Lt , H2: compare ?x1 ?x0 = Lt |- _ ]
    => exfalso; specialize (lt_contradiction H1 H2); easy
  | [ H1: compare_leq ?x0 ?x1, H2: compare ?x0 ?x1 = Gt |- _ ]
    => destruct H1; compare_contradiction
  end.

Ltac comparison_contradiction F :=
  repeat comparison_symmetry;
  match goal with
  | [ H1: F ?x0 ?x1 = Gt , H2: F ?x0 ?x1 = Lt |- _ ]
    => exfalso; assert (Gt = Lt); try (rewrite <- H1; rewrite <- H2; reflexivity); discriminate
  | [ H1: F ?x0 ?x1 = Gt , H2: F ?x0 ?x1 = Eq |- _ ]
    => exfalso; assert (Gt = Eq); try (rewrite <- H1; rewrite <- H2; reflexivity); discriminate
  | [ H1: F ?x0 ?x1 = Eq , H2: F ?x0 ?x1 = Lt |- _ ]
    => exfalso; assert (Eq = Lt); try (rewrite <- H1; rewrite <- H2; reflexivity); discriminate
  end.

Theorem example_gt_reflex_discriminate:
  forall
    {A: Type}
    (c: Cmp A)
    (x: A)
    (H: compare x x = Gt),
  False.
Proof.
intros.
compare_contradiction.
Qed.

Example example_gt_contradiction:
  forall
    {A: Type}
    (c: Cmp A)
    (x y: A)
    (H1: compare x y = Gt)
    (H2: compare y x = Gt),
  False.
Proof.
intros.
compare_contradiction.
Qed.

Example example_gt_lt_contradiction:
  forall
    {A: Type}
    (c: Cmp A)
    (x y: A)
    (H1: compare x y = Lt)
    (H2: compare x y = Gt),
  False.
Proof.
intros.
comparison_contradiction compare.
Qed.


(* compare_to_eq turns an hypothesis or goal:
  `Eq = compare x y` or `compare x y = Eq` into:
into:
  `x = y`
  and in the case of the hypothesis tries to rewrite with it.
*)
Ltac compare_to_eq :=
  repeat compare_symmetry;
  match goal with
  | [ H_Eq_Compare : compare ?X ?Y = Eq |- _ ] =>
    rewrite compare_eq_is_equal in H_Eq_Compare;
    try (rewrite H_Eq_Compare)
  | [ |- context [compare ?X ?Y = Eq] ] =>
    rewrite compare_eq_is_equal
  | [ |- context [Eq = compare ?X ?Y] ] =>
    rewrite compare_eq_is_equal_r
  end.

Lemma test_tactic_compare_to_eq
  : forall {A: Type}
           {cmp: Cmp A}
           (x y: A)
           (p: Eq = compare x y),
  x = y.
Proof.
intros.
compare_to_eq.
reflexivity.
Qed.

Ltac induction_on_compare_Heqc :=
  (* remember (compare a b) =>
    [
    c: comparison
    Heqc: c = compare a b
    |- _ ]
  *)
  match goal with
  | [ C: comparison |- _ ] =>
    induction C; [ (* Eq *) compare_to_eq | (* Lt *) | (* Gt *)]; repeat compare_symmetry
      ; repeat compare_contradiction
  end
.

Ltac induction_on_compare_goal :=
  (*
  Find an expression (compare ?X ?Y)
  inside the goal and remember it.
  *)
  match goal with
  | [ |- context [(compare ?X ?Y)] ] =>
    remember (compare X Y)
  end;
  induction_on_compare_Heqc
.

Ltac induction_on_compare_in H :=
  (*
  Find an expression (compare ?X ?Y)
  inside the goal and remember it.
  *)
  match goal with
  | [H: context [compare ?X ?Y] |- _ ] =>
    remember (compare X Y)
  end;
  induction_on_compare_Heqc
.

Ltac induction_on_comparison_Heqc :=
  (* remember (compare a b) =>
    [
    c: comparison
    Heqc: c = compare a b
    |- _ ]
  *)
  match goal with
  | [ C: comparison |- _ ] =>
    induction C; [ (* Eq *) | (* Lt *) | (* Gt *)]
    ; repeat comparison_symmetry
    ; repeat (comparison_contradiction compare)
  end
.

Ltac induction_on_comparison_goal F X Y :=
  match goal with
  | [ |- context [F X Y]] =>
    remember (F X Y)
  end;
  induction_on_comparison_Heqc
.

Ltac induction_on_comparison_in F X Y H :=
  match goal with
  | [H: context [F X Y] |- _] =>
    remember (F X Y)
  end;
  induction_on_comparison_Heqc
.

(* induction_on_compare starts induction on a `compare` expression in the goal.
   It makes sense to remember this comparison, so that it be rewritten to an
   equality in the Eq induction goal.
*)
Tactic Notation "induction_on_compare" := induction_on_compare_goal.
Tactic Notation "induction_on_compare" "in" hyp(H) := induction_on_compare_in H.

(* induction_on_comparison is like induction_on_compare, but doesn't assume that the function is called compare or has any proofs associated with it.
  This tactic is useful when proving that a new compare function is an instance of Cmp.
*)
Tactic Notation "induction_on_comparison" constr(F) constr(X) constr(Y) := induction_on_comparison_goal F X Y.
Tactic Notation "induction_on_comparison" constr(F) constr(X) constr(Y) "in" hyp(H) := induction_on_comparison_in F X Y H.

Theorem proof_compare_eq_symm
  : forall {A: Type}
           {cmp: Cmp A}
           (x y: A)
           (p: compare x y = Eq)
  , compare y x = Eq.
Proof.
intros.
assert (p1 := p).
apply proof_compare_eq_implies_equal in p.
rewrite p.
rewrite p in p1.
assumption.
Qed.

Theorem compare_eq_is_only_equal
  : forall {A: Type}
           {cmp: Cmp A}
           (x1 x2: A)
           (p: compare x1 x2 = compare x2 x1)
  , compare x1 x2 = Eq.
Proof.
intros.
induction_on_compare.
Qed.

(* Test for induction_on_comparison_in  *)
Example test_compare_Nat_eq_is_only_equal_goal
  : forall (x1 x2: nat)
           (q: Nat.compare x1 x2 <> Eq -> Nat.compare x1 x2 <> Nat.compare x2 x1)
           (p: Nat.compare x1 x2 = Nat.compare x2 x1)
  , Nat.compare x1 x2 = Eq.
Proof.
intros.
induction_on_comparison Nat.compare x1 x2 in p.
- assert (Lt <> Eq). discriminate.
  specialize (q H) as q.
  symmetry in p.
  contradiction.
- assert (Gt <> Eq). discriminate.
  specialize (q H) as q.
  symmetry in p.
  contradiction.
Qed.

(* Test for induction_on_comparison_goal  *)
Example test_compare_Nat_eq_is_only_equal_in
  : forall (x1 x2: nat)
           (q: Nat.compare x1 x2 <> Eq -> Nat.compare x1 x2 <> Nat.compare x2 x1)
           (p: Nat.compare x1 x2 = Nat.compare x2 x1)
  , Nat.compare x1 x2 = Eq.
Proof.
intros.
induction_on_comparison Nat.compare x1 x2.
- assert (Lt <> Eq). discriminate.
  specialize (q H) as q.
  symmetry in p.
  contradiction.
- assert (Gt <> Eq). discriminate.
  specialize (q H) as q.
  symmetry in p.
  contradiction.
Qed.

Theorem compare_lt_not_symm_1
  : forall {A: Type}
           {cmp: Cmp A}
           (x1 x2: A)
           (c12: compare x1 x2 = Lt)
           (c21: compare x2 x1 = Lt)
  , False.
Proof.
intros.
assert (p1 := proof_compare_lt_trans x1 x2 x1 c12 c21).
assert (p2 := proof_compare_eq_reflex x1).
rewrite p1 in p2.
discriminate.
Qed.

Theorem compare_lt_not_symm_2
  : forall {A: Type}
           {cmp: Cmp A}
           (x1 x2: A)
           (c12: compare x1 x2 = Lt)
           (c21: compare x2 x1 = Lt)
  , False.
Proof.
intros.
assert (c := c21).
rewrite <- c12 in c.
apply compare_eq_is_only_equal in c.
rewrite c21 in c.
discriminate.
Qed.

Theorem compare_gt_not_symm
  : forall {A: Type}
           {cmp: Cmp A}
           (x1 x2: A)
           (c12: compare x1 x2 = Gt)
           (c21: compare x2 x1 = Gt)
  , False.
Proof.
intros.
assert (c := c12).
rewrite <- c21 in c.
apply compare_eq_is_only_equal in c.
rewrite c12 in c.
discriminate.
Qed.

(* Also severves as an example of how to prove using induction on compare, without using the induction_on_compare tactic *)
Theorem compare_lt_gt_symm
  : forall {A: Type}
           {cmp: Cmp A}
           (x1 x2: A)
           (p: compare x1 x2 = Lt)
  , compare x2 x1 = Gt.
Proof.
intros.
remember (compare x2 x1) as iH.
symmetry in HeqiH.
induction iH.
- apply proof_compare_eq_symm in HeqiH.
  rewrite HeqiH in p.
  discriminate.
- assert (a := proof_compare_lt_trans x1 x2 x1 p HeqiH).
  rewrite proof_compare_eq_reflex in a.
  discriminate.
- reflexivity.
Qed.

Theorem compare_gt_lt_symm
  : forall {A: Type}
           {cmp: Cmp A}
           (x1 x2: A)
           (p: compare x1 x2 = Gt)
  , compare x2 x1 = Lt.
Proof.
intros.
induction_on_compare.
rewrite Heqc in p.
compare_contradiction.
Qed.

Theorem proof_compare_anti_symm
  : forall {A: Type} {c: Cmp A} (x y : A)
  , compare x y = CompOpp (compare y x).
Proof.
intros.
induction_on_compare.
- constructor.
- apply compare_lt_gt_symm in Heqc0.
  rewrite Heqc0.
  constructor.
- apply compare_gt_lt_symm in Heqc0.
  rewrite Heqc0.
  constructor.
Qed.

Lemma compare_leq_trans {A: Type} {cmp: Cmp A} (x y z: A) :
  (compare_leq x y) -> (compare_leq y z) -> (compare_leq x z).
Proof.
intros.
unfold compare_leq in *.

destruct H; destruct H0;
  try ((left; apply proof_compare_eq_trans with (y0 := y); assumption)
        || (right; apply proof_compare_lt_trans with (y0 := y); assumption));
  try (compare_to_eq; subst);
  try (left; assumption);
  try (right; assumption).
Qed.

Lemma compare_lt_leq_trans {A: Type} {cmp: Cmp A} (x y z: A) :
  (compare x y = Lt)
    -> (compare_leq y z)
    -> (compare x z = Lt).
Proof.
intros H1 H2.
destruct H2 as [H2 | H2].
- compare_to_eq.
  subst. assumption.
- apply proof_compare_lt_trans with (y0 := y); assumption.
Qed.

Lemma compare_leq_reflex {A: Type} {cmp: Cmp A} (x : A) :
  (compare_leq x x).
Proof.
intros.
unfold compare_leq.
left.
apply proof_compare_eq_reflex.
Qed.

Lemma compare_eq_dec {A: Type} {cmp: Cmp A} (x y : A):
  {x = y} + {x <> y}.
Proof.
destruct (compare x y) eqn:Heqc;
  try (right;
        unfold not; intro;
        subst;
        rewrite proof_compare_eq_reflex in Heqc;
        discriminate).
- compare_to_eq.
  left.
  reflexivity.
Qed.
