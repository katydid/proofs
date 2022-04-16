(* fequal tactic automates the application of the f_equal theorem. *)

Definition curry_2_to_4
  {A: Type} {B: Type} {C: Type} {D: Type} {E: Type}
  (f: A -> B -> C -> D -> E)
  (x1: A) (x3: C) (x4: D) (x2: B): E :=
f x1 x2 x3 x4.

Lemma curry_2_to_4_is_f:
  forall
  {A: Type} {B: Type} {C: Type} {D: Type} {E: Type}
  (f: A -> B -> C -> D -> E)
  (x1: A) (x2: B) (x3: C) (x4: D),
  curry_2_to_4 f x1 x3 x4 x2 = f x1 x2 x3 x4.
Proof.
intros.
unfold curry_2_to_4.
reflexivity.
Qed.

(* test rewrite with curry_2_to_4_is_f and applying f_equal. *)
Example test_curry_2_to_4:
  forall (a b x y z: bool)
  (f: bool -> bool -> bool -> bool -> bool)
  (H: a = b),
  f x a y z = f x b y z.
Proof.
intros.
rewrite <- curry_2_to_4_is_f.
rewrite <- (curry_2_to_4_is_f f x b y z).
apply f_equal.
exact H.
Qed.

(* TODO add more permuations and different numbers of parameters. *)
Ltac fequal :=
  match goal with
  | [ |- ?F ?X ?A ?Y ?Z = ?F ?X ?B ?Y ?Z ] =>
    rewrite <- (curry_2_to_4_is_f F X A Y Z);
    rewrite <- (curry_2_to_4_is_f F X B Y Z);
    apply f_equal
  end.

(* test rewrite with curry_2_to_4_is_f and applying f_equal  via the fequal tactic. *)
Example test_curry_2_to_4':
  forall (a b x y z: bool)
  (f: bool -> bool -> bool -> bool -> bool)
  (H: a = b),
  f x a y z = f x b y z.
Proof.
intros.
fequal.
exact H.
Qed.