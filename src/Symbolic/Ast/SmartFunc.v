Require Import CoqStock.List.

Require Import Symbolic.Ast.Func.

(* For the hash field to mean anything, it needs an associated property that it was constructed using a smart constructor:
*)

Inductive IsSmart (f: Func): Prop :=
| isSmart: forall
    (name: nat)
    (params: list Func)
    (hash: nat)
  ,   f = mkFunc name params hash
  ->  hash = hash_from_func f
  ->  Forall IsSmart params
  ->  IsSmart f
.

Ltac destructIsSmart S :=
  let Name := fresh "name" in
  let Params := fresh "params" in
  let Hash := fresh "hash" in
  let Feq := fresh "feq" in
  let Heq := fresh "heq" in
  let HSmarts := fresh "Hsmarts" in
  destruct S as [Name Params Hash Feq Heq HSmarts].

Definition SmartFunc := { func | IsSmart func }.

Ltac destructSmartFunc SF :=
  let F := fresh "f" in
  let S := fresh "s" in
  destruct SF as [F S];
  destructIsSmart S.

Definition get_func (x: SmartFunc): Func :=
  match x with
  | exist _ f p => f
  end.

Definition get_shash (x: SmartFunc): nat :=
  match x with
  | exist _ f p => get_hash f
  end.

Definition hash_from_params (hname: nat) (params: list Func): nat :=
  let param_hashes := map hash_from_func params in
  fold_left hash_per_elem param_hashes hname.

Definition hash_from_sparams (hname: nat) (sparams: list SmartFunc): nat :=
  let param_hashes := map get_shash sparams in
  fold_left hash_per_elem param_hashes hname.

Lemma hash_from_params_is_hash_from_sparams:
  forall (hname: nat) (sparams: list SmartFunc),
    hash_from_sparams hname sparams
    =
    hash_from_params hname (map get_func sparams).
Proof.
intros.

(* induction on params *)
generalize dependent hname.
induction sparams as [| sp sps].
- reflexivity.
- intros.

  (* step hash_from_params *)
  unfold hash_from_params.
  cbn [map].
  cbn [fold_left].
  assert (
    fold_left
      hash_per_elem
      (map hash_from_func (map get_func sps))
      (hash_per_elem hname (hash_from_func (get_func sp)))
    =
      hash_from_params (31 * hname + (get_shash sp)) (map get_func sps)
  ) as Hfunc.
+ destructSmartFunc sp.
  cbn [get_func].
  cbn [get_shash].
  unfold hash_from_params.
  unfold hash_per_elem.
  rewrite <- heq.
  rewrite feq.
  cbn [get_hash].
  reflexivity.
+ rewrite Hfunc. clear Hfunc.

  (* step hash_from_sparams *)
  unfold hash_from_sparams.
  cbn [map].
  cbn [fold_left].
  assert (
    fold_left
      hash_per_elem
      (map get_shash sps)
      (hash_per_elem hname (get_shash sp))
    =
      hash_from_sparams (31 * hname + (get_shash sp)) sps
  ) as HsmartFunc.
* destructSmartFunc sp.
  cbn [get_shash].
  unfold hash_from_sparams.
  rewrite feq.
  cbn [get_hash].
  unfold hash_per_elem.
  reflexivity.
* rewrite HsmartFunc. clear HsmartFunc.
  apply IHsps.
Qed.

Lemma forall_smart_from_sparams
  (sparams: list SmartFunc):
  Forall IsSmart (map get_func sparams).
Proof.
induction sparams as [| p ps].
- cbn. constructor.
- cbn.
  destruct p as [f s].
  cbn.
  constructor.
  + exact s.
  + exact IHps.
Qed.

Lemma smart_from_sparam
  (s: SmartFunc):
  IsSmart (get_func s).
Proof.
destructSmartFunc s.
cbn.
apply (isSmart f name params hash); assumption.
Qed.

Lemma is_smart (name: nat) (sparams: list SmartFunc):
  IsSmart
    (mkFunc
      name
      (map get_func sparams)
      (hash_from_sparams (31 * 17 * name) sparams)
    ).
Proof.
induction sparams as [| p ps].
- cbn [map].
  apply (isSmart _ name [] (hash_from_sparams (31 * 17 * name) [])).
  + reflexivity.
  + reflexivity.
  + constructor.
- apply (isSmart _ name (map get_func (p :: ps)) (hash_from_params (31 * 17 * name) (map get_func (p::ps)))).
  + rewrite hash_from_params_is_hash_from_sparams. reflexivity.
  + unfold hash_from_params.
    unfold hash_from_func.
    fold hash_from_func.
    reflexivity.
  + apply forall_smart_from_sparams.
Qed.

Definition mkSmartFunc (name: nat) (sparams: list SmartFunc): SmartFunc :=
exist
  _
  (mkFunc
    name
    (map get_func sparams)
    (hash_from_sparams
      (31 * 17 * name)
      sparams
    )
  )
  (is_smart
    name
    sparams
  )
.


(*
We can reconstruct our list of SmartFunc again from our list of params and the Forall property.
*)

Definition getSmartParamsFromMkFunc (name : nat) (params : list Func) (hash : nat)
  (is : IsSmart (mkFunc name params hash)): Forall IsSmart params :=
match is with
| isSmart _ _ _ _ feq _ Hsmarts =>
  eq_ind_r
    (fun params' : list Func => Forall IsSmart params')
    Hsmarts
    (f_equal get_params feq)
end.

Definition get_smart_sig_params (s : SmartFunc): {params : list Func | Forall IsSmart params} :=
let (f, is) := s in
match f as f' return (IsSmart f' -> {params : list Func | Forall IsSmart params}) with
| mkFunc name params hash =>
  (fun (is' : IsSmart (mkFunc name params hash)) =>
    exist
      (fun params' : list Func => Forall IsSmart params')
      params
      (getSmartParamsFromMkFunc name params hash is')
  )
end is.

Definition Forall_cons_if
  {A : Type} {P : A -> Prop} (x : A) (xs : list A)
  (HForall : Forall P (x :: xs)): P x /\ Forall P xs :=
match
  HForall in (Forall _ xxs) return (xxs = x :: xs -> P x /\ Forall P xs)
with
| Forall_nil _ =>
	fun Heq_refl : [] = x :: xs =>
    False_ind (P x /\ Forall P xs) (
      eq_ind []
        (fun e : list A => match e with
                           | [] => True
                           | _ :: _ => False
                           end) I (x :: xs) Heq_refl
    )
| @Forall_cons _ _ x' xs' Px' Pxs' =>
    fun Heq_refl : x' :: xs' = x :: xs =>
    let xeq : x' = x :=
      f_equal (fun e : list A => match e with
                                 | [] => x'
                                 | a :: _ => a
                                 end) Heq_refl in
    (let xseq : xs' = xs :=
       f_equal (fun e : list A => match e with
                                  | [] => xs'
                                  | _ :: l => l
                                  end) Heq_refl in
      eq_ind xs' (fun xs'' : list A => P x /\ Forall P xs'')
        (eq_ind x' (fun x'' : A => P x'' /\ Forall P xs')
          (conj Px' Pxs') x xeq)
        xs xseq)
end eq_refl.

Fixpoint zip_list_of_smart_params
  (params : list Func)
  (smarts : Forall IsSmart params):
  list SmartFunc :=
  match params as ps return (Forall IsSmart ps -> list SmartFunc) with
  | [] => fun _ : Forall IsSmart [] => []
  | p :: ps => fun (smarts' : Forall IsSmart (p :: ps))
      =>
        match (Forall_cons_if p ps smarts': IsSmart p /\ Forall IsSmart ps) with
        | conj sp sps => (exist _ p sp) :: (zip_list_of_smart_params ps sps)
        end
  end smarts.

Definition get_smart_params (s : SmartFunc): list SmartFunc :=
  let (params, Hsmarts) := get_smart_sig_params s in
  zip_list_of_smart_params params Hsmarts.

Theorem get_smart_params_is_correct:
  forall (s: SmartFunc),
  map get_func (get_smart_params s)
  =
  get_params (get_func s)
.
Proof.
intros.
destruct s as [f is].
destruct f.
cbn [get_func].
cbn [get_params].
unfold get_smart_params.
unfold get_smart_sig_params.
unfold getSmartParamsFromMkFunc.
destructIsSmart is.
injection feq.
intros.
subst params0.
subst name0.
rewrite <- H in heq.
subst hash0.
clear heq.
induction params as [| p ps].
- reflexivity.
- cbn.
  destruct Forall_cons_if as [sp sps].
  cbn.
  apply list_cons_eq.
  split.
  + reflexivity.
  + specialize (IHps eq_refl sps).
    rewrite <- IHps.
    cbn.
    reflexivity.
Qed.