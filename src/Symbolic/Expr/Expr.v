Require Import CoqStock.Cmp.
Require Import CoqStock.DubStep.
Require Import CoqStock.List.

(*
  Parsed is the all the parsed information about the expression.
  This includes the function name and the parameters.
*)
Inductive Parsed: Type :=
  mkParsed :
    forall
    (label: nat)
    (children: list Parsed),
  Parsed.

(* Parsed: Getters *)

Definition get_label (x: Parsed): nat :=
  match x with
  | mkParsed label _ => label
  end.

Definition get_children (x: Parsed): list Parsed :=
  match x with
  | mkParsed _ children => children
  end.

(* Parsed: Hash *)

Definition parsed_calculate_hash_per_elem (state: nat) (x: nat): nat :=
    31 * state + x.

Fixpoint parsed_calculate_hash_parsed (p: Parsed): nat :=
  match p with
  | mkParsed label children =>
    let label_hashed := 31 * 17 * label in
    let param_hashes := map parsed_calculate_hash_parsed children in
    fold_left parsed_calculate_hash_per_elem param_hashes label_hashed
  end.

(* Defined for the purpose of a generalized proof *)
Definition parsed_calculate_hash'' (label_hashed: nat) (children: list Parsed): nat :=
  let param_hashes := map parsed_calculate_hash_parsed children in
  fold_left parsed_calculate_hash_per_elem param_hashes label_hashed.

Definition parsed_calculate_hash' (label: nat) (children: list Parsed): nat :=
  parsed_calculate_hash'' (31 * 17 * label) children.

Definition parsed_calculate_hash (p: Parsed): nat :=
  match p with
  | mkParsed label children =>
    parsed_calculate_hash' label children
  end.

Lemma same_calculate_hash_parsed_as_calculate_hash:
  forall (label: nat) (children: list Parsed),
  parsed_calculate_hash' label children = parsed_calculate_hash_parsed (mkParsed label children).
Proof.
intros.
unfold parsed_calculate_hash.
unfold parsed_calculate_hash'.
unfold parsed_calculate_hash_parsed.
reflexivity.
Qed.

(*
  Info is the all the information about the Parsed expression.
  This is mostly used to efficiently compare two expressions.
  This includes a hash, a property about how the hash was calculated and whether the expression has a variable.
*)
Inductive Info: Type :=
  mkInfo:
    forall
    (name: nat)
    (params: list Info)
    (hasvar: bool)
    (hash: nat),
  Info.

(* Info: Getters *)

Definition get_name' (x: Info): nat :=
  match x with
  | mkInfo name _ _ _ => name
  end.

Definition get_params' (x: Info): list Info :=
  match x with
  | mkInfo _ params _ _ => params
  end.

Definition get_hasvar' (x: Info): bool :=
  match x with
  | mkInfo _ _ hasvar _ => hasvar
  end.

Definition get_hash' (x: Info): nat :=
  match x with
  | mkInfo _ _ _ hash => hash
  end.



(* Info: HasVar *)

Fixpoint any (xs: list bool): bool :=
  match xs with
  | [] => false
  | (x::xs) =>
    match x with
    | true => true
    | _ => any xs
    end
  end.

Definition has_var_info (params: list Info): bool :=
  let param_hasvars := map get_hasvar' params in
  any param_hasvars.

(* Info: Hash *)

Definition info_hash_per_elem (state: nat) (x: nat): nat :=
    31 * state + x.

Fixpoint info_calculate_hash_info (i: Info): nat :=
  match i with
  | mkInfo label children _ _ =>
    let label_hashed := 31 * 17 * label in
    let param_hashes := map info_calculate_hash_info children in
    fold_left info_hash_per_elem param_hashes label_hashed
  end.

Inductive IsSmart (i: Info): Prop :=
  | isSmart :
    get_hash' i = info_calculate_hash_info i ->
    Forall IsSmart (get_params' i) ->
    (* get_hasvar' i = true \/ get_hasvar' i = has_var_info (get_params' i) -> *)
  IsSmart i
  .

Definition has_var_smart_info (params: list {i: Info & IsSmart i}): bool :=
  let param_infos := map (fun s => projT1 s) params in
  let param_hasvars := map get_hasvar' param_infos in
  any param_hasvars.

Inductive SmartInfo: Type :=
  mkSmart:
    forall
    (info: Info)
    (smart: IsSmart info),
  SmartInfo.

(* Defined for the purpose of a generalized proof *)
Definition info_calculate_hash' (label_hashed: nat) (children: list Info): nat :=
  let param_hashes := map info_calculate_hash_info children in
  fold_left info_hash_per_elem param_hashes label_hashed.

Definition info_calculate_hash (label: nat) (children: list Info): nat :=
  info_calculate_hash' (31 * 17 * label) children.

Lemma same_calculate_hash_info_as_calculate_hash:
  forall (label: nat) (children: list Info) (hasvar: bool) (hash: nat),
  info_calculate_hash label children = info_calculate_hash_info (mkInfo label children hasvar hash).
Proof.
intros.
unfold info_calculate_hash.
unfold info_calculate_hash'.
unfold info_calculate_hash_info.
reflexivity.
Qed.

Definition info_hash' (name_hash: nat) (params: list Info) : nat :=
  let param_hashes := map get_hash' params in
  fold_left info_hash_per_elem param_hashes name_hash.

Definition info_hash (name: nat) (params: list Info): nat :=
  info_hash' (31 * 17 * name) params.

Lemma same_info_hash_as_calculate_hash':
  forall (name_hash: nat) (params: list Info) (smartParams: Forall IsSmart params),
    info_hash' name_hash params
    =
    info_calculate_hash' name_hash params.
Proof.
intros.

(* induction on params *)
generalize dependent name_hash.
rename params into is.
induction is; try reflexivity; intros.
rename a into i.

(* step info_hash' *)
unfold info_hash'; dubstep map; dubstep fold_left.
assert (
  fold_left
    info_hash_per_elem
    (map get_hash' is)
    (info_hash_per_elem name_hash (get_hash' i))
  =
    info_hash' (31 * name_hash + (get_hash' i)) is
) as Info.
unfold info_hash'; unfold info_hash_per_elem; reflexivity.
rewrite Info; clear Info.

(* step calculate_hash' *)
unfold info_calculate_hash'; dubstep map; dubstep fold_left.
assert (
  fold_left
    info_hash_per_elem
    (map info_calculate_hash_info is)
    (info_hash_per_elem name_hash (info_calculate_hash_info i))
  =
    info_calculate_hash' (31 * name_hash + (info_calculate_hash_info i)) is
) as Calculate.
unfold info_calculate_hash'. unfold info_hash_per_elem. reflexivity.
rewrite Calculate; clear Calculate.

assert (
  get_hash' i
  =
  info_calculate_hash_info i
) as Hash.
destruct i. simpl get_hash'.
inversion smartParams.
inversion H1.
rewrite <- H3.
unfold get_hash'.
reflexivity.
rewrite Hash.

apply IHis.
inversion smartParams.
assumption.
Qed.

Require Import CoqStock.Invs.

(*
Lemma same_info_hash_as_calculate_hash':
  forall (name_hash: nat) (params: list Info) (smartParams: Forall IsSmart params),
    info_hash' name_hash params
    =
    info_calculate_hash' name_hash params.
*)

(* fold_left info_hash_per_elem (map get_hash' l) label_hashed *)

(*
Definition info_calculate_hash' (label_hashed: nat) (children: list Info): nat :=
  (* let param_hashes := map info_calculate_hash_info children in *)
  fold_left info_hash_per_elem (map info_calculate_hash_info children) label_hashed.
*)

(*
Lemma same_calculate_hash_info_as_calculate_hash:
  forall (label: nat) (children: list Info) (hasvar: bool) (hash: nat),
  info_calculate_hash label children = info_calculate_hash_info (mkInfo label children hasvar hash).
*)

Definition smartInfo (name: nat) (params: list {i: Info & IsSmart i}): { i : Info & IsSmart i }.
exists (mkInfo name params (has_var_smart_info params) (info_hash name params)).
constructor.
- dubstep get_hash'.
  dubstep info_calculate_hash_info.
  induction smartChildren.
  + reflexivity.
  + induction H.
    dubstep map.
    rewrite <- H.
    unfold info_hash.
    unfold info_hash'.
    dubstep map.
    unfold info_hash in IHsmartChildren.
    unfold info_hash' in IHsmartChildren.
    dubstep fold_left.
    fold (info_calculate_hash' (info_hash_per_elem (31 * 17 * name) (get_hash' x)) l).
    rewrite <- same_info_hash_as_calculate_hash'.
    reflexivity.
    assumption.
- unfold get_params'.
  assumption.
Qed.

Fixpoint smartInfo_from_parsed (p: Parsed): { i : Info & IsSmart i }.
Proof.
  exists (match p with
  | mkParsed label children =>
    smartInfo label (map smartInfo_from_parsed children)
  end).
.

(*
Defintion was_created_from_smart_info (info: Info)

Lemma every_smart_info_comes:
  forall (name: nat) (params: list Info),
  (was_created_from_smart_info params) ->
  (smartInfo name params) =
  smartInfo_from_parsed (parsed_from_info (smartInfo name params)).
  *)

Theorem calculated_hash_is_equal_to_cached_hash:
  forall (p: Parsed),
  parsed_calculate_hash_parsed p =
  get_hash' (smartInfo_from_parsed p).
Proof.
destruct p.
induction children.
- reflexivity.
- dubstep parsed_calculate_hash_parsed.
  dubstep map.
  dubstep fold_left.
  dubstep smartInfo_from_parsed.
  dubstep map.




































(* Info: Smart Constructor *)

Definition smartInfoVar (name: nat) (params: list Info): SmartInfo.
refine (
  let parsed := mkParsed name (map get_parsed' params) in
  mkInfo name params true (info_hash name params) parsed _ _
).
- reflexivity.
- unfold info_hash.
  destruct parsed.
  rewrite <- same_calculate_hash_parsed_as_calculate_hash.
  unfold calculate_hash.
  rewrite same_info_hash_as_calculate_hash'.
  generalize dependent name.

  induction params.
  + reflexivity.
  + unfold info_hash in IHparams.
    unfold calculate_hash in IHparams.
    dubstep map in parsed.
    unfold info_hash.
    unfold info_hash'.
    dubstep map.
    dubstep fold_left.
    assert (calculate_hash parsed = calculate_hash (mkParsed name (get_parsed' a :: map get_parsed' params))) as P. simpl. reflexivity. rewrite P. clear P.
    unfold calculate_hash.
    dubstep calculate_hash'.
    dubstep get_children.
    dubstep map.
    dubstep fold_left.
    dubstep get_label.
    assert (
      fold_left
        info_hash_per_elem
        (map get_hash' params)
        (info_hash_per_elem (31 * 17 + name) (get_hash' a))
      =
      info_hash' (31 * 17 + name) (get_hash' a) params
    ) as P. unfold info_hash'. unfold info_hash_per_elem. reflexivity. rewrite P. clear P.
    assert (
      fold_left
        calculate_hash_per_elem
        (map (calculate_hash' 17) (map get_parsed' params))
        (calculate_hash_per_elem (31 * 17 + name)(calculate_hash' 17 (get_parsed' a)))
      =
      calculate_hash' (31 * 17 + name) (calculate_hash' 17 (get_parsed' a)) (map get_parsed' params)
    ).
    fold (info_hash' (17 * 31 + name) (get_hash' a) params).




    assert (
      (fix calculate_hash (x : Parsed) : nat :=
        fold_left calculate_hash_per_elem
          (map calculate_hash (get_children x))
          (17 * 31 + get_label x)
      )
      parsed
      =
      (fix calculate_hash (x : Parsed) : nat :=
        fold_left calculate_hash_per_elem
          (map calculate_hash (get_children x))
          (17 * 31 + get_label x)
      )
      (mkParsed name (get_parsed' a :: map get_parsed' params))
    ) as P. reflexivity.
    rewrite P.





Definition SmartInfo := { i : Info & IsSmart i }.

(*
  RExpr is the underlying representation of an expression.
  Unlike Expr which is the class abstraction that will be exposed, RExpr is only meant for internal usage.
*)
Record RExpr {A: Set} (B: Set): Type :=
  mkRExpr {
    fn: A -> B
    ; info: { i : Info & IsSmart i }
    (*TODO: ; smart_constructed: IsSmartConsructed Info *)
  }.

(* Getters *)

Definition get_fn {A: Set} {B: Set} (x: RExpr B): A -> B :=
  fn B x.

Definition get_info {A: Set} {B: Set} (x: RExpr B): Info :=
  @info A B x.

Definition get_name {A: Set} {B: Set} (x: RExpr B): nat :=
  match @get_info A B x with
  | mkInfo name _ _ _ => name
  end.

Definition get_params {A: Set} {B: Set} (x: RExpr B): list Info :=
  match @get_info A B x with
  | mkInfo _ params _ _ => params
  end.

Definition get_hasvar {A: Set} {B: Set} (x: RExpr B): bool :=
  match @get_info A B x with
  | mkInfo _ _ hasvar _ => hasvar
  end.

Definition get_hash {A: Set} {B: Set} (x: RExpr B): nat :=
  match @get_info A B x with
  | mkInfo _ _ _ hash => hash
  end.

(* Smart Constructor for RExpr *)

Definition smartRExpr {A: Set} {B: Set} (fn: A -> B) (name: nat) (params: list Info): RExpr B :=
  mkRExpr A B fn (smartInfo name params).

Definition smartRExprVar {A: Set} {B: Set} (fn: A -> B) (name: nat) (params: list Info): RExpr B :=
  mkRExpr A B fn (smartInfoVar name params).