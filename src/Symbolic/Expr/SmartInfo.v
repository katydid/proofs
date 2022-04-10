Require Import CoqStock.Cmp.
Require Import CoqStock.DubStep.
Require Import CoqStock.List.
Require Import CoqStock.Invs.
Require Import CoqStock.ForAll.

Require Import Symbolic.Expr.Info.

(*
  IsSmart indicates that Info was constructed with a smart constructor.
*)

Inductive IsSmartHash (i: Info): Prop :=
  | isSmartHash:
     get_hash i = hash_from_info i
  -> Forall IsSmartHash (get_params i)
  -> IsSmartHash i
  .

Inductive IsSmartHasVar (i: Info): Prop :=
  | isSmartHasVar :
     get_hasvar i = true
  \/ get_hasvar i = has_var_from_params (get_params i)
  -> ForAll IsSmartHasVar (get_params i)
  -> IsSmartHasVar i
  .

Inductive IsSmart (i: Info): Prop :=
  | isSmart :
     IsSmartHasVar i
  -> IsSmartHash i
  -> IsSmart i
  .

Inductive SmartInfo: Type :=
  mkSmart:
    forall
    (info: Info)
    (smart: IsSmart info),
  SmartInfo.

Definition get_info (s: SmartInfo): Info :=
  match s with
  | mkSmart info _ => info
  end.

(* Helper function for get_smart_params. *)
Fixpoint get_smart_params'
  (params: list Info)
  (smartHasVars: Forall IsSmartHasVar params)
  (smartHashes: Forall IsSmartHash params)
  : list SmartInfo.
destruct params as [|p ps].
- exact [].
- apply Forall_cons_iff in smartHasVars.
  apply Forall_cons_iff in smartHashes.
  destruct smartHasVars as [smartHasVar smartHasVars].
  destruct smartHashes as [smartHash smartHashes].
  exact (
    (mkSmart p (isSmart p smartHasVar smartHash))
    :: (get_smart_params' ps  smartHasVars smartHashes)
  ).
Defined.

(* Duplicate definition of get_smart_params' done using refine. *)
Fixpoint get_smart_params''
  (params: list Info)
  (smartHasVars: Forall IsSmartHasVar params)
  (smartHashes: Forall IsSmartHash params)
  : list SmartInfo.
Proof.
refine (
match params as params' return (Forall IsSmartHash params' -> Forall IsSmartHasVar params' -> list SmartInfo) with
  | [] =>
    fun (_ : Forall IsSmartHash []) (_ : Forall IsSmartHasVar []) => []
  | (p::ps) =>
      (fun
        (smartHashes' : Forall IsSmartHash (p :: ps))
        (smartHasVars' : Forall IsSmartHasVar (p :: ps)) =>
          _
      )
end smartHashes smartHasVars
).
apply Forall_cons_iff in smartHasVars'.
apply Forall_cons_iff in smartHashes'.
destruct smartHasVars' as [smartHasVar smartHasVars'].
destruct smartHashes' as [smartHash smartHashes'].
exact (
    (mkSmart p (isSmart p smartHasVar smartHash))
    :: (get_smart_params' ps smartHasVars' smartHashes')
  ).
Defined.

Print get_smart_params''.

Definition magic
  (A : Type) (P : A -> Prop) (a : A) (l : list A)
  (for_all: Forall P (a :: l)): P a /\ Forall P l :=
  match Forall_cons_iff P a l with
  | conj uncons _ =>
      uncons for_all
  end.

Theorem get_smart_params'_is_correct
    (params: list Info)
    (smartHasVars: Forall IsSmartHasVar params)
    (smartHashes: Forall IsSmartHash params)
  :
  map get_info (get_smart_params' params smartHasVars smartHashes)
  =
  params
.
Proof.
intros.
refine (
  match params as params'
  return
    ( forall
      (smartHasVars': Forall IsSmartHasVar params')
      (smartHashes': Forall IsSmartHash params')
      , map get_info (get_smart_params' params' smartHasVars' smartHashes')
      =
      params'
    ) with
    | [] =>
      _
    | (p::ps) =>
      fun (smartHasVars' : Forall IsSmartHasVar (p :: ps))
          (smartHashes' : Forall IsSmartHash (p :: ps))
      =>
      let smartHashVars'' : IsSmartHasVar p /\ Forall IsSmartHasVar ps :=
      magic Info IsSmartHasVar p ps smartHasVars' in
      let smartHashes'' : IsSmartHash p /\ Forall IsSmartHash ps :=
      magic Info IsSmartHash p ps smartHashes' in
      _
  end smartHasVars smartHashes
).
intros.
- cbn. reflexivity.
- clear smartHasVars smartHashes params.
  cbn.
specialize (magic Info IsSmartHasVar p ps smartHasVars') as smartHasVars''.
Abort.
(* TODO *)

Definition get_smart_params (s: SmartInfo): list SmartInfo.
destruct s.
destruct info.
destruct smart as [smartHasVar smartHash].
destruct smartHash as [_  smartHashes].
destruct smartHasVar as [_ smartHasVars].
cbn in *.
exact (get_smart_params' params smartHasVars smartHashes).
Defined.

Theorem get_smart_params_is_correct:
  forall (smart_info: SmartInfo),
  map get_info (get_smart_params smart_info)
  =
  get_params (get_info smart_info)
.
Proof.
intros.
destruct smart_info.
destruct info.
dubstep get_params.
destruct smart as [smartHasVar smartHash].
destruct smartHash as [smartHash smartHashes].
destruct smartHasVar as [smartHasVar smartHasVars].
unfold get_smart_params.
(* TODO *)
Abort.

(* hname is an already hashed name *)
Definition hash_from_smart_params (hname: nat) (sparams: list SmartInfo) : nat :=
  let param_hashes := map (fun sp => get_hash (get_info sp)) sparams in
  fold_left hash_per_elem param_hashes hname.

Lemma hash_from_params_is_hash_from_smart_params:
  forall (hname: nat) (sparams: list SmartInfo),
    hash_from_smart_params hname sparams
    =
    hash_from_params hname (map get_info sparams).
Proof.
intros.

(* induction on params *)
generalize dependent hname.
induction sparams as [| sp sps].
- reflexivity.
- intros.

(* step hash_from_params *)
unfold hash_from_params.
dubstep map.
dubstep fold_left.
assert (
  fold_left
    hash_per_elem
    (map hash_from_info (map get_info sps))
    (hash_per_elem hname (hash_from_info (get_info sp)))
  =
    hash_from_params (31 * hname + (get_hash (get_info sp))) (map get_info sps)
) as Hinfo.
destruct sp.
destruct smart as [smartHasVar smartHash].
destruct smartHash as [Heq Hforall].
dubstep get_info.
unfold hash_from_params.
unfold hash_per_elem.
rewrite Heq.
reflexivity.
rewrite Hinfo.
clear Hinfo.

(* step hash_from_smart_params *)
unfold hash_from_smart_params.
dubstep map.
dubstep fold_left.
assert (
  fold_left
    hash_per_elem
    (map (fun sp' => get_hash (get_info sp')) sps)
    (hash_per_elem hname (get_hash (get_info sp)))
  =
    hash_from_smart_params (31 * hname + (get_hash (get_info sp))) sps
) as HsmartInfo.
destruct sp.
destruct smart as [smartHasVar smartHash].
destruct smartHash as [Heq Hforall].
dubstep get_info.
unfold hash_from_smart_params.
rewrite Heq.
unfold hash_per_elem.
reflexivity.
rewrite HsmartInfo.
clear HsmartInfo.

apply IHsps.
Qed.

Definition has_var_from_smart_params (sparams: list SmartInfo): bool :=
  let params := map get_info sparams in
  let param_hasvars := map get_hasvar params in
  any param_hasvars.

(* get_smart_params (s: SmartInfo): list SmartInfo *)

Definition forall_smart_has_var_from_smart_params
  (sparams: list SmartInfo):
  Forall IsSmartHasVar (map get_info sparams).
induction sparams as [| p ps].
- cbn. constructor.
- cbn.
  destruct p.
  cbn.
  constructor.
  + destruct smart as [smartHasVar smartHash].
    exact smartHasVar.
  + exact IHps.
Qed.

Definition forall_smart_hash_from_smart_params
  (sparams: list SmartInfo):
  Forall IsSmartHash (map get_info sparams).
induction sparams as [| p ps].
- cbn. constructor.
- cbn.
  destruct p.
  cbn.
  constructor.
  + destruct smart as [smartHasVar smartHash].
    exact smartHash.
  + exact IHps.
Qed.

Lemma is_smart_has_var (name: nat) (sparams: list SmartInfo) (has_var: bool):
  IsSmartHasVar
    (mkInfo
      name
      (map get_info sparams)
      (has_var || has_var_from_smart_params sparams)
      (hash_from_smart_params (31 * 17 * name) sparams)
    ).
Proof.
apply isSmartHasVar.
- destruct has_var.
  + left.
    cbn.
    reflexivity.
  + right.
    cbn.
    unfold has_var_from_smart_params.
    reflexivity.
- cbn.
  apply forall_smart_has_var_from_smart_params.
Qed.

Lemma is_smart_hash (name: nat) (sparams: list SmartInfo) (has_var: bool):
  IsSmartHash
    (mkInfo
      name
      (map get_info sparams)
      (has_var || has_var_from_smart_params sparams)
      (hash_from_smart_params (31 * 17 * name) sparams)
    ).
Proof.
apply isSmartHash.
- dubstep get_hash.
  dubstep hash_from_info.
  rewrite hash_from_params_is_hash_from_smart_params.
  unfold hash_from_params.
  reflexivity.
- cbn.
  apply forall_smart_hash_from_smart_params.
Qed.

Definition smartInfo' (name: nat) (sparams: list SmartInfo) (has_var: bool): SmartInfo.
exists
  (mkInfo
    name
    (map get_info sparams)
    (has_var || has_var_from_smart_params sparams)
    (hash_from_smart_params
      (31 * 17 * name)
      sparams
    )
  ).
apply isSmart.
- apply is_smart_has_var.
- apply is_smart_hash.
Defined.

Definition smartInfo (name: nat) (sparams: list SmartInfo): SmartInfo :=
  smartInfo' name sparams false.

Definition smartInfoVar (name: nat) (sparams: list SmartInfo): SmartInfo :=
  smartInfo' name sparams true.