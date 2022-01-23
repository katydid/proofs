

Require Import CoqStock.List.


Inductive Info: (Info -> Prop) -> Type :=
  mkInfo:
    forall
    (name: nat)
    (params: list Info)
    (hasvar: bool)
    (hash: nat),
  Info.


Inductive Info: Type :=
  | base:
    forall
    (name: nat)
    (hasvar: bool)
    (hash: nat)
    (hash)
    ,
    Info
  | notbase:
    forall
    (params: list Info)
    (name: nat)
    (hasvar: bool)
    (hash: nat),
    Info
  .


  mkInfo:
    forall
    (name: nat)
    (params: list Info)
    (hasvar: bool)
    (hash: nat),
  Info.


  Inductive IsSmartHasVar (i: Info): Prop :=
  | isSmartHasVar :
     get_hasvar i = true
  \/ get_hasvar i = has_var_from_params (get_params i)
  -> Forall IsSmartHasVar (get_params i)
  -> IsSmartHasVar i
  .