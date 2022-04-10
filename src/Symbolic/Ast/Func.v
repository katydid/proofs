Require Import CoqStock.List.

(*
We want to represent some nested function calls for a very restricted language, for example:

  and(lt(3, 5), contains("abcd", "bc"))

We represent the parsed ast, like so:
*)

Inductive Func: Type :=
  mkFunc:
    forall
    (name: nat) (* TODO: We are still using `nat` instead of string to represent the names. *)
    (params: list Func)
    (hash: nat),
  Func.

(*
The `hash` field is important, because it is used to efficiently compare functions calls, so that we can reorder and simplify.  For example:

 - and(lt(3, 5), contains("abcd", "bc")) => and(contains("abcd", "bc"), lt(3, 5))
 - and(lt(3, 5), lt(3, 5)) => lt(3, 5)
 - or(and(lt(3, 5), contains("abcd", "bc")), and(contains("abcd", "bc"), lt(3, 5))) => and(contains("abcd", "bc"), lt(3, 5))
*)

Definition get_params (x: Func): list Func :=
  match x with
  | mkFunc _ params _ => params
  end.

Definition get_hash (x: Func): nat :=
  match x with
  | mkFunc _ _ hash => hash
  end.

Definition hash_per_elem (state: nat) (x: nat): nat :=
    31 * state + x.

Fixpoint hash_from_func (f: Func): nat :=
  match f with
  | mkFunc name params _ =>
    let name_hashed := 31 * 17 * name in
    let param_hashes := map hash_from_func params in
    fold_left hash_per_elem param_hashes name_hashed
  end.