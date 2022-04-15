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
    (hash: nat)
    (static: bool),
  Func.

(*
The `hash` field is important, because it is used to efficiently compare functions calls, so that we can reorder and simplify.  For example:

 - and(lt(3, 5), contains("abcd", "bc")) => and(contains("abcd", "bc"), lt(3, 5))
 - and(lt(3, 5), lt(3, 5)) => lt(3, 5)
 - or(and(lt(3, 5), contains("abcd", "bc")), and(contains("abcd", "bc"), lt(3, 5))) => and(contains("abcd", "bc"), lt(3, 5))
*)

(* static tells us whether the function is lacking variables and can be evaluated at compile time. *)

Definition get_params (x: Func): list Func :=
  match x with
  | mkFunc _ params _ _ => params
  end.

Definition get_hash (x: Func): nat :=
  match x with
  | mkFunc _ _ hash _ => hash
  end.

Definition get_static (x: Func): bool :=
  match x with
  | mkFunc _ _ _ static => static
  end.

Definition hash_per_elem (state: nat) (x: nat): nat :=
    31 * state + x.

Fixpoint hash_from_func (f: Func): nat :=
  match f with
  | mkFunc name params _ _ =>
    let name_hashed := 31 * 17 * name in
    let param_hashes := map hash_from_func params in
    fold_left hash_per_elem param_hashes name_hashed
  end.

Fixpoint all (xs: list bool): bool :=
  match xs with
  | [] => true
  | (x::xs) =>
    match x with
    | true => all xs
    | _ => false
    end
  end.

Definition static_from_params (params: list Func): bool :=
  let param_static := map get_static params in
  all param_static.