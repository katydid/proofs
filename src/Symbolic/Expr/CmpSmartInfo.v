Require Import CoqStock.List.
Require Export CoqStock.Cmp.
Require Import CoqStock.CmpNat.
Require Import CoqStock.DubStep.

Require Import Symbolic.Expr.Info.
Require Import Symbolic.Expr.SmartInfo.

Fixpoint compare_info (x y: Info) {struct x}: comparison :=
  match x with
  | mkInfo xname xparams _ xhash =>
    match y with
    | mkInfo yname yparams _ yhash =>
      match compare xhash yhash with
      | Lt => Lt
      | Gt => Gt
      | Eq =>
        match compare xname yname with
        | Lt => Lt
        | Gt => Gt
        | Eq => ((fix compare_params (xs ys: list Info) {struct xs} :=
        (match xs with
         | [] =>
           match ys with
           | [] => Eq
           | _ => Lt
           end
         | (x'::xs') =>
           match ys with
           | [] => Gt
           | (y'::ys') =>
             match compare_info x' y' with
             | Lt => Lt
             | Gt => Gt
             | Eq => compare_params xs' ys'
             end
           end
         end)) xparams yparams)
        end
      end
    end
  end
.

Definition compare_smart_info (xsmart ysmart: SmartInfo): comparison :=
  match xsmart with
  | mkSmart xinfo x_is_smart =>
    match ysmart with
    | mkSmart yinfo y_is_smart =>
      compare_info xinfo yinfo
    end
  end.

(* Fixpoint compare_smart_info (xsmart ysmart: SmartInfo) {struct xsmart}: comparison.
specialize (get_smart_params xsmart) as xsmartparams.
specialize (get_smart_params ysmart) as ysmartparams.
destruct xsmart as [xinfo x_is_smart].
destruct ysmart as [yinfo y_is_smart].
destruct xinfo as [xname xparams xhasvar xhash].
destruct yinfo as [yname yparams yhasvar yhash].
destruct x_is_smart as [x_smart_hasvar x_smart_hash].
destruct y_is_smart as [y_smart_hasvar y_smart_hash].
destruct x_smart_hasvar as [x_smart_hasvar' x_smart_hasvars].



  match xsmart with
  | mkSmart xinfo x_is_smart =>
    match ysmart with
    | mkSmart yinfo y_is_smart =>
      match xinfo as xinfo' return (IsSmart xinfo' -> comparison) with
      | mkInfo xname xparams xhasvar xhash =>
        (fun (xsmart: IsSmart (mkInfo xname xparams xhasvar xhash)) =>
          match yinfo as yinfo' return (IsSmart yinfo' -> comparison) with
          | mkInfo yname yparams yhasvar yhash =>
            (fun (ysmart: IsSmart (mkInfo yname yparams yhasvar yhash)) =>
              Eq
            )
          end y_is_smart
        )
      end x_is_smart
    end
  end.

Fixpoint compare_smart_info (xsmart ysmart: SmartInfo) {struct xsmart}: comparison :=
  match xsmart with
  | mkSmart xinfo x_is_smart =>
    match ysmart with
    | mkSmart yinfo y_is_smart =>
      match xinfo as xinfo' return (IsSmart xinfo' -> comparison) with
      | mkInfo xname xparams xhasvar xhash =>
        (fun (xsmart: IsSmart (mkInfo xname xparams xhasvar xhash)) =>
          match yinfo as yinfo' return (IsSmart yinfo' -> comparison) with
          | mkInfo yname yparams yhasvar yhash =>
            (fun (ysmart: IsSmart (mkInfo yname yparams yhasvar yhash)) =>
              Eq
            )
          end y_is_smart
        )
      end x_is_smart
    end
  end.


Definition get_sparams (s : SmartInfo): list SmartInfo :=
  match s with
  | mkSmart info smart =>
     match info as i return (IsSmart i -> list SmartInfo) with
     | mkInfo name params hasvar hash =>
         (fun
            (smart1 : IsSmart (mkInfo name params hasvar hash)) =>
          match smart1 with
          | isSmart _ x x0 =>
              (fun
                 (smartHasVar : IsSmartHasVar
                                  (mkInfo name params hasvar hash))
                 (smartHash : IsSmartHash
                                (mkInfo name params hasvar hash)) =>
               match smartHash with
               | isSmartHash _ x1 x2 =>
                   (fun
                      (_ : get_hash (mkInfo name params hasvar hash) =
                           hash_from_info
                             (mkInfo name params hasvar hash))
                      (smartHashes : Forall IsSmartHash
                                       (get_params
                                          (mkInfo name params hasvar hash)))
                    =>
                    match smartHasVar with
                    | isSmartHasVar _ x3 x4 =>
                        (fun
                           (_ : get_hasvar
                                  (mkInfo name params hasvar hash) = true \/
                                get_hasvar
                                  (mkInfo name params hasvar hash) =
                                has_var_from_params
                                  (get_params
                                     (mkInfo name params hasvar hash)))
                           (smartHasVars : Forall IsSmartHasVar
                                             (get_params
                                                (mkInfo name params hasvar
                                                 hash))) =>
                         get_smart_params' params smartHasVars smartHashes)
                          x3 x4
                    end) x1 x2
               end) x x0
          end)
     end smart
end.


Definition get_sparams (s : SmartInfo): list SmartInfo :=
  match s with
  | mkSmart info smart =>
  (fun (info0 : Info) (smart0 : IsSmart info0) =>
     match info0 as i return (IsSmart i -> list SmartInfo) with
     | mkInfo name params hasvar hash =>
         (fun (name0 : nat) (params0 : list Info)
            (hasvar0 : bool) (hash0 : nat)
            (smart1 : IsSmart (mkInfo name0 params0 hasvar0 hash0)) =>
          match smart1 with
          | isSmart _ x x0 =>
              (fun
                 (smartHasVar : IsSmartHasVar
                                  (mkInfo name0 params0 hasvar0 hash0))
                 (smartHash : IsSmartHash
                                (mkInfo name0 params0 hasvar0 hash0)) =>
               match smartHash with
               | isSmartHash _ x1 x2 =>
                   (fun
                      (_ : get_hash (mkInfo name0 params0 hasvar0 hash0) =
                           hash_from_info
                             (mkInfo name0 params0 hasvar0 hash0))
                      (smartHashes : Forall IsSmartHash
                                       (get_params
                                          (mkInfo name0 params0 hasvar0 hash0)))
                    =>
                    match smartHasVar with
                    | isSmartHasVar _ x3 x4 =>
                        (fun
                           (_ : get_hasvar
                                  (mkInfo name0 params0 hasvar0 hash0) = true \/
                                get_hasvar
                                  (mkInfo name0 params0 hasvar0 hash0) =
                                has_var_from_params
                                  (get_params
                                     (mkInfo name0 params0 hasvar0 hash0)))
                           (smartHasVars : Forall IsSmartHasVar
                                             (get_params
                                                (mkInfo name0 params0 hasvar0
                                                 hash0))) =>
                         get_smart_params' params0 smartHasVars smartHashes)
                          x3 x4
                    end) x1 x2
               end) x x0
          end) name params hasvar hash
     end smart0) info smart
end.


Fixpoint compare_smart_info (xsmart ysmart: SmartInfo) {struct xsmart} :=
  match xsmart with
  | mkSmart xinfo x_is_smart =>
    match ysmart with
    | mkSmart yinfo y_is_smart =>
      match xinfo with
      | mkInfo xname xparams _ xhash =>
        match yinfo with
        | mkInfo yname yparams _ yhash =>
          match Nat.compare xhash yhash with
          | Lt => Lt
          | Gt => Gt
          | Eq =>
            match Nat.compare xname yname with
            | Lt => Lt
            | Gt => Gt
            | Eq => ((fix compare_params (xs ys: list SmartInfo) {struct xs} :=
              (match xs with
              | [] =>
                match ys with
                | [] => Eq
                | _ => Lt
                end
              | (x'::xs') =>
                match ys with
                | [] => Gt
                | (y'::ys') =>
                  match compare_smart_info x' y' with
                  | Lt => Lt
                  | Gt => Gt
                  | Eq => compare_params xs' ys'
                  end
                end
              end)) (get_smart_params xsmart) (get_smart_params ysmart))
            end
          end
        end
      end
    end
  end.

Print compare_smart_info.
 *)


Theorem proof_compare_smart_info_eq_implies_equal: forall (x y: SmartInfo)
  (c: compare_smart_info x y = Eq)
  , x = y.
Proof.
destruct x as [xinfo x_is_smart].
destruct y as [yinfo y_is_smart].
destruct xinfo as [xname xparams xhasvar xhash].
destruct yinfo as [yname yparams yhasvar yhash].
destruct x_is_smart as [x_smart_hasvar x_smart_hash].
destruct y_is_smart as [y_smart_hasvar y_smart_hash].
destruct x_smart_hasvar as [x_smart_hasvar' x_smart_hasvars].
destruct y_smart_hasvar as [y_smart_hasvar' y_smart_hasvars].
destruct x_smart_hash as [x_smart_hash' x_smart_hashes].
destruct y_smart_hash as [y_smart_hash' y_smart_hashes].
unfold compare_smart_info.
dubstep compare_info.
intros.
induction_on_compare.
subst.
induction_on_compare.
subst.
induction xparams.
- cbn in x_smart_hashes.
  induction yparams.
    cbn in y_smart_hashes.
    destruct xhasvar, yhasvar.
    * cbn in x_smart_hasvars.
      cbn in y_smart_hasvars.
      rewrite (Forall_nil_iff IsSmartHash) in x_smart_hashes.
      destruct x_smart_hashes.
      --- admit.
      ---
remember (compare xhash yhash).
induction c0.

rewrite_nat_compare_to_compare.


rewrite_nat_compare_to_compare.
induction_on_compare.

intros.

(*TODO*)
Admitted.

Theorem proof_compare_smart_info_eq_reflex: forall (p: SmartInfo)
  , compare_smart_info p p = Eq.
(*TODO*)
Admitted.

Theorem proof_compare_smart_info_eq_trans: forall (x y z: SmartInfo)
  (xy: compare_smart_info x y = Eq)
  (yz: compare_smart_info y z = Eq)
  , compare_smart_info x z = Eq.
(*TODO*)
Admitted.

Theorem proof_compare_smart_info_lt_trans: forall (x y z: SmartInfo)
  (xy: compare_smart_info x y = Lt)
  (yz: compare_smart_info y z = Lt)
  , compare_smart_info x z = Lt.
(*TODO*)
Admitted.

Theorem proof_compare_smart_info_gt_trans: forall (x y z: SmartInfo)
  (xy: compare_smart_info x y = Gt)
  (yz: compare_smart_info y z = Gt)
  , compare_smart_info x z = Gt.
(*TODO*)
Admitted.

#[export]
Instance CmpSmartInfo: Cmp (SmartInfo) :=
  {
    compare := compare_smart_info
  ; proof_compare_eq_implies_equal := proof_compare_smart_info_eq_implies_equal
  ; proof_compare_eq_reflex := proof_compare_smart_info_eq_reflex
  ; proof_compare_eq_trans := proof_compare_smart_info_eq_trans
  ; proof_compare_lt_trans := proof_compare_smart_info_lt_trans
  ; proof_compare_gt_trans := proof_compare_smart_info_gt_trans
  }.