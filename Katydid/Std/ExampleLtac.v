Local Ltac list_empty :=
   discriminate
|| match goal with
| [ |- [] <> ?X ++ (?Y :: ?YS) ] =>
  apply app_cons_not_nil
| [ H: ?XS ++ ?YS = [] |- _ ] =>
  let H0 := fresh "H0" in
  let H1 := fresh "H1" in
  apply app_eq_nil in H;
  destruct H as [H0 H1];
  try rewrite H0 in *;
  try rewrite H1 in *
| [ H: context [[] ++ _] |- _ ] =>
  rewrite app_nil_l in H
| [ |- context [(?X :: ?XS) ++ ?YS] ] =>
  rewrite <- app_comm_cons
end.