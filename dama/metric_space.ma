(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)



include "ordered_divisible_group.ma".

record metric_space (R : todgroup) : Type ≝ {
  ms_carr :> Type;
  metric: ms_carr → ms_carr → R;
  mpositive: ∀a,b:ms_carr. 0 ≤ metric a b; 
  mreflexive: ∀a. metric a a ≈ 0;
  msymmetric: ∀a,b. metric a b ≈ metric b a;
  mtineq: ∀a,b,c:ms_carr. metric a b ≤ metric a c + metric c b
  (* manca qualcosa per essere una metrica e non una semimetrica *)
}.

notation < "\nbsp \delta a \nbsp b" non associative with precedence 80 for @{ 'delta2 $a $b}.
interpretation "metric" 'delta2 a b = (cic:/matita/metric_space/metric.con _ _ a b).
notation "\delta" non associative with precedence 80 for @{ 'delta }.
interpretation "metric" 'delta = (cic:/matita/metric_space/metric.con _ _).

definition apart_metric:=
  λR.λms:metric_space R.λa,b:ms.0 < δ a b.

lemma apart_of_metric_space: ∀R:todgroup.metric_space R → apartness.
intros (R ms); apply (mk_apartness ? (apart_metric ? ms)); unfold apart_metric; unfold;
[1: intros 2 (x H); cases H (H1 H2); 
    lapply (ap_rewr ???? (eq_sym ??? (mreflexive ??x)) H2);
    apply (ap_coreflexive R 0); assumption;
|2: intros (x y H); cases H; split;
    [1: apply (le_rewr ???? (msymmetric ????)); assumption
    |2: apply (ap_rewr ???? (msymmetric ????)); assumption]
|3: simplify; intros (x y z H); cases H (LExy Axy);
    lapply (mtineq ?? x y z) as H1; whd in Axy; cases Axy (H2 H2); [cases (LExy H2)]
    clear LExy; lapply (lt_le_transitive ???? H H1) as LT0;
    apply (lt0plus_orlt ????? LT0); apply mpositive;]
qed.
    
coercion cic:/matita/metric_space/apart_of_metric_space.con.
