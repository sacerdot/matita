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

record metric_space (R: todgroup) : Type ≝ {
  ms_carr :> Type;
  metric: ms_carr → ms_carr → R;
  mpositive: ∀a,b:ms_carr. 0 ≤ metric a b; 
  mreflexive: ∀a. metric a a ≈ 0;
  msymmetric: ∀a,b. metric a b ≈ metric b a;
  mtineq: ∀a,b,c:ms_carr. metric a b ≤ metric a c + metric c b
}.

notation < "\nbsp \delta a \nbsp b" non associative with precedence 80 for @{ 'delta2 $a $b}.
interpretation "metric" 'delta2 a b = (metric ? ? a b).
notation "\delta" non associative with precedence 80 for @{ 'delta }.
interpretation "metric" 'delta = (metric ? ?).

lemma apart_of_metric_space: ∀R.metric_space R → apartness.
intros (R ms); apply (mk_apartness ? (λa,b:ms.0 < δ a b)); unfold;
[1: intros 2 (x H); cases H (H1 H2); clear H; 
    lapply (Ap≫ ? (eq_sym ??? (mreflexive ??x)) H2);
    apply (ap_coreflexive R 0); assumption;
|2: intros (x y H); cases H; split;
    [1: apply (Le≫ ? (msymmetric ????)); assumption
    |2: apply (Ap≫ ? (msymmetric ????)); assumption]
|3: simplify; intros (x y z H); elim H (LExy Axy);
    lapply (mtineq ?? x y z) as H1; elim (ap2exc ??? Axy) (H2 H2); [cases (LExy H2)]
    clear LExy; lapply (lt_le_transitive ???? H H1) as LT0;
    apply (lt0plus_orlt ????? LT0); apply mpositive;]
qed.
    
lemma ap2delta: ∀R.∀m:metric_space R.∀x,y:m.ap_apart (apart_of_metric_space ? m) x y → 0 < δ x y.
intros 2 (R m); cases m 0; simplify; intros; assumption; qed. 
