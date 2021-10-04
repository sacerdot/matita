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

include "ground/arith/nat_pred_succ.ma".
include "ground/relocation/pr_pat_tls.ma".
include "ground/relocation/pr_ist_tls.ma".
include "ground/relocation/pr_after_pat_tls.ma".

(* RELATIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

(*** H_after_inj *)
definition H_pr_after_inj: predicate pr_map ≝
           λf1. 𝐓❪f1❫ →
           ∀f,f21,f22. f1 ⊚ f21 ≘ f → f1 ⊚ f22 ≘ f → f21 ≡ f22.

(* Main destructions with pr_ist ********************************************)

(*** after_inj_O_aux *)
corec fact pr_after_inj_unit_aux:
           ∀f1. @❪𝟏, f1❫ ≘ 𝟏 → H_pr_after_inj f1.
#f1 #H1f1 #H2f1 #f #f21 #f22 #H1f #H2f
cases (pr_pat_inv_unit_bi … H1f1) -H1f1 [|*: // ] #g1 #H1
lapply (pr_ist_inv_push … H2f1 … H1) -H2f1 #H2g1
cases (H2g1 (𝟏)) #p #Hp
cases (pr_after_inv_push_sn … H1f … H1) -H1f * #g21 #g #H1g #H21 #H
[ cases (pr_after_inv_push_sn_push … H2f … H1 H) -f1 -f #g22 #H2g #H22
  @(pr_eq_push … H21 H22) -f21 -f22
| cases (pr_after_inv_push_sn_next … H2f … H1 H) -f1 -f #g22 #H2g #H22
  @(pr_eq_next … H21 H22) -f21 -f22
]
@(pr_after_inj_unit_aux (⫰*[↓p]g1) … (⫰*[↓p]g)) -pr_after_inj_unit_aux
/2 width=1 by pr_after_tls_sn_tls, pr_ist_tls, pr_pat_unit_succ_tls/
qed-.

(*** after_inj_aux *)
fact pr_after_inj_aux:
     (∀f1. @❪𝟏, f1❫ ≘ 𝟏 → H_pr_after_inj f1) →
     ∀i2,f1. @❪𝟏, f1❫ ≘ i2 → H_pr_after_inj f1.
#H0 #i2 elim i2 -i2 /2 width=1 by/ -H0
#i2 #IH #f1 #H1f1 #H2f1 #f #f21 #f22 #H1f #H2f
elim (pr_pat_inv_unit_succ … H1f1) -H1f1 [|*: // ] #g1 #H1g1 #H1
elim (pr_after_inv_next_sn … H1f … H1) -H1f #g #H1g #H
lapply (pr_after_inv_next_sn_next … H2f … H1 H) -f #H2g
/3 width=6 by pr_ist_inv_next/
qed-.

(*** after_inj *)
theorem pr_after_inj:
        ∀f1. H_pr_after_inj f1.
#f1 #H cases (H (𝟏))
/3 width=7 by pr_after_inj_aux, pr_after_inj_unit_aux/
qed-.
