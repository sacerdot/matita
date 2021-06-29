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
include "ground/relocation/gr_pat_tls.ma".
include "ground/relocation/gr_ist_tls.ma".
include "ground/relocation/gr_after_pat_tls.ma".

(* RELATIONAL COMPOSITION FOR GENERIC RELOCATION MAPS ***********************)

(*** H_after_inj *)
definition H_gr_after_inj: predicate gr_map ≝
           λf1. 𝐓❪f1❫ →
           ∀f,f21,f22. f1 ⊚ f21 ≘ f → f1 ⊚ f22 ≘ f → f21 ≡ f22.

(* Main destructions with gr_ist ********************************************)

(*** after_inj_O_aux *)
corec fact gr_after_inj_unit_aux:
           ∀f1. @❪𝟏, f1❫ ≘ 𝟏 → H_gr_after_inj f1.
#f1 #H1f1 #H2f1 #f #f21 #f22 #H1f #H2f
cases (gr_pat_inv_unit_bi … H1f1) -H1f1 [|*: // ] #g1 #H1
lapply (gr_ist_inv_push … H2f1 … H1) -H2f1 #H2g1
cases (H2g1 (𝟏)) #p #Hp
cases (gr_after_inv_push_sn … H1f … H1) -H1f * #g21 #g #H1g #H21 #H
[ cases (gr_after_inv_push_sn_push … H2f … H1 H) -f1 -f #g22 #H2g #H22
  @(gr_eq_push … H21 H22) -f21 -f22
| cases (gr_after_inv_push_sn_next … H2f … H1 H) -f1 -f #g22 #H2g #H22
  @(gr_eq_next … H21 H22) -f21 -f22
]
@(gr_after_inj_unit_aux (⫰*[↓p]g1) … (⫰*[↓p]g)) -gr_after_inj_unit_aux
/2 width=1 by gr_after_tls_sn_tls, gr_ist_tls, gr_pat_unit_succ_tls/
qed-.

(*** after_inj_aux *)
fact gr_after_inj_aux:
     (∀f1. @❪𝟏, f1❫ ≘ 𝟏 → H_gr_after_inj f1) →
     ∀i2,f1. @❪𝟏, f1❫ ≘ i2 → H_gr_after_inj f1.
#H0 #i2 elim i2 -i2 /2 width=1 by/ -H0
#i2 #IH #f1 #H1f1 #H2f1 #f #f21 #f22 #H1f #H2f
elim (gr_pat_inv_unit_succ … H1f1) -H1f1 [|*: // ] #g1 #H1g1 #H1
elim (gr_after_inv_next_sn … H1f … H1) -H1f #g #H1g #H
lapply (gr_after_inv_next_sn_next … H2f … H1 H) -f #H2g
/3 width=6 by gr_ist_inv_next/
qed-.

(*** after_inj *)
theorem gr_after_inj:
        ∀f1. H_gr_after_inj f1.
#f1 #H cases (H (𝟏))
/3 width=7 by gr_after_inj_aux, gr_after_inj_unit_aux/
qed-.
