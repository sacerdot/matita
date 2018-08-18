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

include "basic_2/rt_transition/cpr.ma".
include "basic_2/rt_computation/fpbg_fqup.ma".
include "basic_2/dynamic/cnv_fsb.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Inversion lemmas with degree-based equivalence for terms *****************)

lemma cnv_cpr_tdeq_fwd_refl (a) (h) (o) (G) (L):
                            ∀T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h] T2 → T1 ≛[h,o] T2 →
                            ⦃G, L⦄ ⊢ T1 ![a,h] → T1 = T2.
#a #h #o #G #L #T1 #T2 #H @(cpr_ind … H) -G -L -T1 -T2
[ //
| #G #K #V1 #V2 #X2 #_ #_ #_ #H1 #_ -a -G -K -V1 -V2
  lapply (tdeq_inv_lref1 … H1) -H1 #H destruct //
| #I #G #K #T2 #X2 #i #_ #_ #_ #H1 #_ -a -I -G -K -T2
  lapply (tdeq_inv_lref1 … H1) -H1 #H destruct //
| #p #I #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #H1 #H2
  elim (tdeq_inv_pair1 … H1) -H1 #V0 #T0 #HV0 #HT0 #H destruct
  elim (cnv_inv_bind … H2) -H2 #HV1 #HT1
  /3 width=3 by eq_f2/
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #H1 #H2
  elim (tdeq_inv_pair1 … H1) -H1 #V0 #T0 #HV0 #HT0 #H destruct
  elim (cnv_fwd_flat … H2) -H2 #HV1 #HT1
  /3 width=3 by eq_f2/
| #G #K #V #T1 #X1 #X2 #HXT1 #HX12 #_ #H1 #H2
  elim (cnv_fpbg_refl_false … o … H2) -a
  @(fpbg_tdeq_div … H1) -H1
  /3 width=9 by cpm_tdneq_cpm_fpbg, cpm_zeta, tdeq_lifts_inv_pair_sn/
| #G #L #U #T1 #T2 #HT12 #_ #H1 #H2
  elim (cnv_fpbg_refl_false … o … H2) -a
  @(fpbg_tdeq_div … H1) -H1
  /3 width=6 by cpm_tdneq_cpm_fpbg, cpm_eps, tdeq_inv_pair_xy_y/
| #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #H1 #_
  elim (tdeq_inv_pair … H1) -H1 #H #_ #_ destruct
| #p #G #L #V1 #V2 #X2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #_ #H1 #_
  elim (tdeq_inv_pair … H1) -H1 #H #_ #_ destruct
]
qed-.

lemma cpm_tdeq_inv_bind (a) (h) (o) (n) (p) (I) (G) (L):
                        ∀V,T1. ⦃G, L⦄ ⊢ ⓑ{p,I}V.T1 ![a,h] →
                        ∀X. ⦃G, L⦄ ⊢ ⓑ{p,I}V.T1 ➡[n,h] X → ⓑ{p,I}V.T1 ≛[h,o] X →
                        ∃∃T2. ⦃G, L.ⓑ{I}V⦄ ⊢ T1 ➡[n,h] T2 & T1 ≛[h,o] T2 & X = ⓑ{p,I}V.T2.
#a #h #o #n #p #I #G #L #V #T1 #H0 #X #H1 #H2
elim (cpm_inv_bind1 … H1) -H1 *
[ #XV #T2 #HXV #HT12 #H destruct
  elim (tdeq_inv_pair … H2) -H2 #_ #H2XV #H2T12
  elim (cnv_inv_bind … H0) -H0 #HV #_
  lapply (cnv_cpr_tdeq_fwd_refl … HXV H2XV HV) #H destruct -HXV -H2XV -HV
  /2 width=4 by ex3_intro/
| #X1 #HXT1 #HX1 #H1 #H destruct
  elim (cnv_fpbg_refl_false … o … H0) -a
  @(fpbg_tdeq_div … H2) -H2
  /3 width=9 by cpm_tdneq_cpm_fpbg, cpm_zeta, tdeq_lifts_inv_pair_sn/
]
qed-.

lemma cpm_tdeq_inv_appl (a) (h) (o) (n) (G) (L):
                        ∀V,T1. ⦃G, L⦄ ⊢ ⓐV.T1 ![a,h] →
                        ∀X. ⦃G, L⦄ ⊢ ⓐV.T1 ➡[n,h] X → ⓐV.T1 ≛[h,o] X →
                        ∃∃T2. ⦃G, L⦄ ⊢ T1 ➡[n,h] T2 & T1 ≛[h,o] T2 & X = ⓐV.T2.
#a #h #o #n #G #L #V #T1 #H0 #X #H1 #H2
elim (cpm_inv_appl1 … H1) -H1 *
[ #XV #T2 #HXV #HT12 #H destruct
  elim (tdeq_inv_pair … H2) -H2 #_ #H2XV #H2T12
  elim (cnv_inv_appl … H0) -H0 #m #q #W #U #_ #HV #_ #_ #_ -m -q -W -U
  lapply (cnv_cpr_tdeq_fwd_refl … HXV H2XV HV) #H destruct -HXV -H2XV -HV
  /2 width=4 by ex3_intro/
| #q #V2 #W1 #W2 #XT #T2 #_ #_ #_ #H1 #H destruct -H0
  elim (tdeq_inv_pair … H2) -H2 #H #_ #_ destruct
| #q #V2 #XV #W1 #W2 #XT #T2 #_ #_ #_ #_ #H1 #H destruct -H0
  elim (tdeq_inv_pair … H2) -H2 #H #_ #_ destruct
]
qed-.

lemma cpm_tdeq_inv_cast (a) (h) (o) (n) (G) (L):
                        ∀U1,T1. ⦃G, L⦄ ⊢ ⓝU1.T1 ![a,h] →
                        ∀X. ⦃G, L⦄ ⊢ ⓝU1.T1 ➡[n,h] X → ⓝU1.T1 ≛[h,o] X →
                        ∃∃U2,T2. ⦃G, L⦄ ⊢ U1 ➡[n,h] U2 & U1 ≛[h,o] U2 & ⦃G, L⦄ ⊢ T1 ➡[n,h] T2 & T1 ≛[h,o] T2 & X = ⓝU2.T2.
#a #h #o #n #G #L #U1 #T1 #H0 #X #H1 #H2
elim (cpm_inv_cast1 … H1) -H1 [ * || * ]
[ #U2 #T2 #HU12 #HT12 #H destruct -H0
  elim (tdeq_inv_pair … H2) -H2 #_ #H2U12 #H2T12
  /2 width=7 by ex5_2_intro/
| #HT1X
  elim (cnv_fpbg_refl_false … o … H0) -a
  @(fpbg_tdeq_div … H2) -H2
  /3 width=6 by cpm_tdneq_cpm_fpbg, cpm_eps, tdeq_inv_pair_xy_y/
| #m #HU1X #H destruct
  elim (cnv_fpbg_refl_false … o … H0) -a
  @(fpbg_tdeq_div … H2) -H2
  /3 width=6 by cpm_tdneq_cpm_fpbg, cpm_ee, tdeq_inv_pair_xy_x/
]
qed-.
