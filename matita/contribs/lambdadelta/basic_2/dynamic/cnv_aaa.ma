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

include "ground_2/lib/arith_2b.ma".
include "basic_2/rt_computation/cpms_aaa.ma".
include "basic_2/rt_computation/lprs_cpms.ma".
include "basic_2/dynamic/cnv.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Forward lemmas on atomic arity assignment for terms **********************)

(* Basic_2A1: uses: snv_fwd_aaa *)
lemma cnv_fwd_aaa (a) (h): ∀G,L,T. ⦃G, L⦄ ⊢ T ![a, h] → ∃A. ⦃G, L⦄ ⊢ T ⁝ A.
#a #h #G #L #T #H elim H -G -L -T
[ /2 width=2 by aaa_sort, ex_intro/
| #I #G #L #V #_ * /3 width=2 by aaa_zero, ex_intro/
| #I #G #L #K #_ * /3 width=2 by aaa_lref, ex_intro/
| #p * #G #L #V #T #_ #_ * #B #HV * #A #HA
  /3 width=2 by aaa_abbr, aaa_abst, ex_intro/
| #n #p #G #L #V #W #T0 #U0 #_ #_ #_ #HVW #HTU0 * #B #HV * #X #HT
  lapply (cpms_aaa_conf … HV … HVW) -HVW #H1W
  lapply (cpms_aaa_conf … HT … HTU0) -HTU0 #H
  elim (aaa_inv_abst … H) -H #B0 #A #H2W #HU #H destruct
  lapply (aaa_mono … H2W … H1W) -W #H destruct
  /3 width=4 by aaa_appl, ex_intro/
| #G #L #U #T #U0 #_ #_ #HU0 #HTU0 * #B #HU * #A #HT
  lapply (cpms_aaa_conf … HU … HU0) -HU0 #HU0
  lapply (cpms_aaa_conf … HT … HTU0) -HTU0 #H
  lapply (aaa_mono … H … HU0) -U0 #H destruct
  /3 width=3 by aaa_cast, ex_intro/
]
qed-.

(* Forward lemmas with t_bound rt_transition for terms **********************)

lemma cnv_fwd_cpm_SO (a) (h) (G) (L):
      ∀T. ⦃G, L⦄ ⊢ T ![a, h] → ∃U. ⦃G,L⦄ ⊢ T ➡[1,h] U.
#a #h #G #L #T #H
elim (cnv_fwd_aaa … H) -H #A #HA
/2 width=2 by aaa_cpm_SO/
qed-.

(* Forward lemmas with t_bound rt_computation for terms *********************)

lemma cnv_fwd_cpms_total (a) (h) (n) (G) (L):
      ∀T. ⦃G, L⦄ ⊢ T ![a, h] → ∃U. ⦃G,L⦄ ⊢ T ➡*[n,h] U.
#a #h #n #G #L #T #H
elim (cnv_fwd_aaa … H) -H #A #HA
/2 width=2 by cpms_total_aaa/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma cnv_inv_appl_pred (a) (h) (G) (L):
      ∀V,T. ⦃G, L⦄ ⊢ ⓐV.T ![yinj a, h] →
      ∃∃p,W0,U0. ⦃G, L⦄ ⊢ V ![a, h] & ⦃G, L⦄ ⊢ T ![a, h] &
                   ⦃G, L⦄ ⊢ V ➡*[1, h] W0 & ⦃G, L⦄ ⊢ T ➡*[↓a, h] ⓛ{p}W0.U0.
#a #h #G #L #V #T #H
elim (cnv_inv_appl … H) -H #n #p #W #U #Ha #HV #HT #HVW #HTU
lapply (ylt_inv_inj … Ha) -Ha #Ha
elim (cnv_fwd_aaa … HT) #A #HA
elim (cpms_total_aaa h … (a-↑n) … (ⓛ{p}W.U))
[|*: /2 width=8 by cpms_aaa_conf/ ] -HA #X #HU0
elim (cpms_inv_abst_sn … HU0) #W0 #U0 #HW0 #_ #H destruct
lapply (cpms_trans … HVW … HW0) -HVW -HW0 #HVW0
lapply (cpms_trans … HTU … HU0) -HTU -HU0
>(arith_m2 … Ha) -Ha #HTU0
/2 width=5 by ex4_3_intro/
qed-.
