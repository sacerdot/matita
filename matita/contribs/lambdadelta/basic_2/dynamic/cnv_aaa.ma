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

include "basic_2/rt_computation/cpms_aaa.ma".
include "basic_2/dynamic/cnv.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Forward lemmas on atomic arity assignment for terms **********************)

(* Basic_2A1: uses: snv_fwd_aaa *)
lemma cnv_fwd_aaa (h) (a):
      ∀G,L,T. ❪G,L❫ ⊢ T ![h,a] → ∃A. ❪G,L❫ ⊢ T ⁝ A.
#h #a #G #L #T #H elim H -G -L -T
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

lemma cnv_fwd_cpm_SO (h) (a) (G) (L):
      ∀T. ❪G,L❫ ⊢ T ![h,a] → ∃U. ❪G,L❫ ⊢ T ➡[h,1] U.
#h #a #G #L #T #H
elim (cnv_fwd_aaa … H) -H #A #HA
/2 width=2 by aaa_cpm_SO/
qed-.

(* Forward lemmas with t_bound rt_computation for terms *********************)

lemma cnv_fwd_cpms_total (h) (a) (n) (G) (L):
      ∀T. ❪G,L❫ ⊢ T ![h,a] → ∃U. ❪G,L❫ ⊢ T ➡*[h,n] U.
#h #a #n #G #L #T #H
elim (cnv_fwd_aaa … H) -H #A #HA
/2 width=2 by cpms_total_aaa/
qed-.

lemma cnv_fwd_cpms_abst_dx_le (h) (a) (G) (L) (W) (p):
      ∀T. ❪G,L❫ ⊢ T ![h,a] →
      ∀n1,U1. ❪G,L❫ ⊢ T ➡*[h,n1] ⓛ[p]W.U1 → ∀n2. n1 ≤ n2 →
      ∃∃U2. ❪G,L❫ ⊢ T ➡*[h,n2] ⓛ[p]W.U2 & ❪G,L.ⓛW❫ ⊢ U1 ➡*[h,n2-n1] U2.
#h #a #G #L #W #p #T #H
elim (cnv_fwd_aaa … H) -H #A #HA
/2 width=2 by cpms_abst_dx_le_aaa/
qed-.

(* Advanced properties ******************************************************)

lemma cnv_appl_ge (h) (a) (n1) (p) (G) (L):
      ∀n2. n1 ≤ n2 → ad a n2 →
      ∀V. ❪G,L❫ ⊢ V ![h,a] → ∀T. ❪G,L❫ ⊢ T ![h,a] →
      ∀X. ❪G,L❫ ⊢ V ➡*[h,1] X → ∀W. ❪G,L❫ ⊢ W ➡*[h,0] X →
      ∀U. ❪G,L❫ ⊢ T ➡*[h,n1] ⓛ[p]W.U → ❪G,L❫ ⊢ ⓐV.T ![h,a].
#h #a #n1 #p #G #L #n2 #Hn12 #Ha #V #HV #T #HT #X #HVX #W #HW #X #HTX
elim (cnv_fwd_cpms_abst_dx_le  … HT … HTX … Hn12) #U #HTU #_ -n1
/4 width=11 by cnv_appl, cpms_bind, cpms_cprs_trans/
qed.
