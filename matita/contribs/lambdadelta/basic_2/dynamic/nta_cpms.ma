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

include "basic_2/rt_computation/cprs_cprs.ma".
include "basic_2/dynamic/cnv_aaa.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Properties with advanced rt_computation for terms ************************)

(* Basic_2A1: uses by definition nta_appl ntaa_appl *)
lemma nta_appl_abst (a) (h) (p) (G) (L):
      ∀n. appl a n →
      ∀V,W. ⦃G,L⦄ ⊢ V :[a,h] W →
      ∀T,U. ⦃G,L.ⓛW⦄ ⊢ T :[a,h] U → ⦃G,L⦄ ⊢ ⓐV.ⓛ{p}W.T :[a,h] ⓐV.ⓛ{p}W.U.
#a #h #p #G #L #n #Ha #V #W #H1 #T #U #H2
elim (cnv_inv_cast … H1) -H1 #X1 #HW #HV #HWX1 #HVX1
elim (cnv_inv_cast … H2) -H2 #X2 #HU #HT #HUX2 #HTX2
/4 width=11 by cnv_appl_ge, cnv_cast, cnv_bind, cpms_appl_dx, cpms_bind_dx/
qed.

(* Basic_1: was by definition: ty3_appl *)
(* Basic_2A1: was nta_appl_old *)
lemma nta_appl (a) (h) (p) (G) (L):
      ∀n. 1 ≤ n → appl a n →
      ∀V,W. ⦃G,L⦄ ⊢ V :[a,h] W →
      ∀T,U. ⦃G,L⦄ ⊢ T :[a,h] ⓛ{p}W.U → ⦃G,L⦄ ⊢ ⓐV.T :[a,h] ⓐV.ⓛ{p}W.U.
#a #h #p #G #L #n #Hn #Ha #V #W #H1 #T #U #H2
elim (cnv_inv_cast … H1) -H1 #X1 #HW #HV #HWX1 #HVX1
elim (cnv_inv_cast … H2) -H2 #X2 #HU #HT #HUX2 #HTX2
elim (cpms_inv_abst_sn … HUX2) #W0 #U0 #HW0 #HU0 #H destruct
elim (cprs_conf … HWX1 … HW0) -HW0 #X0 #HX10 #HWX0
@(cnv_cast … (ⓐV.ⓛ{p}W0.U0)) (**) (* full auto too slow *)
[ /2 width=11 by cnv_appl_ge/
| /3 width=11 by cnv_appl_ge, cpms_cprs_trans/
| /2 width=1 by cpms_appl_dx/
| /2 width=1 by cpms_appl_dx/
]
qed.

(* Inversion lemmas with advanced rt_computation for terms ******************)

lemma nta_inv_abst_bi_cnv (a) (h) (p) (G) (K) (W):
      ∀T,U. ⦃G,K⦄ ⊢ ⓛ{p}W.T :[a,h] ⓛ{p}W.U →
      ∧∧ ⦃G,K⦄ ⊢ W ![a,h] & ⦃G,K.ⓛW⦄ ⊢ T :[a,h] U.
#a #h #p #G #K #W #T #U #H
elim (cnv_inv_cast … H) -H #X #HWU #HWT #HUX #HTX
elim (cnv_inv_bind … HWU) -HWU #HW #HU
elim (cnv_inv_bind … HWT) -HWT #_ #HT
elim (cpms_inv_abst_sn … HUX) -HUX #W0 #X0 #_ #HUX0 #H destruct
elim (cpms_inv_abst_bi … HTX) -HTX #_ #_ #HTX0 -W0
/3 width=3 by cnv_cast, conj/
qed-.
