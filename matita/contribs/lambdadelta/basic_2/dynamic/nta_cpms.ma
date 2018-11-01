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
include "basic_2/rt_computation/lprs_cpms.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Properties with rt_computation for terms *********************************)

(* Basic_2A1: was by definition nta_appl ntaa_appl *)
lemma nta_beta (a) (h) (p) (G) (K):
      ∀V,W. ⦃G,K⦄ ⊢ V :[a,h] W →
      ∀T,U. ⦃G,K.ⓛW⦄ ⊢ T :[a,h] U → ⦃G,K⦄ ⊢ ⓐV.ⓛ{p}W.T :[a,h] ⓐV.ⓛ{p}W.U.
#a #h #p #G #K #V #W #H1 #T #U #H2
elim (cnv_inv_cast … H1) -H1 #X1 #HW #HV #HWX1 #HVX1
elim (cnv_inv_cast … H2) -H2 #X2 #HU #HT #HUX2 #HTX2
/4 width=7 by cnv_bind, cnv_appl, cnv_cast, cpms_appl_dx, cpms_bind_dx/
qed.

(* Basic_1: was by definition: ty3_appl *)
(* Basic_2A1: was nta_appl_old *)
lemma nta_appl (a) (h) (p) (G) (L):
      ∀V,W. ⦃G,L⦄ ⊢ V :[a,h] W →
      ∀T,U. ⦃G,L⦄ ⊢ T :[a,h] ⓛ{p}W.U → ⦃G,L⦄ ⊢ ⓐV.T :[a,h] ⓐV.ⓛ{p}W.U.
#a #h #p #G #L #V #W #H1 #T #U #H2
elim (cnv_inv_cast … H1) -H1 #X1 #HW #HV #HWX1 #HVX1
elim (cnv_inv_cast … H2) -H2 #X2 #HU #HT #HUX2 #HTX2
elim (cpms_inv_abst_sn … HUX2) #W0 #U0 #HW0 #HU0 #H destruct
elim (cprs_conf … HWX1 … HW0) -HW0 #X0 #HX10 #HWX0
@(cnv_cast … (ⓐV.ⓛ{p}W0.U0)) (**) (* full auto too slow *)
[ /3 width=7 by cnv_appl, cpms_bind/
| /4 width=11 by cnv_appl, cpms_cprs_trans, cpms_bind/
| /2 width=1 by cpms_appl_dx/
| /2 width=1 by cpms_appl_dx/
]
qed.
