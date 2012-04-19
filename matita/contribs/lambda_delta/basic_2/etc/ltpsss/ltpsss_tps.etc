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

include "basic_2/unfold/ltpss_tps.ma".
include "basic_2/unfold/ltpsss.ma".

(* ITERATED PARTIAL UNFOLD ON LOCAL ENVIRONMENTS ****************************)

(* Properties concerning partial substitution on terms **********************)

lemma ltpsss_tps_trans_ge: ∀L1,L0,d1,e1. L1 [d1, e1] ▶** L0 →
                           ∀T2,U2,d2,e2. L0 ⊢ T2 [d2, e2] ▶ U2 →
                           d1 + e1 ≤ d2 → L1 ⊢ T2 [d2, e2] ▶ U2.
#L1 #L0 #d1 #e1 #H @(ltpsss_ind … H) -L0 //
#L #L0 #_ #HL0 #IHL #T2 #U2 #d2 #e2 #HTU2 #Hde1d2
lapply (ltpss_tps_trans_ge … HTU2 … HL0 ?) -HL0 -HTU2 // /2 width=1/
qed.

lemma ltpsss_tps_conf_ge: ∀L0,L1,T2,U2,d1,e1,d2,e2. d1 + e1 ≤ d2 → 
                          L0 ⊢ T2 [d2, e2] ▶ U2 → L0 [d1, e1] ▶** L1 →
                          L1 ⊢ T2 [d2, e2] ▶ U2.
#L0 #L1 #T2 #U2 #d1 #e1 #d2 #e2 #Hde1d2 #HTU2 #H @(ltpsss_ind … H) -L1 //
-HTU2 #L #L1 #_ #HL1 #IHL
lapply (ltpss_tps_conf_ge … IHL … HL1 ?) -HL1 -IHL //
qed.
