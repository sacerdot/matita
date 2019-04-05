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

include "basic_2/rt_transition/cpm_simple.ma".
include "basic_2/rt_transition/cnr.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE R-TRANSITION **************************)

(* Inversion lemmas with simple terms ***************************************)

lemma cnr_inv_appl (h) (G) (L):
      ∀V,T. ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃ⓐV.T⦄ → ∧∧ ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃V⦄ & ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃T⦄ & 𝐒⦃T⦄.
#h #G #L #V1 #T1 #HVT1 @and3_intro
[ #V2 #HV2 lapply (HVT1 (ⓐV2.T1) ?) -HVT1 /2 width=1 by cpr_pair_sn/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓐV1.T2) ?) -HVT1 /2 width=1 by cpr_flat/ -HT2 #H destruct //
| generalize in match HVT1; -HVT1 elim T1 -T1 * // #a * #W1 #U1 #_ #_ #H
  [ elim (lifts_total V1 𝐔❴1❵) #V2 #HV12
    lapply (H (ⓓ{a}W1.ⓐV2.U1) ?) -H /2 width=3 by cpm_theta/ -HV12 #H destruct
  | lapply (H (ⓓ{a}ⓝW1.V1.U1) ?) -H /2 width=1 by cpm_beta/ #H destruct
  ]
]
qed-.

(* Properties with simple terms *********************************************)

(* Basic_1: was only: nf2_appl_lref *)
lemma cnr_appl_simple (h) (G) (L):
      ∀V,T. ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃V⦄ → ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃T⦄ → 𝐒⦃T⦄ → ⦃G, L⦄ ⊢ ➡[h] 𝐍⦃ⓐV.T⦄.
#h #G #L #V #T #HV #HT #HS #X #H
elim (cpm_inv_appl1_simple … H) -H // #V0 #T0 #HV0 #HT0 #H destruct
<(HV … HV0) -V0 <(HT … HT0) -T0 //
qed.
