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
include "basic_2/rt_transition/cnu.ma".

(* NORMAL TERMS FOR T-UNUNBOUND RT-TRANSITION *******************************)

(* Advanced properties with simple terms and normal terms for r-transition **)

lemma cnu_appl_simple (h) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ➡[h] 𝐍⦃V⦄ → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃T⦄ → 𝐒⦃T⦄ → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃ⓐV.T⦄.
#h #G #L #V1 #T1 #HV1 #HT1 #HS #n #X #H
elim (cpm_inv_appl1_simple … H HS) -H -HS #V2 #T2 #HV12 #HT12 #H destruct
lapply (HV1 … HV12) -HV1 -HV12 #H destruct
/3 width=2 by tueq_appl/
qed.
