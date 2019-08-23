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
include "basic_2/rt_transition/cnh.ma".

(* NORMAL TERMS HEAD FOR T-UNUNBOUND RT-TRANSITION **************************)

(* Advanced properties with simple terms ************************************)

lemma cnh_appl_simple (h) (G) (L): ∀V,T. 𝐒⦃T⦄ → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃ⓐV.T⦄.
#h #G #L #V1 #T1 #HT1 #n #X #H
elim (cpm_inv_appl1_simple … H HT1) -H -HT1 #V2 #T2 #_ #_ #H destruct
/1 width=1 by theq_pair/
qed.
