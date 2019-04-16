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

include "basic_2/rt_transition/cnr.ma".
include "basic_2/rt_transition/cnu.ma".

(* NORMAL TERMS FOR T-UNUNBOUND RT-TRANSITION *******************************)

(* Advanced properties with normal terms for r-transition *******************)

lemma cnu_abst (h) (p) (G) (L):
      ∀W. ⦃G,L⦄ ⊢ ➡[h] 𝐍⦃W⦄ → ∀T.⦃G,L.ⓛW⦄ ⊢ ⥲[h] 𝐍⦃T⦄ → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃ⓛ{p}W.T⦄.
#h #p #G #L #W1 #HW1 #T1 #HT1 #n #X #H
elim (cpm_inv_abst1 … H) -H #W2 #T2 #HW12 #HT12 #H destruct
<(HW1 … HW12) -W2 /3 width=2 by tueq_bind/
qed.

lemma cnu_abbr_neg (h) (G) (L):
      ∀V. ⦃G,L⦄ ⊢ ➡[h] 𝐍⦃V⦄ → ∀T.⦃G,L.ⓓV⦄ ⊢ ⥲[h] 𝐍⦃T⦄ → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃-ⓓV.T⦄.
#h #G #L #V1 #HV1 #T1 #HT1 #n #X #H
elim (cpm_inv_abbr1 … H) -H *
[ #V2 #T2 #HV12 #HT12 #H destruct
  <(HV1 … HV12) -V2 /3 width=2 by tueq_bind/
| #X1 #_ #_ #H destruct
]
qed. 
