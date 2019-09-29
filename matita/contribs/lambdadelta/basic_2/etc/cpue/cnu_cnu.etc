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

include "static_2/syntax/tueq_tueq.ma".
include "basic_2/rt_transition/cpm_tueq.ma".
include "basic_2/rt_transition/cnu.ma".

(* NORMAL TERMS FOR T-UNUNBOUND RT-TRANSITION *******************************)

(* Advanced properties ******************************************************)

lemma cnu_tueq_trans (h) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃T1⦄ → ∀T2.T1 ≅ T2 → ⦃G,L⦄ ⊢ ⥲[h] 𝐍⦃T2⦄.
#h #G #L #T1 #HT1 #T2 #HT12 #n #T0 #HT20
@(tueq_canc_sn … HT12)
elim (tueq_cpm_trans … HT12 … HT20) -T2 #T2 #HT13 #HT30
/3 width=3 by tueq_trans/
qed-.
