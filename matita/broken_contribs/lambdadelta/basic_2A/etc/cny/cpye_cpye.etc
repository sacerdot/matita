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

include "basic_2/substitution/cpys_cny.ma".
include "basic_2/substitution/cpys_cpys.ma".
include "basic_2/substitution/cpye.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE EXTENDED SUBSTITUTION ON TERMS **********)

(* Advanced properties ******************************************************)

lemma cpye_cpys_conf: ∀G,L,T,T2,d,e. ⦃G, L⦄ ⊢ T ▶*[d, e] 𝐍⦃T2⦄ →
                      ∀T1. ⦃G, L⦄ ⊢ T ▶*[d, e] T1 → ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2.
#G #L #T #T2 #d #e * #H2 #HT2 #T1 #H1 elim (cpys_conf_eq … H1 … H2) -T
#T0 #HT10 #HT20 >(cpys_inv_cny1 … HT2 … HT20) -T2 //
qed-.
   