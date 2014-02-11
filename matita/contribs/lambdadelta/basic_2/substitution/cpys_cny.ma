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

include "basic_2/relocation/cny.ma".
include "basic_2/substitution/cpys.ma".

(* CONTEXT-SENSITIVE EXTENDED MULTIPLE SUBSTITUTION FOR TERMS ***************)

(* Inversion lemmas on normality for extended substitution ******************)

lemma cpys_inv_cny1: ∀G,L,T1,d,e. ⦃G, L⦄ ⊢ ▶[d, e] 𝐍⦃T1⦄ →
                     ∀T2. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → T1 = T2.
#G #L #T1 #d #e #HT1 #T2 #H @(cpys_ind … H) -T2 //
#T #T2 #_ #HT2 #IHT1 destruct <(HT1 … HT2) -T //
qed-.
