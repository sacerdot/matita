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

include "basic_2/rt_computation/cpms_aaa.ma".
include "basic_2/rt_equivalence/cpcs_cprs.ma".

(* CONTEXT-SENSITIVE PARALLEL EQUIVALENCE ON TERMS **************************)

(* Main inversion lemmas with atomic arity assignment on terms **************)

(* Note: lemma 1500 *)
theorem cpcs_aaa_mono (h) (G) (L): ∀T1,T2. ❨G,L❩ ⊢ T1 ⬌*[h] T2 →
                                   ∀A1. ❨G,L❩ ⊢ T1 ⁝ A1 → ∀A2. ❨G,L❩ ⊢ T2 ⁝ A2 →
                                   A1 = A2.
#h #G #L #T1 #T2 #HT12 #A1 #HA1 #A2 #HA2
elim (cpcs_inv_cprs … HT12) -HT12 #T #HT1 #HT2
lapply (cpms_aaa_conf … HA1 … HT1) -T1 #HA1
lapply (cpms_aaa_conf … HA2 … HT2) -T2 #HA2
lapply (aaa_mono … HA1 … HA2) -L -T //
qed-.
