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

include "basic_2/rt_transition/cpg_simple.ma".
include "basic_2/rt_transition/cpx.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS **************)

(* Inversion lemmas with simple terms ***************************************)

lemma cpx_inv_appl1_simple (G) (L):
      ∀V1,T1,U. ❨G,L❩ ⊢ ⓐV1.T1 ⬈ U → 𝐒❨T1❩ →
      ∃∃V2,T2. ❨G,L❩ ⊢ V1 ⬈ V2 & ❨G,L❩ ⊢ T1 ⬈ T2 & U = ⓐV2.T2.
#G #L #V1 #T1 #U * #c #H #HT1 elim (cpg_inv_appl1_simple … H) -H
/3 width=5 by ex3_2_intro, ex_intro/
qed-.
