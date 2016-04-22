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

include "basic_2/relocation/drops.ma".
include "basic_2/rt_transition/cpg.ma".

(* CONTEXT-SENSITIVE GENERIC PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with generic slicing for local environments *******************)

(* Note: the main property of simple terms *)
lemma cpg_inv_appl1_simple: ∀h,r,G,L,V1,T1,U. ⦃G, L⦄ ⊢ ⓐV1.T1 ➡[h, r] U → 𝐒⦃T1⦄ →
                            ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, r] V2 & ⦃G, L⦄ ⊢ T1 ➡[h, r] T2 &
                                     U = ⓐV2.T2.
#h #r #G #L #V1 #T1 #U #H #HT1
elim (cpg_inv_appl1 … H) -H *
[ /2 width=5 by ex3_2_intro/
| #a #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
| #a #V #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
]
qed-.
