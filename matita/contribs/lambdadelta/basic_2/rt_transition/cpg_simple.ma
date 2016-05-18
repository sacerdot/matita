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

include "basic_2/grammar/term_simple.ma".
include "basic_2/rt_transition/cpg.ma".

(* CONTEXT-SENSITIVE GENERIC PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Properties with simple terms *********************************************)

(* Note: the main property of simple terms *)
lemma cpg_inv_appl1_simple: ∀c,h,G,L,V1,T1,U. ⦃G, L⦄ ⊢ ⓐV1.T1 ➡[c, h] U → 𝐒⦃T1⦄ →
                            ∃∃cV,cT,V2,T2. ⦃G, L⦄ ⊢ V1 ➡[cV, h] V2 & ⦃G, L⦄ ⊢ T1 ➡[cT, h] T2 &
                                           U = ⓐV2.T2 & c = (↓cV)+cT.
#c #h #G #L #V1 #T1 #U #H #HT1 elim (cpg_inv_appl1 … H) -H *
[ /2 width=8 by ex4_4_intro/
| #cV #cW #cT #p #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #H destruct
  elim (simple_inv_bind … HT1)
| #cV #cW #cT #p #V #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #_ #H destruct
  elim (simple_inv_bind … HT1)
]
qed-.
