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

include "basic_2/rt_transition/cpm_drops.ma".

(* CONTEXT-SENSITIVE PARALLEL R-TRANSITION FOR TERMS ************************)

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: includes: cpr_inv_atom1 *)
lemma cpr_inv_atom1_drops: ∀h,I,G,L,T2. ⦃G, L⦄ ⊢ ⓪{I} ➡[h] T2 →
                           ∨∨ T2 = ⓪{I}
                            | ∃∃K,V,V2,i. ⬇*[i] L ≘ K.ⓓV & ⦃G, K⦄ ⊢ V ➡[h] V2 &
                                          ⬆*[↑i] V2 ≘ T2 & I = LRef i.
#h #I #G #L #T2 #H elim (cpm_inv_atom1_drops … H) -H *
[ /2 width=1 by or_introl/
| #s #_ #_ #H destruct
| /3 width=8 by ex4_4_intro, or_intror/
| #m #K #V1 #V2 #i #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic_1: includes: pr0_gen_lref pr2_gen_lref *)
(* Basic_2A1: includes: cpr_inv_lref1 *)
lemma cpr_inv_lref1_drops: ∀h,G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡[h] T2 →
                           ∨∨ T2 = #i
                            | ∃∃K,V,V2. ⬇*[i] L ≘ K. ⓓV & ⦃G, K⦄ ⊢ V ➡[h] V2 &
                                        ⬆*[↑i] V2 ≘ T2.
#h #G #L #T2 #i #H elim (cpm_inv_lref1_drops … H) -H *
[ /2 width=1 by or_introl/
| /3 width=6 by ex3_3_intro, or_intror/
| #m #K #V1 #V2 #_ #_ #_ #H destruct
]
qed-.
