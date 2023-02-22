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

include "basic_2/rt_computation/cpms_drops.ma".

(* CONTEXT-SENSITIVE PARALLEL R-COMPUTATION FOR TERMS ***********************)

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was: pr3_gen_lref *)
(* Basic_2A1: was: cprs_inv_lref1 *)
lemma cprs_inv_lref1_drops (h) (G): ∀L,T2,i. ❨G,L❩ ⊢ #i ➡*[h,0] T2 →
                                    ∨∨ T2 = #i
                                     | ∃∃K,V1,T1. ⇩[i] L ≘ K.ⓓV1 & ❨G,K❩ ⊢ V1 ➡*[h,0] T1 &
                                                  ⇧[↑i] T1 ≘ T2.
#h #G #L #T2 #i #H elim (cpms_inv_lref1_drops … H) -H *
[ /2 width=1 by or_introl/
| /3 width=6 by ex3_3_intro, or_intror/
| #m #K #V #V2 #_ #_ #_ #H destruct
]
qed-.
