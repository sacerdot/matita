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

include "static_2/syntax/teqx.ma".
include "basic_2/rt_transition/cpm_drops.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Inversion lemmas with sort-irrelevant equivalence for terms **************)

lemma cpm_teqx_inv_lref_sn (n) (h) (G) (L) (i):
                           ∀X.  ❪G,L❫ ⊢ #i ➡[n,h] X → #i ≛ X →
                           ∧∧ X = #i & n = 0.
#n #h #G #L #i #X #H1 #H2
lapply (teqx_inv_lref1 … H2) -H2 #H destruct
elim (cpm_inv_lref1_drops … H1) -H1 // * [| #m ]
#K #V1 #V2 #_ #_ #H -V1
elim (lifts_inv_lref2_uni_lt … H) -H //
qed-.

lemma cpm_teqx_inv_atom_sn (n) (h) (I) (G) (L):
                           ∀X. ❪G,L❫ ⊢ ⓪[I] ➡[n,h] X → ⓪[I] ≛ X →
                           ∨∨ ∧∧ X = ⓪[I] & n = 0
                            | ∃∃s. X = ⋆(⫯[h]s) & I = Sort s & n = 1.
#n #h * #s #G #L #X #H1 #H2
[ elim (cpm_inv_sort1 … H1) -H1
  cases n -n [| #n ] #H #Hn destruct -H2
  [ /3 width=1 by or_introl, conj/
  | <(le_n_O_to_eq n) [| /2 width=3 by le_S_S_to_le/ ] -n
    /3 width=3 by ex3_intro, or_intror/
  ]
| elim (cpm_teqx_inv_lref_sn … H1 H2) -H1 -H2 /3 width=1 by or_introl, conj/
| elim (cpm_inv_gref1 … H1) -H1 -H2 /3 width=1 by or_introl, conj/
]
qed-.
