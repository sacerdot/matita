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

include "static_2/syntax/term_vector.ma".
include "static_2/syntax/toeq_simple.ma".

(* SORT-IRRELEVANT OUTER EQUIVALENCE FOR TERMS ******************************)

(* Advanced inversion lemmas with simple (neutral) terms ********************)

(* Basic_1: was only: iso_flats_lref_bind_false iso_flats_flat_bind_false *)
(* Basic_2A1: was: tsts_inv_bind_applv_simple *)
lemma toeq_inv_applv_bind_simple (p) (I):
      ∀Vs,V2,T1,T2. ⒶVs.T1 ⩳ ⓑ{p,I}V2.T2 → 𝐒⦃T1⦄ → ⊥.
#p #I #Vs #V2 #T1 #T2 #H elim (toeq_inv_pair2 … H) -H
#V0 #T0 elim Vs -Vs normalize
[ #H destruct #H /2 width=5 by simple_inv_bind/
| #V #Vs #_ #H destruct
]
qed-.
