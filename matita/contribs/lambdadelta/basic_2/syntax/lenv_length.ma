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

include "basic_2/syntax/lenv.ma".

(* LENGTH OF A LOCAL ENVIRONMENT ********************************************)

rec definition length L ≝ match L with
[ LAtom       ⇒ 0
| LPair L _ _ ⇒ ⫯(length L)
].

interpretation "length (local environment)" 'card L = (length L).

(* Basic properties *********************************************************)

lemma length_atom: |⋆| = 0.
// qed.

lemma length_pair: ∀I,L,V. |L.ⓑ{I}V| = ⫯|L|.
// qed.

(* Basic inversion lemmas ***************************************************)

lemma length_inv_zero_dx: ∀L. |L| = 0 → L = ⋆.
* // #L #I #V >length_pair
#H destruct
qed-.

lemma length_inv_zero_sn: ∀L. 0 = |L| → L = ⋆.
/2 width=1 by length_inv_zero_dx/ qed-.

(* Basic_2A1: was: length_inv_pos_dx *)
lemma length_inv_succ_dx: ∀n,L. |L| = ⫯n →
                          ∃∃I,K,V. |K| = n & L = K. ⓑ{I}V.
#n * [ >length_atom #H destruct ]
#L #I #V >length_pair /3 width=5 by ex2_3_intro, injective_S/
qed-.

(* Basic_2A1: was: length_inv_pos_sn *)
lemma length_inv_succ_sn: ∀n,L. ⫯n = |L| →
                          ∃∃I,K,V. n = |K| & L = K. ⓑ{I}V.
#l #L #H lapply (sym_eq ??? H) -H 
#H elim (length_inv_succ_dx … H) -H /2 width=5 by ex2_3_intro/
qed-.

(* Basic_2A1: removed theorems 1: length_inj *)