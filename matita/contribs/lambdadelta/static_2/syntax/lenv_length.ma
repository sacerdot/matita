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

include "static_2/syntax/lenv.ma".

(* LENGTH OF A LOCAL ENVIRONMENT ********************************************)

rec definition length L ≝ match L with
[ LAtom     ⇒ 0
| LBind L _ ⇒ ↑(length L)
].

interpretation "length (local environment)" 'card L = (length L).

(* Basic properties *********************************************************)

lemma length_atom: |⋆| = 0.
// qed.

(* Basic_2A1: uses: length_pair *)
lemma length_bind: ∀I,L. |L.ⓘ{I}| = ↑|L|.
// qed.

(* Basic inversion lemmas ***************************************************)

lemma length_inv_zero_dx: ∀L. |L| = 0 → L = ⋆.
* // #L #I >length_bind
#H destruct
qed-.

lemma length_inv_zero_sn: ∀L. 0 = |L| → L = ⋆.
/2 width=1 by length_inv_zero_dx/ qed-.

(* Basic_2A1: was: length_inv_pos_dx *)
lemma length_inv_succ_dx: ∀n,L. |L| = ↑n →
                          ∃∃I,K. |K| = n & L = K. ⓘ{I}.
#n *
[ >length_atom #H destruct
| #L #I >length_bind /3 width=4 by ex2_2_intro, injective_S/
]
qed-.

(* Basic_2A1: was: length_inv_pos_sn *)
lemma length_inv_succ_sn: ∀n,L. ↑n = |L| →
                          ∃∃I,K. n = |K| & L = K. ⓘ{I}.
#n #L #H lapply (sym_eq ??? H) -H 
#H elim (length_inv_succ_dx … H) -H /2 width=4 by ex2_2_intro/
qed-.

(* Basic_2A1: removed theorems 1: length_inj *)
