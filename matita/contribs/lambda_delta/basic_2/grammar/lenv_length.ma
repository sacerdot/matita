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

include "basic_2/grammar/lenv.ma".

(* LENGTH OF A LOCAL ENVIRONMENT ********************************************)

let rec length L ≝ match L with
[ LAtom       ⇒ 0
| LPair L _ _ ⇒ length L + 1
].

interpretation "length (local environment)" 'card L = (length L).

(* Basic inversion lemmas ***************************************************)

lemma length_inv_zero_dx: ∀L. |L| = 0 → L = ⋆.
* // #L #I #V normalize <plus_n_Sm #H destruct
qed-.

lemma length_inv_zero_sn: ∀L. 0 = |L| → L = ⋆.
* // #L #I #V normalize <plus_n_Sm #H destruct
qed-.

lemma length_inv_pos_dx: ∀d,L. |L| = d + 1 →
                         ∃∃I,K,V. |K| = d & L = K. ⓑ{I}V.
#d *
[ normalize <plus_n_Sm #H destruct
| #K #I #V #H
  lapply (injective_plus_l … H) -H /2 width=5/
]
qed-.

lemma length_inv_pos_sn: ∀d,L. d + 1 = |L| →
                         ∃∃I,K,V. d = |K| & L = K. ⓑ{I}V.
#d *
[ normalize <plus_n_Sm #H destruct
| #K #I #V #H
  lapply (injective_plus_l … H) -H /2 width=5/
]
qed-.
