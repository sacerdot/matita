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

include "ground_2/ynat/ynat_lt.ma".
include "basic_2/grammar/lenv.ma".

(* LENGTH OF A LOCAL ENVIRONMENT ********************************************)

let rec length L ≝ match L with
[ LAtom       ⇒ 0
| LPair L _ _ ⇒ ⫯(length L)
].

interpretation "length (local environment)" 'card L = (length L).

(* Basic properties *********************************************************)

lemma length_atom: |⋆| = 0.
// qed.

lemma length_pair: ∀I,L,V. |L.ⓑ{I}V| = ⫯|L|.
// qed.

lemma length_inj: ∀L. |L| < ∞.
#L elim L -L /2 width=1 by ylt_succ_Y/
qed.

(* Basic inversion lemmas ***************************************************)

lemma length_inv_zero_dx: ∀L. |L| = 0 → L = ⋆.
* // #L #I #V >length_pair
#H elim (ysucc_inv_O_dx … H)
qed-.

lemma length_inv_zero_sn: ∀L. yinj 0 = |L| → L = ⋆.
/2 width=1 by length_inv_zero_dx/ qed-.

lemma length_inv_pos_dx: ∀l,L. |L| = ⫯l →
                         ∃∃I,K,V. |K| = l & L = K. ⓑ{I}V.
#l * /3 width=5 by ysucc_inj, ex2_3_intro/
>length_atom #H elim (ysucc_inv_O_sn … H)
qed-.

lemma length_inv_pos_sn: ∀l,L. ⫯l = |L| →
                         ∃∃I,K,V. l = |K| & L = K. ⓑ{I}V.
#l #L #H lapply (sym_eq ??? H) -H 
#H elim (length_inv_pos_dx … H) -H /2 width=5 by ex2_3_intro/
qed-.
