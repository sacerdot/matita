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

include "basic_2/grammar/term_weight.ma".
include "basic_2/grammar/lenv.ma".

(* WEIGHT OF A LOCAL ENVIRONMENT ********************************************)

let rec lw L ≝ match L with
[ LAtom       ⇒ 0
| LPair L _ V ⇒ lw L + #[V]
].

interpretation "weight (local environment)" 'Weight L = (lw L).

(* Basic properties *********************************************************)

lemma lw_pair: ∀I,L,V. #[L] < #[(L.ⓑ{I}V)].
/3 width=1/ qed.

(* Basic eliminators ********************************************************)

axiom lw_wf_ind: ∀R:predicate lenv.
                 (∀L2. (∀L1. #[L1] < #[L2] → R L1) → R L2) →
                 ∀L. R L.

(* Basic_1: removed theorems 2: clt_cong clt_head clt_thead *)
(* Basic_1: note: clt_thead should be renamed clt_ctail *)
