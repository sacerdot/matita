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

include "Basic_2/grammar/term.ma".

(* WEIGHT OF A TERM *********************************************************)

let rec tw T ≝ match T with
[ TAtom _     ⇒ 1
| TPair _ V T ⇒ tw V + tw T + 1
].

interpretation "weight (term)" 'Weight T = (tw T).

(* Basic properties *********************************************************)

lemma tw_pos: ∀T. 1 ≤ #[T].
#T elim T -T /2/ 
qed.

(* Basic eliminators ********************************************************)

axiom tw_wf_ind: ∀R:term→Prop.
                 (∀T2. (∀T1. #[T1] < #[T2] → R T1) → R T2) →
                 ∀T. R T.

(* Basic_1: removed theorems 11:
            wadd_le wadd_lt wadd_O weight_le weight_eq weight_add_O
	    weight_add_S tlt_trans tlt_head_sx tlt_head_dx tlt_wf_ind
            removed local theorems 1: q_ind
*)
