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

include "static_2/notation/functions/weight_1.ma".
include "static_2/syntax/term.ma".

(* WEIGHT OF A TERM *********************************************************)

rec definition tw T ≝ match T with
[ TAtom _     ⇒ 1
| TPair _ V T ⇒ ↑(tw V + tw T)
].

interpretation "weight (term)" 'Weight T = (tw T).

(* Basic properties *********************************************************)

(* Basic_1: was: tweight_lt *)
lemma tw_pos: ∀T. 1 ≤ ♯{T}.
#T elim T -T //
qed.

(* Basic_1: removed theorems 11:
            wadd_le wadd_lt wadd_O weight_le weight_eq weight_add_O
            weight_add_S tlt_trans tlt_head_sx tlt_head_dx tlt_wf_ind
*)
(* Basic_1: removed local theorems 1: q_ind *)
