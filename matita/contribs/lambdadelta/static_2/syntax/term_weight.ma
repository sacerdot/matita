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

include "ground/arith/pnat_lt_plus.ma".
include "static_2/notation/functions/weight_1.ma".
include "static_2/syntax/term.ma".

(* WEIGHT OF A TERM *********************************************************)

rec definition tw T â match T with
[ TAtom _     â ğ
| TPair _ V T â â(tw V + tw T)
].

interpretation "weight (term)" 'Weight T = (tw T).

(* Basic properties *********************************************************)

lemma tw_atom_unfold (I): ğ = â¯â¨âª[I]â©.
// qed.

lemma tw_pair_unfold (I) (V) (T): â(â¯â¨Vâ© + â¯â¨Tâ©) = â¯â¨â¡[I]V.Tâ©.
// qed.

lemma tw_le_pair_dx (I): âV,T. â¯â¨Tâ© < â¯â¨â¡[I]V.Tâ©.
/2 width=1 by plt_succ_dx_trans/
qed.

(* Basic_1: removed theorems 12:
            tweight_lt
            wadd_le wadd_lt wadd_O weight_le weight_eq weight_add_O
            weight_add_S tlt_trans tlt_head_sx tlt_head_dx tlt_wf_ind
*)
(* Basic_1: removed local theorems 1: q_ind *)
