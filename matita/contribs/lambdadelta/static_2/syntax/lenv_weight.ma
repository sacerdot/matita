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

include "static_2/syntax/bind_weight.ma".
include "static_2/syntax/lenv.ma".

(* WEIGHT OF A LOCAL ENVIRONMENT ********************************************)

rec definition lw L â match L with
[ LAtom     â ð
| LBind L I â lw L + â¯â¨Iâ©
].

interpretation "weight (local environment)" 'Weight L = (lw L).

(* Basic properties *********************************************************)

lemma lw_atom_unfold: ð = â¯â¨ââ©.
// qed.

lemma lw_bind_unfold (I) (L): â¯â¨Lâ© + â¯â¨Iâ© = â¯â¨L.â[I]â©.
// qed.

(* Basic_2A1: uses: lw_pair *)
lemma lw_bind: âI,L. â¯â¨Lâ© < â¯â¨L.â[I]â©.
// qed.

(* Basic_1: removed theorems 4: clt_cong clt_head clt_thead clt_wf_ind *)
(* Basic_1: removed local theorems 1: clt_wf__q_ind *)
(* Basic_1: note: clt_thead should be renamed clt_ctail *)
