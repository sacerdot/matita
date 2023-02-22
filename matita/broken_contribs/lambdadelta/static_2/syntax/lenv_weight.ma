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

rec definition lw L ≝ match L with
[ LAtom     ⇒ 𝟏
| LBind L I ⇒ lw L + ♯❨I❩
].

interpretation "weight (local environment)" 'Weight L = (lw L).

(* Basic properties *********************************************************)

lemma lw_atom_unfold: 𝟏 = ♯❨⋆❩.
// qed.

lemma lw_bind_unfold (I) (L): ♯❨L❩ + ♯❨I❩ = ♯❨L.ⓘ[I]❩.
// qed.

(* Basic_2A1: uses: lw_pair *)
lemma lw_bind: ∀I,L. ♯❨L❩ < ♯❨L.ⓘ[I]❩.
// qed.

(* Basic_1: removed theorems 4: clt_cong clt_head clt_thead clt_wf_ind *)
(* Basic_1: removed local theorems 1: clt_wf__q_ind *)
(* Basic_1: note: clt_thead should be renamed clt_ctail *)
