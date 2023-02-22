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

include "static_2/syntax/term_weight.ma".
include "static_2/syntax/bind.ma".

(* WEIGHT OF A BINDER FOR LOCAL ENVIRONMENTS *******************************)

rec definition bw I ≝ match I with
[ BUnit _   ⇒ 𝟏
| BPair _ V ⇒ ♯❨V❩
].

interpretation
  "weight (binder for local environments)"
  'Weight I = (bw I).

(* Basic properties *********************************************************)

lemma bw_unit_unfold (I): 𝟏 = ♯❨BUnit I❩.
// qed.

lemma bw_pair_unfold (I) (V): ♯❨V❩ = ♯❨BPair I V❩.
// qed.
