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
[ BUnit _   ⇒ 1
| BPair _ V ⇒ ♯❨V❩
].

interpretation "weight (binder for local environments)" 'Weight I = (bw I).

(* Basic properties *********************************************************)

lemma bw_pos: ∀I. 1 ≤ ♯❨I❩.
* //
qed.
