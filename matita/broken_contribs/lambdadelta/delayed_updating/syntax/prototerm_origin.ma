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

include "ground/lib/subset_le.ma".
include "ground/lib/subset_empty.ma".
include "delayed_updating/syntax/subset_fired.ma".
include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/notation/functions/subset_o_0.ma".

(* ORIGIN FOR PROTOTERM ************************************************)

definition toc: 𝒫❨𝕋❩ ≝
           {t | 𝐅❨t❩ ⊆ Ⓕ}
.

interpretation
  "origin (prototerm)"
  'SubsetO = (toc).

(* Basic properties *********************************************************)

lemma toc_mk (t):
      (𝐅❨t❩) ⊆ Ⓕ → t ϵ 𝐎.
/2 width=1 by/
qed.
