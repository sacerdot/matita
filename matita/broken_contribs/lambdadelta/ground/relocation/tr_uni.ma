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

include "ground/arith/nat_succ.ma".
include "ground/notation/functions/element_u_1.ma".
include "ground/relocation/tr_id.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS *******************************)

definition tr_uni (n:nat): tr_map ≝ ↑n ⨮ 𝐢.

interpretation
  "uniform elements (total relocation maps)"
  'ElementU n = (tr_uni n).

(* Basic constructions ******************************************************)

lemma tr_uni_unfold (n): ↑n ⨮ 𝐢 = 𝐮❨n❩.
// qed.

lemma tr_uni_zero: 𝐢 = 𝐮❨𝟎❩.
<tr_id_unfold //
qed.

lemma tr_uni_succ (n): ↑𝐮❨n❩ = 𝐮❨↑n❩.
// qed.
