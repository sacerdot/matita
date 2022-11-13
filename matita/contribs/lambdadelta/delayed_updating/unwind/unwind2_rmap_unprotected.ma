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

include "delayed_updating/unwind/unwind2_rmap_closed.ma".
include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/syntax/path_structure.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Example of unprotected balanced path *************************************)

definition l3_b: path ≝ 𝐞◖𝗔◖𝗟◖𝗱𝟏.

lemma l3_b_unfold: 𝐞◖𝗔◖𝗟◖𝗱𝟏 = l3_b.
// qed.

lemma l3_b_balanced: ⊗l3_b ϵ 𝐁.
<l3_b_unfold <structure_d_dx
/2 width=1 by pbc_empty, pbc_redex/
qed.

lemma l3_b_closed: l3_b ϵ 𝐂❨Ⓕ,𝟎❩.
/4 width=1 by pcc_A_sn, pcc_empty, pcc_false_d_dx, pcc_L_dx/
qed.

lemma l3_b_unwind2_rmap_unfold (f):
      (⫯f)∘𝐮❨𝟏❩ = ▶[f]l3_b.
// qed.

lemma l3_b_unwind2_rmap_pap_unit (f):
      ↑(f＠⧣❨𝟏❩) = ▶[f]l3_b＠⧣❨𝟏❩.
// qed.
