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

include "delayed_updating/unwind0/unwind2_rmap.ma".
include "ground/relocation/tr_id_compose.ma".

(* EXTENDED UNWIND FOR RELOCATION MAP ***************************************)

(* Advanced constructions ***************************************************)

lemma unwind2_rmap_id (p):
      ▶p ≗ ▶[𝐢]p.
// qed.

lemma unwind2_rmap_empty (f):
      f ≗ ▶[f]𝐞.
// qed.

lemma unwind2_rmap_d_sn (f) (p) (n):
      ▶[𝐮❨f@❨n❩❩]p ≗ ▶[f](𝗱n◗p).
#f #p #n
<unwind2_rmap_unfold <unwind2_rmap_unfold
<lift_rmap_d_sn <lift_rmap_id
<lift_path_d_sn <lift_path_id <unwind1_rmap_d_sn //
qed.
