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
include "delayed_updating/unwind0/unwind2_path.ma".
include "delayed_updating/unwind0/unwind1_path_structure.ma".

(* EXTENDED UNWIND FOR PATH *************************************************)

(* Constructions with structure *********************************************)

lemma unwind2_path_d_dx (f) (p) (n):
      (⊗p)◖𝗱((▶[f]p)@❨n❩) = ▼[f](p◖𝗱n).
#f #p #n
<unwind2_path_unfold <lift_path_d_dx <unwind1_path_d_dx
<structure_lift >tr_compose_pap //
qed.
