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

include "delayed_updating/substitution/prelift_rmap.ma".
include "ground/relocation/trz_id_tls.ma".
include "ground/relocation/trz_id_push.ma".

(* PRELIFT FOR RELOCATION MAP ***********************************************)

(* Constructions with trz_id ************************************************)

lemma prelift_rmap_id (l):
      (𝐢) ≐ 🠢[𝐢]l.
* [ #k ] //
qed.
