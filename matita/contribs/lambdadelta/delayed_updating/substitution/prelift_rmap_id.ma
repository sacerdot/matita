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
include "ground/relocation/tr_id_tls.ma".

(* PRELIFT FOR RELOCATION MAP ***********************************************)

(* Constructions with tr_id *************************************************)

lemma prelift_rmap_id (l):
      (𝐢) = ↑[l]𝐢.
* [ #k ] //
qed.
