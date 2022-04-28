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

include "delayed_updating/unwind0/unwind1_rmap.ma".
include "ground/relocation/tr_id_compose.ma".

(* BASIC UNWIND FOR RELOCATION MAP ******************************************)

(* Constructions with stream_eq *********************************************)

lemma unwind1_rmap_d_empty (n:pnat):
      (𝐮❨n❩) ≗ ▶(𝗱n◗𝐞).
// qed.
