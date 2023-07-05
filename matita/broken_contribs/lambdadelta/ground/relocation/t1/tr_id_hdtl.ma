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

include "ground/relocation/t1/tr_pn_hdtl.ma".
include "ground/relocation/t1/tr_id.ma".

(* IDENTITY ELEMENT FOR TOTAL RELOCATION MAPS *******************************)

(* Constructions with stream_hd *********************************************)

lemma tr_hd_id:
      (𝟏) = ⇃𝐢.
// qed.

(* Constructions with stream_tl *********************************************)

lemma tr_tl_id:
      (𝐢) = ⇂𝐢.
// qed.
