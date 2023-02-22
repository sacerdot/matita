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

include "ground/relocation/tr_id_tls.ma".
include "ground/relocation/tr_uni_hdtl.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS *******************************)

(* Constructions with stream_tls ********************************************)

lemma tr_tls_succ_uni (m) (n):
      (𝐢) = ⇂*[↑m]𝐮❨n❩.
// qed.
