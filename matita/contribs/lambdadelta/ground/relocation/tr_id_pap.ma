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

include "ground/relocation/tr_pap.ma".
include "ground/relocation/tr_id.ma".

(* IDENTITY ELEMENT FOR TOTAL RELOCATION MAPS *******************************)

(* Coonstructions with tr_pap ***********************************************)

lemma tr_pap_id (p):
      p = 𝐢@❨p❩.
#p elim p -p //
#p #IH <tr_id_unfold <tr_pap_succ //
qed.
