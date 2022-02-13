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

include "ground/relocation/tr_pap_pushs.ma".
include "ground/relocation/tr_id_pushs.ma".

(* IDENTITY ELEMENT FOR TOTAL RELOCATION MAPS *******************************)

(* Coonstructions with tr_pap ***********************************************)

lemma tr_id_pap (p):
      p = 𝐢@❨p❩.
#p >(tr_pushs_id p)
/2 width=1 by tr_pap_pushs_le/
qed.
