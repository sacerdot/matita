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

include "delayed_updating/syntax/path_closed.ma".
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/syntax/path_depth.ma".

(* CLOSED CONDITION FOR PATH ************************************************)

(* Constructions with path_clear and depth **********************************)

lemma pcc_clear (p):
      ⓪p ϵ 𝐂❨♭p❩.
#p elim p -p //
* [ #k ] #p #IH
/2 width=1 by pcc_d_dx, pcc_L_dx, pcc_A_dx, pcc_S_dx/
qed.
