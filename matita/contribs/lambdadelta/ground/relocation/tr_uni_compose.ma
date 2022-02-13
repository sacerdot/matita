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

include "ground/relocation/tr_uni_pap.ma".
include "ground/relocation/tr_compose_pap.ma".
include "ground/relocation/tr_pap_eq.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS *******************************)

(* Main constructions with tr_compose and tr_tls ****************************)

theorem tr_compose_uni_dx (f) (p):
        (𝐮❨f@❨p❩❩∘⇂*[p]f ≗ f∘𝐮❨p❩).
#f #p
@nstream_eq_inv_ext #q
<tr_compose_pap <tr_compose_pap
<tr_uni_pap <tr_uni_pap
<tr_pap_plus //
qed.
