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

include "ground/lib/stream_tls.ma".
include "ground/relocation/tr_id_hdtl.ma".

(* IDENTITY ELEMENT FOR TOTAL RELOCATION MAPS *******************************)

(* Constructions with stream_tls ********************************************)

lemma tr_tls_id (n):
      (𝐢) = ⇂*[n]𝐢.
#n @(nat_ind_succ … n) -n //
qed.
