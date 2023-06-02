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

include "ground/relocation/trz_id.ma".
include "ground/relocation/trz_tls.ma".

(* IDENTITY ELEMENT FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************)

(* Constructions with trz_tls ***********************************************)

lemma trz_tls_id (z):
      (𝐢) ≐ ⫰*[z]𝐢.
// qed.
