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

include "ground/relocation/fb/fbr_rconss_plus.ma".
include "ground/relocation/fb/fbr_uni_after.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS WITH BOOLEANS ****************)

(* Constructions with nat_plus **********************************************)

lemma fbr_after_uni_bi (m) (n):
      (𝐮❨⁤m+n❩) = 𝐮❨n❩•𝐮❨⁤m❩.
#m #n
<fbr_after_uni_sn >fbr_rconss_plus //
qed.
