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

include "ground/relocation/fb/fbr_uni.ma".
include "ground/relocation/fb/fbr_rconss_after.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS WITH BOOLEANS ****************)

(* Constructions with fbr_after *********************************************)

lemma fbr_after_pushs_uni (g) (n):
      ↑*[n]g = ⫯*[n]g•𝐮❨n❩.
// qed.

lemma fbr_after_uni_sn (f) (n):
      ↑*[n]f = 𝐮❨n❩•f.
// qed.
