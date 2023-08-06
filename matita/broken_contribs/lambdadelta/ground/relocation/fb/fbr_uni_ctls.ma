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

include "ground/relocation/fb/fbr_uni_after.ma".
include "ground/relocation/fb/fbr_rconss_ctls.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS WITH BOOLEANS ****************)

(* Constructions with fbr_ctls **********************************************)

theorem fbr_after_uni_dx (g) (n):
        (𝐮❨g＠❨n❩❩)•⫰*[n]g = g•𝐮❨n❩.
// qed.
