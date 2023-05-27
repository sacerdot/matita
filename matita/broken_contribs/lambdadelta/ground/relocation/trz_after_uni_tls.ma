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

include "ground/relocation/trz_after.ma".
include "ground/relocation/trz_tls.ma".
include "ground/relocation/trz_uni.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS WITH INTEGERS **********************)

(* constructions with trz_uni and trz_tls ***********************************)

theorem trz_after_uni_dx_dapp (f) (z):
        (𝐮❨f＠⧣❨z❩❩•⫰*[z]f) ≐ f•𝐮❨z❩.
#f #z #z0
<trz_after_unfold <trz_after_unfold
<trz_tls_unfold <trz_uni_unfold <trz_uni_unfold
<zminus_plus_simpl //
qed.
