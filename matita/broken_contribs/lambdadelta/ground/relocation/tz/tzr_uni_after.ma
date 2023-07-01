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

include "ground/relocation/tz/tzr_uni_tls.ma".
include "ground/relocation/tz/tzr_tls_after.ma".
include "ground/relocation/tz/tzr_id_after.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS WITH INTEGERS *******************)

(* constructions with tzr_after and tzr_tls ***********************************)

theorem tzr_after_uni_dx_dapp (f) (z):
        (𝐮❨f＠⧣❨z❩❩•⫰*[z]f) ≐ f•𝐮❨z❩.
#f #z #z0
<tzr_after_dapp <tzr_after_dapp
<tzr_tls_dapp <tzr_uni_dapp <tzr_uni_dapp
<zminus_plus_simpl //
qed.

theorem tzr_after_uni_bi (z2) (z1):
        (𝐮❨z1+z2❩) ≐ 𝐮❨z2❩•𝐮❨z1❩.
// qed.

lemma tzr_tls_after_uni_dx (f) (p) (n):
      (⫰*[p+n]f) ≐ ⫰*[p](f•𝐮❨n❩).
#f #p #n
@(tzr_eq_trans … (tzr_tls_after_dapp …))
@(tzr_eq_trans … (tzr_after_eq_repl …))
/1 width=5 by/
qed.
