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

include "ground/relocation/trz_uni_tls.ma".
include "ground/relocation/trz_tls_after.ma".
include "ground/relocation/trz_id_after.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS WITH INTEGERS *******************)

(* constructions with trz_after and trz_tls ***********************************)

theorem trz_after_uni_dx_dapp (f) (z):
        (𝐮❨f＠⧣❨z❩❩•⫰*[z]f) ≐ f•𝐮❨z❩.
#f #z #z0
<trz_after_unfold <trz_after_unfold
<trz_tls_unfold <trz_uni_unfold <trz_uni_unfold
<zminus_plus_simpl //
qed.

theorem trz_after_uni_bi (z2) (z1):
        (𝐮❨z1+z2❩) ≐ 𝐮❨z2❩•𝐮❨z1❩.
// qed.

lemma trz_tls_after_uni_dx (f) (p) (n):
      (⫰*[p+n]f) ≐ ⫰*[p](f•𝐮❨n❩).
#f #p #n
@(trz_eq_trans … (trz_tls_after …))
@(trz_eq_trans … (trz_after_eq_repl …))
/1 width=5 by/
qed.
