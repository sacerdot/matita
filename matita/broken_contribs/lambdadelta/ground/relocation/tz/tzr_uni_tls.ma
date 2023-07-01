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

include "ground/relocation/tz/tzr_uni.ma".
include "ground/relocation/tz/tzr_id.ma".
include "ground/relocation/tz/tzr_tls.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************)

(* Constructions with tzr_tls ***********************************************)

lemma tzr_tls_uni (z2) (z1):
      (𝐢) ≐ ⫰*[z2]𝐮❨z1❩.
#z2 #z1 #z0
<tzr_id_dapp <tzr_tls_dapp <tzr_uni_dapp <tzr_uni_dapp
>zplus_assoc in ⊢ (???(?%?)); //
qed.
