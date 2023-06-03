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

include "ground/relocation/trz_uni.ma".
include "ground/relocation/trz_id.ma".
include "ground/relocation/trz_tls.ma".

(* UNIFORM ELEMENTS FOR TOTAL RELOCATION MAPS WITH INTEGERS *****************)

(* Constructions with trz_tls ***********************************************)

lemma trz_tls_uni (z2) (z1):
      (𝐢) ≐ ⫰*[z2]𝐮❨z1❩.
#z2 #z1 #z0
<trz_id_dapp <trz_tls_dapp <trz_uni_dapp <trz_uni_dapp
>zplus_assoc in ⊢ (???(?%?)); //
qed.
