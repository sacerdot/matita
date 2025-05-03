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

include "ground/relocation/fb/fbr_dapp_eq.ma".
include "ground_2B/relocation/fbr_isid.ma".

(* IDENTITY CLASS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with fbf_dapp **********************************************)

lemma fbr_dapp_isid (f):
      (∀p. p = f＠⧣❨p❩) → f ϵ 𝐈.
/3 width=1 by fbr_eq_id_sn_isid, fbr_dxeq_inv_eq/
qed.

(* Inversions with fbr_dapp *************************************************)

lemma fbr_isid_inv_dapp (f) (p):
      f ϵ 𝐈 → p = f＠⧣❨p❩.
#f #p #Hf
lapply (fbr_isid_inv_eq_id_sn … Hf) -Hf #Hf
<(fbr_dapp_eq_repl p … Hf) //
qed-.
