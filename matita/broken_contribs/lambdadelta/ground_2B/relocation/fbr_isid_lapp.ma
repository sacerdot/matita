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

include "ground/relocation/fb/fbr_lapp.ma".
include "ground_2B/relocation/fbr_isid_dapp.ma".

(* IDENTITY CLASS FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Constructions with fbf_lapp **********************************************)

lemma fbr_lapp_isid (f):
      (∀n. n = f＠§❨n❩) → f ϵ 𝐈.
#f #Hf
@fbr_dapp_isid #p
>(npsucc_pnpred … p) <fbr_dapp_succ_lapp <Hf -Hf //
qed.

(* Inversions with fbr_lapp *************************************************)

lemma fbr_isid_inv_lapp (f) (n):
      f ϵ 𝐈 → n = f＠§❨n❩.
#f #n #Hf
<(fbr_isid_inv_dapp … (↑n) Hf) //
qed-.
