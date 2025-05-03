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

include "ground/relocation/fb/fbr_uni_plus.ma".
include "ground_2B/relocation/fbr_isafter.ma".

(* COMPOSITION CLASS FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************)

(* Inversions with fbr_uni **************************************************)

lemma fbr_isafter_inv_uni_bi (f) (n1) (n2):
      f ϵ 𝐮❨n2❩ ⊚ 𝐮❨n1❩ → f ≐ 𝐮❨n1+n2❩.
//
qed-.
