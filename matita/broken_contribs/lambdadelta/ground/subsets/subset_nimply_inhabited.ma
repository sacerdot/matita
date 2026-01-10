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

include "ground/subsets/subset_le.ma".
include "ground/subsets/subsets_inhabited.ma".
include "ground/subsets/subset_nimply.ma".

(* DIFFERENCE FOR SUBSETS ***************************************************)

(* Destructions with subset_inh *********************************************)

lemma subset_in_des_nimp_inh (A) (u1) (u2):
      u2 ⧵ u1 ϵ ⊙❪A❫ → u2 ⧸⊆ u1.
#A #u1 #u2 #H0
elim (subsets_inh_inv_in … H0) -H0 #a * #H1a #H2a
/3 width=1 by/
qed-.
