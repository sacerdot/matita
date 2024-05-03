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

include "ground/subsets/subsets_inhabited.ma".
include "ground/subsets/subset_listed.ma".

(* SUBSET WITH LISTED ELEMENTS **********************************************)

(* Inversions with subsets_inh **********************************************)

lemma subset_nin_inv_empty_inh (A):
      (Ⓕ{A}) ⧸ϵ ⊙.
#A #H0
elim (subsets_inh_inv_in … H0) -H0 #a #Ha
/2 width=3 by subset_nin_inv_empty/
qed-.
