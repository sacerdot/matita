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

include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_beta.ma".

(* PATHS FOR β-REDUCTION ****************************************************)

(* Constructions with structure *********************************************)

lemma path_structure_beta (p) (b) (q) (n):
      (𝐫❨⊗p,⊗b,⊗q❩) = ⊗𝐫❨p,b,q,n❩.
#p #b #q #n
<path_beta_unfold_sx <path_pbeta_unfold_sx //
qed.

lemma path_structure_pbeta (p) (b) (q):
      (𝐫❨⊗p,⊗b,⊗q❩) = ⊗𝐫❨p,b,q❩.
#p #b #q
<path_pbeta_unfold_sx <path_pbeta_unfold_sx //
qed.
