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

include "delayed_updating/syntax/path_closed_height.ma".
include "delayed_updating/syntax/path_structure.ma".

(* CLOSED CONDITION FOR PATH ************************************************)

(* Constructions with structure *********************************************)

lemma pcc_structure (p):
      ⊗p ϵ 𝐂❨♭p❩.
#p elim p -p //
* [ #k ] #p #IH
/2 width=1 by pcc_L_dx, pcc_A_dx, pcc_S_dx/
qed.

lemma pcc_structure_height (p) (n):
      p ϵ 𝐂❨n❩ → ⊗p ϵ 𝐂❨♯p+n❩.
#p #n #Hn
>pcc_depth //
qed.

(* Inversions with structure ************************************************)

lemma pcc_inv_structure (p) (n):
      ⊗p ϵ 𝐂❨n❩ → n = ♭p.
/2 width=3 by pcc_mono/
qed-.
