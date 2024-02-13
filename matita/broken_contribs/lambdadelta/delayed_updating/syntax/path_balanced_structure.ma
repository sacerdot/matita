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

include "delayed_updating/syntax/path_balanced.ma".
include "delayed_updating/syntax/path_structure.ma".

(* BALANCE CONDITION FOR PATH ***********************************************)

(* Destructions with path_structure *****************************************)

lemma pbc_des_structure (b):
      b ϵ 𝐁 → b = ⊗b.
#b #Hb elim Hb -b //
[ #b #_ #IH
  <structure_A_sn <structure_L_dx <IH -IH //
| #b1 #b2 #_ #_ #IH1 #IH2
  <structure_append <IH1 <IH2 -IH1 -IH2 //
]
qed-.
