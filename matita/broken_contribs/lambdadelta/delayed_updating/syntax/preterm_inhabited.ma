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
include "delayed_updating/syntax/preterm.ma".

(* PRETERM ******************************************************************)

(* Constructions with subsets_inhabited *************************************)

lemma term_grafted_S_dx_inh (t) (p):
      t ϵ 𝐓 → p◖𝗔 ϵ ▵t → ⋔[p◖𝗦]t ϵ ⊙.
#t #p #Ht #Hp
lapply (term_full_A_post … Ht … Hp) -Hp * #r #Hr
/2 width=2 by subsets_inh_in/
qed.
