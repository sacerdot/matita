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

(* INHABITED SUBSETS ********************************************************)

(* Constructions with subset_le *********************************************)

lemma subsets_inh_le_repl_fwd (A) (u1) (u2):
      u1 ϵ ⊙→ u1 ⊆ u2 → u2 ϵ ⊙{A}.
#A #u1 #u2 #H0
elim (subsets_inh_inv_in … H0) -H0 #a #Hu1 #Hu
/3 width=2 by subsets_inh_in/
qed.
