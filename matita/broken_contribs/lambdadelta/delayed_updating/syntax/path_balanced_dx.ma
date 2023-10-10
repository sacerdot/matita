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
include "delayed_updating/syntax/path_depth.ma".
include "ground/arith/wf1_ind_nlt.ma".
include "ground/arith/nat_lt_plus.ma".

(* BALANCE CONDITION FOR PATH ***********************************************)

(* Advanced eliminators *****************************************************)

lemma pbc_ind_dx (Q:predicate …):
      Q (𝐞) →
      (∀b1,b2. b1 ϵ 𝐁 → b2 ϵ 𝐁 → Q b1 → Q b2 → Q (b1●𝗔◗b2◖𝗟)) →
      ∀b. b ϵ 𝐁 → Q b.
#Q #IH1 #IH2 @(wf1_ind_nlt ? depth)
#n #IH #b #Hn #Hb destruct
elim (pbc_inv_gen_dx … Hb) -Hb [ #H0 | * #b1 #b2 #Hb1 #Hb2 #H0 ] destruct
/3 width=1 by/
qed-.
