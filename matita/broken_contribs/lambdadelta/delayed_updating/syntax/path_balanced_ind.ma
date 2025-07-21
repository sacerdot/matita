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

lemma pbc_ind_sn (Q:predicate …):
      Q (𝐞) →
      (∀b1,b2. b1 ϵ 𝐁 → b2 ϵ 𝐁 → Q b1 → Q b2 → Q (𝗔◗b1◖𝗟●b2)) →
      ∀b. b ϵ 𝐁 → Q b.
#Q #IH1 #IH2 @(wf1_ind_nlt ? depth)
#n #IH #b #Hn #Hb destruct
elim (pbc_inv_gen_sn … Hb) -Hb [ #H0 | * #b1 #b2 #Hb1 #Hb2 #H0 ] destruct
/3 width=1 by/
qed-.

lemma pbc_ind_dx (Q:predicate …):
      Q (𝐞) →
      (∀b1,b2. b1 ϵ 𝐁 → b2 ϵ 𝐁 → Q b1 → Q b2 → Q (b1●𝗔◗b2◖𝗟)) →
      ∀b. b ϵ 𝐁 → Q b.
#Q #IH1 #IH2 @(wf1_ind_nlt ? depth)
#n #IH #b #Hn #Hb destruct
elim (pbc_inv_gen_dx … Hb) -Hb [ #H0 | * #b1 #b2 #Hb1 #Hb2 #H0 ] destruct
/3 width=1 by/
qed-.

(* Advanced inversions ******************************************************)

lemma pbc_inv_insert_pbc (b):
      b ϵ 𝐁 → ∀q,p. p●b●q ϵ 𝐁 → p●q ϵ 𝐁.
#b #Hb @(pbc_ind_dx … Hb) -b //
#b1 #b2 #_ #_ #IH1 #IH2 #q #p #H9
lapply (IH1 ((𝗔◗b2◖𝗟)●q) p ?) // -b1 #H0
lapply (IH2 (𝗟◗q) (p◖𝗔) ?) // -b2 #H0
/2 width=1 by pbc_inv_insert_redex/
qed-.

lemma pbc_inv_append_sn (b1) (b2):
      b1●b2 ϵ 𝐁 → b1 ϵ 𝐁 → b2 ϵ 𝐁.
#b1 #b2 #Hb12 #Hb1
>(list_append_empty_dx … b2)
/2 width=3 by pbc_inv_insert_pbc/
qed-.

lemma pbc_inv_append_dx (b1) (b2):
      b1●b2 ϵ 𝐁 → b2 ϵ 𝐁 → b1 ϵ 𝐁.
#b1 #b2 #Hb12 #Hb2
>(list_append_empty_sn … b1)
/2 width=3 by pbc_inv_insert_pbc/
qed-.
