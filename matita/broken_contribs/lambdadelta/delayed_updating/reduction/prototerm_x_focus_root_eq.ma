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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_listed_le.ma".
include "delayed_updating/syntax/path_root_eq.ma".
include "delayed_updating/reduction/prototerm_x_focus_root_le.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Constructions with path_root_neq *****************************************)

(* Was: grafted_brxf_nol *)
lemma grafted_brxf_nreq (p1) (p2) (b) (q) (n):
      p1◖𝗔 ⧸≚ p2 → Ⓕ ⇔ ⋔[p2]𝐅❨p1,b,q,n❩.
#p1 #p2 #b #q #n #Hnp12
@conj [ /2 width=1 by subset_empty_le_sx/ ] #x #Hx
lapply (in_comp_brxf_inv_rle … Hx) -Hx
<path_beta_unfold_b <list_append_assoc #Hx (* ** UNFOLD *)
elim Hnp12 -Hnp12
/3 width=5 by path_req_weak, path_req_mk_le/
qed.
