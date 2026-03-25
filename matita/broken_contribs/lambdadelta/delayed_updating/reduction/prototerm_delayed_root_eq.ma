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
include "delayed_updating/reduction/prototerm_delayed.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

(* Constructions with path_root_neq *****************************************)

(* Was: grafted_brd_nol *) 
lemma grafted_brd_nreq (t) (p1) (p2) (b) (q) (n):
      p1◖𝗔 ⧸≚  p2 → Ⓕ ⇔ ⋔[p2]𝐃❨t,p1,b,q,n❩.
#t #p1 #p2 #b #q #n #Hnp12
@conj [ /2 width=1 by subset_empty_le_sx/ ] #x #Hx
elim (term_in_append_inv_gen … Hx) -Hx #y #_
<path_beta_unfold_b <list_append_assoc <list_append_assoc #H0 (* ** UNFOLD *)
elim Hnp12 -Hnp12
/2 width=3 by path_req_mk_append/
qed.
