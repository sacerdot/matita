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

include "delayed_updating/syntax/path_beta.ma".
include "delayed_updating/syntax/prototerm.ma".

(* PROTOTERM ****************************************************************)

(* Constructions with path_beta *********************************************)

lemma path_beta_in_slice_pA (p) (b) (q) (n):
      (𝐫❨p,b,q,n❩) ϵ ↑(p◖𝗔).
#p #b #q #n
<path_beta_unfold_b //
qed.

(* Destructions with path_beta **********************************************)

lemma path_beta_pA_in_root (t) (p) (b) (q) (n):
     (𝐫❨p,b,q,n❩) ϵ t → p◖𝗔 ϵ ▵t.
#t #p #b #q #n <path_beta_unfold_b #Ht
/2 width=2 by term_in_root/
qed-.
