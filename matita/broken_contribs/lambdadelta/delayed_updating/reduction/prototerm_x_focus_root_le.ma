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

include "delayed_updating/syntax/path_root_le.ma".
include "delayed_updating/reduction/prototerm_x_focus.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

(* Constructions with path_root_le ******************************************)

lemma brxf_mk_rle (r) (p) (b) (q) (n):
      (𝐫❨p,b,q,⁤↑n❩ ⊑ r) → r ϵ 𝐅❨p,b,q,n❩.
//
qed.

(* Inversions with path_root_le *********************************************)

lemma in_comp_brxf_inv_rle (r) (p) (b) (q) (n):
      r ϵ 𝐅❨p,b,q,n❩ → 𝐫❨p,b,q,⁤↑n❩ ⊑ r.
//
qed-.
