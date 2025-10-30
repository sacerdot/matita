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

include "ground/lib/list_tl.ma".
include "delayed_updating/syntax/path_beta.ma".

(* PATHS FOR β-REDUCTION ****************************************************)

(* Inversions with list_tl **************************************************)

lemma path_eq_inv_xSy_q_beta (x) (y) (q) (n):
      x◖𝗦●y = 𝐫❨q,n❩ →
      ∧∧ (⇂y)◖𝗱n = y & x◖𝗦●⇂y = q.
#x * [| #l #y ] #q #n <path_qbeta_unfold
[ <list_append_empty_sx | <list_append_lcons_sx ] #H0 destruct
/2 width=1 by conj/
qed-.
