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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/class_i_0.ma".
include "ground/lib/subset.ma".

(* INNER CONDITION FOR PATH *************************************************)

definition pic: predicate path ≝
           λp. ∀q,n. q◖𝗱n = p → ⊥
.

interpretation
  "inner condition (path)"
  'ClassI = (pic).

(* Basic constructions ******************************************************)

lemma pic_empty: 𝐞 ϵ 𝐈.
#q #n #H0
elim (eq_inv_list_empty_rcons ??? (sym_eq … H0))
qed.

lemma pic_m_dx (p): p◖𝗺 ϵ 𝐈.
#p #q #n #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
qed.

lemma pic_L_dx (p): p◖𝗟 ϵ 𝐈.
#p #q #n #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
qed.

lemma pic_A_dx (p): p◖𝗔 ϵ 𝐈.
#p #q #n #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
qed.

lemma pic_S_dx (p): p◖𝗦 ϵ 𝐈.
#p #q #n #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
qed.

(* Basic inversions ********************************************************)

lemma pic_inv_d_dx (p) (n):
      p◖𝗱n ϵ 𝐈 → ⊥.
#p #n #H0 @H0 -H0 //
qed-.
