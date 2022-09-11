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
include "ground/generated/insert_eq_1.ma".

(* INNER CONDITION FOR PATH *************************************************)

inductive pic: predicate path ≝
| pic_empty: (𝐞) ϵ pic
| pic_m_dx (p): p◖𝗺 ϵ pic
| pic_L_dx (p): p◖𝗟 ϵ pic
| pic_A_dx (p): p◖𝗔 ϵ pic
| pic_S_dx (p): p◖𝗦 ϵ pic
.

interpretation
  "inner condition (path)"
  'ClassI = (pic).

(* Basic inversions ********************************************************)

lemma pic_inv_d_dx (p) (k):
      p◖𝗱k ϵ 𝐈 → ⊥.
#p #k @(insert_eq_1 … (p◖𝗱k))
#q * -q [|*: #q ] #H0 destruct
qed-.

(* Constructions with path_lcons ********************************************)

lemma pic_m_sn (p):
      p ϵ 𝐈 → 𝗺◗p ϵ 𝐈.
#p * -p //
qed.

lemma pic_L_sn (p):
      p ϵ 𝐈 → 𝗟◗p ϵ 𝐈.
#p * -p //
qed.

lemma pic_A_sn (p):
      p ϵ 𝐈 → 𝗔◗p ϵ 𝐈.
#p * -p //
qed.

lemma pic_S_sn (p):
      p ϵ 𝐈 → 𝗦◗p ϵ 𝐈.
#p * -p //
qed.
