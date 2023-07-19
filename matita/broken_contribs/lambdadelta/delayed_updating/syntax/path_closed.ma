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

include "delayed_updating/syntax/path_width.ma".
include "delayed_updating/notation/functions/class_c_0.ma".
include "ground/lib/subset.ma".
include "ground/arith/int_le.ma".
include "ground/generated/insert_eq_1.ma".

(* CLOSED CONDITION FOR PATH ************************************************)

inductive pcc: predicate path ≝
| pcc_empty: (𝐞) ϵ pcc
| pcc_d_dx (p) (k): p ϵ pcc → k ≤ ♮p → p◖𝗱k ϵ pcc
| pcc_m_dx (p): p ϵ pcc → p◖𝗺 ϵ pcc
| pcc_L_dx (p): p ϵ pcc → 𝟎 ≤ ♮p → p◖𝗟 ϵ pcc
| pcc_A_dx (p): p ϵ pcc → p◖𝗔 ϵ pcc
| pcc_S_dx (p): p ϵ pcc → p◖𝗦 ϵ pcc
.

interpretation
  "closed condition (path)"
  'ClassC = (pcc).

(* Basic inversions ********************************************************)

lemma pcc_inv_d_dx (p) (k):
      p◖𝗱k ϵ 𝐂 → ∧∧ p ϵ 𝐂 & k ≤ ♮p.
#p #h @(insert_eq_1 … (p◖𝗱h))
#q * -q [|*: #q [ #k ] #H1q [ #H2q || #H2q ]] #H0 destruct
/2 width=1 by conj/
qed-.

lemma pcc_inv_m_dx (p):
      p◖𝗺 ϵ 𝐂 → p ϵ 𝐂.
#p @(insert_eq_1 … (p◖𝗺))
#q * -q [|*: #q [ #k ] #H1q [ #H2q || #H2q ]] #H0 destruct //
qed-.

lemma pcc_inv_L_dx (p):
      p◖𝗟 ϵ 𝐂 → ∧∧ p ϵ 𝐂 & 𝟎 ≤ ♮p.
#p @(insert_eq_1 … (p◖𝗟))
#q * -q [|*: #q [ #k ] #H1q [ #H2q || #H2q ]] #H0 destruct
/2 width=1 by conj/
qed-.

lemma pcc_inv_A_dx (p):
      p◖𝗔 ϵ 𝐂 → p ϵ 𝐂.
#p @(insert_eq_1 … (p◖𝗔))
#q * -q [|*: #q [ #k ] #H1q [ #H2q || #H2q ]] #H0 destruct //
qed-.

lemma pcc_inv_S_dx (p):
      p◖𝗦 ϵ 𝐂 → p ϵ 𝐂.
#p @(insert_eq_1 … (p◖𝗦))
#q * -q [|*: #q [ #k ] #H1q [ #H2q || #H2q ]] #H0 destruct //
qed-.

(* Destructions with path_append ********************************************)

lemma pcc_des_append (p) (q):
      p●q ϵ 𝐂 → p ϵ 𝐂.
#p #q elim q -q //
* [ #k ] #q #IH #H0
[ elim (pcc_inv_d_dx … H0) -H0 #H0 #_
  /2 width=1 by/
| /3 width=1 by pcc_inv_m_dx/
| elim (pcc_inv_L_dx … H0) -H0 #H0 #_
  /2 width=1 by/
| /3 width=1 by pcc_inv_A_dx/
| /3 width=1 by pcc_inv_S_dx/
]
qed-.
