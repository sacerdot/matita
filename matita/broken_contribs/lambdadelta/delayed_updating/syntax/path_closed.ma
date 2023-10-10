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
include "delayed_updating/notation/functions/class_c_1.ma".
include "ground/arith/nat_plus.ma".
include "ground/arith/nat_pred_succ.ma".
include "ground/lib/subset.ma".
include "ground/generated/insert_eq_1.ma".

(* CLOSED CONDITION FOR PATH ************************************************)

inductive pcc: relation2 nat path ≝
| pcc_empty:
  pcc (𝟎) (𝐞)
| pcc_d_dx (p) (n) (k):
  pcc (n+k) p → pcc n (p◖𝗱k)
| pcc_m_dx (p) (n):
  pcc n p → pcc n (p◖𝗺)
| pcc_L_dx (p) (n):
  pcc n p → pcc (⁤↑n) (p◖𝗟)
| pcc_A_dx (p) (n):
  pcc n p → pcc n (p◖𝗔)
| pcc_S_dx (p) (n):
  pcc n p → pcc n (p◖𝗦)
.

interpretation
  "closed condition (path)"
  'ClassC n = (pcc n).

(* Basic inversions ********************************************************)

lemma pcc_inv_empty (n):
      (𝐞) ϵ 𝐂❨n❩ → 𝟎 = n.
#n @(insert_eq_1 … (𝐞))
#x * -n //
#p #n [ #k ] #_ #H0 destruct
qed-.

lemma pcc_inv_d_dx (p) (n) (k):
      p◖𝗱k ϵ 𝐂❨n❩ → p ϵ 𝐂❨n+k❩.
#p #n #h @(insert_eq_1 … (p◖𝗱h))
#x * -x -n
[|*: #x #n [ #k ] #Hx ] #H0 destruct //
qed-.

lemma pcc_inv_m_dx (p) (n):
      p◖𝗺 ϵ 𝐂❨n❩ → p ϵ 𝐂❨n❩.
#p #n @(insert_eq_1 … (p◖𝗺))
#x * -x -n
[|*: #x #n [ #k ] #Hx ] #H0 destruct //
qed-.

lemma pcc_inv_L_dx (p) (n):
      p◖𝗟 ϵ 𝐂❨n❩ →
      ∧∧ p ϵ 𝐂❨⫰n❩ & n = (⁤↑⫰n).
#p #n @(insert_eq_1 … (p◖𝗟))
#x * -x -n
[|*: #x #n [ #k ] #Hx ] #H0 destruct
<npred_succ /2 width=1 by conj/
qed-.

lemma pcc_inv_A_dx (p) (n):
      p◖𝗔 ϵ 𝐂❨n❩ → p ϵ 𝐂❨n❩.
#p #n @(insert_eq_1 … (p◖𝗔))
#x * -x -n
[|*: #x #n [ #k ] #Hx ] #H0 destruct //
qed-.

lemma pcc_inv_S_dx (p) (n):
      p◖𝗦 ϵ 𝐂❨n❩ → p ϵ 𝐂❨n❩.
#p #n @(insert_eq_1 … (p◖𝗦))
#x * -x -n
[|*: #x #n [ #k ] #Hx ] #H0 destruct //
qed-.

(* Advanced inversions ******************************************************)

lemma pcc_inv_empty_succ (n):
      (𝐞) ϵ 𝐂❨⁤↑n❩ → ⊥.
#n #H0
lapply (pcc_inv_empty … H0) -H0 #H0
/2 width=7 by eq_inv_zero_npos/
qed-.

lemma pcc_inv_L_dx_zero (p):
      p◖𝗟 ϵ 𝐂❨𝟎❩ → ⊥.
#p #H0
elim (pcc_inv_L_dx … H0) -H0 #_ #H0
/2 width=7 by eq_inv_zero_npos/
qed-.

lemma pcc_inv_L_dx_succ (p) (n):
      p◖𝗟 ϵ 𝐂❨⁤↑n❩ → p ϵ 𝐂❨n❩.
#p #n #H0
elim (pcc_inv_L_dx … H0) -H0 //
qed-.

(* Main constructions with path_append **************************************)

theorem pcc_append_bi (p) (q) (m) (n):
        p ϵ 𝐂❨m❩ → q ϵ 𝐂❨n❩ → p●q ϵ 𝐂❨m+n❩.
#p #q #m #n #Hm #Hm elim Hm -Hm // -Hm
#p #n [ #k ] #_ #IH [3: <nplus_succ_dx ]
/2 width=1 by pcc_d_dx, pcc_m_dx, pcc_L_dx, pcc_A_dx, pcc_S_dx/
qed.

(* Constructions with path_lcons ********************************************)

lemma pcc_m_sn (q) (n):
      q ϵ 𝐂❨n❩ → (𝗺◗q) ϵ 𝐂❨n❩.
#q #n #Hq
lapply (pcc_append_bi (𝐞◖𝗺) … Hq) -Hq
/2 width=3 by pcc_m_dx/
qed.

lemma pcc_L_sn (q) (n):
      q ϵ 𝐂❨n❩ → (𝗟◗q) ϵ 𝐂❨⁤↑n❩.
#q #n #Hq
lapply (pcc_append_bi (𝐞◖𝗟) … Hq) -Hq
/2 width=3 by pcc_L_dx/
qed.

lemma pcc_A_sn (q) (n):
      q ϵ 𝐂❨n❩ → (𝗔◗q) ϵ 𝐂❨n❩.
#q #n #Hq
lapply (pcc_append_bi (𝐞◖𝗔) … Hq) -Hq
/2 width=3 by pcc_A_dx/
qed.

lemma pcc_S_sn (q) (n):
      q ϵ 𝐂❨n❩ → (𝗦◗q) ϵ 𝐂❨n❩.
#q #n #Hq
lapply (pcc_append_bi (𝐞◖𝗦) … Hq) -Hq
/2 width=3 by pcc_S_dx/
qed.

(* Main inversions **********************************************************)

theorem pcc_mono (q) (n1):
        q ϵ 𝐂❨n1❩ → ∀n2. q ϵ 𝐂❨n2❩ → n1 = n2.
#q1 #n1 #Hn1 elim Hn1 -q1 -n1
[|*: #q1 #n1 [ #k1 ] #_ #IH ] #n2 #Hn2
[ <(pcc_inv_empty … Hn2) -n2 //
| lapply (pcc_inv_d_dx … Hn2) -Hn2 #Hn2
  lapply (IH … Hn2) -q1 #H0
  /2 width=2 by eq_inv_nplus_bi_dx/
| lapply (pcc_inv_m_dx … Hn2) -Hn2 #Hn2
  <(IH … Hn2) -q1 -n2 //
| elim (pcc_inv_L_dx … Hn2) -Hn2 #Hn2 #H0
  >(IH … Hn2) -q1 //
| lapply (pcc_inv_A_dx … Hn2) -Hn2 #Hn2
  <(IH … Hn2) -q1 -n2 //
| lapply (pcc_inv_S_dx … Hn2) -Hn2 #Hn2
  <(IH … Hn2) -q1 -n2 //
]
qed-.

theorem pcc_inj_L_sn (p1) (p2) (q1) (n):
        q1 ϵ 𝐂❨n❩ → ∀q2. q2 ϵ 𝐂❨n❩ →
        p1●𝗟◗q1 = p2●𝗟◗q2 → q1 = q2.
#p1 #p2 #q1 #n #Hq1 elim Hq1 -q1 -n
[|*: #q1 #n1 [ #k1 ] #_ #IH ] * //
[1,3,5,7,9,11: #l2 #q2 ] #Hq2
<list_append_lcons_sn <list_append_lcons_sn #H0
elim (eq_inv_list_lcons_bi ????? H0) -H0 #H0 #H1 destruct
[ elim (pcc_inv_L_dx_zero … Hq2)
| lapply (pcc_inv_d_dx … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| lapply (pcc_inv_m_dx … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| lapply (pcc_inv_L_dx_succ … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| lapply (pcc_inv_A_dx … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| lapply (pcc_inv_S_dx … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| elim (pcc_inv_empty_succ … Hq2)
]
qed-.

theorem pcc_inv_L_sn (q) (n) (m):
        (𝗟◗q) ϵ 𝐂❨n❩ → q ϵ 𝐂❨m❩ →
        ∧∧ ⫰n = m & n = (⁤↑⫰n).
#q #n #m #H1q #H2q
lapply (pcc_L_sn … H2q) -H2q #H2q
<(pcc_mono … H2q … H1q) -q -n
/2 width=1 by conj/
qed-.
