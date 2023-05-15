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
include "delayed_updating/notation/functions/class_c_3.ma".
include "ground/arith/nat_plus_pred.ma".
include "ground/lib/subset.ma".
include "ground/lib/bool_and.ma".
include "ground/generated/insert_eq_1.ma".
include "ground/xoa/ex_3_2.ma".

(* CLOSED CONDITION FOR PATH ************************************************)

inductive pcc (o) (e): relation2 (ℕ) path ≝
| pcc_empty:
  pcc o e e (𝐞)
| pcc_d_dx (p) (n) (k):
  (Ⓣ = o → n = ↑⫰n) →
  pcc o e (n+ninj k) p → pcc o e n (p◖𝗱k)
| pcc_m_dx (p) (n):
  pcc o e n p → pcc o e n (p◖𝗺)
| pcc_L_dx (p) (n):
  pcc o e n p → pcc o e (↑n) (p◖𝗟)
| pcc_A_dx (p) (n):
  pcc o e n p → pcc o e n (p◖𝗔)
| pcc_S_dx (p) (n):
  pcc o e n p → pcc o e n (p◖𝗦)
.

interpretation
  "closed condition (path)"
  'ClassC o n e = (pcc o e n).

(* Advanced constructions ***************************************************)

lemma pcc_false_d_dx (e) (p) (n) (k:ℤ⁺):
      p ϵ 𝐂❨Ⓕ,n+k,e❩ → p◖𝗱k ϵ 𝐂❨Ⓕ,n,e❩.
#e #p #n #k #H0
@pcc_d_dx [| // ]
#H0 destruct
qed.

lemma pcc_true_d_dx (e) (p) (n:ℤ⁺) (k:ℤ⁺):
      p ϵ 𝐂❨Ⓣ,n+k,e❩ → p◖𝗱k ϵ 𝐂❨Ⓣ,n,e❩.
/2 width=1 by pcc_d_dx/
qed.

lemma pcc_plus_bi_dx (o) (e) (p) (n):
      p ϵ 𝐂❨o,n,e❩ →
      ∀m. p ϵ 𝐂❨o,n+m,e+m❩.
#o #e #p #n #H0 elim H0 -p -n //
#p #n [ #k #Ho ] #_ #IH #m
[|*: /2 width=1 by pcc_m_dx, pcc_L_dx, pcc_A_dx, pcc_S_dx/ ]
@pcc_d_dx // -IH #H0
>Ho -Ho // <nplus_succ_sn <npred_succ //
qed.

(* Basic inversions ********************************************************)

lemma pcc_inv_empty (o) (e) (n):
      (𝐞) ϵ 𝐂❨o,n,e❩ → e = n.
#o #e #n @(insert_eq_1 … (𝐞))
#x * -n //
#p #n [ #k #_ ] #_ #H0 destruct
qed-.

lemma pcc_inv_d_dx (o) (e) (p) (n) (k):
      p◖𝗱k ϵ 𝐂❨o,n,e❩ →
      ∧∧ (Ⓣ = o → n = ↑⫰n)
       & p ϵ 𝐂❨o,n+k,e❩.
#o #e #p #n #h @(insert_eq_1 … (p◖𝗱h))
#x * -x -n
[|*: #x #n [ #k #Ho ] #Hx ] #H0 destruct
/3 width=1 by conj/
qed-.

lemma pcc_inv_m_dx (o) (e) (p) (n):
      p◖𝗺 ϵ 𝐂❨o,n,e❩ → p ϵ 𝐂❨o,n,e❩.
#o #e #p #n @(insert_eq_1 … (p◖𝗺))
#x * -x -n
[|*: #x #n [ #k #_ ] #Hx ] #H0 destruct //
qed-.

lemma pcc_inv_L_dx (o) (e) (p) (n):
      p◖𝗟 ϵ 𝐂❨o,n,e❩ →
      ∧∧ p ϵ 𝐂❨o,⫰n,e❩ & n = ↑⫰n.
#o #e #p #n @(insert_eq_1 … (p◖𝗟))
#x * -x -n
[|*: #x #n [ #k #_ ] #Hx ] #H0 destruct
<npred_succ /2 width=1 by conj/
qed-.

lemma pcc_inv_A_dx (o) (e) (p) (n):
      p◖𝗔 ϵ 𝐂❨o,n,e❩ → p ϵ 𝐂❨o,n,e❩.
#o #e #p #n @(insert_eq_1 … (p◖𝗔))
#x * -x -n
[|*: #x #n [ #k #_ ] #Hx ] #H0 destruct //
qed-.

lemma pcc_inv_S_dx (o) (e) (p) (n):
      p◖𝗦 ϵ 𝐂❨o,n,e❩ → p ϵ 𝐂❨o,n,e❩.
#o #e #p #n @(insert_eq_1 … (p◖𝗦))
#x * -x -n
[|*: #x #n [ #k #_ ] #Hx ] #H0 destruct //
qed-.

(* Advanced destructions ****************************************************)

lemma pcc_des_d_dx (o) (e) (p) (n) (k):
      p◖𝗱k ϵ 𝐂❨o,n,e❩ → p ϵ 𝐂❨o,n+k,e❩.
#o #e #p #n #k #H0
elim (pcc_inv_d_dx … H0) -H0 #H1 #H2 //
qed-.

lemma pcc_des_gen (o) (e) (p) (n):
      p ϵ 𝐂❨o,n,e❩ → p ϵ 𝐂❨Ⓕ,n,e❩.
#o #e #p #n #H0 elim H0 -p -n //
#p #n [ #k #Ho ] #_ #IH
/2 width=1 by pcc_m_dx, pcc_L_dx, pcc_A_dx, pcc_S_dx, pcc_false_d_dx/
qed-.

(* Advanced inversions ******************************************************)

lemma pcc_inv_empty_succ_zero (o) (n):
      (𝐞) ϵ 𝐂❨o,↑n,𝟎❩ → ⊥.
#o #n #H0
lapply (pcc_inv_empty … H0) -H0 #H0
/2 width=7 by eq_inv_zero_ninj/
qed-.

lemma pcc_true_inv_d_dx_zero_sn (e) (p) (k):
      p◖𝗱k ϵ 𝐂❨Ⓣ,𝟎, e❩ → ⊥.
#e #p #k #H0
elim (pcc_inv_d_dx … H0) -H0 #H0 #_
elim (eq_inv_zero_ninj … (H0 ?)) -H0 //
qed-.

lemma pcc_inv_L_dx_zero_sn (o) (e) (p):
      p◖𝗟 ϵ 𝐂❨o,𝟎,e❩ → ⊥.
#o #e #p #H0
elim (pcc_inv_L_dx … H0) -H0 #_ #H0
/2 width=7 by eq_inv_zero_ninj/
qed-.

lemma pcc_inv_L_dx_succ (o) (e) (p) (n):
      p◖𝗟 ϵ 𝐂❨o,↑n,e❩ → p ϵ 𝐂❨o,n,e❩.
#o #e #p #n #H0
elim (pcc_inv_L_dx … H0) -H0 //
qed-.

(* Constructions with land **************************************************)

lemma pcc_land_dx (o1) (o2) (e) (p) (n):
      p ϵ 𝐂❨o1,n,e❩ → p ϵ 𝐂❨o1∧o2,n,e❩.
#o1 * /2 width=2 by pcc_des_gen/
qed.

lemma pcc_land_sn (o1) (o2) (e) (p) (n):
      p ϵ 𝐂❨o2,n,e❩ → p ϵ 𝐂❨o1∧o2,n,e❩.
* /2 width=2 by pcc_des_gen/
qed.

(* Main constructions with path_append **************************************)

theorem pcc_append_bi (o1) (o2) (e1) (e2) (p) (q) (m) (n):
        p ϵ 𝐂❨o1,m,e1❩ → q ϵ 𝐂❨o2,n,e2❩ → p●q ϵ 𝐂❨o1∧o2,m+n,e1+e2❩.
#o1 #o2 #e1 #e2 #p #q #m #n #Hm #Hn elim Hn -q -n
/3 width=1 by pcc_land_dx, pcc_m_dx, pcc_A_dx, pcc_S_dx, pcc_plus_bi_dx/
#q #n [ #k #Ho2 ] #_ #IH
[ @pcc_d_dx // #H0
  elim (andb_inv_true_sn … H0) -H0 #_ #H0 >Ho2 //
  <nplus_succ_dx <npred_succ //
| <nplus_succ_dx /2 width=1 by pcc_L_dx/
]
qed.

(* Inversions with path_append **********************************************)

lemma pcc_false_zero_dx_inv_append_bi (x) (m) (n):
      x ϵ 𝐂❨Ⓕ,m+n,𝟎❩ →
      ∃∃p,q. p ϵ 𝐂❨Ⓕ,m,𝟎❩ & q ϵ 𝐂❨Ⓕ,n,𝟎❩ & p●q = x.
#x #m #n #Hx
@(insert_eq_1 … (m+n) … Hx) -Hx #y #Hy
generalize in match n; -n
generalize in match m; -m
elim Hy -x -y [|*: #x #y [ #k #_ ] #Hx #IH ] #m #n #Hy destruct
[ elim (eq_inv_nplus_zero … Hy) -Hy #H1 #H2 destruct
  /2 width=5 by pcc_empty, ex3_2_intro/
| elim (IH m (n+k)) -IH // #p #q #Hp #Hq #H0 destruct -Hx
  /3 width=5 by pcc_false_d_dx, ex3_2_intro/
| elim (IH m n) -IH // #p #q #Hp #Hq #H0 destruct -Hx
  /3 width=5 by pcc_m_dx, ex3_2_intro/
| elim (eq_inv_succ_nplus_dx … (sym_eq … Hy)) -Hy * #H1 #H2 (**) (* sym_eq *)
  [ destruct -IH
    /3 width=5 by pcc_empty, pcc_L_dx, ex3_2_intro/
  | elim (IH m (⫰n)) -IH // #p #q #Hp #Hq #H0 destruct -Hx
    /3 width=5 by pcc_L_dx, ex3_2_intro/
  ]
| elim (IH m n) -IH // #p #q #Hp #Hq #H0 destruct -Hx
  /3 width=5 by pcc_A_dx, ex3_2_intro/
| elim (IH m n) -IH // #p #q #Hp #Hq #H0 destruct -Hx
  /3 width=5 by pcc_S_dx, ex3_2_intro/
]
qed-.


(* Constructions with path_lcons ********************************************)

lemma pcc_m_sn (o) (e) (q) (n):
      q ϵ 𝐂❨o,n,e❩ → (𝗺◗q) ϵ 𝐂❨o,n,e❩.
#o #e #q #n #Hq
lapply (pcc_append_bi (Ⓣ) … (𝟎) e … (𝐞◖𝗺) … Hq) -Hq
/2 width=3 by pcc_m_dx/
qed.

lemma pcc_L_sn (o) (e) (q) (n):
      q ϵ 𝐂❨o,n,e❩ → (𝗟◗q) ϵ 𝐂❨o,↑n,e❩.
#o #e #q #n #Hq
lapply (pcc_append_bi (Ⓣ) … (𝟎) e … (𝐞◖𝗟) … Hq) -Hq
/2 width=3 by pcc_L_dx/
qed.

lemma pcc_A_sn (o) (e) (q) (n):
      q ϵ 𝐂❨o,n,e❩ → (𝗔◗q) ϵ 𝐂❨o,n,e❩.
#o #e #q #n #Hq
lapply (pcc_append_bi (Ⓣ) … (𝟎) e … (𝐞◖𝗔) … Hq) -Hq
/2 width=3 by pcc_A_dx/
qed.

lemma pcc_S_sn (o) (e) (q) (n):
      q ϵ 𝐂❨o,n,e❩ → (𝗦◗q) ϵ 𝐂❨o,n,e❩.
#o #e #q #n #Hq
lapply (pcc_append_bi (Ⓣ) … (𝟎) e … (𝐞◖𝗦) … Hq) -Hq
/2 width=3 by pcc_S_dx/
qed.

(* Main inversions **********************************************************)

theorem pcc_mono (o1) (o2) (e) (q) (n1):
        q ϵ 𝐂❨o1,n1,e❩ → ∀n2. q ϵ 𝐂❨o2,n2,e❩ → n1 = n2.
#o1 #o2 #e #q1 #n1 #Hn1 elim Hn1 -q1 -n1
[|*: #q1 #n1 [ #k1 #_ ] #_ #IH ] #n2 #Hn2
[ <(pcc_inv_empty … Hn2) -n2 //
| lapply (pcc_des_d_dx … Hn2) -Hn2 #Hn2
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

theorem pcc_zero_dx_inj_L_sn (o1) (o2) (p1) (p2) (q1) (n):
        q1 ϵ 𝐂❨o1,n,𝟎❩ → ∀q2. q2 ϵ 𝐂❨o2,n,𝟎❩ →
        p1●𝗟◗q1 = p2●𝗟◗q2 → q1 = q2.
#o1 #o2 #p1 #p2 #q1 #n #Hq1 elim Hq1 -q1 -n
[|*: #q1 #n1 [ #k1 #_ ] #_ #IH ] * //
[1,3,5,7,9,11: #l2 #q2 ] #Hq2
<list_append_lcons_sn <list_append_lcons_sn #H0
elim (eq_inv_list_lcons_bi ????? H0) -H0 #H0 #H1 destruct
[ elim (pcc_inv_L_dx_zero_sn … Hq2)
| lapply (pcc_des_d_dx … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| lapply (pcc_inv_m_dx … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| lapply (pcc_inv_L_dx_succ … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| lapply (pcc_inv_A_dx … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| lapply (pcc_inv_S_dx … Hq2) -Hq2 #Hq2
  <(IH … Hq2) //
| elim (pcc_inv_empty_succ_zero … Hq2)
]
qed-.

theorem pcc_inv_L_sn (o) (e) (q) (n) (m):
        (𝗟◗q) ϵ 𝐂❨o,n,e❩ → q ϵ 𝐂❨o,m,e❩ →
        ∧∧ ⫰n = m & n = ↑⫰n.
#o #e #q #n #m #H1q #H2q
lapply (pcc_L_sn … H2q) -H2q #H2q
<(pcc_mono … H2q … H1q) -q -n <npred_succ
/2 width=1 by conj/
qed-.
