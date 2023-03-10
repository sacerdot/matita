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

inductive pcc (o) (e): relation2 nat path ā
| pcc_empty:
  pcc o e e (š)
| pcc_d_dx (p) (n) (k):
  (ā = o ā n = āān) ā
  pcc o e (n+ninj k) p ā pcc o e n (pāš±k)
| pcc_m_dx (p) (n):
  pcc o e n p ā pcc o e n (pāšŗ)
| pcc_L_dx (p) (n):
  pcc o e n p ā pcc o e (ān) (pāš)
| pcc_A_dx (p) (n):
  pcc o e n p ā pcc o e n (pāš)
| pcc_S_dx (p) (n):
  pcc o e n p ā pcc o e n (pāš¦)
.

interpretation
  "closed condition (path)"
  'ClassC o n e = (pcc o e n).

(* Advanced constructions ***************************************************)

lemma pcc_false_d_dx (e) (p) (n) (k:pnat):
      p Ļµ šāØā»,n+k,eā© ā pāš±k Ļµ šāØā»,n,eā©.
#e #p #n #k #H0
@pcc_d_dx [| // ]
#H0 destruct
qed.

lemma pcc_true_d_dx (e) (p) (n:pnat) (k:pnat):
      p Ļµ šāØā,n+k,eā© ā pāš±k Ļµ šāØā,n,eā©.
/2 width=1 by pcc_d_dx/
qed.

lemma pcc_plus_bi_dx (o) (e) (p) (n):
      p Ļµ šāØo,n,eā© ā
      ām. p Ļµ šāØo,n+m,e+mā©.
#o #e #p #n #H0 elim H0 -p -n //
#p #n [ #k #Ho ] #_ #IH #m
[|*: /2 width=1 by pcc_m_dx, pcc_L_dx, pcc_A_dx, pcc_S_dx/ ]
@pcc_d_dx // -IH #H0
>Ho -Ho // <nplus_succ_sn //
qed.

(* Basic inversions ********************************************************)

lemma pcc_inv_empty (o) (e) (n):
      (š) Ļµ šāØo,n,eā© ā e = n.
#o #e #n @(insert_eq_1 ā¦ (š))
#x * -n //
#p #n [ #k #_ ] #_ #H0 destruct
qed-.

(**) (* alias *)
alias symbol "DownArrow" (instance 4) = "predecessor (non-negative integers)".
alias symbol "UpArrow" (instance 3) = "successor (non-negative integers)".
alias symbol "and" (instance 1) = "logical and".

lemma pcc_inv_d_dx (o) (e) (p) (n) (k):
      pāš±k Ļµ šāØo,n,eā© ā
      ā§ā§ (ā = o ā n = āān)
       & p Ļµ šāØo,n+k,eā©.
#o #e #p #n #h @(insert_eq_1 ā¦ (pāš±h))
#x * -x -n
[|*: #x #n [ #k #Ho ] #Hx ] #H0 destruct
/3 width=1 by conj/
qed-.

lemma pcc_inv_m_dx (o) (e) (p) (n):
      pāšŗ Ļµ šāØo,n,eā© ā p Ļµ šāØo,n,eā©.
#o #e #p #n @(insert_eq_1 ā¦ (pāšŗ))
#x * -x -n
[|*: #x #n [ #k #_ ] #Hx ] #H0 destruct //
qed-.

lemma pcc_inv_L_dx (o) (e) (p) (n):
      pāš Ļµ šāØo,n,eā© ā
      ā§ā§ p Ļµ šāØo,ān,eā© & n = āān.
#o #e #p #n @(insert_eq_1 ā¦ (pāš))
#x * -x -n
[|*: #x #n [ #k #_ ] #Hx ] #H0 destruct
<npred_succ /2 width=1 by conj/
qed-.

lemma pcc_inv_A_dx (o) (e) (p) (n):
      pāš Ļµ šāØo,n,eā© ā p Ļµ šāØo,n,eā©.
#o #e #p #n @(insert_eq_1 ā¦ (pāš))
#x * -x -n
[|*: #x #n [ #k #_ ] #Hx ] #H0 destruct //
qed-.

lemma pcc_inv_S_dx (o) (e) (p) (n):
      pāš¦ Ļµ šāØo,n,eā© ā p Ļµ šāØo,n,eā©.
#o #e #p #n @(insert_eq_1 ā¦ (pāš¦))
#x * -x -n
[|*: #x #n [ #k #_ ] #Hx ] #H0 destruct //
qed-.

(* Advanced destructions ****************************************************)

lemma pcc_des_d_dx (o) (e) (p) (n) (k):
      pāš±k Ļµ šāØo,n,eā© ā p Ļµ šāØo,n+k,eā©.
#o #e #p #n #k #H0
elim (pcc_inv_d_dx ā¦ H0) -H0 #H1 #H2 //
qed-.

lemma pcc_des_gen (o) (e) (p) (n):
      p Ļµ šāØo,n,eā© ā p Ļµ šāØā»,n,eā©.
#o #e #p #n #H0 elim H0 -p -n //
#p #n [ #k #Ho ] #_ #IH
/2 width=1 by pcc_m_dx, pcc_L_dx, pcc_A_dx, pcc_S_dx, pcc_false_d_dx/
qed-.

(* Advanced inversions ******************************************************)

lemma pcc_inv_empty_succ_zero (o) (n):
      (š) Ļµ šāØo,ān,šā© ā ā„.
#o #n #H0
lapply (pcc_inv_empty ā¦ H0) -H0 #H0
/2 width=7 by eq_inv_zero_nsucc/
qed-.

lemma pcc_true_inv_d_dx_zero_sn (e) (p) (k):
      pāš±k Ļµ šāØā,š, eā© ā ā„.
#e #p #k #H0
elim (pcc_inv_d_dx ā¦ H0) -H0 #H0 #_
elim (eq_inv_zero_nsucc ā¦ (H0 ?)) -H0 //
qed-.

lemma pcc_inv_L_dx_zero_sn (o) (e) (p):
      pāš Ļµ šāØo,š,eā© ā ā„.
#o #e #p #H0
elim (pcc_inv_L_dx ā¦ H0) -H0 #_ #H0
/2 width=7 by eq_inv_zero_nsucc/
qed-.

lemma pcc_inv_L_dx_succ (o) (e) (p) (n):
      pāš Ļµ šāØo,ān,eā© ā p Ļµ šāØo,n,eā©.
#o #e #p #n #H0
elim (pcc_inv_L_dx ā¦ H0) -H0 //
qed-.

(* Constructions with land **************************************************)

lemma pcc_land_dx (o1) (o2) (e) (p) (n):
      p Ļµ šāØo1,n,eā© ā p Ļµ šāØo1ā§o2,n,eā©.
#o1 * /2 width=2 by pcc_des_gen/
qed.

lemma pcc_land_sn (o1) (o2) (e) (p) (n):
      p Ļµ šāØo2,n,eā© ā p Ļµ šāØo1ā§o2,n,eā©.
* /2 width=2 by pcc_des_gen/
qed.

(* Main constructions with path_append **************************************)

theorem pcc_append_bi (o1) (o2) (e1) (e2) (p) (q) (m) (n):
        p Ļµ šāØo1,m,e1ā© ā q Ļµ šāØo2,n,e2ā© ā pāq Ļµ šāØo1ā§o2,m+n,e1+e2ā©.
#o1 #o2 #e1 #e2 #p #q #m #n #Hm #Hn elim Hn -q -n
/3 width=1 by pcc_land_dx, pcc_m_dx, pcc_A_dx, pcc_S_dx, pcc_plus_bi_dx/
#q #n [ #k #Ho2 ] #_ #IH
[ @pcc_d_dx // #H0
  elim (andb_inv_true_sn ā¦ H0) -H0 #_ #H0 >Ho2 //
  <nplus_succ_dx <npred_succ //
| <nplus_succ_dx /2 width=1 by pcc_L_dx/
]
qed.

(* Inversions with path_append **********************************************)

lemma pcc_false_zero_dx_inv_append_bi (x) (m) (n):
      x Ļµ šāØā»,m+n,šā© ā
      āāp,q. p Ļµ šāØā»,m,šā© & q Ļµ šāØā»,n,šā© & pāq = x.
#x #m #n #Hx
@(insert_eq_1 ā¦ (m+n) ā¦ Hx) -Hx #y #Hy
generalize in match n; -n
generalize in match m; -m
elim Hy -x -y [|*: #x #y [ #k #_ ] #Hx #IH ] #m #n #Hy destruct
[ elim (eq_inv_nplus_zero ā¦ Hy) -Hy #H1 #H2 destruct
  /2 width=5 by pcc_empty, ex3_2_intro/
| elim (IH m (n+k)) -IH // #p #q #Hp #Hq #H0 destruct -Hx
  /3 width=5 by pcc_false_d_dx, ex3_2_intro/
| elim (IH m n) -IH // #p #q #Hp #Hq #H0 destruct -Hx
  /3 width=5 by pcc_m_dx, ex3_2_intro/
| elim (eq_inv_succ_nplus_dx ā¦ (sym_eq ā¦ Hy)) -Hy * #H1 #H2 (**) (* sym_eq *)
  [ destruct -IH
    /3 width=5 by pcc_empty, pcc_L_dx, ex3_2_intro/
  | elim (IH m (ān)) -IH // #p #q #Hp #Hq #H0 destruct -Hx
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
      q Ļµ šāØo,n,eā© ā (šŗāq) Ļµ šāØo,n,eā©.
#o #e #q #n #Hq
lapply (pcc_append_bi (ā) ā¦ (š) e ā¦ (šāšŗ) ā¦ Hq) -Hq
/2 width=3 by pcc_m_dx/
qed.

lemma pcc_L_sn (o) (e) (q) (n):
      q Ļµ šāØo,n,eā© ā (šāq) Ļµ šāØo,ān,eā©.
#o #e #q #n #Hq
lapply (pcc_append_bi (ā) ā¦ (š) e ā¦ (šāš) ā¦ Hq) -Hq
/2 width=3 by pcc_L_dx/
qed.

lemma pcc_A_sn (o) (e) (q) (n):
      q Ļµ šāØo,n,eā© ā (šāq) Ļµ šāØo,n,eā©.
#o #e #q #n #Hq
lapply (pcc_append_bi (ā) ā¦ (š) e ā¦ (šāš) ā¦ Hq) -Hq
/2 width=3 by pcc_A_dx/
qed.

lemma pcc_S_sn (o) (e) (q) (n):
      q Ļµ šāØo,n,eā© ā (š¦āq) Ļµ šāØo,n,eā©.
#o #e #q #n #Hq
lapply (pcc_append_bi (ā) ā¦ (š) e ā¦ (šāš¦) ā¦ Hq) -Hq
/2 width=3 by pcc_S_dx/
qed.

(* Main inversions **********************************************************)

theorem pcc_mono (o1) (o2) (e) (q) (n1):
        q Ļµ šāØo1,n1,eā© ā ān2. q Ļµ šāØo2,n2,eā© ā n1 = n2.
#o1 #o2 #e #q1 #n1 #Hn1 elim Hn1 -q1 -n1
[|*: #q1 #n1 [ #k1 #_ ] #_ #IH ] #n2 #Hn2
[ <(pcc_inv_empty ā¦ Hn2) -n2 //
| lapply (pcc_des_d_dx ā¦ Hn2) -Hn2 #Hn2
  lapply (IH ā¦ Hn2) -q1 #H0
  /2 width=2 by eq_inv_nplus_bi_dx/
| lapply (pcc_inv_m_dx ā¦ Hn2) -Hn2 #Hn2
  <(IH ā¦ Hn2) -q1 -n2 //
| elim (pcc_inv_L_dx ā¦ Hn2) -Hn2 #Hn2 #H0
  >(IH ā¦ Hn2) -q1 //
| lapply (pcc_inv_A_dx ā¦ Hn2) -Hn2 #Hn2
  <(IH ā¦ Hn2) -q1 -n2 //
| lapply (pcc_inv_S_dx ā¦ Hn2) -Hn2 #Hn2
  <(IH ā¦ Hn2) -q1 -n2 //
]
qed-.

theorem pcc_zero_dx_inj_L_sn (o1) (o2) (p1) (p2) (q1) (n):
        q1 Ļµ šāØo1,n,šā© ā āq2. q2 Ļµ šāØo2,n,šā© ā
        p1āšāq1 = p2āšāq2 ā q1 = q2.
#o1 #o2 #p1 #p2 #q1 #n #Hq1 elim Hq1 -q1 -n
[|*: #q1 #n1 [ #k1 #_ ] #_ #IH ] * //
[1,3,5,7,9,11: #l2 #q2 ] #Hq2
<list_append_lcons_sn <list_append_lcons_sn #H0
elim (eq_inv_list_lcons_bi ????? H0) -H0 #H0 #H1 destruct
[ elim (pcc_inv_L_dx_zero_sn ā¦ Hq2)
| lapply (pcc_des_d_dx ā¦ Hq2) -Hq2 #Hq2
  <(IH ā¦ Hq2) //
| lapply (pcc_inv_m_dx ā¦ Hq2) -Hq2 #Hq2
  <(IH ā¦ Hq2) //
| lapply (pcc_inv_L_dx_succ ā¦ Hq2) -Hq2 #Hq2
  <(IH ā¦ Hq2) //
| lapply (pcc_inv_A_dx ā¦ Hq2) -Hq2 #Hq2
  <(IH ā¦ Hq2) //
| lapply (pcc_inv_S_dx ā¦ Hq2) -Hq2 #Hq2
  <(IH ā¦ Hq2) //
| elim (pcc_inv_empty_succ_zero ā¦ Hq2)
]
qed-.

theorem pcc_inv_L_sn (o) (e) (q) (n) (m):
        (šāq) Ļµ šāØo,n,eā© ā q Ļµ šāØo,m,eā© ā
        ā§ā§ ān = m & n = āān.
#o #e #q #n #m #H1q #H2q
lapply (pcc_L_sn ā¦ H2q) -H2q #H2q
<(pcc_mono ā¦ H2q ā¦ H1q) -q -n
/2 width=1 by conj/
qed-.
