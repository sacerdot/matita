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

include "delayed_updating/unwind_k/unwind2_path.ma".
include "delayed_updating/syntax/path_inner.ma".
include "delayed_updating/syntax/path_proper.ma".
include "ground/xoa/ex_4_2.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

(* Constructions with pic ***************************************************)

lemma unwind2_path_pic (f) (p):
      p Ļµ š ā āp = ā¼[f]p.
#f * // * // #k #q #Hq
elim (pic_inv_d_dx ā¦ Hq)
qed-.

(* Constructions with append and pic ****************************************)

lemma unwind2_path_append_pic_sn (f) (p) (q): p Ļµ š ā
      (āp)ā(ā¼[ā¶[f]p]q) = ā¼[f](pāq).
#f #p * [ #Hp | * [ #k ] #q #_ ] //
[ <(unwind2_path_pic ā¦ Hp) -Hp //
| <unwind2_path_d_dx <unwind2_path_d_dx
  /2 width=3 by trans_eq/
| <unwind2_path_L_dx <unwind2_path_L_dx //
| <unwind2_path_A_dx <unwind2_path_A_dx //
| <unwind2_path_S_dx <unwind2_path_S_dx //
]
qed.

(* Constructions with append and ppc ****************************************)

lemma unwind2_path_append_ppc_dx (f) (p) (q): q Ļµ š ā
      (āp)ā(ā¼[ā¶[f]p]q) = ā¼[f](pāq).
#f #p * [ #Hq | * [ #k ] #q #_ ] //
[ elim (ppc_inv_empty ā¦ Hq)
| <unwind2_path_d_dx <unwind2_path_d_dx
  /2 width=3 by trans_eq/
| <unwind2_path_L_dx <unwind2_path_L_dx //
| <unwind2_path_A_dx <unwind2_path_A_dx //
| <unwind2_path_S_dx <unwind2_path_S_dx //
]
qed.

(* Constructions with path_lcons ********************************************)

lemma unwind2_path_d_empty (f) (k):
      (š±(fļ¼ ā§£āØkā©)āš) = ā¼[f](š±kāš).
// qed.

lemma unwind2_path_d_lcons (f) (p) (l) (k:pnat):
      ā¼[fāš®āØkā©](lāp) = ā¼[f](š±kālāp).
#f #p #l #k <unwind2_path_append_ppc_dx in ā¢ (???%); //
qed.

lemma unwind2_path_m_sn (f) (p):
      ā¼[f]p = ā¼[f](šŗāp).
#f #p <unwind2_path_append_pic_sn //
qed.

lemma unwind2_path_L_sn (f) (p):
      (šāā¼[ā«Æf]p) = ā¼[f](šāp).
#f #p <unwind2_path_append_pic_sn //
qed.

lemma unwind2_path_A_sn (f) (p):
      (šāā¼[f]p) = ā¼[f](šāp).
#f #p <unwind2_path_append_pic_sn //
qed.

lemma unwind2_path_S_sn (f) (p):
      (š¦āā¼[f]p) = ā¼[f](š¦āp).
#f #p <unwind2_path_append_pic_sn //
qed.

(* Destructions with pic ****************************************************)

lemma unwind2_path_des_pic (f) (p):
      ā¼[f]p Ļµ š ā p Ļµ š.
#f * // * [ #k ] #p //
<unwind2_path_d_dx #H0
elim (pic_inv_d_dx ā¦ H0)
qed-.

(* Destructions with append and pic *****************************************)

lemma unwind2_path_des_append_pic_sn (f) (p) (q1) (q2):
      q1 Ļµ š ā q1āq2 = ā¼[f]p ā
      āāp1,p2. q1 = āp1 & q2 = ā¼[ā¶[f]p1]p2 & p1āp2 = p.
#f #p #q1 * [| * [ #k ] #q2 ] #Hq1
[ <list_append_empty_sn #H0 destruct
  lapply (unwind2_path_des_pic ā¦ Hq1) -Hq1 #Hp
  <(unwind2_path_pic ā¦ Hp) -Hp
  /2 width=5 by ex3_2_intro/
| #H0 elim (eq_inv_d_dx_unwind2_path ā¦ H0) -H0 #r #h #Hr #H1 #H2 destruct
  elim (eq_inv_append_structure ā¦ Hr) -Hr #s1 #s2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| #H0 elim (eq_inv_m_dx_unwind2_path ā¦ H0)
| #H0 elim (eq_inv_L_dx_unwind2_path ā¦ H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (eq_inv_append_structure ā¦ Hr1) -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro ā¦ s1 (s2āšār2)) //
  <unwind2_path_append_ppc_dx //
  <unwind2_path_L_sn <Hr2 -Hr2 //
| #H0 elim (eq_inv_A_dx_unwind2_path ā¦ H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (eq_inv_append_structure ā¦ Hr1) -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro ā¦ s1 (s2āšār2)) //
  <unwind2_path_append_ppc_dx //
  <unwind2_path_A_sn <Hr2 -Hr2 //
| #H0 elim (eq_inv_S_dx_unwind2_path ā¦ H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (eq_inv_append_structure ā¦ Hr1) -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro ā¦ s1 (s2āš¦ār2)) //
  <unwind2_path_append_ppc_dx //
  <unwind2_path_S_sn <Hr2 -Hr2 //
]
qed-.

(* Inversions with append and ppc *******************************************)

lemma unwind2_path_inv_append_ppc_dx (f) (p) (q1) (q2):
      q2 Ļµ š ā q1āq2 = ā¼[f]p ā
      āāp1,p2. q1 = āp1 & q2 = ā¼[ā¶[f]p1]p2 & p1āp2 = p.
#f #p #q1 * [| * [ #k ] #q2 ] #Hq1
[ <list_append_empty_sn #H0 destruct
  elim (ppc_inv_empty ā¦ Hq1)
| #H0 elim (eq_inv_d_dx_unwind2_path ā¦ H0) -H0 #r #h #Hr #H1 #H2 destruct
  elim (eq_inv_append_structure ā¦ Hr) -Hr #s1 #s2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| #H0 elim (eq_inv_m_dx_unwind2_path ā¦ H0)
| #H0 elim (eq_inv_L_dx_unwind2_path ā¦ H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (eq_inv_append_structure ā¦ Hr1) -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro ā¦ s1 (s2āšār2)) //
  <unwind2_path_append_ppc_dx //
  <unwind2_path_L_sn <Hr2 -Hr2 //
| #H0 elim (eq_inv_A_dx_unwind2_path ā¦ H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (eq_inv_append_structure ā¦ Hr1) -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro ā¦ s1 (s2āšār2)) //
  <unwind2_path_append_ppc_dx //
  <unwind2_path_A_sn <Hr2 -Hr2 //
| #H0 elim (eq_inv_S_dx_unwind2_path ā¦ H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (eq_inv_append_structure ā¦ Hr1) -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro ā¦ s1 (s2āš¦ār2)) //
  <unwind2_path_append_ppc_dx //
  <unwind2_path_S_sn <Hr2 -Hr2 //
]
qed-.

(* Inversions with path_lcons ***********************************************)

lemma eq_inv_d_sn_unwind2_path (f) (q) (p) (k):
      (š±kāq) = ā¼[f]p ā
      āār,h. š = ār & ā¶[f]rļ¼ ā§£āØhā© = k & š = q & rāš±h = p.
#f * [| #l #q ] #p #k
[ <list_cons_comm #H0
  elim (eq_inv_d_dx_unwind2_path ā¦ H0) -H0 #r1 #r2 #Hr1 #H1 #H2 destruct
  /2 width=5 by ex4_2_intro/
| >list_cons_comm #H0
  elim (unwind2_path_inv_append_ppc_dx ā¦ H0) -H0 // #r1 #r2 #Hr1 #_ #_ -r2
  elim (eq_inv_d_dx_structure ā¦ Hr1)
]
qed-.

lemma eq_inv_m_sn_unwind2_path (f) (q) (p):
      (šŗāq) = ā¼[f]p ā ā„.
#f #q #p
>list_cons_comm #H0
elim (unwind2_path_des_append_pic_sn ā¦ H0) <list_cons_comm in H0; //
#H0 #r1 #r2 #Hr1 #H1 #H2 destruct
elim (eq_inv_m_dx_structure ā¦ Hr1)
qed-.

lemma eq_inv_L_sn_unwind2_path (f) (q) (p):
      (šāq) = ā¼[f]p ā
      āār1,r2. š = ār1 & q = ā¼[ā«Æā¶[f]r1]r2 & r1āšār2 = p.
#f #q #p
>list_cons_comm #H0
elim (unwind2_path_des_append_pic_sn ā¦ H0) <list_cons_comm in H0; //
#H0 #r1 #r2 #Hr1 #H1 #H2 destruct
elim (eq_inv_L_dx_structure ā¦ Hr1) -Hr1 #s1 #s2 #H1 #_ #H3 destruct
<list_append_assoc in H0; <list_append_assoc
<unwind2_path_append_ppc_dx //
<unwind2_path_L_sn <H1 <list_append_empty_dx #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_
/2 width=5 by ex3_2_intro/
qed-.

lemma eq_inv_A_sn_unwind2_path (f) (q) (p):
      (šāq) = ā¼[f]p ā
      āār1,r2. š = ār1 & q = ā¼[ā¶[f]r1]r2 & r1āšār2 = p.
#f #q #p
>list_cons_comm #H0
elim (unwind2_path_des_append_pic_sn ā¦ H0) <list_cons_comm in H0; //
#H0 #r1 #r2 #Hr1 #H1 #H2 destruct
elim (eq_inv_A_dx_structure ā¦ Hr1) -Hr1 #s1 #s2 #H1 #_ #H3 destruct
<list_append_assoc in H0; <list_append_assoc
<unwind2_path_append_ppc_dx //
<unwind2_path_A_sn <H1 <list_append_empty_dx #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_
/2 width=5 by ex3_2_intro/
qed-.

lemma eq_inv_S_sn_unwind2_path (f) (q) (p):
      (š¦āq) = ā¼[f]p ā
      āār1,r2. š = ār1 & q = ā¼[ā¶[f]r1]r2 & r1āš¦ār2 = p.
#f #q #p
>list_cons_comm #H0
elim (unwind2_path_des_append_pic_sn ā¦ H0) <list_cons_comm in H0; //
#H0 #r1 #r2 #Hr1 #H1 #H2 destruct
elim (eq_inv_S_dx_structure ā¦ Hr1) -Hr1 #s1 #s2 #H1 #_ #H3 destruct
<list_append_assoc in H0; <list_append_assoc
<unwind2_path_append_ppc_dx //
<unwind2_path_S_sn <H1 <list_append_empty_dx #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_
/2 width=5 by ex3_2_intro/
qed-.

(* Advanced eliminations with path ******************************************)

lemma path_ind_unwind (Q:predicate ā¦):
      Q (š) ā
      (āk. Q (š) ā Q (š±kāš)) ā
      (āk,l,p. Q (lāp) ā Q (š±kālāp)) ā
      (āp. Q p ā Q (šŗāp)) ā
      (āp. Q p ā Q (šāp)) ā
      (āp. Q p ā Q (šāp)) ā
      (āp. Q p ā Q (š¦āp)) ā
      āp. Q p.
#Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #p
@(list_ind_rcons ā¦ p) -p // #p * [ #k ]
[ @(list_ind_rcons ā¦ p) -p ]
/2 width=1 by/
qed-.
