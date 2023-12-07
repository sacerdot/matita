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

include "delayed_updating/unwind/unwind2_path.ma".
include "delayed_updating/syntax/path_structure_inner.ma".
include "delayed_updating/syntax/path_proper.ma".
include "ground/xoa/ex_4_2.ma".

(* TAILED UNWIND FOR PATH ***************************************************)

(* Constructions with pic ***************************************************)

lemma unwind2_path_pic (f) (p):
      p ϵ 𝐈 → ⊗p = ▼[f]p.
#f * // * // #k #q #Hq
elim (pic_inv_d_dx … Hq)
qed-.

(* Constructions with append and pic ****************************************)

lemma unwind2_path_append_pic_sn (f) (p) (q): p ϵ 𝐈 →
      (⊗p)●(▼[▶[p]f]q) = ▼[f](p●q).
#f #p * [ #Hp | * [ #k ] #q #_ ]
[ <(unwind2_path_pic … Hp) -Hp //
| <unwind2_path_d_dx <unwind2_path_d_dx
  /2 width=3 by trans_eq/
| <unwind2_path_L_dx <unwind2_path_L_dx //
| <unwind2_path_A_dx <unwind2_path_A_dx //
| <unwind2_path_S_dx <unwind2_path_S_dx //
]
qed.

(* Constructions with append and ppc ****************************************)

lemma unwind2_path_append_ppc_dx (f) (p) (q): q ϵ 𝐏 →
      (⊗p)●(▼[▶[p]f]q) = ▼[f](p●q).
#f #p * [ #Hq | * [ #k ] #q #_ ]
[ elim (ppc_inv_empty … Hq)
| <unwind2_path_d_dx <unwind2_path_d_dx
  /2 width=3 by trans_eq/
| <unwind2_path_L_dx <unwind2_path_L_dx //
| <unwind2_path_A_dx <unwind2_path_A_dx //
| <unwind2_path_S_dx <unwind2_path_S_dx //
]
qed.

(* Constructions with path_lcons ********************************************)

lemma unwind2_path_d_empty (f) (k):
      (𝗱(f＠❨k❩)◗𝐞) = ▼[f](𝗱k◗𝐞).
// qed.

lemma unwind2_path_d_lcons (f) (p) (l) (k):
      ▼[f•𝐮❨k❩](l◗p) = ▼[f](𝗱k◗l◗p).
#f #p #l #k <unwind2_path_append_ppc_dx in ⊢ (???%); //
qed.

lemma unwind2_path_L_sn (f) (p):
      (𝗟◗▼[⫯f]p) = ▼[f](𝗟◗p).
#f #p <unwind2_path_append_pic_sn //
qed.

lemma unwind2_path_A_sn (f) (p):
      (𝗔◗▼[f]p) = ▼[f](𝗔◗p).
#f #p <unwind2_path_append_pic_sn //
qed.

lemma unwind2_path_S_sn (f) (p):
      (𝗦◗▼[f]p) = ▼[f](𝗦◗p).
#f #p <unwind2_path_append_pic_sn //
qed.

(* Destructions with pic ****************************************************)

lemma unwind2_path_des_pic (f) (p):
      ▼[f]p ϵ 𝐈 → p ϵ 𝐈.
#f * // * [ #k ] #p //
<unwind2_path_d_dx #H0
elim (pic_inv_d_dx … H0)
qed-.

(* Destructions with append and pic *****************************************)

lemma unwind2_path_des_append_pic_sn (f) (p) (q1) (q2):
      q1 ϵ 𝐈 → q1●q2 = ▼[f]p →
      ∃∃p1,p2. p1 ϵ 𝐈 & q1 = ⊗p1 & q2 = ▼[▶[p1]f]p2 & p1●p2 = p.
#f #p #q1 * [| * [ #k ] #q2 ] #Hq1
[ <list_append_empty_sn #H0 destruct
  lapply (unwind2_path_des_pic … Hq1) -Hq1 #Hp
  <(unwind2_path_pic … Hp)
  /2 width=6 by ex4_2_intro/
| #H0 elim (eq_inv_d_dx_unwind2_path … H0) -H0 #r #h #Hr #H1 #H2 destruct
  elim (eq_inv_append_structure_pic … Hr) -Hr #s1 #s2 #Hs1 #H1 #H2 #H3 destruct
  /2 width=6 by ex4_2_intro/
| #H0 elim (eq_inv_L_dx_unwind2_path … H0) -H0 #r #Hr #H2 destruct
  elim (eq_inv_append_structure_pic … Hr) -Hr #s1 #s2 #Hs1 #H1 #H2 #H3 destruct
  /2 width=6 by ex4_2_intro/
| #H0 elim (eq_inv_A_dx_unwind2_path … H0) -H0 #r #Hr #H0 destruct
  elim (eq_inv_append_structure_pic … Hr) -Hr #s1 #s2 #Hs1 #H1 #H2 #H3 destruct
  /2 width=6 by ex4_2_intro/
| #H0 elim (eq_inv_S_dx_unwind2_path … H0) -H0 #r #Hr #H0 destruct
  elim (eq_inv_append_structure_pic … Hr) -Hr #s1 #s2 #Hs1 #H1 #H2 #H3 destruct
  /2 width=6 by ex4_2_intro/
]
qed-.

(* Inversions with append and ppc *******************************************)

lemma unwind2_path_inv_append_ppc_dx (f) (p) (q1) (q2):
      q2 ϵ 𝐏 → q1●q2 = ▼[f]p →
      ∃∃p1,p2. q1 = ⊗p1 & q2 = ▼[▶[p1]f]p2 & p1●p2 = p.
#f #p #q1 * [| * [ #k ] #q2 ] #Hq1
[ <list_append_empty_sn #H0 destruct
  elim (ppc_inv_empty … Hq1)
| #H0 elim (eq_inv_d_dx_unwind2_path … H0) -H0 #r #h #Hr #H1 #H2 destruct
  elim (eq_inv_append_structure … Hr) -Hr #s1 #s2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| #H0 elim (eq_inv_L_dx_unwind2_path … H0) -H0 #r #Hr #H2 destruct
  elim (eq_inv_append_structure … Hr) -Hr #s1 #s2 #H1 #H2 #H3 destruct
  /2 width=5 by refl, ex3_2_intro/
| #H0 elim (eq_inv_A_dx_unwind2_path … H0) -H0 #r #Hr #H0 destruct
  elim (eq_inv_append_structure … Hr) -Hr #s1 #s2 #H1 #H2 #H3 destruct
  /2 width=5 by refl, ex3_2_intro/
| #H0 elim (eq_inv_S_dx_unwind2_path … H0) -H0 #r #Hr #H0 destruct
  elim (eq_inv_append_structure … Hr) -Hr #s1 #s2 #H1 #H2 #H3 destruct
  /2 width=5 by refl, ex3_2_intro/
]
qed-.

(* Inversions with path_lcons ***********************************************)

lemma eq_inv_d_sn_unwind2_path (f) (q) (p) (k):
      (𝗱k◗q) = ▼[f]p →
      ∃∃r,h. 𝐞 = ⊗r & (▶[r]f)＠❨h❩ = k & 𝐞 = q & r◖𝗱h = p.
#f * [| #l #q ] #p #k
[ <list_cons_comm #H0
  elim (eq_inv_d_dx_unwind2_path … H0) -H0 #r1 #r2 #Hr1 #H1 #H2 destruct
  /2 width=5 by ex4_2_intro/
| >list_cons_comm #H0
  elim (unwind2_path_inv_append_ppc_dx … H0) -H0 // #r1 #r2 #Hr1 #_ #_ -r2
  elim (eq_inv_d_dx_structure … Hr1)
]
qed-.

lemma eq_inv_L_sn_unwind2_path (f) (q) (p):
      (𝗟◗q) = ▼[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ▼[⫯▶[r1]f]r2 & r1●𝗟◗r2 = p.
#f #q #p
>list_cons_comm #H0
elim (unwind2_path_des_append_pic_sn … H0) <list_cons_comm in H0; //
#H0 #r1 #r2 #_ #H2r1 #H1 #H2 destruct
elim (eq_inv_L_dx_structure … H2r1) -H2r1 #s1 #s2 #H1 #_ #H3 destruct
<list_append_assoc in H0; <list_append_assoc
<unwind2_path_append_ppc_dx //
<unwind2_path_L_sn <H1 <list_append_empty_dx #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_
/2 width=5 by ex3_2_intro/
qed-.

lemma eq_inv_A_sn_unwind2_path (f) (q) (p):
      (𝗔◗q) = ▼[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ▼[▶[r1]f]r2 & r1●𝗔◗r2 = p.
#f #q #p
>list_cons_comm #H0
elim (unwind2_path_des_append_pic_sn … H0) <list_cons_comm in H0; //
#H0 #r1 #r2 #_ #H2r1 #H1 #H2 destruct
elim (eq_inv_A_dx_structure … H2r1) -H2r1 #s1 #s2 #H1 #_ #H3 destruct
<list_append_assoc in H0; <list_append_assoc
<unwind2_path_append_ppc_dx //
<unwind2_path_A_sn <H1 <list_append_empty_dx #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_
/2 width=5 by ex3_2_intro/
qed-.

lemma eq_inv_S_sn_unwind2_path (f) (q) (p):
      (𝗦◗q) = ▼[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ▼[▶[r1]f]r2 & r1●𝗦◗r2 = p.
#f #q #p
>list_cons_comm #H0
elim (unwind2_path_des_append_pic_sn … H0) <list_cons_comm in H0; //
#H0 #r1 #r2 #_ #H2r1 #H1 #H2 destruct
elim (eq_inv_S_dx_structure … H2r1) -H2r1 #s1 #s2 #H1 #_ #H3 destruct
<list_append_assoc in H0; <list_append_assoc
<unwind2_path_append_ppc_dx //
<unwind2_path_S_sn <H1 <list_append_empty_dx #H0
elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_
/2 width=5 by ex3_2_intro/
qed-.

(* Advanced eliminations with path ******************************************)

lemma path_ind_unwind (Q:predicate …):
      Q (𝐞) →
      (∀k. Q (𝐞) → Q (𝗱k◗𝐞)) →
      (∀k,l,p. Q (l◗p) → Q (𝗱k◗l◗p)) →
      (∀p. Q p → Q (𝗟◗p)) →
      (∀p. Q p → Q (𝗔◗p)) →
      (∀p. Q p → Q (𝗦◗p)) →
      ∀p. Q p.
#Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #p
@(list_ind_rcons … p) -p // #p * [ #k ]
[ @(list_ind_rcons … p) -p ]
/2 width=1 by/
qed-.
