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

include "delayed_updating/unwind/unwind_gen.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_inner.ma".
include "delayed_updating/syntax/path_proper.ma".
include "ground/xoa/ex_4_2.ma".
include "ground/xoa/ex_3_2.ma".

(* GENERIC UNWIND FOR PATH *************************************************)

(* Basic constructions with structure **************************************)

lemma structure_unwind_gen (p) (f):
      ⊗p = ⊗◆[f]p.
#p @(path_ind_unwind … p) -p //
qed.

lemma unwind_gen_structure (p) (f):
      ⊗p = ◆[f]⊗p.
#p @(path_ind_unwind … p) -p //
qed.

(* Destructions with structure **********************************************)

lemma unwind_gen_des_structure (q) (p) (f):
      ⊗q = ◆[f]p → ⊗q = ⊗p.
// qed-.

(* Constructions with proper condition for path *****************************)

lemma unwind_gen_append_proper_dx (p2) (p1) (f): p2 ϵ 𝐏 →
      (⊗p1)●(◆[f]p2) = ◆[f](p1●p2).
#p2 #p1 @(path_ind_unwind … p1) -p1 //
[ #n | #n #l #p1 |*: #p1 ] #IH #f #Hp2
[ elim (ppc_inv_lcons … Hp2) -Hp2 #l #q #H0 destruct //
| <unwind_gen_d_lcons <IH //
| <unwind_gen_m_sn <IH //
| <unwind_gen_L_sn <IH //
| <unwind_gen_A_sn <IH //
| <unwind_gen_S_sn <IH //
]
qed-.

(* Constructions with inner condition for path ******************************)

lemma unwind_gen_append_inner_sn (p1) (p2) (f): p1 ϵ 𝐈 →
      (⊗p1)●(◆[f]p2) = ◆[f](p1●p2).
#p1 @(list_ind_rcons … p1) -p1 //
#p1 * [ #n ] #_ #p2 #f #Hp1
[ elim (pic_inv_d_dx … Hp1)
| <list_append_rcons_sn <unwind_gen_append_proper_dx //
| <list_append_rcons_sn <unwind_gen_append_proper_dx //
  <structure_L_dx <list_append_rcons_sn //
| <list_append_rcons_sn <unwind_gen_append_proper_dx //
  <structure_A_dx <list_append_rcons_sn //
| <list_append_rcons_sn <unwind_gen_append_proper_dx //
  <structure_S_dx <list_append_rcons_sn //
]
qed-.

(* Advanced constructions with list_rcons ***********************************)

lemma unwind_gen_d_dx (f) (p) (n):
      (⊗p)◖𝗱(f＠⧣❨n❩) = ◆[f](p◖𝗱n).
#f #p #n <unwind_gen_append_proper_dx //
qed.

lemma unwind_gen_m_dx (f) (p):
      ⊗p = ◆[f](p◖𝗺).
#f #p <unwind_gen_append_proper_dx //
qed.

lemma unwind_gen_L_dx (f) (p):
      (⊗p)◖𝗟 = ◆[f](p◖𝗟).
#f #p <unwind_gen_append_proper_dx //
qed.

lemma unwind_gen_A_dx (f) (p):
      (⊗p)◖𝗔 = ◆[f](p◖𝗔).
#f #p <unwind_gen_append_proper_dx //
qed.

lemma unwind_gen_S_dx (f) (p):
      (⊗p)◖𝗦 = ◆[f](p◖𝗦).
#f #p <unwind_gen_append_proper_dx //
qed.

lemma unwind_gen_root (f) (p):
      ∃∃r. 𝐞 = ⊗r & ⊗p●r = ◆[f]p.
#f #p @(list_ind_rcons … p) -p
[ /2 width=3 by ex2_intro/
| #p * [ #n ] /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversions ******************************************************)

lemma unwind_gen_inv_d_sn (k) (q) (p) (f):
      (𝗱k◗q) = ◆[f]p →
      ∃∃r,h. 𝐞 = ⊗r & f＠⧣❨h❩ = k & 𝐞 = q & r◖𝗱h = p.
#k #q #p @(path_ind_unwind … p) -p
[| #n | #n #l #p |*: #p ] [|*: #IH ] #f
[ <unwind_gen_empty #H destruct
| <unwind_gen_d_empty #H destruct -IH
  /2 width=5 by ex4_2_intro/
| <unwind_gen_d_lcons #H
  elim (IH … H) -IH -H #r #h #Hr #Hh #Hq #Hp destruct
  /2 width=5 by ex4_2_intro/
| <unwind_gen_m_sn #H
  elim (IH … H) -IH -H #r #h #Hr #Hh #Hq #Hp destruct
  /2 width=5 by ex4_2_intro/
| <unwind_gen_L_sn #H destruct
| <unwind_gen_A_sn #H destruct
| <unwind_gen_S_sn #H destruct
]
qed-.

lemma unwind_gen_inv_m_sn (q) (p) (f):
      (𝗺◗q) = ◆[f]p → ⊥.
#q #p @(path_ind_unwind … p) -p
[| #n | #n #l #p |*: #p ] [|*: #IH ] #f
[ <unwind_gen_empty #H destruct
| <unwind_gen_d_empty #H destruct
| <unwind_gen_d_lcons #H /2 width=2 by/
| <unwind_gen_m_sn #H /2 width=2 by/
| <unwind_gen_L_sn #H destruct
| <unwind_gen_A_sn #H destruct
| <unwind_gen_S_sn #H destruct
]
qed-.

lemma unwind_gen_inv_L_sn (q) (p) (f):
      (𝗟◗q) = ◆[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ◆[f]r2 & r1●𝗟◗r2 = p.
#q #p @(path_ind_unwind … p) -p
[| #n | #n #l #p |*: #p ] [|*: #IH ] #f
[ <unwind_gen_empty #H destruct
| <unwind_gen_d_empty #H destruct
| <unwind_gen_d_lcons #H
  elim (IH … H) -IH -H #r1 #r2 #Hr1 #Hq #Hp destruct
  /2 width=5 by ex3_2_intro/
| <unwind_gen_m_sn #H
  elim (IH … H) -IH -H #r1 #r2 #Hr1 #Hq #Hp destruct
  /2 width=5 by ex3_2_intro/
| <unwind_gen_L_sn #H destruct -IH
  /2 width=5 by ex3_2_intro/
| <unwind_gen_A_sn #H destruct
| <unwind_gen_S_sn #H destruct
]
qed-.

lemma unwind_gen_inv_A_sn (q) (p) (f):
      (𝗔◗q) = ◆[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ◆[f]r2 & r1●𝗔◗r2 = p.
#q #p @(path_ind_unwind … p) -p
[| #n | #n #l #p |*: #p ] [|*: #IH ] #f
[ <unwind_gen_empty #H destruct
| <unwind_gen_d_empty #H destruct
| <unwind_gen_d_lcons #H
  elim (IH … H) -IH -H #r1 #r2 #Hr1 #Hq #Hp destruct
  /2 width=5 by ex3_2_intro/
| <unwind_gen_m_sn #H
  elim (IH … H) -IH -H #r1 #r2 #Hr1 #Hq #Hp destruct
  /2 width=5 by ex3_2_intro/
| <unwind_gen_L_sn #H destruct
| <unwind_gen_A_sn #H destruct -IH
  /2 width=5 by ex3_2_intro/
| <unwind_gen_S_sn #H destruct
]
qed-.

lemma unwind_gen_inv_S_sn (q) (p) (f):
      (𝗦◗q) = ◆[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ◆[f]r2 & r1●𝗦◗r2 = p.
#q #p @(path_ind_unwind … p) -p
[| #n | #n #l #p |*: #p ] [|*: #IH ] #f
[ <unwind_gen_empty #H destruct
| <unwind_gen_d_empty #H destruct
| <unwind_gen_d_lcons #H
  elim (IH … H) -IH -H #r1 #r2 #Hr1 #Hq #Hp destruct
  /2 width=5 by ex3_2_intro/
| <unwind_gen_m_sn #H
  elim (IH … H) -IH -H #r1 #r2 #Hr1 #Hq #Hp destruct
  /2 width=5 by ex3_2_intro/| <unwind_gen_L_sn #H destruct
| <unwind_gen_A_sn #H destruct
| <unwind_gen_S_sn #H destruct -IH
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Inversions with proper condition for path ********************************)

lemma unwind_gen_inv_append_proper_dx (q2) (q1) (p) (f):
      q2 ϵ 𝐏 → q1●q2 = ◆[f]p →
      ∃∃p1,p2. ⊗p1 = q1 & ◆[f]p2 = q2 & p1●p2 = p.
#q2 #q1 elim q1 -q1
[ #p #f #Hq2 <list_append_empty_sn #H destruct
  /2 width=5 by ex3_2_intro/
| * [ #n1 ] #q1 #IH #p #f #Hq2 <list_append_lcons_sn #H
  [ elim (unwind_gen_inv_d_sn … H) -H #r1 #m1 #_ #_ #H0 #_ -IH
    elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 destruct
    elim Hq2 -Hq2 //
  | elim (unwind_gen_inv_m_sn … H)
  | elim (unwind_gen_inv_L_sn … H) -H #r1 #s1 #Hr1 #Hs1 #H0 destruct
    elim (IH … Hs1) -IH -Hs1 // -Hq2 #p1 #p2 #H1 #H2 #H3 destruct
    @(ex3_2_intro … (r1●𝗟◗p1)) //
    <structure_append <Hr1 -Hr1 //
  | elim (unwind_gen_inv_A_sn … H) -H #r1 #s1 #Hr1 #Hs1 #H0 destruct
    elim (IH … Hs1) -IH -Hs1 // -Hq2 #p1 #p2 #H1 #H2 #H3 destruct
    @(ex3_2_intro … (r1●𝗔◗p1)) //
    <structure_append <Hr1 -Hr1 //
  | elim (unwind_gen_inv_S_sn … H) -H #r1 #s1 #Hr1 #Hs1 #H0 destruct
    elim (IH … Hs1) -IH -Hs1 // -Hq2 #p1 #p2 #H1 #H2 #H3 destruct
    @(ex3_2_intro … (r1●𝗦◗p1)) //
    <structure_append <Hr1 -Hr1 //
  ]
]
qed-.

(* Inversions with inner condition for path *********************************)

lemma unwind_gen_inv_append_inner_sn (q1) (q2) (p) (f):
      q1 ϵ 𝐈 → q1●q2 = ◆[f]p →
      ∃∃p1,p2. ⊗p1 = q1 & ◆[f]p2 = q2 & p1●p2 = p.
#q1 @(list_ind_rcons … q1) -q1
[ #q2 #p #f #Hq1 <list_append_empty_sn #H destruct
  /2 width=5 by ex3_2_intro/
| #q1 * [ #n1 ] #_ #q2 #p #f #Hq2
  [ elim (pic_inv_d_dx … Hq2)
  | <list_append_rcons_sn #H0
    elim (unwind_gen_inv_append_proper_dx … H0) -H0 // #p1 #p2 #H1 #H2 #H3 destruct
    elim (unwind_gen_inv_m_sn … (sym_eq … H2))
  | <list_append_rcons_sn #H0
    elim (unwind_gen_inv_append_proper_dx … H0) -H0 // #p1 #p2 #H1 #H2 #H3 destruct
    elim (unwind_gen_inv_L_sn … (sym_eq … H2)) -H2 #r2 #s2 #Hr2 #Hs2 #H0 destruct
    @(ex3_2_intro … (p1●r2◖𝗟)) [1,3: // ]
    [ <structure_append <structure_L_dx <Hr2 -Hr2 //
    | <list_append_assoc <list_append_rcons_sn //
    ]
  | <list_append_rcons_sn #H0
    elim (unwind_gen_inv_append_proper_dx … H0) -H0 // #p1 #p2 #H1 #H2 #H3 destruct
    elim (unwind_gen_inv_A_sn … (sym_eq … H2)) -H2 #r2 #s2 #Hr2 #Hs2 #H0 destruct
    @(ex3_2_intro … (p1●r2◖𝗔)) [1,3: // ]
    [ <structure_append <structure_A_dx <Hr2 -Hr2 //
    | <list_append_assoc <list_append_rcons_sn //
    ]
  | <list_append_rcons_sn #H0
    elim (unwind_gen_inv_append_proper_dx … H0) -H0 // #p1 #p2 #H1 #H2 #H3 destruct
    elim (unwind_gen_inv_S_sn … (sym_eq … H2)) -H2 #r2 #s2 #Hr2 #Hs2 #H0 destruct
    @(ex3_2_intro … (p1●r2◖𝗦)) [1,3: // ]
    [ <structure_append <structure_S_dx <Hr2 -Hr2 //
    | <list_append_assoc <list_append_rcons_sn //
    ]
  ]
]
qed-.
