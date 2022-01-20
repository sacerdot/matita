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

include "delayed_updating/substitution/lift_eq.ma".
include "delayed_updating/syntax/path_structure.ma".
include "delayed_updating/syntax/path_proper.ma".
include "ground/xoa/ex_4_2.ma".
include "ground/xoa/ex_3_2.ma".

(* LIFT FOR PATH ***********************************************************)

(* Basic constructions with structure **************************************)

lemma structure_lift (p) (f):
      ⊗p = ⊗↑[f]p.
#p @(path_ind_lift … p) -p // #p #IH #f
<lift_path_L_sn //
qed.

lemma lift_structure (p) (f):
      ⊗p = ↑[f]⊗p.
#p @(path_ind_lift … p) -p //
qed.

(* Destructions with structure **********************************************)

lemma lift_des_structure (q) (p) (f):
      ⊗q = ↑[f]p → ⊗q = ⊗p.
// qed-.

(* Constructions with proper condition for path *****************************)

lemma lift_append_proper_dx (p2) (p1) (f): Ꝕp2 →
      (⊗p1)●(↑[↑[p1]f]p2) = ↑[f](p1●p2).
#p2 #p1 @(path_ind_lift … p1) -p1 //
[ #n | #n #l #p1 |*: #p1 ] #IH #f #Hp2
[ elim (ppc_inv_lcons … Hp2) -Hp2 #l #q #H destruct //
| <lift_path_d_lcons_sn <IH //
| <lift_path_L_sn <IH //
| <lift_path_A_sn <IH //
| <lift_path_S_sn <IH //
]
qed-.

(* Advanced constructions with structure ************************************)

lemma lift_d_empty_dx (n) (p) (f):
      (⊗p)◖𝗱((↑[p]f)@❨n❩) = ↑[f](p◖𝗱n).
#n #p #f <lift_append_proper_dx // 
qed.

lemma lift_L_dx (p) (f):
      (⊗p)◖𝗟 = ↑[f](p◖𝗟).
#p #f <lift_append_proper_dx //
qed.

lemma lift_A_dx (p) (f):
      (⊗p)◖𝗔 = ↑[f](p◖𝗔).
#p #f <lift_append_proper_dx //
qed.

lemma lift_S_dx (p) (f):
      (⊗p)◖𝗦 = ↑[f](p◖𝗦).
#p #f <lift_append_proper_dx //
qed.

lemma lift_root (f) (p):
      ∃∃r. 𝐞 = ⊗r & ⊗p●r = ↑[f]p.
#f #p @(list_ind_rcons … p) -p
[ /2 width=3 by ex2_intro/
| #p * [ #n ] /2 width=3 by ex2_intro/
]
qed-.

(* Advanced inversions with proj_path ***************************************)

lemma lift_path_inv_d_sn (k) (q) (p) (f):
      (𝗱k◗q) = ↑[f]p →
      ∃∃r,h. 𝐞 = ⊗r & (↑[r]f)@❨h❩ = k & 𝐞 = q & r◖𝗱h = p.
#k #q #p @(path_ind_lift … p) -p
[| #n | #n #l #p |*: #p ] [|*: #IH ] #f
[ <lift_path_empty #H destruct
| <lift_path_d_empty_sn #H destruct -IH
  /2 width=5 by ex4_2_intro/
| <lift_path_d_lcons_sn #H
  elim (IH … H) -IH -H #r #h #Hr #Hh #Hq #Hp destruct
  /2 width=5 by ex4_2_intro/
| <lift_path_L_sn #H destruct
| <lift_path_A_sn #H destruct
| <lift_path_S_sn #H destruct
]
qed-.

lemma lift_path_inv_L_sn (q) (p) (f):
      (𝗟◗q) = ↑[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ↑[⫯↑[r1]f]r2 & r1●𝗟◗r2 = p.
#q #p @(path_ind_lift … p) -p
[| #n | #n #l #p |*: #p ] [|*: #IH ] #f
[ <lift_path_empty #H destruct
| <lift_path_d_empty_sn #H destruct
| <lift_path_d_lcons_sn #H
  elim (IH … H) -IH -H #r1 #r2 #Hr1 #Hq #Hp destruct
  /2 width=5 by ex3_2_intro/
| <lift_path_L_sn #H destruct -IH
  /2 width=5 by ex3_2_intro/
| <lift_path_A_sn #H destruct
| <lift_path_S_sn #H destruct
]
qed-.

lemma lift_path_inv_A_sn (q) (p) (f):
      (𝗔◗q) = ↑[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ↑[↑[r1]f]r2 & r1●𝗔◗r2 = p.
#q #p @(path_ind_lift … p) -p
[| #n | #n #l #p |*: #p ] [|*: #IH ] #f
[ <lift_path_empty #H destruct
| <lift_path_d_empty_sn #H destruct
| <lift_path_d_lcons_sn #H
  elim (IH … H) -IH -H #r1 #r2 #Hr1 #Hq #Hp destruct
  /2 width=5 by ex3_2_intro/
| <lift_path_L_sn #H destruct
| <lift_path_A_sn #H destruct -IH
  /2 width=5 by ex3_2_intro/
| <lift_path_S_sn #H destruct
]
qed-.

lemma lift_path_inv_S_sn (q) (p) (f):
      (𝗦◗q) = ↑[f]p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ↑[↑[r1]f]r2 & r1●𝗦◗r2 = p.
#q #p @(path_ind_lift … p) -p
[| #n | #n #l #p |*: #p ] [|*: #IH ] #f
[ <lift_path_empty #H destruct
| <lift_path_d_empty_sn #H destruct
| <lift_path_d_lcons_sn #H
  elim (IH … H) -IH -H #r1 #r2 #Hr1 #Hq #Hp destruct
  /2 width=5 by ex3_2_intro/
| <lift_path_L_sn #H destruct
| <lift_path_A_sn #H destruct
| <lift_path_S_sn #H destruct -IH
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Inversions with proper condition for path ********************************)

lemma lift_inv_append_proper_dx (q2) (q1) (p) (f): Ꝕq2 →
      q1●q2 = ↑[f]p →
      ∃∃p1,p2. ⊗p1 = q1 & ↑[↑[p1]f]p2 = q2 & p1●p2 = p.
#q2 #q1 elim q1 -q1
[ #p #f #Hq2 <list_append_empty_sn #H destruct
  /2 width=5 by ex3_2_intro/
| * [ #n1 ] #q1 #IH #p #f #Hq2 <list_append_lcons_sn #H
  [ elim (lift_path_inv_d_sn … H) -H #r1 #m1 #_ #_ #H0 #_ -IH
    elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 destruct
    elim Hq2 -Hq2 //
  | elim (lift_path_inv_L_sn … H) -H #r1 #s1 #Hr1 #Hs1 #H0 destruct
    elim (IH … Hs1) -IH -Hs1 // -Hq2 #p1 #p2 #H1 #H2 #H3 destruct
    @(ex3_2_intro … (r1●𝗟◗p1)) //
    <structure_append <Hr1 -Hr1 //
  | elim (lift_path_inv_A_sn … H) -H #r1 #s1 #Hr1 #Hs1 #H0 destruct
    elim (IH … Hs1) -IH -Hs1 // -Hq2 #p1 #p2 #H1 #H2 #H3 destruct
    @(ex3_2_intro … (r1●𝗔◗p1)) //
    <structure_append <Hr1 -Hr1 //
  | elim (lift_path_inv_S_sn … H) -H #r1 #s1 #Hr1 #Hs1 #H0 destruct
    elim (IH … Hs1) -IH -Hs1 // -Hq2 #p1 #p2 #H1 #H2 #H3 destruct
    @(ex3_2_intro … (r1●𝗦◗p1)) //
    <structure_append <Hr1 -Hr1 //
  ]
]
qed-.
