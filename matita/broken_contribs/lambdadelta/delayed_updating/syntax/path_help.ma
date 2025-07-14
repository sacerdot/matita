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

(* PATH *********************************************************************)

(* Helper constructions *****************************************************)

lemma path_append_append_lcons (p) (q) (r) (l):
      p●(r◖l)●q = p●r●(l◗q).
// qed-.

lemma path_append_lcons_append (p) (q) (r) (l):
      (p◖l)●r●q = p●(l◗r)●q.
// qed-.

lemma path_append_pLbLq (p) (b1) (b2) (q):
      p●𝗟◗(b1●b2●𝗟◗q) = ((p●𝗟◗b1)●b2)●𝗟◗q.
// qed.

lemma path_append_pAbLq_1 (p) (b) (q):
      (p◖𝗔)●b●(𝗟◗q) = p●𝗔◗b●𝗟◗q.
//
qed-.

lemma path_append_pAbLq_2 (p1) (p2) (b1) (b2) (q) (l):
      (p2●p1●𝗔◗b1●b2●𝗟◗q)◖l = (p2●p1◖𝗔)●(b1●b2●𝗟◗q◖l).
// qed-.

lemma path_append_pAbLq_3 (p1) (p2) (b1) (b2) (q):
      p1●p2●𝗔◗b1●b2●𝗟◗q = (p1●p2◖𝗔)●((b1●b2)●𝗟◗q).
// qed-.

lemma path_append_pAbLq_4 (p1) (p2) (b1) (b2) (q):
      p1●p2●𝗔◗b1●b2●𝗟◗q = (p1●p2●𝗔◗b1●b2)●(𝗟◗q).
// qed-.

lemma path_append_pAbLq_5 (p) (b) (q):
      p●𝗔◗b●𝗟◗q = (p●𝗔◗b)●𝗟◗q.
// qed-.

lemma path_append_pAbLq_6 (p) (b) (q):
      (p●𝗔◗b)●𝗟◗q = p●𝗔◗b●𝗟◗q.
// qed-.

lemma path_append_pAbLq_7 (p) (b) (q):
      p●(𝗔◗b●𝗟◗q) = (p●𝗔◗b)●𝗟◗q.
// qed.

lemma path_append_pAbLq_8 (p1) (p2) (b) (q):
      (p1●p2)●𝗔◗b●𝗟◗q = p1●(p2◖𝗔)●b●𝗟◗q.
// qed.

lemma path_append_pAbLq_9 (p1) (p2) (b) (q) (l):
      (p1●p2●𝗔◗b●𝗟◗q)◖l = p1●(p2●(𝗔◗b●𝗟◗q◖l)).
// qed.

lemma path_append_pAbLq_10 (p) (b) (q) (q2) (l):
      (((p◖𝗔)●b◖𝗟)●q)●l◗q2 =
      p●𝗔◗b●𝗟◗q●l◗q2.
// qed.

lemma path_append_pAbLq_11 (p) (b) (q1) (q2):
      (p●𝗔◗b●𝗟◗q1)●q2 = p●𝗔◗b●𝗟◗q1●q2.
// qed.

lemma path_append_pAbLqAbLq_1 (p) (b1) (b2) (q1) (q):
      p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q =
      (p●𝗔◗b1●𝗟◗q1)●𝗔◗b2●𝗟◗q.
// qed.

lemma path_append_pAbLqAbLq_2 (p) (b1) (b2) (q1) (q) (q2) (l):
      p●𝗔◗b1●𝗟◗(q1●𝗔◗b2●𝗟◗q●l◗q2) =
      (p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q◖l)●q2.
// qed.

lemma path_append_pAbLqAbLq_3 (p) (b1) (b2) (q1) (q) (q2) (l1) (l2):
      (p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q)●(l1◗q2◖l2) =
      (p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q●l1◗q2)◖l2.
// qed.

lemma path_append_pAbLqAbLq_4 (p) (b1) (b2) (q1) (q2) (q3):
      (p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q2)●q3 = p●𝗔◗b1●𝗟◗q1●𝗔◗b2●𝗟◗q2●q3.
// qed.

(* Helper destructions ******************************************************)

lemma path_des_append_help_1 (p1) (p2) (q1) (q2) (l1) (l2):
      p2◖l2 = (p1◖l1)●q1 → p1◖l2 = (p2◖l1)●q2 →
      l1 = l2.
#p1 #p2 #q1 #q2 #l1 #l2 #Hq1 #Hq2
elim (eq_inv_list_lcons_append ????? Hq1) -Hq1 *
[ #_ #H1 -q1 destruct //
| #r #_ #H1 -q1 destruct
  elim (eq_inv_list_lcons_append ????? Hq2) -Hq2 *
  [ #_ #H0 -q2
    elim (eq_inv_list_lcons_bi ????? H0) -H0 #_
    >list_append_rcons_sn #H0
    lapply (eq_inv_list_append_dx_dx_refl … H0) -H0 #H0
    elim (eq_inv_list_empty_rcons ??? H0)
  | #q1 #_ -q2
    >list_append_lcons_sn <list_append_assoc >list_append_rcons_sn #H0
    lapply (eq_inv_list_append_dx_dx_refl … H0) -H0 #H0
    elim (eq_inv_list_empty_rcons ??? H0)
  ]
]
qed-.

lemma path_des_append_help_2 (p1) (p2) (q1) (q2) (l1) (l2):
      p2◖l2 = (p1◖l1)●q1 → p2◖l1 = (p1◖l2)●q2 →
      l1 = l2.
#p1 #p2 #q1 #q2 #l1 #l2 #Hq1 #Hq2
elim (eq_inv_list_lcons_append ????? Hq1) -Hq1 *
[ #_ #H1 -q1 destruct //
| #r #_ #H1 -q1 destruct
  elim (eq_inv_list_lcons_append ????? Hq2) -Hq2 *
  [ #_ #H0 -q2
    elim (eq_inv_list_lcons_bi ????? H0) -H0 #H0 #_ destruct //
  | #q1 #_ -q2 #H0
    elim (eq_inv_list_append_bi … H0) -H0 * #q2 #H1q #H2q
    [ -H1q
      elim (eq_inv_list_lcons_append ????? H2q) -H2q *
      [ #_ -q2 #H0 destruct //
      | #r0 #_ -q1 -q2
        >list_append_rcons_sn #H0
        lapply (eq_inv_list_append_dx_dx_refl … H0) -H0 #H0
        elim (eq_inv_list_empty_rcons ??? H0)
      ]
    | -q1
      elim (eq_inv_list_lcons_append ????? H1q) -H1q *
      [ #_ -q2 #H0 destruct //
      | #r0 #_ -q2
        >list_append_rcons_sn #H0
        lapply (eq_inv_list_append_dx_dx_refl … H0) -H0 #H0
        elim (eq_inv_list_empty_rcons ??? H0)
      ]
    ]
  ]
]
qed-.
