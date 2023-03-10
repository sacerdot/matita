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

include "delayed_updating/substitution/prelift_label.ma".
include "delayed_updating/substitution/lift_rmap.ma".

(* LIFT FOR PATH ************************************************************)

rec definition lift_path (f) (p) on p: path â
match p with
[ list_empty     â (ğ)
| list_lcons l q â (lift_path f q)âğ ¡[ğ ¢[f]q]l
].

interpretation
  "lift (path)"
  'UpTriangleArrow f l = (lift_path f l).

(* Basic constructions ******************************************************)

lemma lift_path_empty (f):
      (ğ) = ğ ¡[f]ğ.
// qed.

lemma lift_path_rcons (f) (p) (l):
      (ğ ¡[f]p)âğ ¡[ğ ¢[f]p]l = ğ ¡[f](pâl).
// qed.

lemma lift_path_d_dx (f) (p) (k):
      (ğ ¡[f]p)âğ±(ğ ¢[f]pï¼ â§£â¨kâ©) = ğ ¡[f](pâğ±k).
// qed.

lemma lift_path_m_dx (f) (p):
      (ğ ¡[f]p)âğº = ğ ¡[f](pâğº).
// qed.

lemma lift_path_L_dx (f) (p):
      (ğ ¡[f]p)âğ = ğ ¡[f](pâğ).
// qed.

lemma lift_path_A_dx (f) (p):
      (ğ ¡[f]p)âğ = ğ ¡[f](pâğ).
// qed.

lemma lift_path_S_dx (f) (p):
      (ğ ¡[f]p)âğ¦ = ğ ¡[f](pâğ¦).
// qed.

(* Constructions with path_append *******************************************)

lemma lift_path_append (f) (p) (q):
      (ğ ¡[f]p)â(ğ ¡[ğ ¢[f]p]q) = ğ ¡[f](pâq).
#f #p #q elim q -q //
#l #q #IH
<lift_path_rcons <lift_path_rcons
<list_append_lcons_sn //
qed.

(* Constructions with path_lcons ********************************************)

lemma lift_path_lcons (f) (p) (l):
      (ğ ¡[f]l)âğ ¡[ğ ¢[f]l]p = ğ ¡[f](lâp).
#f #p #l
<lift_path_append //
qed.

lemma lift_path_d_sn (f) (p) (k:pnat):
      (ğ±(fï¼ â§£â¨kâ©)âğ ¡[â*[k]f]p) = ğ ¡[f](ğ±kâp).
// qed.

lemma lift_path_m_sn (f) (p):
      (ğºâğ ¡[f]p) = ğ ¡[f](ğºâp).
// qed.

lemma lift_path_L_sn (f) (p):
      (ğâğ ¡[â«¯f]p) = ğ ¡[f](ğâp).
// qed.

lemma lift_path_A_sn (f) (p):
      (ğâğ ¡[f]p) = ğ ¡[f](ğâp).
// qed.

lemma lift_path_S_sn (f) (p):
      (ğ¦âğ ¡[f]p) = ğ ¡[f](ğ¦âp).
// qed.

(* Basic inversions *********************************************************)

lemma lift_path_inv_empty (f) (p):
      (ğ) = ğ ¡[f]p â ğ = p.
#f * // #p #l
<lift_path_rcons #H0 destruct
qed-.

lemma lift_path_inv_rcons (f) (p2) (q1) (l1):
      q1âl1 = ğ ¡[f]p2 â
      ââq2,l2. q1 = ğ ¡[f]q2 & l1 = ğ ¡[ğ ¢[f]q2]l2 & q2âl2 = p2.
#f * [| #l2 #q2 ] #q1 #l1
[ <lift_path_empty
| <lift_path_rcons
]
#H0 destruct
/2 width=5 by ex3_2_intro/
qed-.

(* Inversions with path_append **********************************************)

lemma lift_path_inv_append_sn (f) (q1) (r1) (p2):
      q1âr1 = ğ ¡[f]p2 â
      ââq2,r2. q1 = ğ ¡[f]q2 & r1 = ğ ¡[ğ ¢[f]q2]r2 & q2âr2 = p2.
#f #q1 #r1 elim r1 -r1 [| #l1 #r1 #IH ] #p2
[ <list_append_empty_sn #H0 destruct
  /2 width=5 by ex3_2_intro/
| <list_append_lcons_sn #H0
  elim (lift_path_inv_rcons â¦ H0) -H0 #x2 #l2 #H0 #H1 #H2 destruct
  elim (IH â¦ H0) -IH -H0 #q2 #r2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Main inversions **********************************************************)

theorem lift_path_inj (f) (p1) (p2):
        ğ ¡[f]p1 = ğ ¡[f]p2 â p1 = p2.
#f #p1 elim p1 -p1 [| #l1 #q1 #IH ] #p2
[ <lift_path_empty #H0
  <(lift_path_inv_empty â¦ H0) -H0 //
| <lift_path_rcons #H0
  elim (lift_path_inv_rcons â¦ H0) -H0 #q2 #l2 #Hq
  <(IH â¦ Hq) -IH -q2 #Hl #H0 destruct
  <(prelift_label_inj â¦ Hl) -l2 //
]
qed-.
