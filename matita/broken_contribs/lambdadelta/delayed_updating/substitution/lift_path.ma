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

rec definition lift_path (f) (p) on p: path ≝
match p with
[ list_empty     ⇒ (𝐞)
| list_lcons l q ⇒ (lift_path f q)◖🠡[🠢[f]q]l
].

interpretation
  "lift (path)"
  'UpTriangleArrow f l = (lift_path f l).

(* Basic constructions ******************************************************)

lemma lift_path_empty (f):
      (𝐞) = 🠡[f]𝐞.
// qed.

lemma lift_path_rcons (f) (p) (l):
      (🠡[f]p)◖🠡[🠢[f]p]l = 🠡[f](p◖l).
// qed.

lemma lift_path_d_dx (f) (p) (k):
      (🠡[f]p)◖𝗱(🠢[f]p＠⧣❨k❩) = 🠡[f](p◖𝗱k).
// qed.

lemma lift_path_m_dx (f) (p):
      (🠡[f]p)◖𝗺 = 🠡[f](p◖𝗺).
// qed.

lemma lift_path_L_dx (f) (p):
      (🠡[f]p)◖𝗟 = 🠡[f](p◖𝗟).
// qed.

lemma lift_path_A_dx (f) (p):
      (🠡[f]p)◖𝗔 = 🠡[f](p◖𝗔).
// qed.

lemma lift_path_S_dx (f) (p):
      (🠡[f]p)◖𝗦 = 🠡[f](p◖𝗦).
// qed.

(* Constructions with path_append *******************************************)

lemma lift_path_append (f) (p) (q):
      (🠡[f]p)●(🠡[🠢[f]p]q) = 🠡[f](p●q).
#f #p #q elim q -q //
#l #q #IH
<lift_path_rcons <lift_path_rcons
<list_append_lcons_sn //
qed.

(* Constructions with path_lcons ********************************************)

lemma lift_path_lcons (f) (p) (l):
      (🠡[f]l)◗🠡[🠢[f]l]p = 🠡[f](l◗p).
#f #p #l
<lift_path_append //
qed.

lemma lift_path_d_sn (f) (p) (k:ℤ⁺):
      (𝗱(f＠⧣❨k❩)◗🠡[⇂*[k]f]p) = 🠡[f](𝗱k◗p).
// qed.

lemma lift_path_m_sn (f) (p):
      (𝗺◗🠡[f]p) = 🠡[f](𝗺◗p).
// qed.

lemma lift_path_L_sn (f) (p):
      (𝗟◗🠡[⫯f]p) = 🠡[f](𝗟◗p).
// qed.

lemma lift_path_A_sn (f) (p):
      (𝗔◗🠡[f]p) = 🠡[f](𝗔◗p).
// qed.

lemma lift_path_S_sn (f) (p):
      (𝗦◗🠡[f]p) = 🠡[f](𝗦◗p).
// qed.

(* Basic inversions *********************************************************)

lemma lift_path_inv_empty (f) (p):
      (𝐞) = 🠡[f]p → 𝐞 = p.
#f * // #p #l
<lift_path_rcons #H0 destruct
qed-.

lemma lift_path_inv_rcons (f) (p2) (q1) (l1):
      q1◖l1 = 🠡[f]p2 →
      ∃∃q2,l2. q1 = 🠡[f]q2 & l1 = 🠡[🠢[f]q2]l2 & q2◖l2 = p2.
#f * [| #l2 #q2 ] #q1 #l1
[ <lift_path_empty
| <lift_path_rcons
]
#H0 destruct
/2 width=5 by ex3_2_intro/
qed-.

(* Inversions with path_append **********************************************)

lemma lift_path_inv_append_sn (f) (q1) (r1) (p2):
      q1●r1 = 🠡[f]p2 →
      ∃∃q2,r2. q1 = 🠡[f]q2 & r1 = 🠡[🠢[f]q2]r2 & q2●r2 = p2.
#f #q1 #r1 elim r1 -r1 [| #l1 #r1 #IH ] #p2
[ <list_append_empty_sn #H0 destruct
  /2 width=5 by ex3_2_intro/
| <list_append_lcons_sn #H0
  elim (lift_path_inv_rcons … H0) -H0 #x2 #l2 #H0 #H1 #H2 destruct
  elim (IH … H0) -IH -H0 #q2 #r2 #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Main inversions **********************************************************)

theorem lift_path_inj (f) (p1) (p2):
        🠡[f]p1 = 🠡[f]p2 → p1 = p2.
#f #p1 elim p1 -p1 [| #l1 #q1 #IH ] #p2
[ <lift_path_empty #H0
  <(lift_path_inv_empty … H0) -H0 //
| <lift_path_rcons #H0
  elim (lift_path_inv_rcons … H0) -H0 #q2 #l2 #Hq
  <(IH … Hq) -IH -q2 #Hl #H0 destruct
  <(prelift_label_inj … Hl) -l2 //
]
qed-.
