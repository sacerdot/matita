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

include "ground/xoa/ex_3_2.ma".
include "ground/lib/list_map.ma".
include "delayed_updating/syntax/label_clear.ma".
include "delayed_updating/syntax/path.ma".

(* CLEAR FOR PATH ***********************************************************)

definition path_clear (p) ≝
           list_map … label_clear p
.

interpretation
  "clear (path)"
  'CircledZero p = (path_clear p).

(* Basic constructions ******************************************************)

lemma path_clear_unfold (p):
      list_map … label_clear p = ⓪p.
//
qed.

lemma path_clear_empty:
      (𝐞) = ⓪𝐞.
// qed.

lemma path_clear_rcons (p) (l):
      (⓪p)◖⓪l = ⓪(p◖l).
// qed.

lemma path_clear_d_dx (p) (k):
      (⓪p)◖𝗱(𝟎) = ⓪(p◖𝗱k).
// qed.

lemma path_clear_L_dx (p):
      (⓪p)◖𝗟 = ⓪(p◖𝗟).
// qed.

lemma path_clear_A_dx (p):
      (⓪p)◖𝗔 = ⓪(p◖𝗔).
// qed.

lemma path_clear_S_dx (p):
      (⓪p)◖𝗦 = ⓪(p◖𝗦).
// qed.

(* Main constructions *******************************************************)

theorem path_clear_idem (p):
        ⓪p = ⓪⓪p.
#p elim p -p //
* [ #k ] #p #IH //
<path_clear_d_dx <path_clear_d_dx //
qed.

theorem path_clear_append (p) (q):
        ⓪p●⓪q = ⓪(p●q).
//
qed.

(* Constructions with path_lcons ********************************************)

lemma path_clear_lcons (p) (l):
      (⓪l)◗⓪p = ⓪(l◗p).
//
qed.

lemma path_clear_d_sx (p) (k):
      (𝗱(𝟎)◗⓪p) = ⓪(𝗱k◗p).
#p #k <path_clear_append //
qed.

lemma path_clear_L_sx (p):
      (𝗟◗⓪p) = ⓪(𝗟◗p).
#p <path_clear_append //
qed.

lemma path_clear_A_sx (p):
      (𝗔◗⓪p) = ⓪(𝗔◗p).
#p <path_clear_append //
qed.

lemma path_clear_S_sx (p):
      (𝗦◗⓪p) = ⓪(𝗦◗p).
#p <path_clear_append //
qed.

(* Basic inversions *********************************************************)

lemma eq_inv_path_empty_clear (p):
      (𝐞) = ⓪p → (𝐞) = p.
* //
* [ #k ] #p
[ <path_clear_d_dx
| <path_clear_L_dx
| <path_clear_A_dx
| <path_clear_S_dx
]
#H0 destruct
qed-.

lemma eq_inv_path_d_dx_clear (x) (p) (k):
      p◖𝗱k = ⓪x →
      ∃∃r,n. p = ⓪r & k = 𝟎 & r◖𝗱n = x.
* [| * [ #n ] #x ] #p #k
[ <path_clear_empty
| <path_clear_d_dx
| <path_clear_L_dx
| <path_clear_A_dx
| <path_clear_S_dx
] #H0 destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma eq_inv_path_L_dx_clear (x) (p):
      p◖𝗟 = ⓪x →
      ∃∃r. p = ⓪r & r◖𝗟 = x.
* [| * [ #n ] #x ] #p
[ <path_clear_empty
| <path_clear_d_dx
| <path_clear_L_dx
| <path_clear_A_dx
| <path_clear_S_dx
] #H0 destruct
/2 width=3 by ex2_intro/
qed-.

lemma eq_inv_path_A_dx_clear (x) (p):
      p◖𝗔 = ⓪x →
      ∃∃r. p = ⓪r & r◖𝗔 = x.
* [| * [ #n ] #x ] #p
[ <path_clear_empty
| <path_clear_d_dx
| <path_clear_L_dx
| <path_clear_A_dx
| <path_clear_S_dx
] #H0 destruct
/2 width=3 by ex2_intro/
qed-.

lemma eq_inv_path_S_dx_clear (x) (p):
      p◖𝗦 = ⓪x →
      ∃∃r. p = ⓪r & r◖𝗦 = x.
* [| * [ #n ] #x ] #p
[ <path_clear_empty
| <path_clear_d_dx
| <path_clear_L_dx
| <path_clear_A_dx
| <path_clear_S_dx
] #H0 destruct
/2 width=3 by ex2_intro/
qed-.

(* main inversions **********************************************************)

theorem eq_inv_path_append_clear (p) (q) (x):
        p●q = ⓪x →
        ∃∃r,s. p = ⓪r & q = ⓪s & r●s = x.
#p #q elim q -q [| * [ #k ] #q #IH ] #x
[ <list_append_empty_sx #H0 destruct
  /2 width=5 by ex3_2_intro/
| <list_append_lcons_sx #H0
  elim (eq_inv_path_d_dx_clear … H0) -H0 #r0 #n #H0 #H1 #H2 destruct
  elim (IH … H0) -IH -H0 #r #s #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| <list_append_lcons_sx #H0
  elim (eq_inv_path_L_dx_clear … H0) -H0 #r0 #H0 #H1 destruct
  elim (IH … H0) -IH -H0 #r #s #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| <list_append_lcons_sx #H0
  elim (eq_inv_path_A_dx_clear … H0) -H0 #r0 #H0 #H1 destruct
  elim (IH … H0) -IH -H0 #r #s #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
| <list_append_lcons_sx #H0
  elim (eq_inv_path_S_dx_clear … H0) -H0 #r0 #H0 #H1 destruct
  elim (IH … H0) -IH -H0 #r #s #H1 #H2 #H3 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic inversions with path_lcons *****************************************)

lemma eq_inv_path_d_sx_clear (x) (q) (k):
      (𝗱k◗q) = ⓪x →
      ∃∃s,n. q = ⓪s & k = 𝟎 & 𝗱n◗s = x.
#x #q #k #H0
elim (eq_inv_path_append_clear … H0) -H0 #x0 #q0 #H0 #H1 #H2 destruct
elim (eq_inv_path_d_dx_clear … H0) -H0 #p0 #n #H0 #H1 #H2 destruct
lapply (eq_inv_path_empty_clear … H0) -H0 #H0 destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma eq_inv_path_L_sx_clear (x) (q):
      (𝗟◗q) = ⓪x →
      ∃∃s. q = ⓪s & 𝗟◗s = x.
#x #q #H0
elim (eq_inv_path_append_clear … H0) -H0 #x0 #q0 #H0 #H1 #H2 destruct
elim (eq_inv_path_L_dx_clear … H0) -H0 #p0 #H0 #H1 destruct
lapply (eq_inv_path_empty_clear … H0) -H0 #H0 destruct
/2 width=3 by ex2_intro/
qed-.

lemma eq_inv_path_A_sx_clear (x) (q):
      (𝗔◗q) = ⓪x →
      ∃∃s. q = ⓪s & 𝗔◗s = x.
#x #q #H0
elim (eq_inv_path_append_clear … H0) -H0 #x0 #q0 #H0 #H1 #H2 destruct
elim (eq_inv_path_A_dx_clear … H0) -H0 #p0 #H0 #H1 destruct
lapply (eq_inv_path_empty_clear … H0) -H0 #H0 destruct
/2 width=3 by ex2_intro/
qed-.

lemma eq_inv_path_S_sx_clear (x) (q):
      (𝗦◗q) = ⓪x →
      ∃∃s. q = ⓪s & 𝗦◗s = x.
#x #q #H0
elim (eq_inv_path_append_clear … H0) -H0 #x0 #q0 #H0 #H1 #H2 destruct
elim (eq_inv_path_S_dx_clear … H0) -H0 #p0 #H0 #H1 destruct
lapply (eq_inv_path_empty_clear … H0) -H0 #H0 destruct
/2 width=3 by ex2_intro/
qed-.
