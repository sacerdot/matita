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
include "delayed_updating/notation/functions/circled_zero_1.ma".

(* CLEAR FOR PATH ***********************************************************)

rec definition path_clear (p) on p ≝
match p with
[ list_empty     ⇒ p
| list_lcons l q ⇒
   match l with
   [ label_d k ⇒ (path_clear q)◖𝗱(𝟎)
   | label_m   ⇒ (path_clear q)◖𝗺
   | label_L   ⇒ (path_clear q)◖𝗟
   | label_A   ⇒ (path_clear q)◖𝗔
   | label_S   ⇒ (path_clear q)◖𝗦
   ]
].

interpretation
  "clear (path)"
  'CircledZero p = (path_clear p).

(* Basic constructions ******************************************************)

lemma path_clear_empty:
      𝐞 = ⓪𝐞.
// qed.

lemma path_clear_d_dx (p) (k):
      (⓪p)◖𝗱(𝟎) = ⓪(p◖𝗱k).
// qed.

lemma path_clear_m_dx (p):
      (⓪p)◖𝗺 = ⓪(p◖𝗺).
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
#p #q elim q -q //
* [ #k ] #q #IH
<list_append_lcons_sn //
qed.

(* Constructions with path_lcons ********************************************)

lemma path_clear_d_sn (p) (k):
      (𝗱(𝟎)◗⓪p) = ⓪(𝗱k◗p).
#p #k <path_clear_append //
qed.

lemma path_clear_m_sn (p):
      (𝗺◗⓪p) = ⓪(𝗺◗p).
#p <path_clear_append //
qed.

lemma path_clear_L_sn (p):
      (𝗟◗⓪p) = ⓪(𝗟◗p).
#p <path_clear_append //
qed.

lemma path_clear_A_sn (p):
      (𝗔◗⓪p) = ⓪(𝗔◗p).
#p <path_clear_append //
qed.

lemma path_clear_S_sn (p):
      (𝗦◗⓪p) = ⓪(𝗦◗p).
#p <path_clear_append //
qed.
