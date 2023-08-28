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
include "delayed_updating/notation/functions/natural_1.ma".
include "ground/arith/int_plus_opp.ma".

(* DEPTH FOR PATH ***********************************************************)

rec definition width (p) on p: ℤ ≝
match p with
[ list_empty     ⇒ 𝟎
| list_lcons l q ⇒
  match l with
  [ label_d k ⇒ width q - k
  | label_m   ⇒ width q
  | label_L   ⇒ ↑(width q)
  | label_A   ⇒ width q
  | label_S   ⇒ width q
  ]
].

interpretation
  "width (path)"
  'Natural p = (width p).

(* Basic constructions ******************************************************)

lemma width_empty: 𝟎 = ♮𝐞.
// qed.

lemma width_d_dx (p) (k):
      ♮p-k = ♮(p◖𝗱k).
// qed.

lemma width_m_dx (p):
      ♮p = ♮(p◖𝗺).
// qed.

lemma width_L_dx (p):
      ↑♮p = ♮(p◖𝗟).
// qed.

lemma width_A_dx (p):
      ♮p = ♮(p◖𝗔).
// qed.

lemma width_S_dx (p):
      ♮p = ♮(p◖𝗦).
// qed.

(* Main constructions *******************************************************)

theorem width_append (p) (q):
        (♮p)+(♮q) = ♮(p●q).
#p #q elim q -q //
* [ #k ] #q #IH <list_append_lcons_sn
[ <width_d_dx <width_d_dx //
| <width_m_dx <width_m_dx //
| <width_L_dx <width_L_dx //
| <width_A_dx <width_A_dx //
| <width_S_dx <width_S_dx //
]
qed.

(* Constructions with path_lcons ********************************************)

lemma width_d_sn (p) (k):
      ♮p-k = ♮(𝗱k◗p).
#p #k <zplus_comm //
qed.

lemma width_m_sn (p):
      ♮p = ♮(𝗺◗p).
// qed.

lemma width_L_sn (p):
      ↑♮p = ♮(𝗟◗p).
// qed.

lemma width_A_sn (p):
      ♮p = ♮(𝗔◗p).
// qed.

lemma width_S_sn (p):
      ♮p = ♮(𝗦◗p).
// qed.
