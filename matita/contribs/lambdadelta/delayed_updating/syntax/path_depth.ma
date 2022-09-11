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
include "delayed_updating/notation/functions/flat_1.ma".
include "ground/arith/nat_plus.ma".

(* DEPTH FOR PATH ***********************************************************)

rec definition depth (p) on p: nat ≝
match p with
[ list_empty     ⇒ 𝟎
| list_lcons l q ⇒
  match l with
  [ label_d k ⇒ depth q
  | label_m   ⇒ depth q
  | label_L   ⇒ ↑(depth q)
  | label_A   ⇒ depth q
  | label_S   ⇒ depth q
  ]
].

interpretation
  "depth (path)"
  'Flat p = (depth p).

(* Basic constructions ******************************************************)

lemma depth_empty: 𝟎 = ♭𝐞.
// qed.

lemma depth_d_dx (p) (k):
      ♭p = ♭(p◖𝗱k).
// qed.

lemma depth_m_dx (p):
      ♭p = ♭(p◖𝗺).
// qed.

lemma depth_L_dx (p):
      ↑♭p = ♭(p◖𝗟).
// qed.

lemma depth_A_dx (p):
      ♭p = ♭(p◖𝗔).
// qed.

lemma depth_S_dx (p):
      ♭p = ♭(p◖𝗦).
// qed.

(* Main constructions *******************************************************)

theorem depth_append (p) (q):
        (♭p)+(♭q) = ♭(p●q).
#p #q elim q -q //
* [ #k ] #q #IH <list_append_lcons_sn
[ <depth_d_dx <depth_d_dx //
| <depth_m_dx <depth_m_dx //
| <depth_L_dx <depth_L_dx //
| <depth_A_dx <depth_A_dx //
| <depth_S_dx <depth_S_dx //
]
qed.

(* Constructions with path_lcons ********************************************)

lemma depth_d_sn (p) (k):
      ♭p = ♭(𝗱k◗p).
// qed.

lemma depth_m_sn (p):
      ♭p = ♭(𝗺◗p).
// qed.

lemma depth_L_sn (p):
      ↑♭p = ♭(𝗟◗p).
// qed.

lemma depth_A_sn (p):
      ♭p = ♭(𝗔◗p).
// qed.

lemma depth_S_sn (p):
      ♭p = ♭(𝗦◗p).
// qed.
