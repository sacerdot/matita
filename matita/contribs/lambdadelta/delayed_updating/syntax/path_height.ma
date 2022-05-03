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

include "ground/arith/nat_plus.ma".
include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/sharp_1.ma".

(* HEIGHT FOR PATH **********************************************************)

rec definition height (p) on p: nat ≝
match p with
[ list_empty     ⇒ 𝟎
| list_lcons l q ⇒
  match l with
  [ label_d n ⇒ n + height q
  | label_m   ⇒ height q
  | label_L   ⇒ height q
  | label_A   ⇒ height q
  | label_S   ⇒ height q
  ]
].

interpretation
  "height (path)"
  'Sharp p = (height p).

(* Basic constructions ******************************************************)

lemma height_empty: 𝟎 = ♯𝐞.
// qed.

lemma height_d_sn (q) (n): ninj n+♯q = ♯(𝗱n◗q).
// qed.

lemma height_m_sn (q): ♯q = ♯(𝗺◗q).
// qed.

lemma height_L_sn (q): ♯q = ♯(𝗟◗q).
// qed.

lemma height_A_sn (q): ♯q = ♯(𝗔◗q).
// qed.

lemma height_S_sn (q): ♯q = ♯(𝗦◗q).
// qed.

(* Main constructions *******************************************************)

theorem height_append (p1) (p2):
        (♯p2+♯p1) = ♯(p1●p2).
#p1 elim p1 -p1 //
* [ #n ] #p1 #IH #p2 <list_append_lcons_sn
[ <height_d_sn <height_d_sn //
| <height_m_sn <height_m_sn //
| <height_L_sn <height_L_sn //
| <height_A_sn <height_A_sn //
| <height_S_sn <height_S_sn //
]
qed.

(* Constructions with list_rcons ********************************************)

lemma height_d_dx (p) (n):
      (♯p)+(ninj n) = ♯(p◖𝗱n).
// qed.

lemma height_m_dx (p):
      (♯p) = ♯(p◖𝗺).
// qed.

lemma height_L_dx (p):
      (♯p) = ♯(p◖𝗟).
// qed.

lemma height_A_dx (p):
      (♯p) = ♯(p◖𝗔).
// qed.

lemma height_S_dx (p):
      (♯p) = ♯(p◖𝗦).
// qed.
