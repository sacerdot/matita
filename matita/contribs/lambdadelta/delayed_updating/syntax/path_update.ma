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
include "delayed_updating/notation/functions/hash_1.ma".

(* UPDATE COUNT FOR PATH ****************************************************)

rec definition update (p) on p: nat ≝
match p with
[ list_empty     ⇒ 𝟎
| list_lcons l q ⇒
  match l with
  [ label_d n ⇒ n + update q
  | label_m   ⇒ update q
  | label_L   ⇒ update q
  | label_A   ⇒ update q
  | label_S   ⇒ update q
  ]
].

interpretation
  "update count (path)"
  'Hash p = (update p).

(* Basic constructions ******************************************************)

lemma update_empty: 𝟎 = ⧣𝐞.
// qed.

lemma update_d_sn (q) (n): ninj n+⧣q = ⧣(𝗱n◗q).
// qed.

lemma update_m_sn (q): ⧣q = ⧣(𝗺◗q).
// qed.

lemma update_L_sn (q): ⧣q = ⧣(𝗟◗q).
// qed.

lemma update_A_sn (q): ⧣q = ⧣(𝗔◗q).
// qed.

lemma update_S_sn (q): ⧣q = ⧣(𝗦◗q).
// qed.

(* Main constructions *******************************************************)

theorem update_append (p1) (p2):
        (⧣p2+⧣p1) = ⧣(p1●p2).
#p1 elim p1 -p1 //
* [ #n ] #p1 #IH #p2 <list_append_lcons_sn
[ <update_d_sn <update_d_sn //
| <update_m_sn <update_m_sn //
| <update_L_sn <update_L_sn //
| <update_A_sn <update_A_sn //
| <update_S_sn <update_S_sn //
]
qed.

(* Constructions with list_rcons ********************************************)

lemma update_d_dx (p) (n):
      (⧣p)+(ninj n) = ⧣(p◖𝗱n).
// qed.

lemma update_m_dx (p):
      (⧣p) = ⧣(p◖𝗺).
// qed.

lemma update_L_dx (p):
      (⧣p) = ⧣(p◖𝗟).
// qed.

lemma update_A_dx (p):
      (⧣p) = ⧣(p◖𝗔).
// qed.

lemma update_S_dx (p):
      (⧣p) = ⧣(p◖𝗦).
// qed.
