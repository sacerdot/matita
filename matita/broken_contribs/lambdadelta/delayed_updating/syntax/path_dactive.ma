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

(* DEACTIVATION FOR PATH ****************************************************)

rec definition pda (p) on p ≝
match p with
[ list_empty     ⇒ p
| list_lcons l q ⇒
   match l with
   [ label_d k ⇒ (pda q)◖𝗱(𝟎)
   | label_m   ⇒ (pda q)◖𝗺
   | label_L   ⇒ (pda q)◖𝗟
   | label_A   ⇒ (pda q)◖𝗔
   | label_S   ⇒ (pda q)◖𝗦
   ]
].

interpretation
  "deactivation (path)"
  'CircledZero p = (pda p).

(* Basic constructions ******************************************************)

lemma pda_empty:
      𝐞 = ⓪𝐞.
// qed.

lemma pda_d_dx (p) (k):
      (⓪p)◖𝗱(𝟎) = ⓪(p◖𝗱k).
// qed.

lemma pda_m_dx (p):
      (⓪p)◖𝗺 = ⓪(p◖𝗺).
// qed.

lemma pda_L_dx (p):
      (⓪p)◖𝗟 = ⓪(p◖𝗟).
// qed.

lemma pda_A_dx (p):
      (⓪p)◖𝗔 = ⓪(p◖𝗔).
// qed.

lemma pda_S_dx (p):
      (⓪p)◖𝗦 = ⓪(p◖𝗦).
// qed.

(* Main constructions *******************************************************)

theorem pda_idem (p):
        ⓪p = ⓪⓪p.
#p elim p -p //
* [ #k ] #p #IH //
<pda_d_dx <pda_d_dx //
qed.

theorem pda_append (p) (q):
        ⓪p●⓪q = ⓪(p●q).
#p #q elim q -q //
* [ #k ] #q #IH
<list_append_lcons_sn //
qed.

(* Constructions with path_lcons ********************************************)

lemma pda_d_sn (p) (k):
      (𝗱(𝟎)◗⓪p) = ⓪(𝗱k◗p).
#p #k <pda_append //
qed.

lemma pda_m_sn (p):
      (𝗺◗⓪p) = ⓪(𝗺◗p).
#p <pda_append //
qed.

lemma pda_L_sn (p):
      (𝗟◗⓪p) = ⓪(𝗟◗p).
#p <pda_append //
qed.

lemma pda_A_sn (p):
      (𝗔◗⓪p) = ⓪(𝗔◗p).
#p <pda_append //
qed.

lemma pda_S_sn (p):
      (𝗦◗⓪p) = ⓪(𝗦◗p).
#p <pda_append //
qed.
