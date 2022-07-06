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
include "delayed_updating/notation/functions/circled_times_1.ma".

(* STRUCTURE FOR PATH *******************************************************)

rec definition structure (p) on p ≝
match p with
[ list_empty     ⇒ 𝐞
| list_lcons l q ⇒
   match l with
   [ label_d k ⇒ structure q
   | label_m   ⇒ structure q
   | label_L   ⇒ (structure q)◖𝗟
   | label_A   ⇒ (structure q)◖𝗔
   | label_S   ⇒ (structure q)◖𝗦
   ]
].

interpretation
  "structure (path)"
  'CircledTimes p = (structure p).

(* Basic constructions ******************************************************)

lemma structure_empty:
      𝐞 = ⊗𝐞.
// qed.

lemma structure_d_dx (p) (k):
      ⊗p = ⊗(p◖𝗱k).
// qed.

lemma structure_m_dx (p):
      ⊗p = ⊗(p◖𝗺).
// qed.

lemma structure_L_dx (p):
      (⊗p)◖𝗟 = ⊗(p◖𝗟).
// qed.

lemma structure_A_dx (p):
      (⊗p)◖𝗔 = ⊗(p◖𝗔).
// qed.

lemma structure_S_dx (p):
      (⊗p)◖𝗦 = ⊗(p◖𝗦).
// qed.

(* Main constructions *******************************************************)

theorem structure_idem (p):
        ⊗p = ⊗⊗p.
#p elim p -p [| * [ #k ] #p #IH ] //
qed.

theorem structure_append (p) (q):
        ⊗p●⊗q = ⊗(p●q).
#p #q elim q -q [| * [ #k ] #q #IH ]
[||*: <list_append_lcons_sn ] //
qed.

(* Constructions with path_lcons ********************************************)

lemma structure_d_sn (p) (k):
      ⊗p = ⊗(𝗱k◗p).
#p #n <structure_append //
qed.

lemma structure_m_sn (p):
      ⊗p = ⊗(𝗺◗p).
#p <structure_append //
qed.

lemma structure_L_sn (p):
      (𝗟◗⊗p) = ⊗(𝗟◗p).
#p <structure_append //
qed.

lemma structure_A_sn (p):
      (𝗔◗⊗p) = ⊗(𝗔◗p).
#p <structure_append //
qed.

lemma structure_S_sn (p):
      (𝗦◗⊗p) = ⊗(𝗦◗p).
#p <structure_append //
qed.
