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
include "delayed_updating/notation/functions/class_i_0.ma".
include "ground/lib/subset.ma".
include "ground/generated/insert_eq_1.ma".

(* INNER CONDITION FOR PATH *************************************************)

inductive pic: predicate path ā
| pic_empty: (š) Ļµ pic
| pic_m_dx (p): pāšŗ Ļµ pic
| pic_L_dx (p): pāš Ļµ pic
| pic_A_dx (p): pāš Ļµ pic
| pic_S_dx (p): pāš¦ Ļµ pic
.

interpretation
  "inner condition (path)"
  'ClassI = (pic).

(* Basic inversions ********************************************************)

lemma pic_inv_d_dx (p) (k):
      pāš±k Ļµ š ā ā„.
#p #k @(insert_eq_1 ā¦ (pāš±k))
#q * -q [|*: #q ] #H0 destruct
qed-.

(* Constructions with path_lcons ********************************************)

lemma pic_m_sn (p):
      p Ļµ š ā šŗāp Ļµ š.
#p * -p //
qed.

lemma pic_L_sn (p):
      p Ļµ š ā šāp Ļµ š.
#p * -p //
qed.

lemma pic_A_sn (p):
      p Ļµ š ā šāp Ļµ š.
#p * -p //
qed.

lemma pic_S_sn (p):
      p Ļµ š ā š¦āp Ļµ š.
#p * -p //
qed.
