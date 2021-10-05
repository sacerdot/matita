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

include "static_2/syntax/sh_lt.ma".
include "static_2/syntax/sd_d.ma".

(* SORT DEGREE **************************************************************)

(* Properties with sh_lt ****************************************************)

lemma deg_SO_gt (h): sh_lt h →
      ∀s1,s2. s1 < s2 → deg_SO h s1 s2 0.
#h #Hh #s1 #s2 #Hs12 @deg_SO_zero * normalize
[ #H destruct
  elim (nlt_inv_refl … Hs12)
| #n #H
  lapply (next_lt … Hh ((pr_next h)^n s2)) >H -H #H
  lapply (nlt_trans … H Hs12) -s1 #H1
  /3 width=5 by nlt_ge_false, nexts_le/ (* full auto too slow *)
]
qed.
