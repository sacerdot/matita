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

include "delayed_updating/reduction/prototerm_reducible_le.ma".
include "delayed_updating/reduction/path_dbf_residuals.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Constructions with subset_le *********************************************)

lemma path_dbfr_le_repl (t1) (t2) (s) (r):
      t1 ⊆ t2 → (s /𝐝𝐛𝐟{t1} r) ⊆ (s /𝐝𝐛𝐟{t2} r).
#t1 #t2 #s #r #Ht12 #x * *
[ #Hnsr #H0 destruct
  /2 width=1 by path_dbfr_neq/
| #p #b #q #q0 #n #Hr #Hs #Hx destruct
  /3 width=6 by path_dbfr_side, xprc_le_repl/
]
qed.

lemma path_dbfr_neq_le (t) (s) (r):
      s ⧸= r → ❴s❵ ⊆ (s /𝐝𝐛𝐟{t} r).
#t #s #r #Hs #x #Hx
>(subset_in_inv_single ??? Hx) -x
/2 width=1 by path_dbfr_neq/
qed.

(* Inversions with subset_le ************************************************)

lemma path_dbfr_le_refl (t) (r):
      (r /𝐝𝐛𝐟{t} r) ⊆ Ⓕ.
#t #r #s #Hs
elim (path_dbfr_inv_refl … Hs)
qed.
