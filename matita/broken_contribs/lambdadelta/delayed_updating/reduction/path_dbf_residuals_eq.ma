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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_listed_le.ma".
include "delayed_updating/reduction/path_dbf_residuals_le.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Constructions with subset_eq *********************************************)

lemma path_dbfr_eq_repl (t1) (t2) (s) (r):
      t1 ⇔ t2 → (s /𝐝𝐛𝐟{t1} r) ⇔ (s /𝐝𝐛𝐟{t2} r).
#t1 #t2 #s #r * #Ht12 #Ht21
/3 width=3 by path_dbfr_le_repl, conj/
qed.

lemma path_dbfr_refl (t) (r):
      Ⓕ ⇔ (r /𝐝𝐛𝐟{t} r).
/3 width=4 by path_dbfr_le_refl, subset_empty_le_sn, conj/
qed.
