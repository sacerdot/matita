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

include "delayed_updating/reduction/path_dbf_residuals_eq.ma".
include "delayed_updating/reduction/prototerm_dbf_residuals_le.ma".

(* RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ******************************)

(* Basic constructions ******************************************************)

lemma term_dbfr_eq_repl (t1) (t2) (u1) (u2) (r):
      t1 ⇔ t2 → u1 ⇔ u2 → (u1 /𝐝𝐛𝐟{t1} r) ⇔ (u2 /𝐝𝐛𝐟{t2} r).
#t1 #t2 #u1 #u2 #r * #Ht12 #Ht21 * #Hu12 #Hu21
/3 width=5 by term_dbfr_le_repl, conj/
qed.

lemma term_dbfr_empty (t) (r):
      Ⓕ ⇔ Ⓕ /𝐝𝐛𝐟{t} r.
#t #r
/3 width=3 by term_dbfr_inv_empty, subset_empty_le_sx, conj/
qed.

lemma term_dbfr_single (t) (s) (r):
      (s /𝐝𝐛𝐟{t} r) ⇔ (❴s❵ /𝐝𝐛𝐟{t} r).
#t #s #r
/3 width=3 by term_dbfr_mk, term_dbfr_inv_single, conj/
qed.

lemma term_dbfr_refl (t) (r):
      Ⓕ ⇔ (❴r❵ /𝐝𝐛𝐟{t} r).
#t #r
@(subset_eq_trans … (term_dbfr_single …)) //
qed.
