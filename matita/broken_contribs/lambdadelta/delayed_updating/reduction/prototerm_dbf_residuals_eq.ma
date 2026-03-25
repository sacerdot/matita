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

(* Constructions with subset_eq *********************************************)

lemma term_dbfr_eq_repl (u1) (u2) (r):
      u1 ⇔ u2 → (u1 /𝐝𝐛𝐟 r) ⇔ (u2 /𝐝𝐛𝐟 r).
#u1 #u2 #r * #Hu12 #Hu21
/3 width=3 by term_dbfr_le_repl, conj/
qed.

lemma term_dbfr_empty (r):
      Ⓕ ⇔ Ⓕ /𝐝𝐛𝐟 r.
#r
/3 width=2 by term_dbfr_inv_empty, subset_empty_le_sx, conj/
qed.

lemma term_dbfr_single (s) (r):
      (s /𝐝𝐛𝐟 r) ⇔ (❴s❵ /𝐝𝐛𝐟 r).
#s #r
/3 width=3 by term_dbfr_mk, term_dbfr_inv_single, conj/
qed.

lemma term_dbfr_refl (r):
      Ⓕ ⇔ (❴r❵ /𝐝𝐛𝐟 r).
#r
@(subset_eq_trans … (term_dbfr_single …)) //
qed.

(* Destructions with subset_eq **********************************************)

lemma term_eq_des_dbfr_bi_neq (u1) (u2) (r1) (r2):
      (∨∨ r1 ϵ u1 | r2 ϵ u2) →
      u1 /𝐝𝐛𝐟 r2 ⇔ u2 /𝐝𝐛𝐟 r1 → r1 = r2.
#u1 #u2 #r1 #r2 * #Hr * [ #Hu #_ | #_ #Hu @sym_eq ]
/2 width=4 by term_le_des_dbfr_bi_neq/
qed-.
