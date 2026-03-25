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

include "delayed_updating/reduction/path_dbf_residuals_le.ma".
include "delayed_updating/reduction/prototerm_dbf_residuals.ma".

(* RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ******************************)

(* Inversions with subset_le ************************************************)

lemma term_dbfr_inv_empty (r):
      Ⓕ /𝐝𝐛𝐟 r ⊆ Ⓕ.
#r #s * #x #Hx #_
elim (subset_nin_inv_empty ?? Hx)
qed.

lemma term_dbfr_inv_single (s) (r):
      (❴s❵ /𝐝𝐛𝐟 r) ⊆ (s /𝐝𝐛𝐟 r).
#s #r #p * #x #Hx #Hp
lapply (subset_in_inv_single ??? Hx) -Hx #H0 destruct //
qed.

(* Basic constructions ******************************************************)

lemma term_dbfr_mk (u) (s) (r):
      s ϵ u → (s /𝐝𝐛𝐟 r) ⊆ (u /𝐝𝐛𝐟 r).
/2 width=3 by ex2_intro/
qed.

lemma term_dbfr_le_repl (u1) (u2) (r):
      u1 ⊆ u2 → (u1 /𝐝𝐛𝐟 r) ⊆ (u2 /𝐝𝐛𝐟 r).
#u1 #u2 #r #Hu12 #s * #x #Hx #Hs
/3 width=3 by term_dbfr_mk/
qed.

lemma term_dbfr_nin (u) (r):
      r ⧸ϵ u  → u ⊆ u /𝐝𝐛𝐟 r.
#u #r #Hr #s #Hs
/4 width=3 by term_dbfr_mk, path_dbfr_neq/
qed.

(* Negated constructions with subset_le *************************************)

lemma term_nle_dbfr_bi_neq (u1) (u2) (r1) (r2):
      r2 ϵ u2 → r2 ⧸= r1 → u2 /𝐝𝐛𝐟 r1 ⧸⊆ u1 /𝐝𝐛𝐟 r2.
#u1 #u2 #r1 #r2 #Hr2 #Hnr #Hu
lapply (Hu r2 ?) -Hu
[ /3 width=3 by term_dbfr_mk, path_dbfr_neq/
| /2 width=4 by term_dbfr_inv_refl_dx/
]
qed-.

(* Destructions with subset_le **********************************************)

lemma term_le_des_dbfr_bi_neq (u1) (u2) (r1) (r2):
      r2 ϵ u2 → u2 /𝐝𝐛𝐟 r1 ⊆ u1 /𝐝𝐛𝐟 r2 → r2 = r1.
#u1 #u2 #r1 #r2 #Hr2 #Hu
elim (eq_path_dec r2 r1) #Hnr destruct //
elim (term_nle_dbfr_bi_neq … Hr2 Hnr Hu)
qed-.
