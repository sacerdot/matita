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

lemma term_dbfr_inv_empty (t) (r):
      Ⓕ /𝐝𝐛𝐟{t} r ⊆ Ⓕ.
#t #r #s * #x #Hx #_
elim (subset_nin_inv_empty ?? Hx)
qed.

lemma term_dbfr_inv_single (t) (s) (r):
      (❴s❵ /𝐝𝐛𝐟{t} r) ⊆ (s /𝐝𝐛𝐟{t} r).
#t #s #r #p * #x #Hx #Hp
lapply (subset_in_inv_single ??? Hx) -Hx #H0 destruct //
qed.

(* Basic constructions ******************************************************)

lemma term_dbfr_mk (t) (u) (s) (r):
      s ϵ u → (s /𝐝𝐛𝐟{t} r) ⊆ (u /𝐝𝐛𝐟{t} r).
/2 width=3 by ex2_intro/
qed.

lemma term_dbfr_le_repl (t1) (t2) (u1) (u2) (r):
      t1 ⊆ t2 → u1 ⊆ u2 → (u1 /𝐝𝐛𝐟{t1} r) ⊆ (u2 /𝐝𝐛𝐟{t2} r).
#t1 #t2 #u1 #u2 #r #Ht12 #Hu12 #s * #x #Hx #Hs
lapply (path_dbfr_le_repl … Ht12 … Hs) -Ht12 -Hs #Hs
@(term_dbfr_mk … Hs) -Hs
/2 width=1 by/
qed.

lemma term_dbfr_nin (t) (u) (r):
      r ⧸ϵ u  → u ⊆ u /𝐝𝐛𝐟{t} r.
#t #u #r #Hr #s #Hs
/4 width=3 by term_dbfr_mk, path_dbfr_neq/
qed.
