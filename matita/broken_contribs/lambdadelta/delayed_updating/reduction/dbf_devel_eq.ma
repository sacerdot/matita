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

include "delayed_updating/reduction/dbf_step_eq.ma".
include "delayed_updating/reduction/prototerm_dbf_residuals_eq.ma".
include "delayed_updating/reduction/dbf_devel.ma".

(* COMPLETE DEVELOPMENT FOR DELAYED BALANCED FOCUSED REDUCTION **************)

(* Constructions with subset_eq *********************************************)

lemma dbfd_eq_repl:
      ∀u,t1,t2. t1 ⫽➡𝐝𝐛𝐟[u] t2 →
      ∀v. u ⇔ v → ∀w1. t1 ⇔ w1 → ∀w2. t2 ⇔ w2 →
      w1 ⫽➡𝐝𝐛𝐟[v] w2.
#u #t1 #t2 #Ht12 elim Ht12 -t1 -t2 -u
[ #u #t1 #t2 #Hu #Ht12 #v * #_ #Huv #w1 #Htw1 #w2 #Htw2
  @dbfd_refl
  [ /2 width=5 by subset_le_trans/
  | /3 width=3 by subset_eq_canc_sn, subset_eq_trans/
  ]
| #u #r #t0 #t1 #t2 #Hr #Ht10 #_ #IH #v #Huv #w1 #Htw1 #w2 #Htw2
  @(dbfd_step … r t0)
  [ /2 width=3 by subset_in_eq_repl_fwd/
  | /2 width=3 by dbfs_eq_canc_sn/
  | /3 width=1 by term_dbfr_eq_repl/
  ]
]
qed-.

lemma dbfd_eq_trans (t) (t1) (t2) (u):
      t1 ⫽➡𝐝𝐛𝐟[u] t → t ⇔ t2 → t1 ⫽➡𝐝𝐛𝐟[u] t2.
/2 width=7 by dbfd_eq_repl/
qed-.

lemma dbfd_eq_canc_dx (t) (t1) (t2) (u):
      t1 ⫽➡𝐝𝐛𝐟[u] t → t2 ⇔ t → t1 ⫽➡𝐝𝐛𝐟[u] t2.
/3 width=3 by dbfd_eq_trans, subset_eq_sym/
qed-.

lemma dbfd_eq_canc_sn (t) (t1) (t2) (u):
      t ⇔ t1 → t ⫽➡𝐝𝐛𝐟[u] t2 → t1 ⫽➡𝐝𝐛𝐟[u] t2.
/2 width=7 by dbfd_eq_repl/
qed-.

lemma eq_dbfd_trans (t) (t1) (t2) (u):
      t1 ⇔ t → t ⫽➡𝐝𝐛𝐟[u] t2 → t1 ⫽➡𝐝𝐛𝐟[u] t2.
/3 width=3 by dbfd_eq_canc_sn, subset_eq_sym/
qed-.

lemma dbfd_empty (t1) (t2) (t) (r):
      t1 ⇔ t2 → t1 ⫽➡𝐝𝐛𝐟[Ⓕ /𝐝𝐛𝐟{t} r] t2.
/2 width=7 by dbfd_eq_repl/
qed.

lemma dbfd_self (t1) (t2) (t) (r):
      t1 ⇔ t2 → t1 ⫽➡𝐝𝐛𝐟[r /𝐝𝐛𝐟{t} r] t2.
/2 width=7 by dbfd_eq_repl/
qed.

lemma dbfd_single (t1) (t2) (t) (s) (r):
      t1 ⫽➡𝐝𝐛𝐟[s /𝐝𝐛𝐟{t} r] t2 → t1 ⫽➡𝐝𝐛𝐟[❴s❵ /𝐝𝐛𝐟{t} r] t2.
/3 width=7 by dbfd_eq_repl, term_dbfr_single/
qed.

lemma dbfs_dbfd (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → t1 ⫽➡𝐝𝐛𝐟[❴r❵] t2.
/4 width=5 by dbfd_single, dbfd_self, dbfd_step/
qed.
