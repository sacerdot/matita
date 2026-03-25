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

include "delayed_updating/reduction/dbf_dstep_eq.ma".
include "delayed_updating/computation/dbf_dsteps.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION IN A DEVELOPMENT ********************)

(* Constructions with subset_eq *********************************************)

lemma dbfdss_eq_canc_sx (t) (t2) (u) (u2):
      t Ꟈ➡*𝐝𝐛𝐟[u,u2] t2 →
      ∀t1,u1. t ⇔ t1 → u ⇔ u1 → t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2.
#t #t2 #u #u2 #H0 elim H0 -t -t2 -u -u2
[ #t #t2 #u #u2 #Ht2 #Hu2 #t1 #u1 #Ht1 #Hu1
  /3 width=3 by dbfdss_refl, subset_eq_canc_sx/
| #t #t2 #u #u2 #Htu2 #t1 #u1 #Ht1 #Hu1
  /3 width=5 by dbfdss_step, dbfds_eq_canc_sx/
| #t0 #t #t2 #u0 #u #u2 #_ #Htu02 #IH0 #_ #t1 #u1 #Ht1 #Hu1
  /3 width=4 by dbfdss_trans/
]
qed-.

lemma eq_dbfdss_trans (t) (t1) (t2) (u) (u1) (u2):
      t1 ⇔ t → u1 ⇔ u → t Ꟈ➡*𝐝𝐛𝐟[u,u2] t2 → t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2.
/3 width=5 by dbfdss_eq_canc_sx, subset_eq_sym/
qed-.

lemma dbfdss_eq_repl (t1) (t2) (u1) (u2) (v1) (v2) (w1) (w2):
      t1 ⇔ u1 → t2 ⇔ u2 → v1 ⇔ w1 → v2 ⇔ w2 →
      t1 Ꟈ➡*𝐝𝐛𝐟[v1,v2] t2 → u1 Ꟈ➡*𝐝𝐛𝐟[w1,w2] u2.
/3 width=5 by dbfdss_eq_canc_sx, dbfdss_eq_trans/
qed-.

(* Advanced constructions ***************************************************)

lemma dbfdss_empty (t1) (t2) (r):
      t1 ⇔ t2 → t1 Ꟈ➡*𝐝𝐛𝐟[Ⓕ /𝐝𝐛𝐟 r, Ⓕ] t2.
/3 width=1 by dbfdss_refl, subset_eq_sym/
qed.

lemma dbfdss_self (t1) (t2) (r):
      t1 ⇔ t2 → t1 Ꟈ➡*𝐝𝐛𝐟[r /𝐝𝐛𝐟 r, Ⓕ] t2.
/3 width=1 by dbfdss_refl, subset_eq_sym/
qed.

lemma dbfs_neq_dbfdss (t1) (t2) (s) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → s ⧸= r → p◖𝗦 ⧸≚ s →
      t1 ➡𝐝𝐛𝐟[s] t2 → t1 Ꟈ➡*𝐝𝐛𝐟[s /𝐝𝐛𝐟 r, Ⓕ] t2.
#t1 #t2 #s #r #p #b #q #n #Hr #Hnsr #Hns #Ht12
@(dbfdss_eq_canc_sx t1)
[3: // |4: @(path_dbfr_neq_eq … Hr) // | skip ]
/3 width=1 by dbfdss_step, dbfds_single/
qed.

lemma dbfs_neq_dbfdss_cx (t0) (t1) (t2) (s) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t0,p,b,q,n❩ → s ⧸= r → p◖𝗦 ⧸≚ s →
      t1 ➡𝐝𝐛𝐟[s] t2 → t1 Ꟈ➡*𝐝𝐛𝐟[s /𝐝𝐛𝐟 r, Ⓕ] t2.
/3 width=6 by pcxr_des_x, dbfs_neq_dbfdss/
qed.

(* Advanved inversions ******************************************************)

lemma dbfdss_inv_step_sx (t1) (t2) (u1) (u2):
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2 →
      ∨∨ ∧∧ t1 ⇔ t2 & u1 ⇔ u2
       | ∃∃t,u. t1 Ꟈ➡𝐝𝐛𝐟[u1,u] t & t Ꟈ➡*𝐝𝐛𝐟[u,u2] t2
.
#t1 #t2 #u1 #u2 #H0 elim H0 -t1 -t2 -u1 -u2
[ /3 width=1 by or_introl, conj/
| /4 width=5 by dbfdss_refl, ex2_2_intro, or_intror/
| #t0 #t1 #t2 #u0 #u1 #u2 #_ #Htu02 #IH10 #IH02
  elim IH10 -IH10 *
  [ #Ht10 #Hu10 elim IH02 -IH02 * -Htu02
    [ #Ht02 #Hu02
      /4 width=3 by subset_eq_trans, or_introl, conj/
    | #t #u #Htu0 #Htu2
      /4 width=8 by eq_dbfds_trans, ex2_2_intro, or_intror/
    ]
  | #t #u #Htu1 #Htu0 -IH02
    /4 width=7 by dbfdss_trans, ex2_2_intro, or_intror/
  ]
]
qed-.
