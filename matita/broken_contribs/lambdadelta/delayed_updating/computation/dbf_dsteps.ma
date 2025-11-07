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

include "ground/generated/insert_eq_2.ma".
include "delayed_updating/reduction/dbf_dstep.ma".
include "delayed_updating/notation/relations/d_stroke_black_rightarrow_star_dbf_4.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION IN A DEVELOPMENT ********************)

inductive dbfdss: relation4 (𝕋) (𝒫❨ℙ❩) (𝕋) (𝒫❨ℙ❩) ≝
| dbfdss_refl (t1) (t2) (u1) (u2):
  t1 ⇔ t2 →  u1 ⇔ u2 → dbfdss t1 u1 t2 u2
| dbfdss_step (t1) (t2) (u1) (u2):
  t1 Ꟈ➡𝐝𝐛𝐟[u1,u2] t2 → dbfdss t1 u1 t2 u2
| dbfdss_trans (t) (t1) (t2) (u) (u1) (u2):
  dbfdss t1 u1 t u → dbfdss t u t2 u2 → dbfdss t1 u1 t2 u2
.

interpretation
  "balanced focused computation with delayed updating in a development (prototerm)"
  'DStrokeBlackRightArrowStarDBF t1 u1 u2 t2 = (dbfdss t1 u1 t2 u2).

(* Constructions with subset_eq *********************************************)

lemma dbfdss_eq_trans (t) (t1) (u) (u1):
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u] t →
      ∀t2,u2. t ⇔ t2 → u ⇔ u2 → t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2.
#t #t1 #u #u1 #H0 elim H0 -t -t1 -u -u1
[ #t1 #t #u1 #u #Ht1 #Hu1 #t2 #u2 #Ht2 #Hu2
  /3 width=3 by dbfdss_refl, subset_eq_trans/
| #t1 #t #u1 #u #Htu1 #t2 #u2 #Ht2 #Hu2
  /3 width=5 by dbfdss_step, dbfds_eq_trans/
| #t0 #t1 #t #u0 #u1 #u #Htu10 #_ #_ #IH0 #t2 #u2 #Ht2 #Hu2
  /3 width=4 by dbfdss_trans/
]
qed-.

lemma dbfdss_eq_canc_dx (t) (t1) (t2) (u) (u1) (u2):
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u] t → t2 ⇔ t → u2 ⇔ u → t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2.
/3 width=5 by dbfdss_eq_trans, subset_eq_sym/
qed-.

(* Basic constructions ******************************************************)

lemma dbfdss_step_sx (t) (t1) (t2) (u) (u1) (u2):
      t1 Ꟈ➡𝐝𝐛𝐟[u1,u] t → t Ꟈ➡*𝐝𝐛𝐟[u,u2] t2 →
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2.
/3 width=4 by dbfdss_step, dbfdss_trans/
qed.

lemma dbfdss_step_dx (t) (t1) (t2) (u) (u1) (u2):
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u] t → t Ꟈ➡𝐝𝐛𝐟[u,u2] t2 →
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2.
/3 width=4 by dbfdss_step, dbfdss_trans/
qed.

(* Advanved inversions ******************************************************)

lemma dbfdss_inv_step_dx (t1) (t2) (u1) (u2):
      t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2 →
      ∨∨ ∧∧ t1 ⇔ t2 & u1 ⇔ u2
       | ∃∃t,u. t1 Ꟈ➡*𝐝𝐛𝐟[u1,u] t & t Ꟈ➡𝐝𝐛𝐟[u,u2] t2
.
#t1 #t2 #u1 #u2 #H0 elim H0 -t1 -t2 -u1 -u2
[ /3 width=1 by or_introl, conj/
| /4 width=5 by dbfdss_refl, ex2_2_intro, or_intror/
| #t0 #t1 #t2 #u0 #u1 #u2 #Htu10 #_ #IH10 #IH02
  elim IH02 -IH02 *
  [ #Ht02 #Hu02 elim IH10 -IH10 * -Htu10
    [ #Ht10 #Hu10
      /4 width=3 by subset_eq_trans, or_introl, conj/
    | #t #u #Htu1 #Htu0
      /4 width=8 by dbfds_eq_trans, ex2_2_intro, or_intror/
    ]
  | #t #u #Htu0 #Htu02 -IH10
    /4 width=4 by dbfdss_trans, ex2_2_intro, or_intror/
  ]
]
qed-.

(* Advanced eliminators *****************************************************)

lemma dbfdss_ind_sx (t2) (u2) (Q:relation2 …):
      (∀t1,t2,u1,u2. t1 ⇔ t2 → u1 ⇔ u2 → Q t2 u2 → Q t1 u1) →
      (Q t2 u2) →
      (∀t,t1,u,u1. t1 Ꟈ➡𝐝𝐛𝐟[u1,u] t → t Ꟈ➡*𝐝𝐛𝐟[u,u2] t2 → Q t u → Q t1 u1) →
      ∀t1,u1. t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2 → Q t1 u1.
#t2 #u2 #Q #H1Q #H2Q #IH #t1 #u1
@(insert_eq_2 … t2 u2) #t0 #u0 #H10 elim H10 -t1 -t0 -u1 -u0
[ #t1 #t0 #u1 #u0 #Ht10 #Hu10 #H1 #H2 destruct -IH
  /2 width=5 by/
| #t1 #t0 #u1 #u0 #H10 #H1 #H2 destruct
  /3 width=6 by dbfdss_refl/
| #t #t1 #t0 #u #u1 #u0 #H1 #H0 #_
  generalize in match H0; -H0
  elim H1 -t1 -t -u1 -u -H2Q
  [ #t1 #t #u1 #u #Ht1 #Hu1 #_ #IH0 #H1 #H2 destruct -IH
    /3 width=5 by/
  | #t1 #t #u1 #u #H1 #H0 #IH0 #H2 #H3 destruct
    /3 width=5 by/
  | #t3 #t1 #t #u3 #u1 #u #_ #H3 #IH13 #IH3 #H0 #IH0 #H1 #H2 destruct -IH
    /4 width=4 by dbfdss_trans/
  ]
]
qed-.

lemma dbfdss_ind_dx (t1) (u1) (Q:relation2 …):
      (replace_2 … (subset_eq …) (subset_eq …) Q) →
      (Q t1 u1) →
      (∀t,t2,u,u2. t1 Ꟈ➡*𝐝𝐛𝐟[u1,u] t → t Ꟈ➡𝐝𝐛𝐟[u,u2] t2 → Q t u → Q t2 u2) →
      ∀t2,u2. t1 Ꟈ➡*𝐝𝐛𝐟[u1,u2] t2 → Q t2 u2.
#t1 #u1 #Q #H1Q #H2Q #IH #t2 #u2
@(insert_eq_2 … t1 u1) #t0 #u0 #H10 elim H10 -t2 -t0 -u2 -u0
[ #t0 #t2 #u0 #u2 #Ht02 #Hu02 #H1 #H2 destruct -IH
  /2 width=5 by/
| #t0 #t2 #u0 #u2 #H02 #H1 #H2 destruct
  /3 width=6 by dbfdss_refl/
| #t #t0 #t2 #u #u0 #u2 #H0 #H2 #IH0 #_
  generalize in match IH0; -IH0
  generalize in match H0; -H0
  elim H2 -t -t2 -u -u2 -H2Q
  [ #t #t2 #u #u2 #Ht2 #Hu2 #_ #IH0 #H1 #H2 destruct -IH
    /3 width=5 by/
  | #t #t2 #u #u2 #H2 #H0 #IH0 #H1 #H3 destruct
    /3 width=5 by/
  | #t3 #t #t2 #u3 #u #u2 #H3 #_ #IH3 #IH32 #H0 #IH0 #H1 #H2 destruct -IH
    /4 width=4 by dbfdss_trans/
  ]
]
qed-.
