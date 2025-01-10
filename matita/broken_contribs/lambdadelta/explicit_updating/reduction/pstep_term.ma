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

include "explicit_updating/syntax/term_relations.ma".
include "explicit_updating/syntax/term_eq.ma".
include "explicit_updating/notation/relations/solidi_black_rightarrow_3.ma".

(* P-REDUCTION FOR TERM *****************************************************)

(* Note: there exists a subset of parallel steps *)
inductive pstep_term (R2:relation6 …): relation2 … ≝

| pstep_term_refl (t1) (t2):
  t1 ≐ t2 → pstep_term R2 t1 t2

| pstep_term_step_2 (v1) (v2) (t1) (t2) (x) (y):
  pstep_term R2 v1 v2 → pstep_term R2 t1 t2 → R2 v1 v2 t1 t2 x y -> pstep_term R2 x y

| pstep_term_abst (b) (t1) (t2):
  pstep_term R2 t1 t2 → pstep_term R2 (𝛌b.t1) (𝛌b.t2)

| pstep_term_appl (v1) (v2) (t1) (t2):
  pstep_term R2 v1 v2 → pstep_term R2 t1 t2 → pstep_term R2 (＠v1.t1) (＠v2.t2)

| pstep_term_lift (f1) (f2) (t1) (t2):
  f1 ≐ f2 → pstep_term R2 t1 t2 → pstep_term R2 (𝛗f1.t1) (𝛗f2.t2)
.

interpretation
  "p-reduction (term)"
  'SolidiBlackRightArrow t1 R2 t2 = (pstep_term R2 t1 t2).

(* Constructions with term_eq ***********************************************)

lemma pstep_term_eq_repl (R2):
      term_replace_6 term_eq R2 →
      replace_2 … term_eq term_eq (pstep_term R2).
#R2 #HR2 #t1 #t2 #H0 elim H0 -t1 -t2
[ #t1 #t2 #Ht12 #u1 #Htu1 #u2 #Htu2
  /3 width=5 by pstep_term_refl, term_eq_repl/
| #v1 #v2 #t1 #t2 #x1 #y1 #_ #_ #Hxy1 #IHv #IHt #x2 #Hx #y2 #Hy
  @(pstep_term_step_2 … (IHv …) (IHt …))
  [5,6,7,8: // |1,2,3,4: skip | @(HR2 … Hxy1) // ]
| #b #t1 #t2 #_ #IH #y1 #H1 #y2 #H2
  elim (term_eq_inv_abst_sx … H1) -H1 #u1 #Htu1 #H0 destruct
  elim (term_eq_inv_abst_sx … H2) -H2 #u2 #Htu2 #H0 destruct
  /3 width=1 by pstep_term_abst/
| #v1 #v2 #t1 #t2 #_ #_ #IHv #IHt #y1 #H1 #y2 #H2
  elim (term_eq_inv_appl_sx … H1) -H1 #w1 #u1 #Hvw1 #Htu1 #H0 destruct
  elim (term_eq_inv_appl_sx … H2) -H2 #w2 #u2 #Hvw2 #Htu2 #H0 destruct
  /3 width=1 by pstep_term_appl/
| #f1 #f2 #t1 #t2 #Hf12 #_ #IH #y1 #H1 #y2 #H2
  elim (term_eq_inv_lift_sx … H1) -H1 #g1 #u1 #Hfg1 #Htu1 #H0 destruct
  elim (term_eq_inv_lift_sx … H2) -H2 #g2 #u2 #Hfg2 #Htu2 #H0 destruct
  /3 width=5 by pstep_term_lift, fbr_eq_repl/
]
qed-.

lemma pstep_term_eq_trans (R2) (t) (t1) (t2):
      term_replace_6 term_eq R2 →
      t1 ⫽➡[R2] t → t ≐ t2 → t1 ⫽➡[R2] t2.
/2 width=5 by pstep_term_eq_repl/
qed-.

lemma eq_pstep_term_trans (R2) (t) (t1) (t2):
      term_replace_6 term_eq R2 →
      t1 ≐ t → t ⫽➡[R2] t2 → t1 ⫽➡[R2] t2.
/3 width=5 by pstep_term_eq_repl, term_eq_sym/
qed-.
