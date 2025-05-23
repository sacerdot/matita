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

include "explicit_updating/syntax/term_eq.ma".
include "explicit_updating/notation/relations/black_rightarrow_3.ma".

(* X-REDUCTION FOR TERM *****************************************************)

(* Note: there exists one step *)
inductive xstep_term (R:relation2 …): relation2 … ≝
| xstep_term_step (t1) (t2):
  R t1 t2 → xstep_term R t1 t2
| xstep_term_abst (b) (t1) (t2):
  xstep_term R t1 t2 → xstep_term R (𝛌b.t1) (𝛌b.t2)
| xstep_term_side (v1) (v2) (t1) (t2):
  xstep_term R v1 v2 → t1 ≐ t2 → xstep_term R (＠v1.t1) (＠v2.t2)
| xstep_term_head (v1) (v2) (t1) (t2):
  v1 ≐ v2 → xstep_term R t1 t2 → xstep_term R (＠v1.t1) (＠v2.t2)
| xstep_term_lift (f1) (f2) (t1) (t2):
  f1 ≐ f2 → xstep_term R t1 t2 → xstep_term R (𝛗f1.t1) (𝛗f2.t2)
.

interpretation
  "x-reduction (term)"
  'BlackRightArrow t1 R t2 = (xstep_term R t1 t2).

(* Advanced constructions ***************************************************)

alias symbol "subseteq" (instance 1) = "2-relation inclusion".
alias symbol "subseteq" (instance 2) = "2-relation inclusion".
lemma xstep_term_subeq (R1) (R2):
      R1 ⊆ R2 → (xstep_term R1) ⊆ (xstep_term R2).
#R1 #R2 #HR #t1 #t2 #Ht elim Ht -t1 -t2
/3 width=1 by xstep_term_step, xstep_term_abst, xstep_term_side, xstep_term_head, xstep_term_lift/
qed.

(* Constructions with term_eq ***********************************************)

lemma xstep_term_eq_repl (R):
      replace_2 … term_eq term_eq R →
      replace_2 … term_eq term_eq (xstep_term R).
#R #HR #t1 #t2 #H0 elim H0 -t1 -t2
[ /3 width=5 by xstep_term_step/
| #b #t1 #u1 #_ #IH #y1 #H1 #y2 #H2
  elim (term_eq_inv_abst_sx … H1) -H1 #t2 #Ht #H0 destruct
  elim (term_eq_inv_abst_sx … H2) -H2 #u2 #Hu #H0 destruct
  /3 width=1 by xstep_term_abst/
| #v1 #w1 #t1 #u1 #_ #Htu1 #IHv #y1 #H1 #y2 #H2
  elim (term_eq_inv_appl_sx … H1) -H1 #v2 #t2 #Hv #Ht #H0 destruct
  elim (term_eq_inv_appl_sx … H2) -H2 #w2 #u2 #Hw #Hu #H0 destruct
  /3 width=5 by xstep_term_side, term_eq_repl/
| #v1 #w1 #t1 #u1 #Hvw11 #_ #IHt #y1 #H1 #y2 #H2
  elim (term_eq_inv_appl_sx … H1) -H1 #v2 #t2 #Hv #Ht #H0 destruct
  elim (term_eq_inv_appl_sx … H2) -H2 #w2 #u2 #Hw #Hu #H0 destruct
  /3 width=5 by xstep_term_head, term_eq_repl/
| #f1 #g1 #t1 #u1 #Hfg1 #_ #IHt #y1 #H1 #y2 #H2
  elim (term_eq_inv_lift_sx … H1) -H1 #f2 #t2 #Hf #Ht #H0 destruct
  elim (term_eq_inv_lift_sx … H2) -H2 #g2 #u2 #Hg #Hu #H0 destruct
  /3 width=5 by xstep_term_lift, fbr_eq_repl/
]
qed-.

lemma xstep_term_eq_trans (R) (t) (t1) (t2):
      replace_2 … term_eq term_eq R →
      t1 ➡[R] t → t ≐ t2 → t1 ➡[R] t2.
/2 width=5 by xstep_term_eq_repl/
qed-.

lemma eq_xstep_term_trans (R) (t) (t1) (t2):
      replace_2 … term_eq term_eq R →
      t1 ≐ t → t ➡[R] t2 → t1 ➡[R] t2.
/3 width=5 by xstep_term_eq_repl, term_eq_sym/
qed-.

(* Basic destructions *******************************************************)

lemma xstep_term_inv_unit_sx (R) (y):
      (𝛏) ➡[R] y → R (𝛏) y.
#R #y @(insert_eq_1 … (𝛏))
#x * -x -y
[ #t1 #t2 #Ht #H0 destruct //
| #b #t1 #t2 #_ #H0 destruct
| #v1 #v2 #t1 #t2 #_ #_ #H0 destruct
| #v1 #v2 #t1 #t2 #_ #_ #H0 destruct
| #f1 #f2 #t1 #t2 #_ #_ #H0 destruct
]
qed-.

lemma xstep_term_inv_abst_sx (R) (b) (t1) (y):
      (𝛌b.t1) ➡[R] y →
      ∨∨ R (𝛌b.t1) y
       | ∃∃t2. t1 ➡[R] t2 & 𝛌b.t2 = y.
#R #z #x1 #y @(insert_eq_1 … (𝛌z.x1))
#x * -x -y
[ #t1 #t2 #Ht #H0 destruct /2 width=1 by or_introl/
| #b #t1 #t2 #Ht #H0 destruct /3 width=3 by ex2_intro, or_intror/
| #v1 #v2 #t1 #t2 #_ #_ #H0 destruct
| #v1 #v2 #t1 #t2 #_ #_ #H0 destruct
| #f1 #f2 #t1 #t2 #_ #_ #H0 destruct
]
qed-.

lemma xstep_term_inv_appl_sx (R) (v1) (t1) (y):
      (＠v1.t1) ➡[R] y →
      ∨∨ R (＠v1.t1) y
       | ∃∃v2,t2. v1 ➡[R] v2 & t1 ≐ t2 & ＠v2.t2 = y
       | ∃∃v2,t2. v1 ≐ v2 & t1 ➡[R] t2 & ＠v2.t2 = y.
#R #z1 #x1 #y @(insert_eq_1 … (＠z1.x1))
#x * -x -y
[ #t1 #t2 #Ht #H0 destruct /2 width=1 by or3_intro0/
| #b #t1 #t2 #_ #H0 destruct
| #v1 #v2 #t1 #t2 #Hv #Ht #H0 destruct /3 width=5 by or3_intro1, ex3_2_intro/
| #v1 #v2 #t1 #t2 #Hv #Ht #H0 destruct /3 width=5 by or3_intro2, ex3_2_intro/
| #f1 #f2 #t1 #t2 #_ #_ #H0 destruct
]
qed-.

lemma xstep_term_inv_lift_sx (R) (f1) (t1) (y):
      (𝛗f1.t1) ➡[R] y →
      ∨∨ R (𝛗f1.t1) y
       | ∃∃f2,t2. f1 ≐ f2 & t1 ➡[R] t2 & 𝛗f2.t2 = y.
#R #z1 #x1 #y @(insert_eq_1 … (𝛗z1.x1))
#x * -x -y
[ #t1 #t2 #Ht #H0 destruct /2 width=1 by or_introl/
| #b #t1 #t2 #_ #H0 destruct
| #v1 #v2 #t1 #t2 #_ #_ #H0 destruct
| #v1 #v2 #t1 #t2 #_ #_ #H0 destruct
| #f1 #f2 #t1 #t2 #Hf #Ht #H0 destruct  /3 width=5 by ex3_2_intro, or_intror/
]
qed-.
