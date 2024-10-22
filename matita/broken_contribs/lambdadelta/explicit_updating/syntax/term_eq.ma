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

include "ground/xoa/ex_3_2.ma".
include "ground/relocation/fb/fbr_eq.ma".
include "explicit_updating/syntax/term.ma".

(* α-EQUIVALENCE FOR TERM ***************************************************)

inductive term_eq: relation2 … ≝
| term_eq_lref (p):
  term_eq (𝛏p) (𝛏p)
| term_eq_abst (b) (t1) (t2):
  term_eq t1 t2 → term_eq (𝛌b.t1) (𝛌b.t2)
| term_eq_appl (v1) (v2) (t1) (t2):
  term_eq v1 v2 → term_eq t1 t2 → term_eq (＠v1.t1) (＠v2.t2)
| term_eq_lift (f1) (f2) (t1) (t2):
  f1 ≐ f2 → term_eq t1 t2 → term_eq (𝛗f1.t1) (𝛗f2.t2)
.

interpretation
  "α-equivalence (term)"
  'DotEq t1 t2 = (term_eq t1 t2).

(* Basic destructions *******************************************************)

lemma term_eq_inv_lref_sx (p) (x2):
      (𝛏p) ≐ x2 → 𝛏p = x2.
#p0 #x2
@(insert_eq_1 … (𝛏p0)) #x1 * -x1 -x2
[ #p #_ //
| #b #t1 #t2 #_ #H0 destruct
| #v1 #v2 #t1 #t2 #_ #_ #H0 destruct
| #f1 #f2 #t1 #t2 #_ #_ #H0 destruct
]
qed-.

lemma term_eq_inv_abst_sx (b) (t1) (x2):
      (𝛌b.t1) ≐ x2 → ∃∃t2. t1 ≐ t2 & 𝛌b.t2 = x2.
#b0 #t0 #x2
@(insert_eq_1 … (𝛌b0.t0)) #x1 * -x1 -x2
[ #p #H0 destruct
| #b #t1 #t2 #Ht #H0 destruct
  /2 width=3 by ex2_intro/
| #v1 #v2 #t1 #t2 #_ #_ #H0 destruct
| #f1 #f2 #t1 #t2 #_ #_ #H0 destruct
]
qed-.

lemma term_eq_inv_appl_sx (v1) (t1) (x2):
      (＠v1.t1) ≐ x2 → ∃∃v2,t2. v1 ≐ v2 & t1 ≐ t2 & ＠v2.t2 = x2.
#v0 #t0 #x2
@(insert_eq_1 … (＠v0.t0)) #x1 * -x1 -x2
[ #p #H0 destruct
| #b #t1 #t2 #Ht #H0 destruct
| #v1 #v2 #t1 #t2 #Hv #Ht #H0 destruct
  /2 width=5 by ex3_2_intro/
| #f1 #f2 #t1 #t2 #_ #_ #H0 destruct
]
qed-.

lemma term_eq_inv_lift_sx (f1) (t1) (x2):
      (𝛗f1.t1) ≐ x2 → ∃∃f2,t2. f1 ≐ f2 & t1 ≐ t2 & 𝛗f2.t2 = x2.
#f0 #t0 #x2
@(insert_eq_1 … (𝛗f0.t0)) #x1 * -x1 -x2
[ #p #H0 destruct
| #b #t1 #t2 #Ht #H0 destruct
| #v1 #v2 #t1 #t2 #_ #_ #H0 destruct
| #f1 #f2 #t1 #t2 #Hf #Ht #H0 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic constructions ******************************************************)

lemma term_eq_refl:
      reflexive … term_eq.
#t elim t -t
/2 width=1 by term_eq_lref, term_eq_abst, term_eq_appl, term_eq_lift/
qed.

lemma term_eq_sym:
      symmetric … term_eq.
#t1 #t2 #Ht elim Ht -t1 -t2
/3 width=1 by term_eq_lref, term_eq_abst, term_eq_appl, term_eq_lift, fbr_eq_sym/
qed-.

(* Main constructions *******************************************************)

theorem term_eq_trans:
        Transitive … term_eq.
#t1 #t #Ht1 elim Ht1 -t1 -t
[ //
| #b #t1 #t #_ #IH #x2 #Hx2
  elim (term_eq_inv_abst_sx … Hx2) -Hx2 #t2 #Ht2 #H0 destruct
  /3 width=1 by term_eq_abst/
| #v1 #v #t1 #t #_ #_ #IHv #IHt #x2 #Hx2
  elim (term_eq_inv_appl_sx … Hx2) -Hx2 #v2 #t2 #Hv2 #Ht2 #H0 destruct
  /3 width=1 by term_eq_appl/
| #f1 #f #t1 #t #Hf #_ #IHt #x2 #Hx2
  elim (term_eq_inv_lift_sx … Hx2) -Hx2 #f2 #t2 #Hf2 #Ht2 #H0 destruct
  /3 width=3 by term_eq_lift, fbr_eq_trans/
]
qed-.

theorem term_eq_canc_sx:
        left_cancellable … term_eq.
/3 width=3 by term_eq_trans, term_eq_sym/
qed-.

theorem term_eq_canc_dx:
        right_cancellable … term_eq.
/3 width=3 by term_eq_trans, term_eq_sym/
qed-.

theorem term_eq_repl:
        replace_2 … term_eq term_eq term_eq.
/3 width=5 by term_eq_trans, term_eq_sym/
qed-.
