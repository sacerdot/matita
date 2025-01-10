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

include "explicit_updating/syntax/unwind_eq.ma".
include "explicit_updating/notation/functions/phi_prime_0.ma".

(* φ-STEP FOR X-REDUCTION ***************************************************)

definition xphi: relation2 … ≝
           λx,y.
           ∃∃f,t. (𝛗f.t) ≐ x & ▼[f]t ≐ y.

interpretation
  "φ-step (x-reduction)"
  'PhiPrime = (xphi).

(* Basic constructions ******************************************************)

lemma xphi_step (f) (t) (x) (y):
      (𝛗f.t) ≐ x → ▼[f]t ≐ y →
      (𝛗′) x y.
/2 width=4 by ex2_2_intro/
qed.

(* Constructions with term_eq ***********************************************)

lemma xphi_eq_repl:
      replace_2 … term_eq term_eq (𝛗′).
#t1 #t2 * #f #t #Ht1 #Ht2 #u1 #Htu1 #u2 #Htu2
/3 width=6 by xphi_step, term_eq_trans/
qed-.

(* Basic inversions *********************************************************)

lemma xphi_inv_unit_sx (y):
      (𝛗′) (𝛏) y → ⊥.
#y * #f1 #t1 #H0
elim (term_eq_inv_lift_sx … H0) -H0 #f2 #t2 #_ #_ #H0 destruct
qed-.

lemma xphi_inv_abst_sx (b) (t) (y):
      (𝛗′) (𝛌b.t) y → ⊥.
#b #t #y * #f1 #t1 #H0
elim (term_eq_inv_lift_sx … H0) -H0 #f2 #t2 #_ #_ #H0 destruct
qed-.

lemma xphi_inv_appl_sx (v) (t) (y):
      (𝛗′) (＠v.t) y → ⊥.
#v #t #y * #f1 #t1 #H0
elim (term_eq_inv_lift_sx … H0) -H0 #f2 #t2 #_ #_ #H0 destruct
qed-.

lemma xphi_inv_lift_sx (f) (t) (y):
      (𝛗′) (𝛗f.t) y → ▼[f]t ≐ y.
#f #t #y * #f1 #t1 #H0
elim (term_eq_inv_lift_sx … H0) -H0 #f2 #t2 #Hf #Ht #H0 destruct
/3 width=3 by unwind_eq_repl, term_eq_canc_sx/
qed-.

(* Advanced destructions ****************************************************)

lemma xphi_des_eq_unwind_bi (f) (t1) (t2):
      (𝛗′) t1 t2 → ▼[f]t1 ≐ ▼[f]t2.
#g #t1 #t2 * #f #t #Ht1 #Ht2
lapply (unwind_eq_repl g g … Ht1) -Ht1 [ // ] #Ht1
lapply (unwind_eq_repl g g … Ht2) -Ht2 [ // ] #Ht2
@(term_eq_repl … Ht1 … Ht2) -t1 -t2
@(term_eq_canc_sx … (unwind_after …)) //
qed-.

(* Main destructions ********************************************************)

theorem xphi_conf (t1) (t2) (u1) (u2):
        (𝛗′) t1 u1 → (𝛗′) t2 u2 →
        t1 ≐ t2 → u1 ≐ u2.
#x1 #x2 #y1 #y2
* #f1 #t1 #Hx1 #Hy1
* #f2 #t2 #Hx2 #Hy2
#Hx12
lapply (term_eq_repl … (term_eq_sym … Hx1) … (term_eq_sym … Hx2)) // -Hx1 -Hx2 #H0
elim (term_eq_inv_lift_bi … H0) -H0 #Hf12 #Ht12
/3 width=5 by unwind_eq_repl, term_eq_repl/
qed-.
