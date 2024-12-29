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

(* φ-REDUCTION STEP *********************************************************)

inductive xphi: relation2 … ≝
| xphi_step (f) (t) (x) (y):
  (𝛗f.t) ≐ x → ▼[f]t ≐ y →
  xphi x y
.

interpretation
  "φ-reduction step (term)"
  'PhiPrime = (xphi).

(* Constructions with term_eq ***********************************************)

lemma xphi_eq_repl:
      replace_2 … term_eq term_eq (𝛗′).
#t1 #t2 *
#f #t #x1 #y1 #Hx1 #Hy1 #x2 #Hx12 #y2 #Hy12
/3 width=6 by xphi_step, term_eq_trans/
qed-.

(* Basic inversions *********************************************************)

lemma xphi_inv_unit_sx (y):
      (𝛗′) (𝛏) y → ⊥.
#y
@(insert_eq_1 … (𝛏)) #x
* -x -y #f1 #t1 #x #y #Hx #_ #H0 destruct
elim (term_eq_inv_lift_sx … Hx) -Hx #f2 #t2 #_ #_ #H0 destruct
qed-.

lemma xphi_inv_abst_sx (b) (t) (y):
      (𝛗′) (𝛌b.t) y → ⊥.
#b #t #y
@(insert_eq_1 … (𝛌b.t)) #x
* -x -y #f1 #t1 #x #y #Hx #_ #H0 destruct
elim (term_eq_inv_lift_sx … Hx) -Hx #f2 #t2 #_ #_ #H0 destruct
qed-.

lemma xphi_inv_appl_sx (v) (t) (y):
      (𝛗′) (＠v.t) y → ⊥.
#v #t #y
@(insert_eq_1 … (＠v.t)) #x
* -x -y #f1 #t1 #x #y #Hx #_ #H0 destruct
elim (term_eq_inv_lift_sx … Hx) -Hx #f2 #t2 #_ #_ #H0 destruct
qed-.

lemma xphi_inv_lift_sx (f) (t) (y):
      (𝛗′) (𝛗f.t) y → ▼[f]t ≐ y.
#f #t #y
@(insert_eq_1 … (𝛗f.t)) #x
* -x -y #f1 #t1 #x #y #Hx #Hy #H0 destruct
elim (term_eq_inv_lift_sx … Hx) -Hx #f2 #t2 #Hf #Ht #H0 destruct
/3 width=3 by unwind_eq_repl, term_eq_canc_sx/
qed-.

(* Advanced destructions ****************************************************)

lemma xphi_des_eq_unwind_bi (f) (t1) (t2):
      (𝛗′) t1 t2 → ▼[f]t1 ≐ ▼[f]t2.
#g #t1 #t2 * #f #t #x #y #Hx #Hy
lapply (unwind_eq_repl g g … Hx) -Hx [ // ] #Hx
lapply (unwind_eq_repl g g … Hy) -Hy [ // ] #Hy
@(term_eq_repl … Hx … Hy) -x -y
@(term_eq_canc_sx … (unwind_after …)) //
qed-.

(* Main destructions ********************************************************)

theorem xphi_conf (t1) (t2) (u1) (u2):
        (𝛗′) t1 u1 → (𝛗′) t2 u2 →
        t1 ≐ t2 → u1 ≐ u2.
#t1 #t2 #u1 #u2
* -t1 -u1 #f1 #t1 #x1 #y1 #Hx1 #Hy1
* -t2 -u2 #f2 #t2 #x2 #y2 #Hx2 #Hy2
#Hx12
lapply (term_eq_repl … (term_eq_sym … Hx1) … (term_eq_sym … Hx2)) // -x1 -x2 #H0
elim (term_eq_inv_lift_bi … H0) -H0 #Hf12 #Hu12
/3 width=5 by unwind_eq_repl, term_eq_repl/
qed-.
