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
include "explicit_updating/syntax/beta_eq.ma".
include "explicit_updating/notation/relations/beta_1.ma".

(* MARKED β-REDUCTION STEP **************************************************)

(* Note: core of β and ϕ (Barendregt, The λ-Calculus, 11.1.4) *)
inductive xbeta1 (b): relation2 … ≝
| xbeta1_unwind (f) (t) (x) (y):
  (𝛗f.t) ≐ x → ▼[f]t ≐ y →
  xbeta1 b x y
| xbeta1_beta (v) (t) (x) (y):
  ＠v.𝛌b.t ≐ x → ⬕[𝟎←v]t ≐ y →
  xbeta1 b x y
.

interpretation
  "marked β-reduction step (term)"
  'Beta b = (xbeta1 b).

(* Basic inversions *********************************************************)

lemma xbeta1_inv_abst_sx (c) (b) (t1) (x2):
      (𝛃c) (𝛌b.t1) x2 → ⊥.
#c #b #t1 #x2
@(insert_eq_1 … (𝛌b.t1)) #x1 * -x1 -x2
[ #f #t #x #y #Hx #_ #H0 destruct
  elim (term_eq_inv_lift_sx … Hx) -Hx #z #x #_ #_ #H0 destruct
| #v #t #x #y #Hx #_ #H0 destruct
  elim (term_eq_inv_appl_sx … Hx) -Hx #z #x #_ #_ #H0 destruct
]
qed-.

(* Constructions with term_eq ***********************************************)

lemma xbeta1_eq_repl (b):
      replace_2 … term_eq term_eq (𝛃b).
#b #t1 #t2 * -t1 -t2
[ #f #t #x1 #y1 #Hx1 #Hy1 #x2 #Hx12 #y2 #Hy12
  /3 width=6 by xbeta1_unwind, term_eq_trans/
| #v #t #x1 #y1 #Hx1 #Hy1 #x2 #Hx12 #y2 #Hy12
  /3 width=7 by xbeta1_beta, term_eq_trans/
]
qed-.
