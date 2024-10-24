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
include "explicit_updating/notation/relations/beta_prime_0.ma".

(* β-REDUCTION STEP *********************************************************)

(* Note: core of β' (Barendregt, The λ-Calculus, 11.1.3 ii) *)
inductive xbeta: relation2 … ≝
| xbeta_unwind (f) (t) (x) (y):
  (𝛗f.t) ≐ x → ▼[f]t ≐ y →
  xbeta x y
| xbeta_beta (b) (v) (t) (x) (y):
  ＠v.𝛌b.t ≐ x → ⬕[𝟎←v]t ≐ y →
  xbeta x y
.

interpretation
  "β-reduction step (term)"
  'BetaPrime = (xbeta).

(* Constructions with term_eq ***********************************************)

lemma xbeta_eq_repl:
      replace_2 … term_eq term_eq (𝛃′).
#t1 #t2 * -t1 -t2
[ #f #t #x1 #y1 #Hx1 #Hy1 #x2 #Hx12 #y2 #Hy12
  /3 width=6 by xbeta_unwind, term_eq_trans/
| #b #v #t #x1 #y1 #Hx1 #Hy1 #x2 #Hx12 #y2 #Hy12
  /3 width=7 by xbeta_beta, term_eq_trans/
]
qed-.
