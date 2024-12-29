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

include "explicit_updating/reduction/xstep_term_lref.ma".
include "explicit_updating/computation/xsteps_term.ma".

(* X-COMPUTATION FOR TERM ***************************************************)

(* Inversions with term_lref ************************************************)

lemma xsteps_term_inv_lref_sx (R):
      replace_2 … term_eq term_eq R →
      (∀p,y. R (𝛏❨p❩) y → R (↑𝛏❨p❩) (↑y)) →
      ∀p,y. (𝛏p) ➡*[R] y →
      ∨∨ ∃∃y0. R (𝛏p) y0 & y0 ➡*[R] y
       | (𝛏p) ≐ y.
#R #H1R #H2R #p #y #H0 elim H0 -y
[ /2 width=1 by or_intror/
| #x #y #_ #Hxy *
  [ * #y0 #Hy0 #Hy0x
    /4 width=5 by xsteps_term_dx, ex2_intro, or_introl/
  | #H0
    lapply (eq_xstep_term_trans … H1R H0 Hxy) -x #Hxy
    lapply (xstep_term_inv_lref_sx … H1R H2R … Hxy) -Hxy #Hy
    /4 width=3 by xsteps_term_refl, ex2_intro, or_introl/
  ]
]
qed-.
