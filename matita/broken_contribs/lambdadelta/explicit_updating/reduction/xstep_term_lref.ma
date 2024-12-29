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

include "explicit_updating/syntax/term_lref.ma".
include "explicit_updating/reduction/xstep_term.ma".

(* X-REDUCTION FOR TERM *****************************************************)

(* Constructions with term_lref *********************************************)

lemma xstep_term_inv_lref_sx (R):
      replace_2 … term_eq term_eq R →
      (∀p,y. R (𝛏❨p❩) y → R (↑𝛏❨p❩) (↑y)) →
      ∀p,y. (𝛏❨p❩) ➡[R] y → R (𝛏❨p❩) y.
#R #H1R #H2R #p elim p -p
[ /2 width=1 by xstep_term_inv_unit_sx/
| #p #IH #y <term_lref_succ #Hy
  elim (xstep_term_inv_lift_sx … Hy) -Hy //
  * #f #t #Hf #Ht #H0 destruct
  lapply (H2R … (IH … Ht)) -H2R -IH -Ht #IH
  /4 width=7 by term_eq_lift, term_eq_sym/
]
qed-.
