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

include "explicit_updating/syntax/term_valid_flat.ma".
include "explicit_updating/reduction/xbeta_beta1.ma".
include "explicit_updating/computation/xsteps_beta_flat.ma".
include "explicit_updating/computation/xsteps_phi.ma".

(* X-COMPUTATION TO ♭-NORMAL FORM FOR TERM **********************************)

(* Advanced inversions ******************************************************)

(* Source: Barendregt, The λ-Calculus, 11.1.8 *)
lemma xsteps_phi_inv_beta1_false (t1) (t2):
      t1 ➡*𝛟 t2 → ♭t1 ➡*[𝛃ⓕ] t2.
#t1 #t2 * #Ht12 #Ht2
<(term_valid_inv_false_eq_flat_refl … Ht2) -Ht2
/4 width=3 by xsteps_beta_flat, xsteps_term_subeq, xbeta_beta1/
qed-.
