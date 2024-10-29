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

include "explicit_updating/reduction/xstep_beta_flat.ma".
include "explicit_updating/computation/xsteps.ma".

(* X-COMPUTATION ************************************************************)

(* Constructions with xbeta and xbeta1 and term_flat ************************)

(* Source: Barendregt, The λ-Calculus, 11.1.6 ii *)
lemma xsteps_beta_flat:
      flattenable (xsteps (𝛃′)) (xsteps (𝛃ⓕ)).
#t1 #t2 #Ht elim Ht -t2
/3 width=3 by xsteps_refl, xsteps_dx, xstep_beta_flat, term_flat_eq_repl/
qed.

(* Inversions with xbeta and xbeta1 and term_flat ***************************)

(* Source: Barendregt, The λ-Calculus, 11.1.6 i *)
lemma xsteps_beta1_false_inv_flat_sx (t1) (u2):
      ♭t1 ➡*[𝛃ⓕ] u2 →
      ∃∃t2. t1 ➡*[𝛃′] t2 & ♭t2 ≐ u2.
#t1 #u2 #Hu elim Hu -u2
[ #u1 #Htu1
  /3 width=3 by xsteps_refl, ex2_intro/
| #u0 #u2 #_ #Hu02 * #t0 #Ht10 #Htu0
  lapply (eq_xstep_trans … Htu0 Hu02) -u0
  [ /2 width=5 by xbeta1_eq_repl/ ] #Hu02
  elim (xstep_beta1_false_inv_flat_sx_aux … Hu02) -Hu02
  [|*: // ] #t2 #Ht02 #Htu2
  /3 width=3 by xsteps_dx, ex2_intro/
]
qed.  
