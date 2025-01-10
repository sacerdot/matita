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

include "explicit_updating/reduction/xbeta_flat.ma".
include "explicit_updating/reduction/xstep_term.ma".

(* X-REDUCTION FOR TERM *****************************************************)

(* Constructions with xbeta and xbeta1 and term_flat ************************)

lemma xstep_beta_flat:
      flattenable (xstep_term (𝛃′)) (xstep_term (𝛃ⓕ)).
#t1 #t2 #Ht elim Ht -t1 -t2
[ /3 width=1 by xbeta_flat, xstep_term_step/
| /2 width=1 by xstep_term_abst/
| /3 width=1 by xstep_term_side, term_flat_eq_repl/
| /3 width=1 by xstep_term_head, term_flat_eq_repl/
| /2 width=1 by xstep_term_lift/
]
qed.

(* Inversions with xbeta and xbeta1 and term_flat ***************************)

lemma xstep_beta1_false_inv_flat_sx_aux (u1) (u2):
      u1 ➡[𝛃ⓕ] u2 → ∀t1. ♭t1 = u1 →
      ∃∃t2. t1 ➡[𝛃′] t2 & ♭t2 ≐ u2.
#u1 #u2 #Hu elim Hu -u1 -u2
[ #u1 #u2 #Hu12 #t1 #Htu1
  elim (xbeta1_false_inv_flat_sx_aux … Hu12 Htu1) -u1 #t2 #Ht12 #Htu2
  /3 width=3 by xstep_term_step, ex2_intro/
| #b #u1 #u2 #_ #IH #x1 #Hx1
  elim (eq_inv_flat_abst … Hx1) -Hx1 #c #t1 #H1 #H2 #H3
  elim (IH … H2) -IH -H2 #t2 #Ht12 #H4 destruct
  /3 width=4 by xstep_term_abst, term_eq_abst, ex2_intro/
| #w1 #w2 #u1 #u2 #_ #Hu12 #IH #x1 #Hx1
  elim (eq_inv_flat_appl … Hx1) -Hx1 #v1 #t1 #H1 #H2 #H3
  elim (IH … H1) -IH -H1 #v2 #Hv12 #H4 destruct
  /3 width=5 by xstep_term_side, term_eq_appl, ex2_intro/
| #w1 #w2 #u1 #u2 #Hw12 #_ #IH #x1 #Hx1
  elim (eq_inv_flat_appl … Hx1) -Hx1 #v1 #t1 #H1 #H2 #H3
  elim (IH … H2) -IH -H2 #t2 #Ht12 #H4 destruct
  /3 width=5 by xstep_term_head, term_eq_appl, ex2_intro/
| #f1 #f2 #u1 #u2 #Hf12 #_ #IH #x1 #Hx1
  elim (eq_inv_flat_lift … Hx1) -Hx1 #t1 #H1 #H2
  elim (IH … H1) -IH -H1 #t2 #Ht12 #H3 destruct
  /3 width=5 by xstep_term_lift, term_eq_lift, ex2_intro/
]
qed-.
