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

include "ground/relocation/fb/fbr_after_eq.ma".
include "explicit_updating/reduction/xphi.ma".
include "explicit_updating/reduction/xstep_term.ma".

(* X-REDUCTION FOR TERM *****************************************************)

(* Destructions with xphi ***************************************************)

lemma xstep_term_phi_des_eq_unwind_bi (t1) (t2):
      t1 ➡[𝛗′] t2 → ∀f. ▼[f]t1 ≐ ▼[f]t2.
#t1 #t2 #Ht12 elim Ht12 -t1 -t2
[ /2 width=1 by xphi_des_eq_unwind_bi/
| #b #t1 #t2 #_ #IH #g
  @(term_eq_trans … (unwind_abst …))
  @(term_eq_canc_sx … (unwind_abst …))
  /2 width=1 by term_eq_abst/
| #v1 #v2 #t1 #t2 #_ #Ht12 #IH #g
  <unwind_appl <unwind_appl
  /3 width=1 by unwind_eq_repl, term_eq_appl/
| #v1 #v2 #t1 #t2 #Hv12 #_ #IH #g
  <unwind_appl <unwind_appl
  /3 width=1 by unwind_eq_repl, term_eq_appl/
| #f1 #f2 #t1 #t2 #Hf12 #_ #IH #g
  @(term_eq_trans … (unwind_lift …))
  @(term_eq_canc_sx … (unwind_lift …))
  @(term_eq_trans … (unwind_eq_repl ? (g•f2) … t1 t1 …))
  /2 width=1 by fbr_after_eq_repl_bi/
]
qed-.

(* Constructions with xphi **************************************************)

lemma xstep_term_phi (f) (t):
      (𝛗f.t) ➡[𝛗′] ▼[f]t.
/3 width=4 by xphi_step, xstep_term_step/
qed.

lemma xstep_term_phi_eq_trans (t) (t1) (t2):
      t1 ➡[𝛗′] t → t ≐ t2 → t1 ➡[𝛗′] t2.
/3 width=5 by xstep_term_eq_trans, xphi_eq_repl/
qed-.

lemma xstep_term_phi_lift_unwind (f) (t1) (t2):
      t1 ➡[𝛗′] t2 → 𝛗f.t1 ➡[𝛗′] ▼[f]t2.
#f #t1 #t2 #Ht12
lapply (xstep_term_phi_des_eq_unwind_bi … Ht12 f) -Ht12 #Ht12
@(xstep_term_phi_eq_trans … Ht12) -Ht12 //
qed.
