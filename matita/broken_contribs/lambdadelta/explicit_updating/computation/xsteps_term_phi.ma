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

include "explicit_updating/reduction/xstep_term_phi.ma".
include "explicit_updating/computation/xsteps_term.ma".

(* X-COMPUTATION FOR TERM ***************************************************)

(* Destructions with xphi ***************************************************)

lemma xsteps_term_phi_des_eq_unwind_bi (f) (t1) (t2):
      t1 ➡*[𝛗′] t2 → ▼[f]t1 ≐ ▼[f]t2.
#f #t1 #t2 #Ht12 elim Ht12 -t2
[ /2 width=1 by subst_tapp_eq_repl/
| #t0 #t2 #_ #Ht02 #IH
  /3 width=3 by xstep_term_phi_des_eq_unwind_bi, term_eq_trans/
]
qed-.

(* Main destructions with xphi **********************************************)

theorem xsteps_term_phi_canc_dx (t0) (t1) (t2):
        t1 ➡*[𝛗′] t0 → t2 ➡*[𝛗′] t0 → ▼[𝐢]t1 ≐ ▼[𝐢]t2.
#t0 #t1 #t2 #Ht10 #Ht20
lapply (xsteps_term_phi_des_eq_unwind_bi (𝐢) … Ht10) -Ht10 #Ht10
lapply (xsteps_term_phi_des_eq_unwind_bi (𝐢) … Ht20) -Ht20 #Ht20
/2 width=3 by term_eq_canc_dx/
qed-.

theorem xsteps_term_phi_canc_sx (t0) (t1) (t2):
        t0 ➡*[𝛗′] t1 → t0 ➡*[𝛗′] t2 → ▼[𝐢]t1 ≐ ▼[𝐢]t2.
#t0 #t1 #t2 #Ht01 #Ht02
lapply (xsteps_term_phi_des_eq_unwind_bi (𝐢) … Ht01) -Ht01 #Ht01
lapply (xsteps_term_phi_des_eq_unwind_bi (𝐢) … Ht02) -Ht02 #Ht02
/2 width=3 by term_eq_canc_sx/
qed-.

(* Constructions with xphi **************************************************)

lemma xsteps_term_phi (f) (t):
      (𝛗f.t) ➡*[𝛗′] ▼[f]t.
/2 width=4 by xsteps_term_step/
qed.

lemma xsteps_term_phi_eq_trans (t) (t1) (t2):
      t1 ➡*[𝛗′] t → t ≐ t2 → t1 ➡*[𝛗′] t2.
/3 width=5 by xsteps_term_eq_trans, xphi_eq_repl/
qed-.

lemma xsteps_term_phi_lift_unwind (f) (t1) (t2):
      t1 ➡*[𝛗′] t2 → 𝛗f.t1 ➡*[𝛗′] ▼[f]t2.
#f #t1 #t2 #Ht12
lapply (xsteps_term_phi_des_eq_unwind_bi f … Ht12) -Ht12 #Ht12
@(xsteps_term_phi_eq_trans … Ht12) -Ht12 //
qed.

lemma xsteps_term_phi_unwind_id (t):
      t ➡*[𝛗′] ▼[𝐢]t.
#t elim t -t
[ >term_lref_unit <unwind_lref <fbr_dapp_id
  /2 width=1 by xsteps_term_refl/
| #b #t #IH
  @(xsteps_term_phi_eq_trans … (unwind_abst …))
  @xsteps_term_abst_bi
  @(xsteps_term_phi_eq_trans … IH) -IH
  /2 width=1 by unwind_eq_repl/
| #v #t #IHv #IHt
  <unwind_appl
  /2 width=1 by xsteps_term_appl_bi/
| #f #t #IH
  @(xsteps_term_phi_eq_trans … (unwind_lift …))
  >fbr_after_id_comm
  @(xsteps_term_phi_eq_trans … (term_eq_sym … (unwind_after …)))
  /2 width=1 by xsteps_term_phi_lift_unwind/
]
qed.

(* Main constructions with xphi *********************************************)

theorem xsteps_term_phi_div (t1) (t2):
        ▼[𝐢]t1 ≐ ▼[𝐢]t2 →
        ∃∃t0. t1 ➡*[𝛗′] t0 & t2 ➡*[𝛗′] t0.
#t1 #t2 #Ht12
lapply (xsteps_term_phi_unwind_id t1) #Ht1
lapply (xsteps_term_phi_unwind_id t2) #Ht2
lapply (xsteps_term_phi_eq_trans … Ht1 … Ht12) -Ht1 -Ht12 #Ht12
/2 width=3 by ex2_intro/
qed-.

theorem xsteps_term_phi_conf (t0) (t1) (t2):
        t0 ➡*[𝛗′] t1 → t0 ➡*[𝛗′] t2 →
        ∃∃t0. t1 ➡*[𝛗′] t0 & t2 ➡*[𝛗′] t0.
/3 width=3 by xsteps_term_phi_div, xsteps_term_phi_canc_sx/
qed-.
