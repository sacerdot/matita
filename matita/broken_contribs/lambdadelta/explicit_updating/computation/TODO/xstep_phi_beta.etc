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

include "ground/xoa/ex_3_1.ma".
include "explicit_updating/reduction/xbeta_valid.ma".
include "explicit_updating/reduction/xstep_phi.ma".

(* X-REDUCTION TO ♭-NORMAL FORM FOR TERM ************************************)

(* Constructions with xbeta *************************************************)

(* Source: Barendregt, The λ-Calculus, stated in 11.1.9 *)
lemma xstep_beta_valid_false (t0) (t1):
      t0 ➡[𝛃′] t1 → ⓕ ⊢ t0 →
      ∃∃t2. t2 ➡𝛟 t1 & ⓣ ⊢ t2 & ♭t2 = t0.
#t0 #t1 #Ht01 elim Ht01 -t0 -t1
[ #t0 #t1 #Ht01 #Ht0
  elim (xbeta_des_valid_false … Ht01 Ht0) -Ht01 -Ht0 #t2 #Ht21 #Ht1 #Ht2 #H0 destruct
  /4 width=4 by xstep_phi_fold, xstep_term_step, ex3_intro/
| #b #t0 #t1 #_ #IH #H0
  elim (term_valid_inv_abst … H0) -H0 #Ht0 #H0 destruct
  elim (IH Ht0) -IH -Ht0 #t2 #Ht21 #Ht2 #H0 destruct
  /3 width=4 by xstep_phi_abst, term_valid_abst, ex3_intro/
| #v0 #v1 #t0 #t1 #_ #Ht01 #IH #H0
  elim (term_valid_inv_appl_false … H0) -H0 #Hv0 #Ht0
  elim (IH Hv0) -IH -Hv0 #v2 #Hv21 #Hv2 #H0 destruct
  lapply (term_valid_inv_false_eq_flat_refl … Ht0) -Ht0 #Ht0
  /4 width=4 by xstep_phi_side, term_valid_eq_repl_fwd, term_valid_appl, ex3_intro/
| #v0 #v1 #t0 #t1 #Hv01 #_ #IH #H0
  elim (term_valid_inv_appl_false … H0) -H0 #Hv0 #Ht0
  elim (IH Ht0) -IH -Ht0 #t2 #Ht21 #Ht2 #H0 destruct
  lapply (term_valid_inv_false_eq_flat_refl … Hv0) -Hv0 #Hv0
  /4 width=4 by xstep_phi_head, term_valid_eq_repl_fwd, term_valid_appl, ex3_intro/
| #f0 #f1 #t0 #t1 #Hf01 #_ #IH #H0
  lapply (term_valid_inv_lift … H0) -H0 #Ht0
  elim (IH Ht0) -IH -Ht0 #t2 #Ht21 #Ht2 #H0 destruct
  /3 width=4 by xstep_phi_lift, term_valid_lift, ex3_intro/
]
qed-.
