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

include "basic_2/rt_computation/lprs_tc.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Eliminators with r-transition for full local environments ****************)

(* Basic_2A1: was: lprs_ind_dx *)
lemma lprs_ind_sn (h) (G) (L2):
      ∀Q:predicate lenv. Q L2 →
      (∀L1,L. ❪G,L1❫ ⊢ ➡[h,0] L → ❪G,L❫ ⊢ ➡*[h,0] L2 → Q L → Q L1) →
      ∀L1. ❪G,L1❫ ⊢ ➡*[h,0] L2 → Q L1.
/4 width=8 by lprs_inv_CTC, lprs_CTC, lpr_cprs_trans, cpr_refl, lex_CTC_ind_sn/ qed-.

(* Basic_2A1: was: lprs_ind *)
lemma lprs_ind_dx (h) (G) (L1):
      ∀Q:predicate lenv. Q L1 →
      (∀L,L2. ❪G,L1❫ ⊢ ➡*[h,0] L → ❪G,L❫ ⊢ ➡[h,0] L2 → Q L → Q L2) →
      ∀L2. ❪G,L1❫ ⊢ ➡*[h,0] L2 → Q L2.
/4 width=8 by lprs_inv_CTC, lprs_CTC, lpr_cprs_trans, cpr_refl, lex_CTC_ind_dx/ qed-.

(* Properties with unbound rt-transition for full local environments ********)

lemma lpr_lprs (h) (G):
      ∀L1,L2. ❪G,L1❫ ⊢ ➡[h,0] L2 → ❪G,L1❫ ⊢ ➡*[h,0] L2.
/4 width=3 by lprs_CTC, lpr_cprs_trans, lex_CTC_inj/ qed.

(* Basic_2A1: was: lprs_strap2 *)
lemma lprs_step_sn (h) (G):
      ∀L1,L. ❪G,L1❫ ⊢ ➡[h,0] L →
      ∀L2.❪G,L❫ ⊢ ➡*[h,0] L2 → ❪G,L1❫ ⊢ ➡*[h,0] L2.
/4 width=3 by lprs_inv_CTC, lprs_CTC, lpr_cprs_trans, lex_CTC_step_sn/ qed-.

(* Basic_2A1: was: lpxs_strap1 *)
lemma lprs_step_dx (h) (G):
      ∀L1,L. ❪G,L1❫ ⊢ ➡*[h,0] L →
      ∀L2. ❪G,L❫ ⊢ ➡[h,0] L2 → ❪G,L1❫ ⊢ ➡*[h,0] L2.
/4 width=3 by lprs_inv_CTC, lprs_CTC, lpr_cprs_trans, lex_CTC_step_dx/ qed-.

lemma lprs_strip (h) (G):
      confluent2 … (lprs h 0 G) (lpr h 0 G).
#h #G #L0 #L1 #HL01 #L2 #HL02
elim (TC_strip1 … L1 ?? HL02) -HL02
[ /3 width=3 by lprs_TC, ex2_intro/ | skip
| /2 width=1 by lprs_inv_TC/
| /2 width=3 by lpr_conf/
]
qed-.
