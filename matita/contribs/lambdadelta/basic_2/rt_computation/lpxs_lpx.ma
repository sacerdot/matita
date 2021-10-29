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

include "static_2/relocation/lex_tc.ma".
include "basic_2/rt_computation/cpxs_lpx.ma".
include "basic_2/rt_computation/lpxs.ma".

(* EXTENDED PARALLEL RT-COMPUTATION FOR FULL LOCAL ENVIRONMENTS *************)

(* Properties with extended rt-transition for full local environments *******)

lemma lpx_lpxs (G):
      ∀L1,L2. ❨G,L1❩ ⊢ ⬈ L2 → ❨G,L1❩ ⊢ ⬈* L2.
/3 width=3 by lpx_cpxs_trans, lex_CTC_inj/ qed.

(* Basic_2A1: was: lpxs_strap2 *)
lemma lpxs_step_sn (G):
      ∀L1,L. ❨G,L1❩ ⊢ ⬈ L →
      ∀L2. ❨G,L❩ ⊢ ⬈* L2 → ❨G,L1❩ ⊢ ⬈* L2.
/3 width=3 by lpx_cpxs_trans, lex_CTC_step_sn/ qed-.

(* Basic_2A1: was: lpxs_strap1 *)
lemma lpxs_step_dx (G):
      ∀L1,L. ❨G,L1❩ ⊢ ⬈* L →
      ∀L2. ❨G,L❩ ⊢ ⬈ L2 → ❨G,L1❩ ⊢ ⬈* L2.
/3 width=3 by lpx_cpxs_trans, lex_CTC_step_dx/ qed-.

(* Eliminators with extended rt-transition for full local environments ******)

(* Basic_2A1: was: lpxs_ind_dx *)
lemma lpxs_ind_sn (G) (L2) (Q:predicate …):
      Q L2 →
      (∀L1,L. ❨G,L1❩ ⊢ ⬈ L → ❨G,L❩ ⊢ ⬈* L2 → Q L → Q L1) →
      ∀L1. ❨G,L1❩ ⊢ ⬈* L2 → Q L1.
/3 width=7 by lpx_cpxs_trans, cpx_refl, lex_CTC_ind_sn/ qed-.

(* Basic_2A1: was: lpxs_ind *)
lemma lpxs_ind_dx (G) (L1) (Q:predicate …):
      Q L1 →
      (∀L,L2. ❨G,L1❩ ⊢ ⬈* L → ❨G,L❩ ⊢ ⬈ L2 → Q L → Q L2) →
      ∀L2. ❨G,L1❩ ⊢ ⬈* L2 → Q L2.
/3 width=7 by lpx_cpxs_trans, cpx_refl, lex_CTC_ind_dx/ qed-.

(* Properties with context-sensitive extended rt-transition for terms *******)

lemma lpxs_cpx_trans (G):
      s_r_transitive … (cpx G) (λ_.lpxs G).
#G #L2 #T1 #T2 #HT12 #L1 #HL12
@(s_r_trans_CTC2 ???????? HT12) -HT12
/2 width=4 by lpx_cpxs_trans, lex_inv_CTC/
qed-.

(* Properties with context-sensitive extended rt-computation for terms ******)

(* Note: alternative proof by s_r_to_s_rs_trans *)
lemma lpxs_cpxs_trans (G):
      s_rs_transitive … (cpx G) (λ_.lpxs G).
#G @s_r_trans_CTC1 /2 width=3 by lpxs_cpx_trans/
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: was: lpxs_pair2 *)
lemma lpxs_pair_dx (G):
      ∀L1,L2. ❨G,L1❩ ⊢ ⬈* L2 →
      ∀V1,V2. ❨G,L2❩ ⊢ V1 ⬈* V2 →
      ∀I. ❨G,L1.ⓑ[I]V1❩ ⊢ ⬈* L2.ⓑ[I]V2.
/3 width=3 by lpxs_pair, lpxs_cpxs_trans/ qed.
