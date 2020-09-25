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

include "basic_2/rt_computation/cpxs.ma".
include "basic_2/rt_computation/fpbs_feqg.ma".
include "basic_2/rt_computation/fpbs_fqus.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with extended context-sensitive parallel rt-computation *******)

lemma cpxs_fpbs:
      ∀G,L,T1,T2. ❪G,L❫ ⊢ T1 ⬈* T2 → ❪G,L,T1❫ ≥ ❪G,L,T2❫.
#G #L #T1 #T2 #H @(cpxs_ind … H) -T2
/3 width=5 by cpx_fpb, fpbs_strap1/
qed.

lemma fpbs_cpxs_trans:
      ∀G1,G,L1,L,T1,T. ❪G1,L1,T1❫ ≥ ❪G,L,T❫ →
      ∀T2. ❪G,L❫ ⊢ T ⬈* T2 → ❪G1,L1,T1❫ ≥ ❪G,L,T2❫.
#G1 #G #L1 #L #T1 #T #H1 #T2 #H @(cpxs_ind … H) -T2
/3 width=5 by fpbs_strap1, cpx_fpb/
qed-.

lemma cpxs_fpbs_trans:
      ∀G1,G2,L1,L2,T,T2. ❪G1,L1,T❫ ≥ ❪G2,L2,T2❫ →
      ∀T1. ❪G1,L1❫ ⊢ T1 ⬈* T → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
#G1 #G2 #L1 #L2 #T #T2 #H1 #T1 #H @(cpxs_ind_dx … H) -T1
/3 width=5 by fpbs_strap2, cpx_fpb/
qed-.

lemma cpxs_teqg_fpbs_trans (S):
      reflexive … S → symmetric … S →
      ∀G1,L1,T1,T. ❪G1,L1❫ ⊢ T1 ⬈* T → ∀T0. T ≛[S] T0 →
      ∀G2,L2,T2. ❪G1,L1,T0❫ ≥ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/3 width=6 by cpxs_fpbs_trans, teqg_fpbs_trans/ qed-.

lemma cpxs_teqg_fpbs (S):
      reflexive … S → symmetric … S →
      ∀G,L,T1,T. ❪G,L❫ ⊢ T1 ⬈* T →
      ∀T2. T ≛[S] T2 → ❪G,L,T1❫ ≥ ❪G,L,T2❫.
/4 width=5 by cpxs_fpbs_trans, feqg_fpbs, teqg_feqg/ qed.

(* Properties with plus-iterated structural successor for closures **********)

lemma cpxs_fqup_fpbs:
      ∀G1,L1,T1,T. ❪G1,L1❫ ⊢ T1 ⬈* T →
      ∀G2,L2,T2. ❪G1,L1,T❫ ⬂+ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/3 width=5 by fpbs_fqup_trans, cpxs_fpbs/ qed.

(* Properties with star-iterated structural successor for closures **********)

lemma cpxs_fqus_fpbs:
      ∀G1,L1,T1,T. ❪G1,L1❫ ⊢ T1 ⬈* T →
      ∀G2,L2,T2. ❪G1,L1,T❫ ⬂* ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/3 width=5 by fpbs_fqus_trans, cpxs_fpbs/ qed.
