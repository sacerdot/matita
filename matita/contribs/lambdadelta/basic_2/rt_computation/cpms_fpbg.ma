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

include "basic_2/rt_computation/fpbg_fqup.ma".
include "basic_2/rt_computation/fpbg_cpxs.ma".
include "basic_2/rt_computation/cpms_fpbs.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Forward lemmas with proper parallel rst-computation for closures *********)

lemma cpms_tneqx_fwd_fpbg (h) (n):
      ∀G,L,T1,T2. ❪G,L❫ ⊢ T1 ➡*[h,n] T2 →
      (T1 ≛ T2 → ⊥) → ❪G,L,T1❫ >[h] ❪G,L,T2❫.
/3 width=2 by cpms_fwd_cpxs, cpxs_tneqx_fpbg/ qed-.

lemma fpbg_cpms_trans (h) (n):
      ∀G1,G2,L1,L2,T1,T. ❪G1,L1,T1❫ >[h] ❪G2,L2,T❫ →
      ∀T2. ❪G2,L2❫ ⊢ T ➡*[h,n] T2 → ❪G1,L1,T1❫ >[h] ❪G2,L2,T2❫.
/3 width=5 by fpbg_fpbs_trans, cpms_fwd_fpbs/ qed-.

lemma cpms_fpbg_trans (h) (n):
      ∀G1,L1,T1,T. ❪G1,L1❫ ⊢ T1 ➡*[h,n] T →
      ∀G2,L2,T2. ❪G1,L1,T❫ >[h] ❪G2,L2,T2❫ → ❪G1,L1,T1❫ >[h] ❪G2,L2,T2❫.
/3 width=5 by fpbs_fpbg_trans, cpms_fwd_fpbs/ qed-.

lemma fqup_cpms_fwd_fpbg (h):
      ∀G1,G2,L1,L2,T1,T. ❪G1,L1,T1❫ ⬂+ ❪G2,L2,T❫ →
      ∀n,T2. ❪G2,L2❫ ⊢ T ➡*[h,n] T2 → ❪G1,L1,T1❫ >[h] ❪G2,L2,T2❫.
/3 width=5 by cpms_fwd_fpbs, fqup_fpbg, fpbg_fpbs_trans/ qed-.

lemma cpm_tneqx_cpm_cpms_teqx_sym_fwd_fpbg (h) (G) (L) (T1):
      ∀n1,T. ❪G,L❫ ⊢ T1 ➡[h,n1] T → (T1 ≛ T → ⊥) →
      ∀n2,T2. ❪G,L❫⊢ T ➡*[h,n2] T2 → T1 ≛ T2 → ❪G,L,T1❫ >[h] ❪G,L,T1❫.
#h #G #L #T1 #n1 #T #H1T1 #H2T1 #n2 #T2 #H1T2 #H2T12
/4 width=7 by cpms_fwd_fpbs, cpm_fpb, fpbs_teqx_trans, teqx_sym, ex2_3_intro/
qed-.
